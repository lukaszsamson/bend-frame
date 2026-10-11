# PROOF_fused.bend -- proofs of LAWS.bend section 18 (v0.2 T4.1, DESIGN.md 16.3 F1-F6): the fused,
# borrowing kernels of src/kernels.bend equal the unfused passes they replace and hand their inputs
# back.
#
# Two shapes of proof:
#  - SIMULATION (a term equality between two loops run from the same state): where the fused loop
#    writes exactly what an existing proven kernel writes, in the same order (map_pb vs map_p, zipb
#    vs zip, zipv's validity vs zip with U32.and, compact3 / compact4 vs one compact_keep per buffer
#    and the cursor vs popcount's fold), one induction shows the fused loop's record IS the existing
#    kernels' outputs and the inputs themselves; the content theorems of PROOF_contents (zip_cell,
#    map_cell, compact_contents, popcount_sum) then apply unchanged. No cell reasoning, no
#    well-formedness.
#  - CELL CHAINS (PROOF_contents' map / zip loop lemmas, re-run): where the fused loop writes a cell
#    no existing kernel writes (map_p's f(p, a[k]); zipv's value and pred_count's mask, each a
#    function of four reads), the forall invariant "every row so far holds its cell" is carried
#    through the loop exactly as map_go / zip_go do (set_other_w, same_false_lt, IncLtU).
# The kept count of pred_count is the modulo sum of the mask words: the loop's running sum is
# described over the inputs (PSum), and each step's word is the mask's final cell by the cell
# theorem itself, re-run on clones of the inputs (a forall is affine; a theorem is not); FSum is
# then popcount's own spec, and two FSum chains over one array have one result.
import Base
import ./src/dtype.bend as D
import ./src/err.bend as E
import ./src/kernels.bend as K
import ./src/column.bend as C
import ./src/strs.bend as ST
import ./src/eval.bend as V
import ./LAWS.bend as Laws
import ./PROOF_lib.bend as L
import ./PROOF_kernels.bend as PK
import ./PROOF_bits.bend as B
import ./PROOF_contents.bend as PC
import ./PROOF_inplace.bend as PI

# ---- a broadcast column reads its value everywhere ----------------------------------------------

def rd_new(-T: Data, d: Nat, +v: T, +n: U32, +i: U32, z: Bool) -> {Laws.rd(T, Array.new(T, d, v), n, i, z) == v : T}:
  match d z:
    case 0n _:
      {==}
    case 1n+p True{}:
      rd_new(T, p, v, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n))))
    case 1n+p False{}:
      rd_new(T, p, v, U32.shr(n), U32.sub(i, U32.shr(n)), U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))

def rd_at_new_k(-T: Data, +d: Nat, +v: T, +k: U32, w: &b: Array<T> -> &n: U32 -> {b == Array.new(T, d, v) : Array<T>} & {Array.size(T, Array.new(T, d, v)) == (b, n) : Array<T> & U32} & {Laws.slots(T, b) == n : U32})
  -> {Laws.rd_at(T, Array.new(T, d, v), k) == v : T}:
  (b, +n, eb, es, sl) = w
  %Equal.sym(Array<T> & U32, Array.size(T, Array.new(T, d, v)), (b, n), es) : {Laws.rd_size(T, k, _) == v : T}
  %Equal.sym(Array<T>, b, Array.new(T, d, v), eb) : {Laws.rd(T, _, n, U32.and(k, U32.sub(n, 1)), U32.is_lt(U32.and(k, U32.sub(n, 1)), U32.shr(n))) == v : T}
  rd_new(T, d, v, n, U32.and(k, U32.sub(n, 1)), U32.is_lt(U32.and(k, U32.sub(n, 1)), U32.shr(n)))

# rd_at of Array.new(d, v) is v at every index (Eval.const_col's broadcast column)
def rd_at_new(-T: Data, +d: Nat, +v: T, +k: U32) -> {Laws.rd_at(T, Array.new(T, d, v), k) == v : T}:
  rd_at_new_k(T, d, v, k, PK.size_same(T, Array.new(T, d, v)))

# ---- Kernel.map_p: out[k] == f(p, a[k]) (PROOF_contents' map chain with the parameter p) ----------

def MPHyp(~T: Data, ~P: Data, ~U: Data, ~f: P -> T -> U, +j: U32, +p: P, +d: Nat, -a: Array<T>, -out: Array<U>) -> Type:
  @k: U32 -> {U32.is_lt(k, j) == True{} : Bool} -> {Laws.rdN(U, d, out, k) == f(p, Laws.rd_at(T, a, k)) : U}

def MPRes(~T: Data, ~P: Data, ~U: Data, ~f: P -> T -> U, +p: P, +d: Nat, -a: Array<T>, o: Array<U>, +bound: U32) -> Type:
  Laws.WFArray(U, d, o) & (@k: U32 -> {U32.is_lt(k, bound) == True{} : Bool} -> {Laws.rdN(U, d, o, k) == f(p, Laws.rd_at(T, a, k)) : U})

def MPGoal(~T: Data, ~P: Data, ~U: Data, ~f: P -> T -> U, fl: Nat, +j: U32, +p: P, +d: Nat, -a: Array<T>, -out: Array<U>, -r: Array<T> & T) -> Type:
  MPHyp(~T, ~P, ~U, ~f, j, p, d, a, out) -> &o: Array<U> -> {K.Kernel.map_p.go(~T, ~P, ~U, ~f, fl, j, p, out, r) == o : Array<U>} & MPRes(~T, ~P, ~U, ~f, p, d, a, o, Laws.addn(j, fl))

def MPSet(~T: Data, ~P: Data, ~U: Data, ~f: P -> T -> U, q: Nat, +j: U32, +p: P, +d: Nat, -a: Array<T>, -out: Array<U>, +y: U) -> Type:
  MPHyp(~T, ~P, ~U, ~f, j, p, d, a, out) -> &o: Array<U> -> {K.Kernel.map_p.go(~T, ~P, ~U, ~f, q, U32.inc(j), p, Array.set(U, out, j, y), Array.get(T, a, U32.inc(j))) == o : Array<U>} & MPRes(~T, ~P, ~U, ~f, p, d, a, o, Laws.addn(j, 1n+q))

def MPC(~T: Data, ~P: Data, ~U: Data, ~f: P -> T -> U, q: Nat, +j: U32, +p: P, +d: Nat, -a: Array<T>, -out: Array<U>, -c: Array<U>, +bound: U32) -> Type:
  MPHyp(~T, ~P, ~U, ~f, j, p, d, a, out) -> &o: Array<U> -> {K.Kernel.map_p.go(~T, ~P, ~U, ~f, q, U32.inc(j), p, c, Array.get(T, a, U32.inc(j))) == o : Array<U>} & MPRes(~T, ~P, ~U, ~f, p, d, a, o, bound)

def mpnext_lt(~T: Data, ~P: Data, ~U: Data, ~f: P -> T -> U, +d: Nat, +j: U32, +k: U32, +p: P, -a: Array<T>, -out: Array<U>, -c: Array<U>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +y: U, g: MPHyp(~T, ~P, ~U, ~f, j, p, d, a, out),
  fj: @k2: U32 -> {Laws.rdN(U, d, c, k2) == Bool.pick(U, Laws.same_at(d, j, k2), y, Laws.rdN(U, d, out, k2)) : U}, +lt: {U32.is_lt(k, j) == True{} : Bool})
  -> {Laws.rdN(U, d, c, k) == f(p, Laws.rd_at(T, a, k)) : U}:
  %Equal.sym(U, Laws.rdN(U, d, c, k), Bool.pick(U, Laws.same_at(d, j, k), y, Laws.rdN(U, d, out, k)), fj(k)) : {_ == f(p, Laws.rd_at(T, a, k)) : U}
  %Equal.sym(Bool, Laws.same_at(d, j, k), False{}, PC.same_false_lt(d, j, k, hj, lt)) : {Bool.pick(U, _, y, Laws.rdN(U, d, out, k)) == f(p, Laws.rd_at(T, a, k)) : U}
  g(k, lt)

def mpnext_b(~T: Data, ~P: Data, ~U: Data, ~f: P -> T -> U, b: Bool, +d: Nat, +j: U32, +k: U32, +p: P, -a: Array<T>, -out: Array<U>, -c: Array<U>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +x: T, ex: {x == Laws.rd_at(T, a, j) : T}, +y: U, ey: {y == f(p, x) : U}, g: MPHyp(~T, ~P, ~U, ~f, j, p, d, a, out),
  fj: @k2: U32 -> {Laws.rdN(U, d, c, k2) == Bool.pick(U, Laws.same_at(d, j, k2), y, Laws.rdN(U, d, out, k2)) : U}, s: PC.IncLtU(b, k, j))
  -> {Laws.rdN(U, d, c, k) == f(p, Laws.rd_at(T, a, k)) : U}:
  match b:
    case True{}:
      mpnext_lt(~T, ~P, ~U, ~f, d, j, k, p, a, out, c, hj, y, g, fj, s)
    case False{}:
      %Equal.sym(U32, k, j, s) : {Laws.rdN(U, d, c, _) == f(p, Laws.rd_at(T, a, _)) : U}
      %Equal.sym(U, Laws.rdN(U, d, c, j), Bool.pick(U, Laws.same_at(d, j, j), y, Laws.rdN(U, d, out, j)), fj(j)) : {_ == f(p, Laws.rd_at(T, a, j)) : U}
      %Equal.sym(Bool, Laws.same_at(d, j, j), True{}, PC.same_at_refl(d, j)) : {Bool.pick(U, _, y, Laws.rdN(U, d, out, j)) == f(p, Laws.rd_at(T, a, j)) : U}
      Equal.trans(U, y, f(p, x), f(p, Laws.rd_at(T, a, j)), ey, Equal.cong(T, U, v => f(p, v), x, Laws.rd_at(T, a, j), ex))

def mpnext_k(~T: Data, ~P: Data, ~U: Data, ~f: P -> T -> U, +d: Nat, +j: U32, +k: U32, +p: P, -a: Array<T>, -out: Array<U>, -c: Array<U>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +x: T, ex: {x == Laws.rd_at(T, a, j) : T}, +y: U, ey: {y == f(p, x) : U}, g: MPHyp(~T, ~P, ~U, ~f, j, p, d, a, out),
  fj: @k2: U32 -> {Laws.rdN(U, d, c, k2) == Bool.pick(U, Laws.same_at(d, j, k2), y, Laws.rdN(U, d, out, k2)) : U}, w: &b: Bool -> PC.IncLtU(b, k, j))
  -> {Laws.rdN(U, d, c, k) == f(p, Laws.rd_at(T, a, k)) : U}:
  (b, s) = w
  mpnext_b(~T, ~P, ~U, ~f, b, d, j, k, p, a, out, c, hj, x, ex, y, ey, g, fj, s)

def mpnext(~T: Data, ~P: Data, ~U: Data, ~f: P -> T -> U, +d: Nat, +j: U32, +p: P, -a: Array<T>, -out: Array<U>, -c: Array<U>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +x: T, +ex: {x == Laws.rd_at(T, a, j) : T}, +y: U, +ey: {y == f(p, x) : U}, g: MPHyp(~T, ~P, ~U, ~f, j, p, d, a, out),
  fj: @k2: U32 -> {Laws.rdN(U, d, c, k2) == Bool.pick(U, Laws.same_at(d, j, k2), y, Laws.rdN(U, d, out, k2)) : U})
  -> MPHyp(~T, ~P, ~U, ~f, U32.inc(j), p, d, a, c):
  +k => hk => mpnext_k(~T, ~P, ~U, ~f, d, j, k, p, a, out, c, hj, x, ex, y, ey, g, fj, PC.inc_lt_u(k, j, hk))

def mp_step2(~T: Data, ~P: Data, ~U: Data, ~f: P -> T -> U, q: Nat, +j: U32, +p: P, +d: Nat, a: Array<T>, -out: Array<U>, +x: T, +ex: {x == Laws.rd_at(T, a, j) : T}, +y: U, +ey: {y == f(p, x) : U}, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, room: Laws.Room(d, U32.inc(j), q),
  ih: @a2: Array<T> -> @c: Array<U> -> Laws.WFArray(U, d, c) -> Laws.Room(d, U32.inc(j), q) -> MPGoal(~T, ~P, ~U, ~f, q, U32.inc(j), p, d, a2, c, Array.get(T, a2, U32.inc(j))),
  w: &c: Array<U> -> {Array.set(U, out, j, y) == c : Array<U>} & Laws.WFArray(U, d, c) & (@k2: U32 -> {Laws.rdN(U, d, c, k2) == Bool.pick(U, Laws.same_at(d, j, k2), y, Laws.rdN(U, d, out, k2)) : U}) & (@k2: U32 -> {Laws.rd_at(U, out, k2) == Laws.rdN(U, d, out, k2) : U}))
  -> MPSet(~T, ~P, ~U, ~f, q, j, p, d, a, out, y):
  (c, ec, wc, fj, cv) = w
  %Equal.sym(Array<U>, Array.set(U, out, j, y), c, ec) : MPC(~T, ~P, ~U, ~f, q, j, p, d, a, out, _, Laws.addn(j, 1n+q))
  %PC.addn_inc(j, q) : MPC(~T, ~P, ~U, ~f, q, j, p, d, a, out, c, _)
  g => ih(a, c, wc, room)(mpnext(~T, ~P, ~U, ~f, d, j, p, a, out, c, hj, x, ex, y, ey, g, fj))

def mp_step1(~T: Data, ~P: Data, ~U: Data, ~f: P -> T -> U, q: Nat, +j: U32, +p: P, +d: Nat, -a: Array<T>, out: Array<U>, wf: Laws.WFArray(U, d, out), room: Laws.Room(d, j, 1n+q),
  ih: @a2: Array<T> -> @c: Array<U> -> Laws.WFArray(U, d, c) -> Laws.Room(d, U32.inc(j), q) -> MPGoal(~T, ~P, ~U, ~f, q, U32.inc(j), p, d, a2, c, Array.get(T, a2, U32.inc(j))),
  w: &b: Array<T> -> &x: T -> {b == a : Array<T>} & {Array.get(T, a, j) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, j) : T})
  -> MPGoal(~T, ~P, ~U, ~f, 1n+q, j, p, d, a, out, Array.get(T, a, j)):
  (hj, room2) = room
  (a2, +x, +ea, e1, ex) = w
  %Equal.sym(Array<T> & T, Array.get(T, a, j), (a, x), e1) : MPGoal(~T, ~P, ~U, ~f, 1n+q, j, p, d, a, out, _)
  %ea : MPGoal(~T, ~P, ~U, ~f, 1n+q, j, p, d, _, out, (_, x))
  mp_step2(~T, ~P, ~U, ~f, q, j, p, d, a2, out, x, Equal.trans(T, x, Laws.rd_at(T, a, j), Laws.rd_at(T, a2, j), ex, Equal.sym(T, Laws.rd_at(T, a2, j), Laws.rd_at(T, a, j), Equal.cong(Array<T>, T, r => Laws.rd_at(T, r, j), a2, a, ea))), f(p, x), {==}, hj, room2, ih, PC.set_other_w(U, d, out, j, f(p, x), wf))

def mp_zero(~T: Data, ~P: Data, ~U: Data, ~f: P -> T -> U, +j: U32, +p: P, +d: Nat, -a: Array<T>, out: Array<U>, wf: Laws.WFArray(U, d, out),
  w: &b: Array<T> -> &x: T -> {b == a : Array<T>} & {Array.get(T, a, j) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, j) : T})
  -> MPGoal(~T, ~P, ~U, ~f, 0n, j, p, d, a, out, Array.get(T, a, j)):
  (a2, +x, ea, e1, ex) = w
  %Equal.sym(Array<T> & T, Array.get(T, a, j), (a, x), e1) : MPGoal(~T, ~P, ~U, ~f, 0n, j, p, d, a, out, _)
  g => (out, {==}, wf, g)

# Kernel.map_p.go: every k < addn(j, fl) holds f(p, a[k]) afterwards
def mp_go(~T: Data, ~P: Data, ~U: Data, ~f: P -> T -> U, fl: Nat, +j: U32, +p: P, +d: Nat, a: Array<T>, out: Array<U>, wf: Laws.WFArray(U, d, out), room: Laws.Room(d, j, fl)) -> MPGoal(~T, ~P, ~U, ~f, fl, j, p, d, a, out, Array.get(T, a, j)):
  match fl:
    case 0n:
      mp_zero(~T, ~P, ~U, ~f, j, p, d, a, out, wf, PC.get_w(T, a, j))
    case 1n++q:
      mp_step1(~T, ~P, ~U, ~f, q, j, p, d, a, out, wf, room, a2 => c => wc => room2 => mp_go(~T, ~P, ~U, ~f, q, U32.inc(j), p, d, a2, c, wc, room2), PC.get_w(T, a, j))

def mphyp0(~T: Data, ~P: Data, ~U: Data, ~f: P -> T -> U, +p: P, +d: Nat, -a: Array<T>, -out: Array<U>) -> MPHyp(~T, ~P, ~U, ~f, 0, p, d, a, out):
  +k => hk => Empty.absurd({Laws.rdN(U, d, out, k) == f(p, Laws.rd_at(T, a, k)) : U}, PC.lt0(k, hk))

def mp_fin(~T: Data, ~P: Data, ~U: Data, ~f: P -> T -> U, +d: Nat, +n: U32, +p: P, -a: Array<T>, +z: U, +k: U32, hk: {U32.is_lt(k, n) == True{} : Bool},
  w: &o: Array<U> -> {K.Kernel.map_p.go(~T, ~P, ~U, ~f, U32.to_nat(n), 0, p, Array.new(U, d, z), Array.get(T, a, 0)) == o : Array<U>} & MPRes(~T, ~P, ~U, ~f, p, d, a, o, Laws.addn(0, U32.to_nat(n))))
  -> {Laws.rd_at(U, K.Kernel.map_p.go(~T, ~P, ~U, ~f, U32.to_nat(n), 0, p, Array.new(U, d, z), Array.get(T, a, 0)), k) == f(p, Laws.rd_at(T, a, k)) : U}:
  (o, eq, wo, spec) = w
  %Equal.sym(Array<U>, K.Kernel.map_p.go(~T, ~P, ~U, ~f, U32.to_nat(n), 0, p, Array.new(U, d, z), Array.get(T, a, 0)), o, eq) : {Laws.rd_at(U, _, k) == f(p, Laws.rd_at(T, a, k)) : U}
  %Equal.sym(U, Laws.rd_at(U, o, k), Laws.rdN(U, d, o, k), Laws.rd_at_wf(U, d, o, k, wo)) : {_ == f(p, Laws.rd_at(T, a, k)) : U}
  spec(k, (%Equal.sym(U32, Laws.addn(0, U32.to_nat(n)), n, B.addn_to_nat(n)) : {U32.is_lt(k, _) == True{} : Bool}; hk))

# Kernel.map_p(n, d, a, p, z): out[k] == f(p, a[k]) for k < n when n <= 2^d
def mp_cell(~T: Data, ~P: Data, ~U: Data, ~f: P -> T -> U, +d: Nat, +n: U32, a: Array<T>, +p: P, +z: U, +k: U32, fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, hk: {U32.is_lt(k, n) == True{} : Bool}) -> {Laws.rd_at(U, K.Kernel.map_p.go(~T, ~P, ~U, ~f, U32.to_nat(n), 0, p, Array.new(U, d, z), Array.get(T, a, 0)), k) == f(p, Laws.rd_at(T, a, k)) : U}:
  mp_fin(~T, ~P, ~U, ~f, d, n, p, a, z, k, hk, mp_go(~T, ~P, ~U, ~f, U32.to_nat(n), 0, p, d, a, Array.new(U, d, z), Laws.wf_new(U, d, z), B.room_from(d, n, fits))(mphyp0(~T, ~P, ~U, ~f, p, d, a, Array.new(U, d, z))))

def Laws.map_p_cell(d, n, a, lit, z, k, fits, hk):
  mp_cell(~U32, ~U32, ~U32, ~(p => w => Bool.to_u32(U32.is_gt(w, p))), d, n, a, lit, z, k, fits, hk)

# ---- Kernel.map_pb IS Kernel.map_p with the operand handed back (simulation) ----------------------

def MPBSim(~T: Data, ~P: Data, ~U: Data, ~f: P -> T -> U, fl: Nat, +j: U32, +p: P, -out: Array<U>, -a: Array<T>) -> Type:
  {K.Kernel.map_pb.go(~T, ~P, ~U, ~f, fl, j, p, out, Array.get(T, a, j)) == (K.Kernel.map_p.go(~T, ~P, ~U, ~f, fl, j, p, out, Array.get(T, a, j)), a) : Array<U> & Array<T>}

def mpb_zero(~T: Data, ~P: Data, ~U: Data, ~f: P -> T -> U, +j: U32, +p: P, -out: Array<U>, -a: Array<T>,
  w: &b: Array<T> -> &x: T -> {b == a : Array<T>} & {Array.get(T, a, j) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, j) : T})
  -> MPBSim(~T, ~P, ~U, ~f, 0n, j, p, out, a):
  (a2, +x, ea, e1, ex) = w
  %Equal.sym(Array<T> & T, Array.get(T, a, j), (a, x), e1) : {K.Kernel.map_pb.go(~T, ~P, ~U, ~f, 0n, j, p, out, _) == (K.Kernel.map_p.go(~T, ~P, ~U, ~f, 0n, j, p, out, _), a) : Array<U> & Array<T>}
  {==}

def mpb_step(~T: Data, ~P: Data, ~U: Data, ~f: P -> T -> U, q: Nat, +j: U32, +p: P, out: Array<U>, -a: Array<T>,
  w: &b: Array<T> -> &x: T -> {b == a : Array<T>} & {Array.get(T, a, j) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, j) : T},
  ih: @a2: Array<T> -> @c: Array<U> -> MPBSim(~T, ~P, ~U, ~f, q, U32.inc(j), p, c, a2))
  -> MPBSim(~T, ~P, ~U, ~f, 1n+q, j, p, out, a):
  (a2, +x, +ea, e1, ex) = w
  %Equal.sym(Array<T> & T, Array.get(T, a, j), (a, x), e1) : {K.Kernel.map_pb.go(~T, ~P, ~U, ~f, 1n+q, j, p, out, _) == (K.Kernel.map_p.go(~T, ~P, ~U, ~f, 1n+q, j, p, out, _), a) : Array<U> & Array<T>}
  %ea : {K.Kernel.map_pb.go(~T, ~P, ~U, ~f, 1n+q, j, p, out, (_, x)) == (K.Kernel.map_p.go(~T, ~P, ~U, ~f, 1n+q, j, p, out, (_, x)), _) : Array<U> & Array<T>}
  ih(a2, Array.set(U, out, j, f(p, x)))

def mpb_sim(~T: Data, ~P: Data, ~U: Data, ~f: P -> T -> U, fl: Nat, +j: U32, +p: P, out: Array<U>, a: Array<T>) -> MPBSim(~T, ~P, ~U, ~f, fl, j, p, out, a):
  match fl:
    case 0n:
      mpb_zero(~T, ~P, ~U, ~f, j, p, out, a, PC.get_w(T, a, j))
    case 1n++q:
      mpb_step(~T, ~P, ~U, ~f, q, j, p, out, a, PC.get_w(T, a, j), a2 => c => mpb_sim(~T, ~P, ~U, ~f, q, U32.inc(j), p, c, a2))

def Laws.map_pb_unfused(d, n, a, lit, z):
  mpb_sim(~U32, ~U32, ~U32, ~(p => w => Bool.to_u32(U32.is_gt(w, p))), U32.to_nat(n), 0, lit, Array.new(U32, d, z), a)

# map_pb's output cell: the simulation on one clone of a, map_p's cell on the other
def mpb_cell_k(~T: Data, ~P: Data, ~U: Data, ~f: P -> T -> U, +d: Nat, +n: U32, -a: Array<T>, +p: P, +z: U, +k: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, hk: {U32.is_lt(k, n) == True{} : Bool},
  w: &a1: Array<T> -> &a2: Array<T> -> {a1 == a : Array<T>} & {a2 == a : Array<T>})
  -> {Laws.rd_at(U, Pair.fst(Array<U>, Array<T>, K.Kernel.map_pb.go(~T, ~P, ~U, ~f, U32.to_nat(n), 0, p, Array.new(U, d, z), Array.get(T, a, 0))), k) == f(p, Laws.rd_at(T, a, k)) : U}:
  (a1, a2, +e1, e2) = w
  %e1 : {Laws.rd_at(U, Pair.fst(Array<U>, Array<T>, K.Kernel.map_pb.go(~T, ~P, ~U, ~f, U32.to_nat(n), 0, p, Array.new(U, d, z), Array.get(T, _, 0))), k) == f(p, Laws.rd_at(T, a, k)) : U}
  %Equal.sym(Array<U> & Array<T>, K.Kernel.map_pb.go(~T, ~P, ~U, ~f, U32.to_nat(n), 0, p, Array.new(U, d, z), Array.get(T, a1, 0)), (K.Kernel.map_p.go(~T, ~P, ~U, ~f, U32.to_nat(n), 0, p, Array.new(U, d, z), Array.get(T, a1, 0)), a1), mpb_sim(~T, ~P, ~U, ~f, U32.to_nat(n), 0, p, Array.new(U, d, z), a1)) : {Laws.rd_at(U, Pair.fst(Array<U>, Array<T>, _), k) == f(p, Laws.rd_at(T, a, k)) : U}
  %Equal.sym(Array<T>, a1, a, e1) : {Laws.rd_at(U, K.Kernel.map_p.go(~T, ~P, ~U, ~f, U32.to_nat(n), 0, p, Array.new(U, d, z), Array.get(T, _, 0)), k) == f(p, Laws.rd_at(T, a, k)) : U}
  %e2 : {Laws.rd_at(U, K.Kernel.map_p.go(~T, ~P, ~U, ~f, U32.to_nat(n), 0, p, Array.new(U, d, z), Array.get(T, _, 0)), k) == f(p, Laws.rd_at(T, _, k)) : U}
  mp_cell(~T, ~P, ~U, ~f, d, n, a2, p, z, k, fits, hk)

def mpb_cell(~T: Data, ~P: Data, ~U: Data, ~f: P -> T -> U, +d: Nat, +n: U32, a: Array<T>, +p: P, +z: U, +k: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, hk: {U32.is_lt(k, n) == True{} : Bool})
  -> {Laws.rd_at(U, Pair.fst(Array<U>, Array<T>, K.Kernel.map_pb.go(~T, ~P, ~U, ~f, U32.to_nat(n), 0, p, Array.new(U, d, z), Array.get(T, a, 0))), k) == f(p, Laws.rd_at(T, a, k)) : U}:
  mpb_cell_k(~T, ~P, ~U, ~f, d, n, a, p, z, k, fits, hk, PC.clone_eq(T, a))

# F1 against the broadcast: map_pb's cell on one clone of a, zip_cell over the broadcast column (which
# reads lit everywhere: rd_at_new) on the other
def bcu_k(+d: Nat, +n: U32, -a: Array<U32>, +lit: U32, +z: U32, +k: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hk: {U32.is_lt(k, n) == True{} : Bool},
  w: &a1: Array<U32> -> &a2: Array<U32> -> {a1 == a : Array<U32>} & {a2 == a : Array<U32>})
  -> {Laws.rd_at(U32, Pair.fst(Array<U32>, Array<U32>, K.Kernel.map_pb(~U32, ~U32, ~U32, ~(p => w => Bool.to_u32(U32.is_gt(w, p))), n, d, a, lit, z)), k) == Laws.rd_at(U32, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, a, Array.new(U32, d, lit), z), k) : U32}:
  (a1, a2, e1, e2) = w
  Equal.trans(U32, Laws.rd_at(U32, Pair.fst(Array<U32>, Array<U32>, K.Kernel.map_pb(~U32, ~U32, ~U32, ~(p => w => Bool.to_u32(U32.is_gt(w, p))), n, d, a, lit, z)), k), Bool.to_u32(U32.is_gt(Laws.rd_at(U32, a, k), lit)), Laws.rd_at(U32, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, a, Array.new(U32, d, lit), z), k),
    (%e1 : {Laws.rd_at(U32, Pair.fst(Array<U32>, Array<U32>, K.Kernel.map_pb(~U32, ~U32, ~U32, ~(p => w => Bool.to_u32(U32.is_gt(w, p))), n, d, _, lit, z)), k) == Bool.to_u32(U32.is_gt(Laws.rd_at(U32, _, k), lit)) : U32}; mpb_cell(~U32, ~U32, ~U32, ~(p => w => Bool.to_u32(U32.is_gt(w, p))), d, n, a1, lit, z, k, fits, hk)),
    Equal.sym(U32, Laws.rd_at(U32, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, a, Array.new(U32, d, lit), z), k), Bool.to_u32(U32.is_gt(Laws.rd_at(U32, a, k), lit)),
      (%e2 : {Laws.rd_at(U32, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, _, Array.new(U32, d, lit), z), k) == Bool.to_u32(U32.is_gt(Laws.rd_at(U32, _, k), lit)) : U32};
       %rd_at_new(U32, d, lit, k) : {Laws.rd_at(U32, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, a2, Array.new(U32, d, lit), z), k) == Bool.to_u32(U32.is_gt(Laws.rd_at(U32, a2, k), _)) : U32};
       PC.zip_cell(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), d, n, a2, Array.new(U32, d, lit), z, k, fits, hk))))

def Laws.map_pb_bcast(d, n, a, lit, z, k, fits, hk):
  bcu_k(d, n, a, lit, z, k, fits, hk, PC.clone_eq(U32, a))

def bcf_k(+d: Nat, +n: U32, -a: Array<F32>, +lit: F32, +z: F32, +k: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hk: {U32.is_lt(k, n) == True{} : Bool},
  w: &a1: Array<F32> -> &a2: Array<F32> -> {a1 == a : Array<F32>} & {a2 == a : Array<F32>})
  -> {Laws.rd_at(F32, Pair.fst(Array<F32>, Array<F32>, K.Kernel.map_pb(~F32, ~F32, ~F32, ~(p => x => F32.sub(p, x)), n, d, a, lit, z)), k) == Laws.rd_at(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.sub(x, y)), n, d, Array.new(F32, d, lit), a, z), k) : F32}:
  (a1, a2, e1, e2) = w
  Equal.trans(F32, Laws.rd_at(F32, Pair.fst(Array<F32>, Array<F32>, K.Kernel.map_pb(~F32, ~F32, ~F32, ~(p => x => F32.sub(p, x)), n, d, a, lit, z)), k), F32.sub(lit, Laws.rd_at(F32, a, k)), Laws.rd_at(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.sub(x, y)), n, d, Array.new(F32, d, lit), a, z), k),
    (%e1 : {Laws.rd_at(F32, Pair.fst(Array<F32>, Array<F32>, K.Kernel.map_pb(~F32, ~F32, ~F32, ~(p => x => F32.sub(p, x)), n, d, _, lit, z)), k) == F32.sub(lit, Laws.rd_at(F32, _, k)) : F32}; mpb_cell(~F32, ~F32, ~F32, ~(p => x => F32.sub(p, x)), d, n, a1, lit, z, k, fits, hk)),
    Equal.sym(F32, Laws.rd_at(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.sub(x, y)), n, d, Array.new(F32, d, lit), a, z), k), F32.sub(lit, Laws.rd_at(F32, a, k)),
      (%e2 : {Laws.rd_at(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.sub(x, y)), n, d, Array.new(F32, d, lit), _, z), k) == F32.sub(lit, Laws.rd_at(F32, _, k)) : F32};
       %rd_at_new(F32, d, lit, k) : {Laws.rd_at(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.sub(x, y)), n, d, Array.new(F32, d, lit), a2, z), k) == F32.sub(_, Laws.rd_at(F32, a2, k)) : F32};
       PC.zip_cell(~F32, ~F32, ~F32, ~(x => y => F32.sub(x, y)), d, n, Array.new(F32, d, lit), a2, z, k, fits, hk))))

def Laws.map_pb_bcast_f32(d, n, a, lit, z, k, fits, hk):
  bcf_k(d, n, a, lit, z, k, fits, hk, PC.clone_eq(F32, a))

# ---- three clones of one array ------------------------------------------------------------------

def clone3_k(-T: Data, -a: Array<T>, -a0: Array<T>, +e0: {a0 == a : Array<T>}, w: &a2: Array<T> -> &a3: Array<T> -> {a2 == a0 : Array<T>} & {a3 == a0 : Array<T>}) -> &a2: Array<T> -> &a3: Array<T> -> {a2 == a : Array<T>} & {a3 == a : Array<T>}:
  (a2, a3, e2, e3) = w
  (a2, a3, (%e0 : {a2 == _ : Array<T>}; e2), (%e0 : {a3 == _ : Array<T>}; e3))

def clone3_m(-T: Data, -a: Array<T>, a1: Array<T>, e1: {a1 == a : Array<T>}, w: &a2: Array<T> -> &a3: Array<T> -> {a2 == a : Array<T>} & {a3 == a : Array<T>}) -> &a1: Array<T> -> &a2: Array<T> -> &a3: Array<T> -> {a1 == a : Array<T>} & {a2 == a : Array<T>} & {a3 == a : Array<T>}:
  (a2, a3, e2, e3) = w
  (a1, a2, a3, e1, e2, e3)

def clone3_j(-T: Data, -a: Array<T>, w: &a1: Array<T> -> &a0: Array<T> -> {a1 == a : Array<T>} & {a0 == a : Array<T>}) -> &a1: Array<T> -> &a2: Array<T> -> &a3: Array<T> -> {a1 == a : Array<T>} & {a2 == a : Array<T>} & {a3 == a : Array<T>}:
  (a1, a0, e1, e0) = w
  clone3_m(T, a, a1, e1, clone3_k(T, a, a0, e0, PC.clone_eq(T, a0)))

def clone3(-T: Data, a: Array<T>) -> &a1: Array<T> -> &a2: Array<T> -> &a3: Array<T> -> {a1 == a : Array<T>} & {a2 == a : Array<T>} & {a3 == a : Array<T>}:
  clone3_j(T, a, PC.clone_eq(T, a))

# ---- Kernel.zipb IS Kernel.zip with both operands handed back (simulation) ----------------------------

def ZBSim(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, fl: Nat, +j: U32, -out: Array<V>, -a: Array<T>, -b: Array<U>) -> Type:
  {K.Kernel.zipb.go(~T, ~U, ~V, ~f, fl, j, out, Array.get(T, a, j), Array.get(U, b, j)) == K.ZB{K.Kernel.zip.go(~T, ~U, ~V, ~f, fl, j, out, Array.get(T, a, j), Array.get(U, b, j)), a, b} : K.ZB<T, U, V>}

def zbs_zero(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +j: U32, -out: Array<V>, -a: Array<T>, -b: Array<U>,
  wa: &a2: Array<T> -> &x: T -> {a2 == a : Array<T>} & {Array.get(T, a, j) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, j) : T},
  wb: &b2: Array<U> -> &y: U -> {b2 == b : Array<U>} & {Array.get(U, b, j) == (b, y) : Array<U> & U} & {y == Laws.rd_at(U, b, j) : U})
  -> ZBSim(~T, ~U, ~V, ~f, 0n, j, out, a, b):
  (a2, +x, ea, e1, ex) = wa
  (b2, +y, eb, e2, ey) = wb
  %Equal.sym(Array<T> & T, Array.get(T, a, j), (a, x), e1) : {K.Kernel.zipb.go(~T, ~U, ~V, ~f, 0n, j, out, _, Array.get(U, b, j)) == K.ZB{K.Kernel.zip.go(~T, ~U, ~V, ~f, 0n, j, out, _, Array.get(U, b, j)), a, b} : K.ZB<T, U, V>}
  %Equal.sym(Array<U> & U, Array.get(U, b, j), (b, y), e2) : {K.Kernel.zipb.go(~T, ~U, ~V, ~f, 0n, j, out, (a, x), _) == K.ZB{K.Kernel.zip.go(~T, ~U, ~V, ~f, 0n, j, out, (a, x), _), a, b} : K.ZB<T, U, V>}
  {==}

def zbs_step2(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, q: Nat, +j: U32, out: Array<V>, -a: Array<T>, -b: Array<U>, +x: T,
  w: &b2: Array<U> -> &y: U -> {b2 == b : Array<U>} & {Array.get(U, b, j) == (b, y) : Array<U> & U} & {y == Laws.rd_at(U, b, j) : U},
  ih: @b3: Array<U> -> @c: Array<V> -> ZBSim(~T, ~U, ~V, ~f, q, U32.inc(j), c, a, b3))
  -> {K.Kernel.zipb.go(~T, ~U, ~V, ~f, 1n+q, j, out, (a, x), Array.get(U, b, j)) == K.ZB{K.Kernel.zip.go(~T, ~U, ~V, ~f, 1n+q, j, out, (a, x), Array.get(U, b, j)), a, b} : K.ZB<T, U, V>}:
  (b2, +y, +eb, e2, ey) = w
  %Equal.sym(Array<U> & U, Array.get(U, b, j), (b, y), e2) : {K.Kernel.zipb.go(~T, ~U, ~V, ~f, 1n+q, j, out, (a, x), _) == K.ZB{K.Kernel.zip.go(~T, ~U, ~V, ~f, 1n+q, j, out, (a, x), _), a, b} : K.ZB<T, U, V>}
  %eb : {K.Kernel.zipb.go(~T, ~U, ~V, ~f, 1n+q, j, out, (a, x), (_, y)) == K.ZB{K.Kernel.zip.go(~T, ~U, ~V, ~f, 1n+q, j, out, (a, x), (_, y)), a, _} : K.ZB<T, U, V>}
  ih(b2, Array.set(V, out, j, f(x, y)))

def zbs_step1(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, q: Nat, +j: U32, out: Array<V>, -a: Array<T>, b: Array<U>,
  w: &a2: Array<T> -> &x: T -> {a2 == a : Array<T>} & {Array.get(T, a, j) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, j) : T},
  ih: @a3: Array<T> -> @b3: Array<U> -> @c: Array<V> -> ZBSim(~T, ~U, ~V, ~f, q, U32.inc(j), c, a3, b3))
  -> ZBSim(~T, ~U, ~V, ~f, 1n+q, j, out, a, b):
  (a2, +x, +ea, e1, ex) = w
  %Equal.sym(Array<T> & T, Array.get(T, a, j), (a, x), e1) : {K.Kernel.zipb.go(~T, ~U, ~V, ~f, 1n+q, j, out, _, Array.get(U, b, j)) == K.ZB{K.Kernel.zip.go(~T, ~U, ~V, ~f, 1n+q, j, out, _, Array.get(U, b, j)), a, b} : K.ZB<T, U, V>}
  %ea : {K.Kernel.zipb.go(~T, ~U, ~V, ~f, 1n+q, j, out, (_, x), Array.get(U, b, j)) == K.ZB{K.Kernel.zip.go(~T, ~U, ~V, ~f, 1n+q, j, out, (_, x), Array.get(U, b, j)), _, b} : K.ZB<T, U, V>}
  zbs_step2(~T, ~U, ~V, ~f, q, j, out, a2, b, x, PC.get_w(U, b, j), b3 => c => ih(a2, b3, c))

def zb_sim(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, fl: Nat, +j: U32, out: Array<V>, a: Array<T>, b: Array<U>) -> ZBSim(~T, ~U, ~V, ~f, fl, j, out, a, b):
  match fl:
    case 0n:
      zbs_zero(~T, ~U, ~V, ~f, j, out, a, b, PC.get_w(T, a, j), PC.get_w(U, b, j))
    case 1n++q:
      zbs_step1(~T, ~U, ~V, ~f, q, j, out, a, b, PC.get_w(T, a, j), a3 => b3 => c => zb_sim(~T, ~U, ~V, ~f, q, U32.inc(j), c, a3, b3))

def Laws.zipb_unfused(d, n, a, b, z):
  zb_sim(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), U32.to_nat(n), 0, Array.new(F32, d, z), a, b)

# zipb's output cell: the simulation on one clone of each operand, zip_cell on the other
def zb_cell_k(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +d: Nat, +n: U32, -a: Array<T>, -b: Array<U>, +z: V, +k: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, hk: {U32.is_lt(k, n) == True{} : Bool},
  wa: &a1: Array<T> -> &a2: Array<T> -> {a1 == a : Array<T>} & {a2 == a : Array<T>}, wb: &b1: Array<U> -> &b2: Array<U> -> {b1 == b : Array<U>} & {b2 == b : Array<U>})
  -> {Laws.rd_at(V, Laws.zb_o(T, U, V, K.Kernel.zipb.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, Array.new(V, d, z), Array.get(T, a, 0), Array.get(U, b, 0))), k) == f(Laws.rd_at(T, a, k), Laws.rd_at(U, b, k)) : V}:
  (a1, a2, +ea1, ea2) = wa
  (b1, b2, +eb1, eb2) = wb
  %ea1 : {Laws.rd_at(V, Laws.zb_o(T, U, V, K.Kernel.zipb.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, Array.new(V, d, z), Array.get(T, _, 0), Array.get(U, b, 0))), k) == f(Laws.rd_at(T, a, k), Laws.rd_at(U, b, k)) : V}
  %eb1 : {Laws.rd_at(V, Laws.zb_o(T, U, V, K.Kernel.zipb.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, Array.new(V, d, z), Array.get(T, a1, 0), Array.get(U, _, 0))), k) == f(Laws.rd_at(T, a, k), Laws.rd_at(U, b, k)) : V}
  %Equal.sym(K.ZB<T, U, V>, K.Kernel.zipb.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, Array.new(V, d, z), Array.get(T, a1, 0), Array.get(U, b1, 0)), K.ZB{K.Kernel.zip.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, Array.new(V, d, z), Array.get(T, a1, 0), Array.get(U, b1, 0)), a1, b1}, zb_sim(~T, ~U, ~V, ~f, U32.to_nat(n), 0, Array.new(V, d, z), a1, b1)) : {Laws.rd_at(V, Laws.zb_o(T, U, V, _), k) == f(Laws.rd_at(T, a, k), Laws.rd_at(U, b, k)) : V}
  %Equal.sym(Array<T>, a1, a, ea1) : {Laws.rd_at(V, K.Kernel.zip.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, Array.new(V, d, z), Array.get(T, _, 0), Array.get(U, b1, 0)), k) == f(Laws.rd_at(T, a, k), Laws.rd_at(U, b, k)) : V}
  %Equal.sym(Array<U>, b1, b, eb1) : {Laws.rd_at(V, K.Kernel.zip.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, Array.new(V, d, z), Array.get(T, a, 0), Array.get(U, _, 0)), k) == f(Laws.rd_at(T, a, k), Laws.rd_at(U, b, k)) : V}
  %ea2 : {Laws.rd_at(V, K.Kernel.zip.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, Array.new(V, d, z), Array.get(T, _, 0), Array.get(U, b, 0)), k) == f(Laws.rd_at(T, _, k), Laws.rd_at(U, b, k)) : V}
  %eb2 : {Laws.rd_at(V, K.Kernel.zip.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, Array.new(V, d, z), Array.get(T, a2, 0), Array.get(U, _, 0)), k) == f(Laws.rd_at(T, a2, k), Laws.rd_at(U, _, k)) : V}
  PC.zip_cell(~T, ~U, ~V, ~f, d, n, a2, b2, z, k, fits, hk)

def zb_cell(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +d: Nat, +n: U32, a: Array<T>, b: Array<U>, +z: V, +k: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, hk: {U32.is_lt(k, n) == True{} : Bool})
  -> {Laws.rd_at(V, Laws.zb_o(T, U, V, K.Kernel.zipb.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, Array.new(V, d, z), Array.get(T, a, 0), Array.get(U, b, 0))), k) == f(Laws.rd_at(T, a, k), Laws.rd_at(U, b, k)) : V}:
  zb_cell_k(~T, ~U, ~V, ~f, d, n, a, b, z, k, fits, hk, PC.clone_eq(T, a), PC.clone_eq(U, b))

# F3: the fused cast product against the cast map then the Mul zip (both through their cell theorems)
def zbc_k(+d: Nat, +n: U32, -a: Array<U32>, -b: Array<F32>, +z: F32, +k: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hk: {U32.is_lt(k, n) == True{} : Bool},
  wa: &a1: Array<U32> -> &a2: Array<U32> -> &a3: Array<U32> -> {a1 == a : Array<U32>} & {a2 == a : Array<U32>} & {a3 == a : Array<U32>}, wb: &b1: Array<F32> -> &b2: Array<F32> -> {b1 == b : Array<F32>} & {b2 == b : Array<F32>})
  -> {Laws.rd_at(F32, Laws.zb_o(U32, F32, F32, K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), n, d, a, b, z)), k) == Laws.rd_at(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, K.Kernel.map(~U32, ~F32, ~(w => U32.to_f32(w)), n, d, a, 0.0), b, z), k) : F32}:
  (a1, a2, a3, ea1, +ea2, ea3) = wa
  (b1, b2, eb1, eb2) = wb
  +e23 = Equal.trans(Array<U32>, a2, a, a3, ea2, Equal.sym(Array<U32>, a3, a, ea3))
  Equal.trans(F32, Laws.rd_at(F32, Laws.zb_o(U32, F32, F32, K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), n, d, a, b, z)), k), F32.mul(U32.to_f32(Laws.rd_at(U32, a, k)), Laws.rd_at(F32, b, k)), Laws.rd_at(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, K.Kernel.map(~U32, ~F32, ~(w => U32.to_f32(w)), n, d, a, 0.0), b, z), k),
    (%ea1 : {Laws.rd_at(F32, Laws.zb_o(U32, F32, F32, K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), n, d, _, b, z)), k) == F32.mul(U32.to_f32(Laws.rd_at(U32, _, k)), Laws.rd_at(F32, b, k)) : F32};
     %eb1 : {Laws.rd_at(F32, Laws.zb_o(U32, F32, F32, K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), n, d, a1, _, z)), k) == F32.mul(U32.to_f32(Laws.rd_at(U32, a1, k)), Laws.rd_at(F32, _, k)) : F32};
     zb_cell(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), d, n, a1, b1, z, k, fits, hk)),
    Equal.sym(F32, Laws.rd_at(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, K.Kernel.map(~U32, ~F32, ~(w => U32.to_f32(w)), n, d, a, 0.0), b, z), k), F32.mul(U32.to_f32(Laws.rd_at(U32, a, k)), Laws.rd_at(F32, b, k)),
      (%ea2 : {Laws.rd_at(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, K.Kernel.map(~U32, ~F32, ~(w => U32.to_f32(w)), n, d, _, 0.0), b, z), k) == F32.mul(U32.to_f32(Laws.rd_at(U32, _, k)), Laws.rd_at(F32, b, k)) : F32};
       %eb2 : {Laws.rd_at(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, K.Kernel.map(~U32, ~F32, ~(w => U32.to_f32(w)), n, d, a2, 0.0), _, z), k) == F32.mul(U32.to_f32(Laws.rd_at(U32, a2, k)), Laws.rd_at(F32, _, k)) : F32};
       %Equal.sym(Array<U32>, a2, a3, e23) : {Laws.rd_at(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, K.Kernel.map(~U32, ~F32, ~(w => U32.to_f32(w)), n, d, a2, 0.0), b2, z), k) == F32.mul(U32.to_f32(Laws.rd_at(U32, _, k)), Laws.rd_at(F32, b2, k)) : F32};
       %PC.map_cell(~U32, ~F32, ~(w => U32.to_f32(w)), d, n, a3, 0.0, k, fits, hk) : {Laws.rd_at(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, K.Kernel.map(~U32, ~F32, ~(w => U32.to_f32(w)), n, d, a2, 0.0), b2, z), k) == F32.mul(_, Laws.rd_at(F32, b2, k)) : F32};
       %e23 : {Laws.rd_at(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, K.Kernel.map(~U32, ~F32, ~(w => U32.to_f32(w)), n, d, a2, 0.0), b2, z), k) == F32.mul(Laws.rd_at(F32, K.Kernel.map(~U32, ~F32, ~(w => U32.to_f32(w)), n, d, _, 0.0), k), Laws.rd_at(F32, b2, k)) : F32};
       PC.zip_cell(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), d, n, K.Kernel.map(~U32, ~F32, ~(w => U32.to_f32(w)), n, d, a2, 0.0), b2, z, k, fits, hk))))

def Laws.zipb_cast_cell(d, n, a, b, z, k, fits, hk):
  zbc_k(d, n, a, b, z, k, fits, hk, clone3(U32, a), PC.clone_eq(F32, b))

# ---- Kernel.zipv: the value cell (four reads, one tracked output; the validity output is carried) ------

# the word zipv writes at a row whose operand cells are x, y and validity words wa, wb
def zvc(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +z: V, +x: T, +wa: U32, +y: U, +wb: U32) -> V:
  Bool.pick(V, U32.is_ne(U32.and(wa, wb), 0), f(x, y), z)

def ZVOHyp(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +j: U32, +z: V, +d: Nat, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -out: Array<V>) -> Type:
  @k: U32 -> {U32.is_lt(k, j) == True{} : Bool} -> {Laws.rdN(V, d, out, k) == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : V}

def ZVORes(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +z: V, +d: Nat, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, o: Array<V>, +bound: U32) -> Type:
  Laws.WFArray(V, d, o) & (@k: U32 -> {U32.is_lt(k, bound) == True{} : Bool} -> {Laws.rdN(V, d, o, k) == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : V})

def ZVOGoal(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, fl: Nat, +j: U32, +z: V, +d: Nat, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -out: Array<V>, -vout: Array<U32>, -ra: Array<T> & T, -rva: Array<U32> & U32, -rb: Array<U> & U, -rvb: Array<U32> & U32) -> Type:
  ZVOHyp(~T, ~U, ~V, ~f, j, z, d, a, va, b, vb, out) -> &o: Array<V> -> {Laws.zv_o(T, U, V, K.Kernel.zipv.go(~T, ~U, ~V, ~f, fl, j, z, out, vout, ra, rva, rb, rvb)) == o : Array<V>} & ZVORes(~T, ~U, ~V, ~f, z, d, a, va, b, vb, o, Laws.addn(j, fl))

def ZVOSet(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, q: Nat, +j: U32, +z: V, +d: Nat, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -out: Array<V>, -vo2: Array<U32>, +y: V) -> Type:
  ZVOHyp(~T, ~U, ~V, ~f, j, z, d, a, va, b, vb, out) -> &o: Array<V> -> {Laws.zv_o(T, U, V, K.Kernel.zipv.go(~T, ~U, ~V, ~f, q, U32.inc(j), z, Array.set(V, out, j, y), vo2, Array.get(T, a, U32.inc(j)), Array.get(U32, va, U32.inc(j)), Array.get(U, b, U32.inc(j)), Array.get(U32, vb, U32.inc(j)))) == o : Array<V>} & ZVORes(~T, ~U, ~V, ~f, z, d, a, va, b, vb, o, Laws.addn(j, 1n+q))

def ZVOC(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, q: Nat, +j: U32, +z: V, +d: Nat, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -out: Array<V>, -c: Array<V>, -vo2: Array<U32>, +bound: U32) -> Type:
  ZVOHyp(~T, ~U, ~V, ~f, j, z, d, a, va, b, vb, out) -> &o: Array<V> -> {Laws.zv_o(T, U, V, K.Kernel.zipv.go(~T, ~U, ~V, ~f, q, U32.inc(j), z, c, vo2, Array.get(T, a, U32.inc(j)), Array.get(U32, va, U32.inc(j)), Array.get(U, b, U32.inc(j)), Array.get(U32, vb, U32.inc(j)))) == o : Array<V>} & ZVORes(~T, ~U, ~V, ~f, z, d, a, va, b, vb, o, bound)

def zvonext_lt(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +d: Nat, +j: U32, +k: U32, +z: V, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -out: Array<V>, -c: Array<V>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +y: V, g: ZVOHyp(~T, ~U, ~V, ~f, j, z, d, a, va, b, vb, out),
  fj: @k2: U32 -> {Laws.rdN(V, d, c, k2) == Bool.pick(V, Laws.same_at(d, j, k2), y, Laws.rdN(V, d, out, k2)) : V}, +lt: {U32.is_lt(k, j) == True{} : Bool})
  -> {Laws.rdN(V, d, c, k) == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : V}:
  %Equal.sym(V, Laws.rdN(V, d, c, k), Bool.pick(V, Laws.same_at(d, j, k), y, Laws.rdN(V, d, out, k)), fj(k)) : {_ == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : V}
  %Equal.sym(Bool, Laws.same_at(d, j, k), False{}, PC.same_false_lt(d, j, k, hj, lt)) : {Bool.pick(V, _, y, Laws.rdN(V, d, out, k)) == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : V}
  g(k, lt)

def zvonext_b(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, bb: Bool, +d: Nat, +j: U32, +k: U32, +z: V, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -out: Array<V>, -c: Array<V>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +y: V,
  ey: {y == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, j), Laws.rd_at(U32, va, j), Laws.rd_at(U, b, j), Laws.rd_at(U32, vb, j)) : V}, g: ZVOHyp(~T, ~U, ~V, ~f, j, z, d, a, va, b, vb, out),
  fj: @k2: U32 -> {Laws.rdN(V, d, c, k2) == Bool.pick(V, Laws.same_at(d, j, k2), y, Laws.rdN(V, d, out, k2)) : V}, s: PC.IncLtU(bb, k, j))
  -> {Laws.rdN(V, d, c, k) == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : V}:
  match bb:
    case True{}:
      zvonext_lt(~T, ~U, ~V, ~f, d, j, k, z, a, va, b, vb, out, c, hj, y, g, fj, s)
    case False{}:
      %Equal.sym(U32, k, j, s) : {Laws.rdN(V, d, c, _) == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, _), Laws.rd_at(U32, va, _), Laws.rd_at(U, b, _), Laws.rd_at(U32, vb, _)) : V}
      %Equal.sym(V, Laws.rdN(V, d, c, j), Bool.pick(V, Laws.same_at(d, j, j), y, Laws.rdN(V, d, out, j)), fj(j)) : {_ == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, j), Laws.rd_at(U32, va, j), Laws.rd_at(U, b, j), Laws.rd_at(U32, vb, j)) : V}
      %Equal.sym(Bool, Laws.same_at(d, j, j), True{}, PC.same_at_refl(d, j)) : {Bool.pick(V, _, y, Laws.rdN(V, d, out, j)) == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, j), Laws.rd_at(U32, va, j), Laws.rd_at(U, b, j), Laws.rd_at(U32, vb, j)) : V}
      ey

def zvonext_k(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +d: Nat, +j: U32, +k: U32, +z: V, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -out: Array<V>, -c: Array<V>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +y: V,
  ey: {y == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, j), Laws.rd_at(U32, va, j), Laws.rd_at(U, b, j), Laws.rd_at(U32, vb, j)) : V}, g: ZVOHyp(~T, ~U, ~V, ~f, j, z, d, a, va, b, vb, out),
  fj: @k2: U32 -> {Laws.rdN(V, d, c, k2) == Bool.pick(V, Laws.same_at(d, j, k2), y, Laws.rdN(V, d, out, k2)) : V}, w: &bb: Bool -> PC.IncLtU(bb, k, j))
  -> {Laws.rdN(V, d, c, k) == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : V}:
  (bb, s) = w
  zvonext_b(~T, ~U, ~V, ~f, bb, d, j, k, z, a, va, b, vb, out, c, hj, y, ey, g, fj, s)

def zvonext(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +d: Nat, +j: U32, +z: V, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -out: Array<V>, -c: Array<V>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +y: V,
  +ey: {y == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, j), Laws.rd_at(U32, va, j), Laws.rd_at(U, b, j), Laws.rd_at(U32, vb, j)) : V}, g: ZVOHyp(~T, ~U, ~V, ~f, j, z, d, a, va, b, vb, out),
  fj: @k2: U32 -> {Laws.rdN(V, d, c, k2) == Bool.pick(V, Laws.same_at(d, j, k2), y, Laws.rdN(V, d, out, k2)) : V})
  -> ZVOHyp(~T, ~U, ~V, ~f, U32.inc(j), z, d, a, va, b, vb, c):
  +k => hk => zvonext_k(~T, ~U, ~V, ~f, d, j, k, z, a, va, b, vb, out, c, hj, y, ey, g, fj, PC.inc_lt_u(k, j, hk))

def zvo_s5(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, q: Nat, +j: U32, +z: V, +d: Nat, a: Array<T>, va: Array<U32>, b: Array<U>, vb: Array<U32>, -out: Array<V>, vo2: Array<U32>, +y: V,
  +ey: {y == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, j), Laws.rd_at(U32, va, j), Laws.rd_at(U, b, j), Laws.rd_at(U32, vb, j)) : V}, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, room: Laws.Room(d, U32.inc(j), q),
  ih: @a2: Array<T> -> @va2: Array<U32> -> @b2: Array<U> -> @vb2: Array<U32> -> @c: Array<V> -> @vo3: Array<U32> -> Laws.WFArray(V, d, c) -> Laws.Room(d, U32.inc(j), q) -> ZVOGoal(~T, ~U, ~V, ~f, q, U32.inc(j), z, d, a2, va2, b2, vb2, c, vo3, Array.get(T, a2, U32.inc(j)), Array.get(U32, va2, U32.inc(j)), Array.get(U, b2, U32.inc(j)), Array.get(U32, vb2, U32.inc(j))),
  w: &c: Array<V> -> {Array.set(V, out, j, y) == c : Array<V>} & Laws.WFArray(V, d, c) & (@k2: U32 -> {Laws.rdN(V, d, c, k2) == Bool.pick(V, Laws.same_at(d, j, k2), y, Laws.rdN(V, d, out, k2)) : V}) & (@k2: U32 -> {Laws.rd_at(V, out, k2) == Laws.rdN(V, d, out, k2) : V}))
  -> ZVOSet(~T, ~U, ~V, ~f, q, j, z, d, a, va, b, vb, out, vo2, y):
  (c, ec, wc, fj, cv) = w
  %Equal.sym(Array<V>, Array.set(V, out, j, y), c, ec) : ZVOC(~T, ~U, ~V, ~f, q, j, z, d, a, va, b, vb, out, _, vo2, Laws.addn(j, 1n+q))
  %PC.addn_inc(j, q) : ZVOC(~T, ~U, ~V, ~f, q, j, z, d, a, va, b, vb, out, c, vo2, _)
  g => ih(a, va, b, vb, c, vo2, wc, room)(zvonext(~T, ~U, ~V, ~f, d, j, z, a, va, b, vb, out, c, hj, y, ey, g, fj))

# the fourth read (vb at j); the written value and its model, then the write
def zvo_s4(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, q: Nat, +j: U32, +z: V, +d: Nat, a: Array<T>, va: Array<U32>, b: Array<U>, -vb: Array<U32>, out: Array<V>, vout: Array<U32>, wf: Laws.WFArray(V, d, out),
  +x: T, +ex: {x == Laws.rd_at(T, a, j) : T}, +wa: U32, +ewa: {wa == Laws.rd_at(U32, va, j) : U32}, +y: U, +ey: {y == Laws.rd_at(U, b, j) : U}, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, room: Laws.Room(d, U32.inc(j), q),
  ih: @a2: Array<T> -> @va2: Array<U32> -> @b2: Array<U> -> @vb2: Array<U32> -> @c: Array<V> -> @vo3: Array<U32> -> Laws.WFArray(V, d, c) -> Laws.Room(d, U32.inc(j), q) -> ZVOGoal(~T, ~U, ~V, ~f, q, U32.inc(j), z, d, a2, va2, b2, vb2, c, vo3, Array.get(T, a2, U32.inc(j)), Array.get(U32, va2, U32.inc(j)), Array.get(U, b2, U32.inc(j)), Array.get(U32, vb2, U32.inc(j))),
  w: &vb2: Array<U32> -> &wb: U32 -> {vb2 == vb : Array<U32>} & {Array.get(U32, vb, j) == (vb, wb) : Array<U32> & U32} & {wb == Laws.rd_at(U32, vb, j) : U32})
  -> ZVOGoal(~T, ~U, ~V, ~f, 1n+q, j, z, d, a, va, b, vb, out, vout, (a, x), (va, wa), (b, y), Array.get(U32, vb, j)):
  (vb2, +wb, +evb, e1, ewb) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, vb, j), (vb, wb), e1) : ZVOGoal(~T, ~U, ~V, ~f, 1n+q, j, z, d, a, va, b, vb, out, vout, (a, x), (va, wa), (b, y), _)
  %evb : ZVOGoal(~T, ~U, ~V, ~f, 1n+q, j, z, d, a, va, b, _, out, vout, (a, x), (va, wa), (b, y), (_, wb))
  zvo_s5(~T, ~U, ~V, ~f, q, j, z, d, a, va, b, vb2, out, Array.set(U32, vout, j, U32.and(wa, wb)), zvc(~T, ~U, ~V, ~f, z, x, wa, y, wb),
    (%ex : {zvc(~T, ~U, ~V, ~f, z, x, wa, y, wb) == zvc(~T, ~U, ~V, ~f, z, _, Laws.rd_at(U32, va, j), Laws.rd_at(U, b, j), Laws.rd_at(U32, vb2, j)) : V};
     %ewa : {zvc(~T, ~U, ~V, ~f, z, x, wa, y, wb) == zvc(~T, ~U, ~V, ~f, z, x, _, Laws.rd_at(U, b, j), Laws.rd_at(U32, vb2, j)) : V};
     %ey : {zvc(~T, ~U, ~V, ~f, z, x, wa, y, wb) == zvc(~T, ~U, ~V, ~f, z, x, wa, _, Laws.rd_at(U32, vb2, j)) : V};
     %Equal.trans(U32, wb, Laws.rd_at(U32, vb, j), Laws.rd_at(U32, vb2, j), ewb, Equal.sym(U32, Laws.rd_at(U32, vb2, j), Laws.rd_at(U32, vb, j), Equal.cong(Array<U32>, U32, r => Laws.rd_at(U32, r, j), vb2, vb, evb))) : {zvc(~T, ~U, ~V, ~f, z, x, wa, y, wb) == zvc(~T, ~U, ~V, ~f, z, x, wa, y, _) : V};
     {==}),
    hj, room, ih, PC.set_other_w(V, d, out, j, zvc(~T, ~U, ~V, ~f, z, x, wa, y, wb), wf))

def zvo_s3(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, q: Nat, +j: U32, +z: V, +d: Nat, a: Array<T>, va: Array<U32>, -b: Array<U>, vb: Array<U32>, out: Array<V>, vout: Array<U32>, wf: Laws.WFArray(V, d, out),
  +x: T, +ex: {x == Laws.rd_at(T, a, j) : T}, +wa: U32, +ewa: {wa == Laws.rd_at(U32, va, j) : U32}, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, room: Laws.Room(d, U32.inc(j), q),
  ih: @a2: Array<T> -> @va2: Array<U32> -> @b2: Array<U> -> @vb2: Array<U32> -> @c: Array<V> -> @vo3: Array<U32> -> Laws.WFArray(V, d, c) -> Laws.Room(d, U32.inc(j), q) -> ZVOGoal(~T, ~U, ~V, ~f, q, U32.inc(j), z, d, a2, va2, b2, vb2, c, vo3, Array.get(T, a2, U32.inc(j)), Array.get(U32, va2, U32.inc(j)), Array.get(U, b2, U32.inc(j)), Array.get(U32, vb2, U32.inc(j))),
  w: &b2: Array<U> -> &y: U -> {b2 == b : Array<U>} & {Array.get(U, b, j) == (b, y) : Array<U> & U} & {y == Laws.rd_at(U, b, j) : U})
  -> ZVOGoal(~T, ~U, ~V, ~f, 1n+q, j, z, d, a, va, b, vb, out, vout, (a, x), (va, wa), Array.get(U, b, j), Array.get(U32, vb, j)):
  (b2, +y, +eb, e1, ey) = w
  %Equal.sym(Array<U> & U, Array.get(U, b, j), (b, y), e1) : ZVOGoal(~T, ~U, ~V, ~f, 1n+q, j, z, d, a, va, b, vb, out, vout, (a, x), (va, wa), _, Array.get(U32, vb, j))
  %eb : ZVOGoal(~T, ~U, ~V, ~f, 1n+q, j, z, d, a, va, _, vb, out, vout, (a, x), (va, wa), (_, y), Array.get(U32, vb, j))
  zvo_s4(~T, ~U, ~V, ~f, q, j, z, d, a, va, b2, vb, out, vout, wf, x, ex, wa, ewa, y, Equal.trans(U, y, Laws.rd_at(U, b, j), Laws.rd_at(U, b2, j), ey, Equal.sym(U, Laws.rd_at(U, b2, j), Laws.rd_at(U, b, j), Equal.cong(Array<U>, U, r => Laws.rd_at(U, r, j), b2, b, eb))), hj, room, ih, PC.get_w(U32, vb, j))

def zvo_s2(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, q: Nat, +j: U32, +z: V, +d: Nat, a: Array<T>, -va: Array<U32>, b: Array<U>, vb: Array<U32>, out: Array<V>, vout: Array<U32>, wf: Laws.WFArray(V, d, out),
  +x: T, +ex: {x == Laws.rd_at(T, a, j) : T}, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, room: Laws.Room(d, U32.inc(j), q),
  ih: @a2: Array<T> -> @va2: Array<U32> -> @b2: Array<U> -> @vb2: Array<U32> -> @c: Array<V> -> @vo3: Array<U32> -> Laws.WFArray(V, d, c) -> Laws.Room(d, U32.inc(j), q) -> ZVOGoal(~T, ~U, ~V, ~f, q, U32.inc(j), z, d, a2, va2, b2, vb2, c, vo3, Array.get(T, a2, U32.inc(j)), Array.get(U32, va2, U32.inc(j)), Array.get(U, b2, U32.inc(j)), Array.get(U32, vb2, U32.inc(j))),
  w: &va2: Array<U32> -> &wa: U32 -> {va2 == va : Array<U32>} & {Array.get(U32, va, j) == (va, wa) : Array<U32> & U32} & {wa == Laws.rd_at(U32, va, j) : U32})
  -> ZVOGoal(~T, ~U, ~V, ~f, 1n+q, j, z, d, a, va, b, vb, out, vout, (a, x), Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j)):
  (va2, +wa, +eva, e1, ewa) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, va, j), (va, wa), e1) : ZVOGoal(~T, ~U, ~V, ~f, 1n+q, j, z, d, a, va, b, vb, out, vout, (a, x), _, Array.get(U, b, j), Array.get(U32, vb, j))
  %eva : ZVOGoal(~T, ~U, ~V, ~f, 1n+q, j, z, d, a, _, b, vb, out, vout, (a, x), (_, wa), Array.get(U, b, j), Array.get(U32, vb, j))
  zvo_s3(~T, ~U, ~V, ~f, q, j, z, d, a, va2, b, vb, out, vout, wf, x, ex, wa, Equal.trans(U32, wa, Laws.rd_at(U32, va, j), Laws.rd_at(U32, va2, j), ewa, Equal.sym(U32, Laws.rd_at(U32, va2, j), Laws.rd_at(U32, va, j), Equal.cong(Array<U32>, U32, r => Laws.rd_at(U32, r, j), va2, va, eva))), hj, room, ih, PC.get_w(U, b, j))

def zvo_s1(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, q: Nat, +j: U32, +z: V, +d: Nat, -a: Array<T>, va: Array<U32>, b: Array<U>, vb: Array<U32>, out: Array<V>, vout: Array<U32>, wf: Laws.WFArray(V, d, out), room: Laws.Room(d, j, 1n+q),
  ih: @a2: Array<T> -> @va2: Array<U32> -> @b2: Array<U> -> @vb2: Array<U32> -> @c: Array<V> -> @vo3: Array<U32> -> Laws.WFArray(V, d, c) -> Laws.Room(d, U32.inc(j), q) -> ZVOGoal(~T, ~U, ~V, ~f, q, U32.inc(j), z, d, a2, va2, b2, vb2, c, vo3, Array.get(T, a2, U32.inc(j)), Array.get(U32, va2, U32.inc(j)), Array.get(U, b2, U32.inc(j)), Array.get(U32, vb2, U32.inc(j))),
  w: &a2: Array<T> -> &x: T -> {a2 == a : Array<T>} & {Array.get(T, a, j) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, j) : T})
  -> ZVOGoal(~T, ~U, ~V, ~f, 1n+q, j, z, d, a, va, b, vb, out, vout, Array.get(T, a, j), Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j)):
  (hj, room2) = room
  (a2, +x, +ea, e1, ex) = w
  %Equal.sym(Array<T> & T, Array.get(T, a, j), (a, x), e1) : ZVOGoal(~T, ~U, ~V, ~f, 1n+q, j, z, d, a, va, b, vb, out, vout, _, Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j))
  %ea : ZVOGoal(~T, ~U, ~V, ~f, 1n+q, j, z, d, _, va, b, vb, out, vout, (_, x), Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j))
  zvo_s2(~T, ~U, ~V, ~f, q, j, z, d, a2, va, b, vb, out, vout, wf, x, Equal.trans(T, x, Laws.rd_at(T, a, j), Laws.rd_at(T, a2, j), ex, Equal.sym(T, Laws.rd_at(T, a2, j), Laws.rd_at(T, a, j), Equal.cong(Array<T>, T, r => Laws.rd_at(T, r, j), a2, a, ea))), hj, room2, ih, PC.get_w(U32, va, j))

def zvo_zero(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +j: U32, +z: V, +d: Nat, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, out: Array<V>, -vout: Array<U32>, wf: Laws.WFArray(V, d, out),
  wa: &a2: Array<T> -> &x: T -> {a2 == a : Array<T>} & {Array.get(T, a, j) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, j) : T},
  wva: &va2: Array<U32> -> &x2: U32 -> {va2 == va : Array<U32>} & {Array.get(U32, va, j) == (va, x2) : Array<U32> & U32} & {x2 == Laws.rd_at(U32, va, j) : U32},
  wb: &b2: Array<U> -> &y: U -> {b2 == b : Array<U>} & {Array.get(U, b, j) == (b, y) : Array<U> & U} & {y == Laws.rd_at(U, b, j) : U},
  wvb: &vb2: Array<U32> -> &y2: U32 -> {vb2 == vb : Array<U32>} & {Array.get(U32, vb, j) == (vb, y2) : Array<U32> & U32} & {y2 == Laws.rd_at(U32, vb, j) : U32})
  -> ZVOGoal(~T, ~U, ~V, ~f, 0n, j, z, d, a, va, b, vb, out, vout, Array.get(T, a, j), Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j)):
  (a2, +x, ea, e1, ex) = wa
  (va2, +x2, eva, e2, ex2) = wva
  (b2, +y, eb, e3, ey) = wb
  (vb2, +y2, evb, e4, ey2) = wvb
  %Equal.sym(Array<T> & T, Array.get(T, a, j), (a, x), e1) : ZVOGoal(~T, ~U, ~V, ~f, 0n, j, z, d, a, va, b, vb, out, vout, _, Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j))
  %Equal.sym(Array<U32> & U32, Array.get(U32, va, j), (va, x2), e2) : ZVOGoal(~T, ~U, ~V, ~f, 0n, j, z, d, a, va, b, vb, out, vout, (a, x), _, Array.get(U, b, j), Array.get(U32, vb, j))
  %Equal.sym(Array<U> & U, Array.get(U, b, j), (b, y), e3) : ZVOGoal(~T, ~U, ~V, ~f, 0n, j, z, d, a, va, b, vb, out, vout, (a, x), (va, x2), _, Array.get(U32, vb, j))
  %Equal.sym(Array<U32> & U32, Array.get(U32, vb, j), (vb, y2), e4) : ZVOGoal(~T, ~U, ~V, ~f, 0n, j, z, d, a, va, b, vb, out, vout, (a, x), (va, x2), (b, y), _)
  g => (out, {==}, wf, g)

# Kernel.zipv.go: every k < addn(j, fl) holds the zvc cell of the four reads afterwards
def zvo_go(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, fl: Nat, +j: U32, +z: V, +d: Nat, a: Array<T>, va: Array<U32>, b: Array<U>, vb: Array<U32>, out: Array<V>, vout: Array<U32>, wf: Laws.WFArray(V, d, out), room: Laws.Room(d, j, fl))
  -> ZVOGoal(~T, ~U, ~V, ~f, fl, j, z, d, a, va, b, vb, out, vout, Array.get(T, a, j), Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j)):
  match fl:
    case 0n:
      zvo_zero(~T, ~U, ~V, ~f, j, z, d, a, va, b, vb, out, vout, wf, PC.get_w(T, a, j), PC.get_w(U32, va, j), PC.get_w(U, b, j), PC.get_w(U32, vb, j))
    case 1n++q:
      zvo_s1(~T, ~U, ~V, ~f, q, j, z, d, a, va, b, vb, out, vout, wf, room, a2 => va2 => b2 => vb2 => c => vo3 => wc => room2 => zvo_go(~T, ~U, ~V, ~f, q, U32.inc(j), z, d, a2, va2, b2, vb2, c, vo3, wc, room2), PC.get_w(T, a, j))

def zvohyp0(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +z: V, +d: Nat, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -out: Array<V>) -> ZVOHyp(~T, ~U, ~V, ~f, 0, z, d, a, va, b, vb, out):
  +k => hk => Empty.absurd({Laws.rdN(V, d, out, k) == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : V}, PC.lt0(k, hk))

def zvo_fin(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +d: Nat, +n: U32, +z: V, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, +k: U32, hk: {U32.is_lt(k, n) == True{} : Bool},
  w: &o: Array<V> -> {Laws.zv_o(T, U, V, K.Kernel.zipv.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, z, Array.new(V, d, z), Array.new(U32, d, 0), Array.get(T, a, 0), Array.get(U32, va, 0), Array.get(U, b, 0), Array.get(U32, vb, 0))) == o : Array<V>} & ZVORes(~T, ~U, ~V, ~f, z, d, a, va, b, vb, o, Laws.addn(0, U32.to_nat(n))))
  -> {Laws.rd_at(V, Laws.zv_o(T, U, V, K.Kernel.zipv.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, z, Array.new(V, d, z), Array.new(U32, d, 0), Array.get(T, a, 0), Array.get(U32, va, 0), Array.get(U, b, 0), Array.get(U32, vb, 0))), k) == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : V}:
  (o, eq, wo, spec) = w
  %Equal.sym(Array<V>, Laws.zv_o(T, U, V, K.Kernel.zipv.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, z, Array.new(V, d, z), Array.new(U32, d, 0), Array.get(T, a, 0), Array.get(U32, va, 0), Array.get(U, b, 0), Array.get(U32, vb, 0))), o, eq) : {Laws.rd_at(V, _, k) == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : V}
  %Equal.sym(V, Laws.rd_at(V, o, k), Laws.rdN(V, d, o, k), Laws.rd_at_wf(V, d, o, k, wo)) : {_ == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : V}
  spec(k, (%Equal.sym(U32, Laws.addn(0, U32.to_nat(n)), n, B.addn_to_nat(n)) : {U32.is_lt(k, _) == True{} : Bool}; hk))

# Kernel.zipv(n, d, a, va, b, vb, z): out[k] == (va[k] & vb[k]) != 0 ? f(a[k], b[k]) : z for k < n
def zvo_cell(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +d: Nat, +n: U32, a: Array<T>, va: Array<U32>, b: Array<U>, vb: Array<U32>, +z: V, +k: U32, fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, hk: {U32.is_lt(k, n) == True{} : Bool})
  -> {Laws.rd_at(V, Laws.zv_o(T, U, V, K.Kernel.zipv.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, z, Array.new(V, d, z), Array.new(U32, d, 0), Array.get(T, a, 0), Array.get(U32, va, 0), Array.get(U, b, 0), Array.get(U32, vb, 0))), k) == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : V}:
  zvo_fin(~T, ~U, ~V, ~f, d, n, z, a, va, b, vb, k, hk, zvo_go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, z, d, a, va, b, vb, Array.new(V, d, z), Array.new(U32, d, 0), Laws.wf_new(V, d, z), B.room_from(d, n, fits))(zvohyp0(~T, ~U, ~V, ~f, z, d, a, va, b, vb, Array.new(V, d, z))))

def Laws.zipv_cell(d, n, a, va, b, vb, z, k, fits, hk):
  zvo_cell(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), d, n, a, va, b, vb, z, k, fits, hk)

# ---- Kernel.zipv's validity IS Kernel.mask_and, and the four operands come back (simulation) ---------

def ZVV(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, fl: Nat, +j: U32, +z: V, -out: Array<V>, -vout: Array<U32>, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -ra: Array<T> & T, -rva: Array<U32> & U32, -rb: Array<U> & U, -rvb: Array<U32> & U32) -> Type:
  {K.Kernel.zipv.go(~T, ~U, ~V, ~f, fl, j, z, out, vout, ra, rva, rb, rvb) == K.ZV{Laws.zv_o(T, U, V, K.Kernel.zipv.go(~T, ~U, ~V, ~f, fl, j, z, out, vout, ra, rva, rb, rvb)), K.Kernel.zip.go(~U32, ~U32, ~U32, ~(x => y => U32.and(x, y)), fl, j, vout, rva, rvb), a, va, b, vb} : K.ZV<T, U, V>}

def zvv_zero(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +j: U32, +z: V, -out: Array<V>, -vout: Array<U32>, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>,
  wa: &a2: Array<T> -> &x: T -> {a2 == a : Array<T>} & {Array.get(T, a, j) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, j) : T},
  wva: &va2: Array<U32> -> &x2: U32 -> {va2 == va : Array<U32>} & {Array.get(U32, va, j) == (va, x2) : Array<U32> & U32} & {x2 == Laws.rd_at(U32, va, j) : U32},
  wb: &b2: Array<U> -> &y: U -> {b2 == b : Array<U>} & {Array.get(U, b, j) == (b, y) : Array<U> & U} & {y == Laws.rd_at(U, b, j) : U},
  wvb: &vb2: Array<U32> -> &y2: U32 -> {vb2 == vb : Array<U32>} & {Array.get(U32, vb, j) == (vb, y2) : Array<U32> & U32} & {y2 == Laws.rd_at(U32, vb, j) : U32})
  -> ZVV(~T, ~U, ~V, ~f, 0n, j, z, out, vout, a, va, b, vb, Array.get(T, a, j), Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j)):
  (a2, +x, ea, e1, ex) = wa
  (va2, +x2, eva, e2, ex2) = wva
  (b2, +y, eb, e3, ey) = wb
  (vb2, +y2, evb, e4, ey2) = wvb
  %Equal.sym(Array<T> & T, Array.get(T, a, j), (a, x), e1) : ZVV(~T, ~U, ~V, ~f, 0n, j, z, out, vout, a, va, b, vb, _, Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j))
  %Equal.sym(Array<U32> & U32, Array.get(U32, va, j), (va, x2), e2) : ZVV(~T, ~U, ~V, ~f, 0n, j, z, out, vout, a, va, b, vb, (a, x), _, Array.get(U, b, j), Array.get(U32, vb, j))
  %Equal.sym(Array<U> & U, Array.get(U, b, j), (b, y), e3) : ZVV(~T, ~U, ~V, ~f, 0n, j, z, out, vout, a, va, b, vb, (a, x), (va, x2), _, Array.get(U32, vb, j))
  %Equal.sym(Array<U32> & U32, Array.get(U32, vb, j), (vb, y2), e4) : ZVV(~T, ~U, ~V, ~f, 0n, j, z, out, vout, a, va, b, vb, (a, x), (va, x2), (b, y), _)
  {==}

def zvv_s4(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, q: Nat, +j: U32, +z: V, out: Array<V>, vout: Array<U32>, a: Array<T>, va: Array<U32>, b: Array<U>, -vb: Array<U32>, +x: T, +wa: U32, +y: U,
  ih: @a2: Array<T> -> @va2: Array<U32> -> @b2: Array<U> -> @vb2: Array<U32> -> @c: Array<V> -> @vo3: Array<U32> -> ZVV(~T, ~U, ~V, ~f, q, U32.inc(j), z, c, vo3, a2, va2, b2, vb2, Array.get(T, a2, U32.inc(j)), Array.get(U32, va2, U32.inc(j)), Array.get(U, b2, U32.inc(j)), Array.get(U32, vb2, U32.inc(j))),
  w: &vb2: Array<U32> -> &wb: U32 -> {vb2 == vb : Array<U32>} & {Array.get(U32, vb, j) == (vb, wb) : Array<U32> & U32} & {wb == Laws.rd_at(U32, vb, j) : U32})
  -> ZVV(~T, ~U, ~V, ~f, 1n+q, j, z, out, vout, a, va, b, vb, (a, x), (va, wa), (b, y), Array.get(U32, vb, j)):
  (vb2, +wb, +evb, e1, ewb) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, vb, j), (vb, wb), e1) : ZVV(~T, ~U, ~V, ~f, 1n+q, j, z, out, vout, a, va, b, vb, (a, x), (va, wa), (b, y), _)
  %evb : ZVV(~T, ~U, ~V, ~f, 1n+q, j, z, out, vout, a, va, b, _, (a, x), (va, wa), (b, y), (_, wb))
  ih(a, va, b, vb2, Array.set(V, out, j, zvc(~T, ~U, ~V, ~f, z, x, wa, y, wb)), Array.set(U32, vout, j, U32.and(wa, wb)))

def zvv_s3(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, q: Nat, +j: U32, +z: V, out: Array<V>, vout: Array<U32>, a: Array<T>, va: Array<U32>, -b: Array<U>, vb: Array<U32>, +x: T, +wa: U32,
  ih: @a2: Array<T> -> @va2: Array<U32> -> @b2: Array<U> -> @vb2: Array<U32> -> @c: Array<V> -> @vo3: Array<U32> -> ZVV(~T, ~U, ~V, ~f, q, U32.inc(j), z, c, vo3, a2, va2, b2, vb2, Array.get(T, a2, U32.inc(j)), Array.get(U32, va2, U32.inc(j)), Array.get(U, b2, U32.inc(j)), Array.get(U32, vb2, U32.inc(j))),
  w: &b2: Array<U> -> &y: U -> {b2 == b : Array<U>} & {Array.get(U, b, j) == (b, y) : Array<U> & U} & {y == Laws.rd_at(U, b, j) : U})
  -> ZVV(~T, ~U, ~V, ~f, 1n+q, j, z, out, vout, a, va, b, vb, (a, x), (va, wa), Array.get(U, b, j), Array.get(U32, vb, j)):
  (b2, +y, +eb, e1, ey) = w
  %Equal.sym(Array<U> & U, Array.get(U, b, j), (b, y), e1) : ZVV(~T, ~U, ~V, ~f, 1n+q, j, z, out, vout, a, va, b, vb, (a, x), (va, wa), _, Array.get(U32, vb, j))
  %eb : ZVV(~T, ~U, ~V, ~f, 1n+q, j, z, out, vout, a, va, _, vb, (a, x), (va, wa), (_, y), Array.get(U32, vb, j))
  zvv_s4(~T, ~U, ~V, ~f, q, j, z, out, vout, a, va, b2, vb, x, wa, y, ih, PC.get_w(U32, vb, j))

def zvv_s2(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, q: Nat, +j: U32, +z: V, out: Array<V>, vout: Array<U32>, a: Array<T>, -va: Array<U32>, b: Array<U>, vb: Array<U32>, +x: T,
  ih: @a2: Array<T> -> @va2: Array<U32> -> @b2: Array<U> -> @vb2: Array<U32> -> @c: Array<V> -> @vo3: Array<U32> -> ZVV(~T, ~U, ~V, ~f, q, U32.inc(j), z, c, vo3, a2, va2, b2, vb2, Array.get(T, a2, U32.inc(j)), Array.get(U32, va2, U32.inc(j)), Array.get(U, b2, U32.inc(j)), Array.get(U32, vb2, U32.inc(j))),
  w: &va2: Array<U32> -> &wa: U32 -> {va2 == va : Array<U32>} & {Array.get(U32, va, j) == (va, wa) : Array<U32> & U32} & {wa == Laws.rd_at(U32, va, j) : U32})
  -> ZVV(~T, ~U, ~V, ~f, 1n+q, j, z, out, vout, a, va, b, vb, (a, x), Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j)):
  (va2, +wa, +eva, e1, ewa) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, va, j), (va, wa), e1) : ZVV(~T, ~U, ~V, ~f, 1n+q, j, z, out, vout, a, va, b, vb, (a, x), _, Array.get(U, b, j), Array.get(U32, vb, j))
  %eva : ZVV(~T, ~U, ~V, ~f, 1n+q, j, z, out, vout, a, _, b, vb, (a, x), (_, wa), Array.get(U, b, j), Array.get(U32, vb, j))
  zvv_s3(~T, ~U, ~V, ~f, q, j, z, out, vout, a, va2, b, vb, x, wa, ih, PC.get_w(U, b, j))

def zvv_s1(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, q: Nat, +j: U32, +z: V, out: Array<V>, vout: Array<U32>, -a: Array<T>, va: Array<U32>, b: Array<U>, vb: Array<U32>,
  ih: @a2: Array<T> -> @va2: Array<U32> -> @b2: Array<U> -> @vb2: Array<U32> -> @c: Array<V> -> @vo3: Array<U32> -> ZVV(~T, ~U, ~V, ~f, q, U32.inc(j), z, c, vo3, a2, va2, b2, vb2, Array.get(T, a2, U32.inc(j)), Array.get(U32, va2, U32.inc(j)), Array.get(U, b2, U32.inc(j)), Array.get(U32, vb2, U32.inc(j))),
  w: &a2: Array<T> -> &x: T -> {a2 == a : Array<T>} & {Array.get(T, a, j) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, j) : T})
  -> ZVV(~T, ~U, ~V, ~f, 1n+q, j, z, out, vout, a, va, b, vb, Array.get(T, a, j), Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j)):
  (a2, +x, +ea, e1, ex) = w
  %Equal.sym(Array<T> & T, Array.get(T, a, j), (a, x), e1) : ZVV(~T, ~U, ~V, ~f, 1n+q, j, z, out, vout, a, va, b, vb, _, Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j))
  %ea : ZVV(~T, ~U, ~V, ~f, 1n+q, j, z, out, vout, _, va, b, vb, (_, x), Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j))
  zvv_s2(~T, ~U, ~V, ~f, q, j, z, out, vout, a2, va, b, vb, x, ih, PC.get_w(U32, va, j))

def zvv_go(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, fl: Nat, +j: U32, +z: V, out: Array<V>, vout: Array<U32>, a: Array<T>, va: Array<U32>, b: Array<U>, vb: Array<U32>)
  -> ZVV(~T, ~U, ~V, ~f, fl, j, z, out, vout, a, va, b, vb, Array.get(T, a, j), Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j)):
  match fl:
    case 0n:
      zvv_zero(~T, ~U, ~V, ~f, j, z, out, vout, a, va, b, vb, PC.get_w(T, a, j), PC.get_w(U32, va, j), PC.get_w(U, b, j), PC.get_w(U32, vb, j))
    case 1n++q:
      zvv_s1(~T, ~U, ~V, ~f, q, j, z, out, vout, a, va, b, vb, a2 => va2 => b2 => vb2 => c => vo3 => zvv_go(~T, ~U, ~V, ~f, q, U32.inc(j), z, c, vo3, a2, va2, b2, vb2), PC.get_w(T, a, j))

def Laws.zipv_valid(d, n, a, va, b, vb, z):
  zvv_go(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), U32.to_nat(n), 0, z, Array.new(U32, d, z), Array.new(U32, d, 0), a, va, b, vb)

# ---- Kernel.zipv against vand + zip + fix (Kernel.mask_and, Kernel.zip, Kernel.mask_data) --------------

# the fused value cell, over the production wrapper
def ZVL(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +n: U32, +d: Nat, +z: V, +k: U32, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>) -> Type:
  {Laws.rd_at(V, Laws.zv_o(T, U, V, K.Kernel.zipv(~T, ~U, ~V, ~f, n, d, a, va, b, vb, z)), k) == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : V}

# the unfused cell: Eval.fix (mask_data) over the zip, with Eval.vand's mask_and as the mask
def ZVU(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +n: U32, +d: Nat, +z: V, +k: U32, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>) -> Type:
  {Laws.rd_at(V, Pair.fst(Array<V>, Array<U32>, K.Kernel.mask_data(~V, n, K.Kernel.zip(~T, ~U, ~V, ~f, n, d, a, b, z), K.Kernel.mask_and(n, d, va, vb), z)), k) == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : V}

# the fused cell over the originals: zvo_cell on clones, rewritten back
def zvl_k(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +n: U32, +d: Nat, +z: V, +k: U32, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -a1: Array<T>, -va1: Array<U32>, -b1: Array<U>, -vb1: Array<U32>,
  ea: {a1 == a : Array<T>}, eva: {va1 == va : Array<U32>}, eb: {b1 == b : Array<U>}, evb: {vb1 == vb : Array<U32>}, h: ZVL(~T, ~U, ~V, ~f, n, d, z, k, a1, va1, b1, vb1)) -> ZVL(~T, ~U, ~V, ~f, n, d, z, k, a, va, b, vb):
  %evb : ZVL(~T, ~U, ~V, ~f, n, d, z, k, a, va, b, _)
  %eb : ZVL(~T, ~U, ~V, ~f, n, d, z, k, a, va, _, vb1)
  %eva : ZVL(~T, ~U, ~V, ~f, n, d, z, k, a, _, b1, vb1)
  %ea : ZVL(~T, ~U, ~V, ~f, n, d, z, k, _, va1, b1, vb1)
  h

def zvu_back(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +n: U32, +d: Nat, +z: V, +k: U32, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -a1: Array<T>, -va1: Array<U32>, -b1: Array<U>, -vb1: Array<U32>,
  ea: {a1 == a : Array<T>}, eva: {va1 == va : Array<U32>}, eb: {b1 == b : Array<U>}, evb: {vb1 == vb : Array<U32>}, h: ZVU(~T, ~U, ~V, ~f, n, d, z, k, a1, va1, b1, vb1)) -> ZVU(~T, ~U, ~V, ~f, n, d, z, k, a, va, b, vb):
  %evb : ZVU(~T, ~U, ~V, ~f, n, d, z, k, a, va, b, _)
  %eb : ZVU(~T, ~U, ~V, ~f, n, d, z, k, a, va, _, vb1)
  %eva : ZVU(~T, ~U, ~V, ~f, n, d, z, k, a, _, b1, vb1)
  %ea : ZVU(~T, ~U, ~V, ~f, n, d, z, k, _, va1, b1, vb1)
  h

def lt_addn0(+n: U32, +k: U32, hk: {U32.is_lt(k, n) == True{} : Bool}) -> {U32.is_lt(k, Laws.addn(0, U32.to_nat(n))) == True{} : Bool}:
  %Equal.sym(U32, Laws.addn(0, U32.to_nat(n)), n, B.addn_to_nat(n)) : {U32.is_lt(k, _) == True{} : Bool}
  hk

# the unfused cell from the two zip witnesses (the data zip o and the mask zip mo) and mask_data's
def zvu_md(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +n: U32, +d: Nat, +z: V, +k: U32, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -o: Array<V>, -mo: Array<U32>,
  +eok: {Laws.rd_at(V, o, k) == f(Laws.rd_at(T, a, k), Laws.rd_at(U, b, k)) : V}, +emk: {Laws.rd_at(U32, mo, k) == U32.and(Laws.rd_at(U32, va, k), Laws.rd_at(U32, vb, k)) : U32},
  w: PI.MDW(~V, n, d, o, mo, z, k))
  -> {Laws.rd_at(V, Pair.fst(Array<V>, Array<U32>, K.Kernel.mask_data(~V, n, o, mo, z)), k) == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : V}:
  (o2, mb, emd, emb, wo2, cell) = w
  %Equal.sym(Array<V> & Array<U32>, K.Kernel.mask_data(~V, n, o, mo, z), (o2, mb), emd) : {Laws.rd_at(V, Pair.fst(Array<V>, Array<U32>, _), k) == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : V}
  %Equal.sym(V, Laws.rd_at(V, o2, k), Laws.rdN(V, d, o2, k), Laws.rd_at_wf(V, d, o2, k, wo2)) : {_ == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : V}
  %Equal.sym(V, Laws.rdN(V, d, o2, k), Bool.pick(V, U32.is_ne(Laws.rd_at(U32, mo, k), 0), Laws.rd_at(V, o, k), z), cell) : {_ == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : V}
  %Equal.sym(U32, Laws.rd_at(U32, mo, k), U32.and(Laws.rd_at(U32, va, k), Laws.rd_at(U32, vb, k)), emk) : {Bool.pick(V, U32.is_ne(_, 0), Laws.rd_at(V, o, k), z) == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : V}
  %Equal.sym(V, Laws.rd_at(V, o, k), f(Laws.rd_at(T, a, k), Laws.rd_at(U, b, k)), eok) : {Bool.pick(V, U32.is_ne(U32.and(Laws.rd_at(U32, va, k), Laws.rd_at(U32, vb, k)), 0), _, z) == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : V}
  {==}

# the cells of the two zip outputs (o, mo: each read twice, so each is cloned with its well-formedness)
def zvu_c(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +n: U32, +d: Nat, +z: V, +k: U32, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -o: Array<V>, -mo: Array<U32>, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hk: {U32.is_lt(k, n) == True{} : Bool},
  co: @k2: U32 -> {U32.is_lt(k2, Laws.addn(0, U32.to_nat(n))) == True{} : Bool} -> {Laws.rdN(V, d, o, k2) == f(Laws.rd_at(T, a, k2), Laws.rd_at(U, b, k2)) : V},
  cmo: @k2: U32 -> {U32.is_lt(k2, Laws.addn(0, U32.to_nat(n))) == True{} : Bool} -> {Laws.rdN(U32, d, mo, k2) == U32.and(Laws.rd_at(U32, va, k2), Laws.rd_at(U32, vb, k2)) : U32},
  wo: &o1: Array<V> -> &o2: Array<V> -> {o1 == o : Array<V>} & {o2 == o : Array<V>} & Laws.WFArray(V, d, o1) & Laws.WFArray(V, d, o2),
  wm: &m1: Array<U32> -> &m2: Array<U32> -> {m1 == mo : Array<U32>} & {m2 == mo : Array<U32>} & Laws.WFArray(U32, d, m1) & Laws.WFArray(U32, d, m2))
  -> {Laws.rd_at(V, Pair.fst(Array<V>, Array<U32>, K.Kernel.mask_data(~V, n, o, mo, z)), k) == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : V}:
  (o1, o2, eo1, eo2, wo1, wo2) = wo
  (m1, m2, em1, em2, wm1, wm2) = wm
  +hk2 = lt_addn0(n, k, hk)
  zvu_md(~T, ~U, ~V, ~f, n, d, z, k, a, va, b, vb, o, mo,
    Equal.trans(V, Laws.rd_at(V, o, k), Laws.rdN(V, d, o, k), f(Laws.rd_at(T, a, k), Laws.rd_at(U, b, k)), (%eo2 : {Laws.rd_at(V, _, k) == Laws.rdN(V, d, _, k) : V}; Laws.rd_at_wf(V, d, o2, k, wo2)), co(k, hk2)),
    Equal.trans(U32, Laws.rd_at(U32, mo, k), Laws.rdN(U32, d, mo, k), U32.and(Laws.rd_at(U32, va, k), Laws.rd_at(U32, vb, k)), (%em2 : {Laws.rd_at(U32, _, k) == Laws.rdN(U32, d, _, k) : U32}; Laws.rd_at_wf(U32, d, m2, k, wm2)), cmo(k, hk2)),
    (%em1 : PI.MDW(~V, n, d, o, _, z, k); %eo1 : PI.MDW(~V, n, d, _, m1, z, k); PI.mask_data_w(~V, n, d, o1, m1, z, k, wo1, fits, hk)))

def zvu_zm(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +n: U32, +d: Nat, +z: V, +k: U32, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hk: {U32.is_lt(k, n) == True{} : Bool},
  wz: &o: Array<V> -> {K.Kernel.zip.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, Array.new(V, d, z), Array.get(T, a, 0), Array.get(U, b, 0)) == o : Array<V>} & PC.ZRes(~T, ~U, ~V, ~f, d, a, b, o, Laws.addn(0, U32.to_nat(n))),
  wm: &mo: Array<U32> -> {K.Kernel.zip.go(~U32, ~U32, ~U32, ~(x => y => U32.and(x, y)), U32.to_nat(n), 0, Array.new(U32, d, 0), Array.get(U32, va, 0), Array.get(U32, vb, 0)) == mo : Array<U32>} & PC.ZRes(~U32, ~U32, ~U32, ~(x => y => U32.and(x, y)), d, va, vb, mo, Laws.addn(0, U32.to_nat(n))))
  -> ZVU(~T, ~U, ~V, ~f, n, d, z, k, a, va, b, vb):
  (o, eo, wo, co) = wz
  (mo, emo, wmo, cmo) = wm
  %Equal.sym(Array<V>, K.Kernel.zip.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, Array.new(V, d, z), Array.get(T, a, 0), Array.get(U, b, 0)), o, eo) : {Laws.rd_at(V, Pair.fst(Array<V>, Array<U32>, K.Kernel.mask_data(~V, n, _, K.Kernel.mask_and(n, d, va, vb), z)), k) == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : V}
  %Equal.sym(Array<U32>, K.Kernel.zip.go(~U32, ~U32, ~U32, ~(x => y => U32.and(x, y)), U32.to_nat(n), 0, Array.new(U32, d, 0), Array.get(U32, va, 0), Array.get(U32, vb, 0)), mo, emo) : {Laws.rd_at(V, Pair.fst(Array<V>, Array<U32>, K.Kernel.mask_data(~V, n, o, _, z)), k) == zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : V}
  zvu_c(~T, ~U, ~V, ~f, n, d, z, k, a, va, b, vb, o, mo, fits, hk, co, cmo, PC.clone_wf(V, d, o, wo), PC.clone_wf(U32, d, mo, wmo))

def zvu_cell(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +n: U32, +d: Nat, +z: V, +k: U32, a: Array<T>, va: Array<U32>, b: Array<U>, vb: Array<U32>, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hk: {U32.is_lt(k, n) == True{} : Bool})
  -> ZVU(~T, ~U, ~V, ~f, n, d, z, k, a, va, b, vb):
  zvu_zm(~T, ~U, ~V, ~f, n, d, z, k, a, va, b, vb, fits, hk,
    PC.zip_go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, d, a, b, Array.new(V, d, z), Laws.wf_new(V, d, z), B.room_from(d, n, fits))(PC.zhyp0(~T, ~U, ~V, ~f, d, a, b, Array.new(V, d, z))),
    PC.zip_go(~U32, ~U32, ~U32, ~(x => y => U32.and(x, y)), U32.to_nat(n), 0, d, va, vb, Array.new(U32, d, 0), Laws.wf_new(U32, d, 0), B.room_from(d, n, fits))(PC.zhyp0(~U32, ~U32, ~U32, ~(x => y => U32.and(x, y)), d, va, vb, Array.new(U32, d, 0))))

def zvf_k(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +n: U32, +d: Nat, +z: V, +k: U32, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hk: {U32.is_lt(k, n) == True{} : Bool},
  wa: &a1: Array<T> -> &a2: Array<T> -> {a1 == a : Array<T>} & {a2 == a : Array<T>}, wva: &va1: Array<U32> -> &va2: Array<U32> -> {va1 == va : Array<U32>} & {va2 == va : Array<U32>},
  wb: &b1: Array<U> -> &b2: Array<U> -> {b1 == b : Array<U>} & {b2 == b : Array<U>}, wvb: &vb1: Array<U32> -> &vb2: Array<U32> -> {vb1 == vb : Array<U32>} & {vb2 == vb : Array<U32>})
  -> {Laws.rd_at(V, Laws.zv_o(T, U, V, K.Kernel.zipv(~T, ~U, ~V, ~f, n, d, a, va, b, vb, z)), k) == Laws.rd_at(V, Pair.fst(Array<V>, Array<U32>, K.Kernel.mask_data(~V, n, K.Kernel.zip(~T, ~U, ~V, ~f, n, d, a, b, z), K.Kernel.mask_and(n, d, va, vb), z)), k) : V}:
  (a1, a2, ea1, ea2) = wa
  (va1, va2, eva1, eva2) = wva
  (b1, b2, eb1, eb2) = wb
  (vb1, vb2, evb1, evb2) = wvb
  Equal.trans(V, Laws.rd_at(V, Laws.zv_o(T, U, V, K.Kernel.zipv(~T, ~U, ~V, ~f, n, d, a, va, b, vb, z)), k), zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)), Laws.rd_at(V, Pair.fst(Array<V>, Array<U32>, K.Kernel.mask_data(~V, n, K.Kernel.zip(~T, ~U, ~V, ~f, n, d, a, b, z), K.Kernel.mask_and(n, d, va, vb), z)), k),
    zvl_k(~T, ~U, ~V, ~f, n, d, z, k, a, va, b, vb, a1, va1, b1, vb1, ea1, eva1, eb1, evb1, zvo_cell(~T, ~U, ~V, ~f, d, n, a1, va1, b1, vb1, z, k, fits, hk)),
    Equal.sym(V, Laws.rd_at(V, Pair.fst(Array<V>, Array<U32>, K.Kernel.mask_data(~V, n, K.Kernel.zip(~T, ~U, ~V, ~f, n, d, a, b, z), K.Kernel.mask_and(n, d, va, vb), z)), k), zvc(~T, ~U, ~V, ~f, z, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)),
      zvu_back(~T, ~U, ~V, ~f, n, d, z, k, a, va, b, vb, a2, va2, b2, vb2, ea2, eva2, eb2, evb2, zvu_cell(~T, ~U, ~V, ~f, n, d, z, k, a2, va2, b2, vb2, fits, hk))))

# zipv == the unfused passes, cell by cell, for any template (the laws are its instances)
def zv_unfused(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +n: U32, +d: Nat, +z: V, +k: U32, a: Array<T>, va: Array<U32>, b: Array<U>, vb: Array<U32>, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hk: {U32.is_lt(k, n) == True{} : Bool})
  -> {Laws.rd_at(V, Laws.zv_o(T, U, V, K.Kernel.zipv(~T, ~U, ~V, ~f, n, d, a, va, b, vb, z)), k) == Laws.rd_at(V, Pair.fst(Array<V>, Array<U32>, K.Kernel.mask_data(~V, n, K.Kernel.zip(~T, ~U, ~V, ~f, n, d, a, b, z), K.Kernel.mask_and(n, d, va, vb), z)), k) : V}:
  zvf_k(~T, ~U, ~V, ~f, n, d, z, k, a, va, b, vb, fits, hk, PC.clone_eq(T, a), PC.clone_eq(U32, va), PC.clone_eq(U, b), PC.clone_eq(U32, vb))

def Laws.zipv_unfused(d, n, a, va, b, vb, z, k, fits, hk):
  zv_unfused(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, d, z, k, a, va, b, vb, fits, hk)

def Laws.zipv_unfused_f32(d, n, a, va, b, vb, z, k, fits, hk):
  zv_unfused(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, z, k, a, va, b, vb, fits, hk)

# ---- Kernel.pred_count: the mask cell (four reads, one tracked output; the count is carried) -----------

# the word pred_count writes (and adds to the count) at a row: the predicate where both validity words
# are set, 0 where either is not
def pcc(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, +p: P, +x: T, +wa: U32, +y: U, +wb: U32) -> U32:
  Bool.pick(U32, U32.is_ne(U32.and(wa, wb), 0), f(p, x, y), 0)

def PCOHyp(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, +j: U32, +p: P, +d: Nat, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -out: Array<U32>) -> Type:
  @k: U32 -> {U32.is_lt(k, j) == True{} : Bool} -> {Laws.rdN(U32, d, out, k) == pcc(~T, ~U, ~P, ~f, p, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : U32}

def PCORes(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, +p: P, +d: Nat, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, o: Array<U32>, +bound: U32) -> Type:
  Laws.WFArray(U32, d, o) & (@k: U32 -> {U32.is_lt(k, bound) == True{} : Bool} -> {Laws.rdN(U32, d, o, k) == pcc(~T, ~U, ~P, ~f, p, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : U32})

def PCOGoal(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, fl: Nat, +j: U32, +cnt: U32, +p: P, +d: Nat, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -out: Array<U32>, -ra: Array<T> & T, -rva: Array<U32> & U32, -rb: Array<U> & U, -rvb: Array<U32> & U32) -> Type:
  PCOHyp(~T, ~U, ~P, ~f, j, p, d, a, va, b, vb, out) -> &o: Array<U32> -> {Laws.pc_m(T, U, K.Kernel.pred_count.go(~T, ~U, ~P, ~f, fl, j, cnt, p, out, ra, rva, rb, rvb)) == o : Array<U32>} & PCORes(~T, ~U, ~P, ~f, p, d, a, va, b, vb, o, Laws.addn(j, fl))

def PCOSet(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, q: Nat, +j: U32, +cnt2: U32, +p: P, +d: Nat, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -out: Array<U32>, +y: U32) -> Type:
  PCOHyp(~T, ~U, ~P, ~f, j, p, d, a, va, b, vb, out) -> &o: Array<U32> -> {Laws.pc_m(T, U, K.Kernel.pred_count.go(~T, ~U, ~P, ~f, q, U32.inc(j), cnt2, p, Array.set(U32, out, j, y), Array.get(T, a, U32.inc(j)), Array.get(U32, va, U32.inc(j)), Array.get(U, b, U32.inc(j)), Array.get(U32, vb, U32.inc(j)))) == o : Array<U32>} & PCORes(~T, ~U, ~P, ~f, p, d, a, va, b, vb, o, Laws.addn(j, 1n+q))

def PCOC(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, q: Nat, +j: U32, +cnt2: U32, +p: P, +d: Nat, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -out: Array<U32>, -c: Array<U32>, +bound: U32) -> Type:
  PCOHyp(~T, ~U, ~P, ~f, j, p, d, a, va, b, vb, out) -> &o: Array<U32> -> {Laws.pc_m(T, U, K.Kernel.pred_count.go(~T, ~U, ~P, ~f, q, U32.inc(j), cnt2, p, c, Array.get(T, a, U32.inc(j)), Array.get(U32, va, U32.inc(j)), Array.get(U, b, U32.inc(j)), Array.get(U32, vb, U32.inc(j)))) == o : Array<U32>} & PCORes(~T, ~U, ~P, ~f, p, d, a, va, b, vb, o, bound)

def pconext_lt(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, +d: Nat, +j: U32, +k: U32, +p: P, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -out: Array<U32>, -c: Array<U32>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +y: U32, g: PCOHyp(~T, ~U, ~P, ~f, j, p, d, a, va, b, vb, out),
  fj: @k2: U32 -> {Laws.rdN(U32, d, c, k2) == Bool.pick(U32, Laws.same_at(d, j, k2), y, Laws.rdN(U32, d, out, k2)) : U32}, +lt: {U32.is_lt(k, j) == True{} : Bool})
  -> {Laws.rdN(U32, d, c, k) == pcc(~T, ~U, ~P, ~f, p, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : U32}:
  %Equal.sym(U32, Laws.rdN(U32, d, c, k), Bool.pick(U32, Laws.same_at(d, j, k), y, Laws.rdN(U32, d, out, k)), fj(k)) : {_ == pcc(~T, ~U, ~P, ~f, p, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : U32}
  %Equal.sym(Bool, Laws.same_at(d, j, k), False{}, PC.same_false_lt(d, j, k, hj, lt)) : {Bool.pick(U32, _, y, Laws.rdN(U32, d, out, k)) == pcc(~T, ~U, ~P, ~f, p, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : U32}
  g(k, lt)

def pconext_b(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, bb: Bool, +d: Nat, +j: U32, +k: U32, +p: P, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -out: Array<U32>, -c: Array<U32>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +y: U32,
  ey: {y == pcc(~T, ~U, ~P, ~f, p, Laws.rd_at(T, a, j), Laws.rd_at(U32, va, j), Laws.rd_at(U, b, j), Laws.rd_at(U32, vb, j)) : U32}, g: PCOHyp(~T, ~U, ~P, ~f, j, p, d, a, va, b, vb, out),
  fj: @k2: U32 -> {Laws.rdN(U32, d, c, k2) == Bool.pick(U32, Laws.same_at(d, j, k2), y, Laws.rdN(U32, d, out, k2)) : U32}, s: PC.IncLtU(bb, k, j))
  -> {Laws.rdN(U32, d, c, k) == pcc(~T, ~U, ~P, ~f, p, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : U32}:
  match bb:
    case True{}:
      pconext_lt(~T, ~U, ~P, ~f, d, j, k, p, a, va, b, vb, out, c, hj, y, g, fj, s)
    case False{}:
      %Equal.sym(U32, k, j, s) : {Laws.rdN(U32, d, c, _) == pcc(~T, ~U, ~P, ~f, p, Laws.rd_at(T, a, _), Laws.rd_at(U32, va, _), Laws.rd_at(U, b, _), Laws.rd_at(U32, vb, _)) : U32}
      %Equal.sym(U32, Laws.rdN(U32, d, c, j), Bool.pick(U32, Laws.same_at(d, j, j), y, Laws.rdN(U32, d, out, j)), fj(j)) : {_ == pcc(~T, ~U, ~P, ~f, p, Laws.rd_at(T, a, j), Laws.rd_at(U32, va, j), Laws.rd_at(U, b, j), Laws.rd_at(U32, vb, j)) : U32}
      %Equal.sym(Bool, Laws.same_at(d, j, j), True{}, PC.same_at_refl(d, j)) : {Bool.pick(U32, _, y, Laws.rdN(U32, d, out, j)) == pcc(~T, ~U, ~P, ~f, p, Laws.rd_at(T, a, j), Laws.rd_at(U32, va, j), Laws.rd_at(U, b, j), Laws.rd_at(U32, vb, j)) : U32}
      ey

def pconext_k(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, +d: Nat, +j: U32, +k: U32, +p: P, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -out: Array<U32>, -c: Array<U32>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +y: U32,
  ey: {y == pcc(~T, ~U, ~P, ~f, p, Laws.rd_at(T, a, j), Laws.rd_at(U32, va, j), Laws.rd_at(U, b, j), Laws.rd_at(U32, vb, j)) : U32}, g: PCOHyp(~T, ~U, ~P, ~f, j, p, d, a, va, b, vb, out),
  fj: @k2: U32 -> {Laws.rdN(U32, d, c, k2) == Bool.pick(U32, Laws.same_at(d, j, k2), y, Laws.rdN(U32, d, out, k2)) : U32}, w: &bb: Bool -> PC.IncLtU(bb, k, j))
  -> {Laws.rdN(U32, d, c, k) == pcc(~T, ~U, ~P, ~f, p, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : U32}:
  (bb, s) = w
  pconext_b(~T, ~U, ~P, ~f, bb, d, j, k, p, a, va, b, vb, out, c, hj, y, ey, g, fj, s)

def pconext(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, +d: Nat, +j: U32, +p: P, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -out: Array<U32>, -c: Array<U32>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +y: U32,
  +ey: {y == pcc(~T, ~U, ~P, ~f, p, Laws.rd_at(T, a, j), Laws.rd_at(U32, va, j), Laws.rd_at(U, b, j), Laws.rd_at(U32, vb, j)) : U32}, g: PCOHyp(~T, ~U, ~P, ~f, j, p, d, a, va, b, vb, out),
  fj: @k2: U32 -> {Laws.rdN(U32, d, c, k2) == Bool.pick(U32, Laws.same_at(d, j, k2), y, Laws.rdN(U32, d, out, k2)) : U32})
  -> PCOHyp(~T, ~U, ~P, ~f, U32.inc(j), p, d, a, va, b, vb, c):
  +k => hk => pconext_k(~T, ~U, ~P, ~f, d, j, k, p, a, va, b, vb, out, c, hj, y, ey, g, fj, PC.inc_lt_u(k, j, hk))

def pco_s5(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, q: Nat, +j: U32, +cnt2: U32, +p: P, +d: Nat, a: Array<T>, va: Array<U32>, b: Array<U>, vb: Array<U32>, -out: Array<U32>, +y: U32,
  +ey: {y == pcc(~T, ~U, ~P, ~f, p, Laws.rd_at(T, a, j), Laws.rd_at(U32, va, j), Laws.rd_at(U, b, j), Laws.rd_at(U32, vb, j)) : U32}, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, room: Laws.Room(d, U32.inc(j), q),
  ih: @a2: Array<T> -> @va2: Array<U32> -> @b2: Array<U> -> @vb2: Array<U32> -> @cnt3: U32 -> @c: Array<U32> -> Laws.WFArray(U32, d, c) -> Laws.Room(d, U32.inc(j), q) -> PCOGoal(~T, ~U, ~P, ~f, q, U32.inc(j), cnt3, p, d, a2, va2, b2, vb2, c, Array.get(T, a2, U32.inc(j)), Array.get(U32, va2, U32.inc(j)), Array.get(U, b2, U32.inc(j)), Array.get(U32, vb2, U32.inc(j))),
  w: &c: Array<U32> -> {Array.set(U32, out, j, y) == c : Array<U32>} & Laws.WFArray(U32, d, c) & (@k2: U32 -> {Laws.rdN(U32, d, c, k2) == Bool.pick(U32, Laws.same_at(d, j, k2), y, Laws.rdN(U32, d, out, k2)) : U32}) & (@k2: U32 -> {Laws.rd_at(U32, out, k2) == Laws.rdN(U32, d, out, k2) : U32}))
  -> PCOSet(~T, ~U, ~P, ~f, q, j, cnt2, p, d, a, va, b, vb, out, y):
  (c, ec, wc, fj, cv) = w
  %Equal.sym(Array<U32>, Array.set(U32, out, j, y), c, ec) : PCOC(~T, ~U, ~P, ~f, q, j, cnt2, p, d, a, va, b, vb, out, _, Laws.addn(j, 1n+q))
  %PC.addn_inc(j, q) : PCOC(~T, ~U, ~P, ~f, q, j, cnt2, p, d, a, va, b, vb, out, c, _)
  g => ih(a, va, b, vb, cnt2, c, wc, room)(pconext(~T, ~U, ~P, ~f, d, j, p, a, va, b, vb, out, c, hj, y, ey, g, fj))

# the predicate word's model from the four read equations
def pcc_eq(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, +p: P, +j: U32, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, +x: T, +wa: U32, +y: U, +wb: U32,
  ex: {x == Laws.rd_at(T, a, j) : T}, ewa: {wa == Laws.rd_at(U32, va, j) : U32}, ey: {y == Laws.rd_at(U, b, j) : U}, ewb: {wb == Laws.rd_at(U32, vb, j) : U32})
  -> {pcc(~T, ~U, ~P, ~f, p, x, wa, y, wb) == pcc(~T, ~U, ~P, ~f, p, Laws.rd_at(T, a, j), Laws.rd_at(U32, va, j), Laws.rd_at(U, b, j), Laws.rd_at(U32, vb, j)) : U32}:
  %ex : {pcc(~T, ~U, ~P, ~f, p, x, wa, y, wb) == pcc(~T, ~U, ~P, ~f, p, _, Laws.rd_at(U32, va, j), Laws.rd_at(U, b, j), Laws.rd_at(U32, vb, j)) : U32}
  %ewa : {pcc(~T, ~U, ~P, ~f, p, x, wa, y, wb) == pcc(~T, ~U, ~P, ~f, p, x, _, Laws.rd_at(U, b, j), Laws.rd_at(U32, vb, j)) : U32}
  %ey : {pcc(~T, ~U, ~P, ~f, p, x, wa, y, wb) == pcc(~T, ~U, ~P, ~f, p, x, wa, _, Laws.rd_at(U32, vb, j)) : U32}
  %ewb : {pcc(~T, ~U, ~P, ~f, p, x, wa, y, wb) == pcc(~T, ~U, ~P, ~f, p, x, wa, y, _) : U32}
  {==}

def pco_s4(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, q: Nat, +j: U32, +cnt: U32, +p: P, +d: Nat, a: Array<T>, va: Array<U32>, b: Array<U>, -vb: Array<U32>, out: Array<U32>, wf: Laws.WFArray(U32, d, out),
  +x: T, +ex: {x == Laws.rd_at(T, a, j) : T}, +wa: U32, +ewa: {wa == Laws.rd_at(U32, va, j) : U32}, +y: U, +ey: {y == Laws.rd_at(U, b, j) : U}, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, room: Laws.Room(d, U32.inc(j), q),
  ih: @a2: Array<T> -> @va2: Array<U32> -> @b2: Array<U> -> @vb2: Array<U32> -> @cnt3: U32 -> @c: Array<U32> -> Laws.WFArray(U32, d, c) -> Laws.Room(d, U32.inc(j), q) -> PCOGoal(~T, ~U, ~P, ~f, q, U32.inc(j), cnt3, p, d, a2, va2, b2, vb2, c, Array.get(T, a2, U32.inc(j)), Array.get(U32, va2, U32.inc(j)), Array.get(U, b2, U32.inc(j)), Array.get(U32, vb2, U32.inc(j))),
  w: &vb2: Array<U32> -> &wb: U32 -> {vb2 == vb : Array<U32>} & {Array.get(U32, vb, j) == (vb, wb) : Array<U32> & U32} & {wb == Laws.rd_at(U32, vb, j) : U32})
  -> PCOGoal(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, d, a, va, b, vb, out, (a, x), (va, wa), (b, y), Array.get(U32, vb, j)):
  (vb2, +wb, +evb, e1, ewb) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, vb, j), (vb, wb), e1) : PCOGoal(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, d, a, va, b, vb, out, (a, x), (va, wa), (b, y), _)
  %evb : PCOGoal(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, d, a, va, b, _, out, (a, x), (va, wa), (b, y), (_, wb))
  pco_s5(~T, ~U, ~P, ~f, q, j, U32.add(cnt, pcc(~T, ~U, ~P, ~f, p, x, wa, y, wb)), p, d, a, va, b, vb2, out, pcc(~T, ~U, ~P, ~f, p, x, wa, y, wb),
    pcc_eq(~T, ~U, ~P, ~f, p, j, a, va, b, vb2, x, wa, y, wb, ex, ewa, ey, Equal.trans(U32, wb, Laws.rd_at(U32, vb, j), Laws.rd_at(U32, vb2, j), ewb, Equal.sym(U32, Laws.rd_at(U32, vb2, j), Laws.rd_at(U32, vb, j), Equal.cong(Array<U32>, U32, r => Laws.rd_at(U32, r, j), vb2, vb, evb)))),
    hj, room, ih, PC.set_other_w(U32, d, out, j, pcc(~T, ~U, ~P, ~f, p, x, wa, y, wb), wf))

def pco_s3(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, q: Nat, +j: U32, +cnt: U32, +p: P, +d: Nat, a: Array<T>, va: Array<U32>, -b: Array<U>, vb: Array<U32>, out: Array<U32>, wf: Laws.WFArray(U32, d, out),
  +x: T, +ex: {x == Laws.rd_at(T, a, j) : T}, +wa: U32, +ewa: {wa == Laws.rd_at(U32, va, j) : U32}, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, room: Laws.Room(d, U32.inc(j), q),
  ih: @a2: Array<T> -> @va2: Array<U32> -> @b2: Array<U> -> @vb2: Array<U32> -> @cnt3: U32 -> @c: Array<U32> -> Laws.WFArray(U32, d, c) -> Laws.Room(d, U32.inc(j), q) -> PCOGoal(~T, ~U, ~P, ~f, q, U32.inc(j), cnt3, p, d, a2, va2, b2, vb2, c, Array.get(T, a2, U32.inc(j)), Array.get(U32, va2, U32.inc(j)), Array.get(U, b2, U32.inc(j)), Array.get(U32, vb2, U32.inc(j))),
  w: &b2: Array<U> -> &y: U -> {b2 == b : Array<U>} & {Array.get(U, b, j) == (b, y) : Array<U> & U} & {y == Laws.rd_at(U, b, j) : U})
  -> PCOGoal(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, d, a, va, b, vb, out, (a, x), (va, wa), Array.get(U, b, j), Array.get(U32, vb, j)):
  (b2, +y, +eb, e1, ey) = w
  %Equal.sym(Array<U> & U, Array.get(U, b, j), (b, y), e1) : PCOGoal(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, d, a, va, b, vb, out, (a, x), (va, wa), _, Array.get(U32, vb, j))
  %eb : PCOGoal(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, d, a, va, _, vb, out, (a, x), (va, wa), (_, y), Array.get(U32, vb, j))
  pco_s4(~T, ~U, ~P, ~f, q, j, cnt, p, d, a, va, b2, vb, out, wf, x, ex, wa, ewa, y, Equal.trans(U, y, Laws.rd_at(U, b, j), Laws.rd_at(U, b2, j), ey, Equal.sym(U, Laws.rd_at(U, b2, j), Laws.rd_at(U, b, j), Equal.cong(Array<U>, U, r => Laws.rd_at(U, r, j), b2, b, eb))), hj, room, ih, PC.get_w(U32, vb, j))

def pco_s2(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, q: Nat, +j: U32, +cnt: U32, +p: P, +d: Nat, a: Array<T>, -va: Array<U32>, b: Array<U>, vb: Array<U32>, out: Array<U32>, wf: Laws.WFArray(U32, d, out),
  +x: T, +ex: {x == Laws.rd_at(T, a, j) : T}, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, room: Laws.Room(d, U32.inc(j), q),
  ih: @a2: Array<T> -> @va2: Array<U32> -> @b2: Array<U> -> @vb2: Array<U32> -> @cnt3: U32 -> @c: Array<U32> -> Laws.WFArray(U32, d, c) -> Laws.Room(d, U32.inc(j), q) -> PCOGoal(~T, ~U, ~P, ~f, q, U32.inc(j), cnt3, p, d, a2, va2, b2, vb2, c, Array.get(T, a2, U32.inc(j)), Array.get(U32, va2, U32.inc(j)), Array.get(U, b2, U32.inc(j)), Array.get(U32, vb2, U32.inc(j))),
  w: &va2: Array<U32> -> &wa: U32 -> {va2 == va : Array<U32>} & {Array.get(U32, va, j) == (va, wa) : Array<U32> & U32} & {wa == Laws.rd_at(U32, va, j) : U32})
  -> PCOGoal(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, d, a, va, b, vb, out, (a, x), Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j)):
  (va2, +wa, +eva, e1, ewa) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, va, j), (va, wa), e1) : PCOGoal(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, d, a, va, b, vb, out, (a, x), _, Array.get(U, b, j), Array.get(U32, vb, j))
  %eva : PCOGoal(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, d, a, _, b, vb, out, (a, x), (_, wa), Array.get(U, b, j), Array.get(U32, vb, j))
  pco_s3(~T, ~U, ~P, ~f, q, j, cnt, p, d, a, va2, b, vb, out, wf, x, ex, wa, Equal.trans(U32, wa, Laws.rd_at(U32, va, j), Laws.rd_at(U32, va2, j), ewa, Equal.sym(U32, Laws.rd_at(U32, va2, j), Laws.rd_at(U32, va, j), Equal.cong(Array<U32>, U32, r => Laws.rd_at(U32, r, j), va2, va, eva))), hj, room, ih, PC.get_w(U, b, j))

def pco_s1(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, q: Nat, +j: U32, +cnt: U32, +p: P, +d: Nat, -a: Array<T>, va: Array<U32>, b: Array<U>, vb: Array<U32>, out: Array<U32>, wf: Laws.WFArray(U32, d, out), room: Laws.Room(d, j, 1n+q),
  ih: @a2: Array<T> -> @va2: Array<U32> -> @b2: Array<U> -> @vb2: Array<U32> -> @cnt3: U32 -> @c: Array<U32> -> Laws.WFArray(U32, d, c) -> Laws.Room(d, U32.inc(j), q) -> PCOGoal(~T, ~U, ~P, ~f, q, U32.inc(j), cnt3, p, d, a2, va2, b2, vb2, c, Array.get(T, a2, U32.inc(j)), Array.get(U32, va2, U32.inc(j)), Array.get(U, b2, U32.inc(j)), Array.get(U32, vb2, U32.inc(j))),
  w: &a2: Array<T> -> &x: T -> {a2 == a : Array<T>} & {Array.get(T, a, j) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, j) : T})
  -> PCOGoal(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, d, a, va, b, vb, out, Array.get(T, a, j), Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j)):
  (hj, room2) = room
  (a2, +x, +ea, e1, ex) = w
  %Equal.sym(Array<T> & T, Array.get(T, a, j), (a, x), e1) : PCOGoal(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, d, a, va, b, vb, out, _, Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j))
  %ea : PCOGoal(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, d, _, va, b, vb, out, (_, x), Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j))
  pco_s2(~T, ~U, ~P, ~f, q, j, cnt, p, d, a2, va, b, vb, out, wf, x, Equal.trans(T, x, Laws.rd_at(T, a, j), Laws.rd_at(T, a2, j), ex, Equal.sym(T, Laws.rd_at(T, a2, j), Laws.rd_at(T, a, j), Equal.cong(Array<T>, T, r => Laws.rd_at(T, r, j), a2, a, ea))), hj, room2, ih, PC.get_w(U32, va, j))

def pco_zero(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, +j: U32, +cnt: U32, +p: P, +d: Nat, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, out: Array<U32>, wf: Laws.WFArray(U32, d, out),
  wa: &a2: Array<T> -> &x: T -> {a2 == a : Array<T>} & {Array.get(T, a, j) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, j) : T},
  wva: &va2: Array<U32> -> &x2: U32 -> {va2 == va : Array<U32>} & {Array.get(U32, va, j) == (va, x2) : Array<U32> & U32} & {x2 == Laws.rd_at(U32, va, j) : U32},
  wb: &b2: Array<U> -> &y: U -> {b2 == b : Array<U>} & {Array.get(U, b, j) == (b, y) : Array<U> & U} & {y == Laws.rd_at(U, b, j) : U},
  wvb: &vb2: Array<U32> -> &y2: U32 -> {vb2 == vb : Array<U32>} & {Array.get(U32, vb, j) == (vb, y2) : Array<U32> & U32} & {y2 == Laws.rd_at(U32, vb, j) : U32})
  -> PCOGoal(~T, ~U, ~P, ~f, 0n, j, cnt, p, d, a, va, b, vb, out, Array.get(T, a, j), Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j)):
  (a2, +x, ea, e1, ex) = wa
  (va2, +x2, eva, e2, ex2) = wva
  (b2, +y, eb, e3, ey) = wb
  (vb2, +y2, evb, e4, ey2) = wvb
  %Equal.sym(Array<T> & T, Array.get(T, a, j), (a, x), e1) : PCOGoal(~T, ~U, ~P, ~f, 0n, j, cnt, p, d, a, va, b, vb, out, _, Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j))
  %Equal.sym(Array<U32> & U32, Array.get(U32, va, j), (va, x2), e2) : PCOGoal(~T, ~U, ~P, ~f, 0n, j, cnt, p, d, a, va, b, vb, out, (a, x), _, Array.get(U, b, j), Array.get(U32, vb, j))
  %Equal.sym(Array<U> & U, Array.get(U, b, j), (b, y), e3) : PCOGoal(~T, ~U, ~P, ~f, 0n, j, cnt, p, d, a, va, b, vb, out, (a, x), (va, x2), _, Array.get(U32, vb, j))
  %Equal.sym(Array<U32> & U32, Array.get(U32, vb, j), (vb, y2), e4) : PCOGoal(~T, ~U, ~P, ~f, 0n, j, cnt, p, d, a, va, b, vb, out, (a, x), (va, x2), (b, y), _)
  g => (out, {==}, wf, g)

def pco_go(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, fl: Nat, +j: U32, +cnt: U32, +p: P, +d: Nat, a: Array<T>, va: Array<U32>, b: Array<U>, vb: Array<U32>, out: Array<U32>, wf: Laws.WFArray(U32, d, out), room: Laws.Room(d, j, fl))
  -> PCOGoal(~T, ~U, ~P, ~f, fl, j, cnt, p, d, a, va, b, vb, out, Array.get(T, a, j), Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j)):
  match fl:
    case 0n:
      pco_zero(~T, ~U, ~P, ~f, j, cnt, p, d, a, va, b, vb, out, wf, PC.get_w(T, a, j), PC.get_w(U32, va, j), PC.get_w(U, b, j), PC.get_w(U32, vb, j))
    case 1n++q:
      pco_s1(~T, ~U, ~P, ~f, q, j, cnt, p, d, a, va, b, vb, out, wf, room, a2 => va2 => b2 => vb2 => cnt3 => c => wc => room2 => pco_go(~T, ~U, ~P, ~f, q, U32.inc(j), cnt3, p, d, a2, va2, b2, vb2, c, wc, room2), PC.get_w(T, a, j))

def pcohyp0(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, +p: P, +d: Nat, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -out: Array<U32>) -> PCOHyp(~T, ~U, ~P, ~f, 0, p, d, a, va, b, vb, out):
  +k => hk => Empty.absurd({Laws.rdN(U32, d, out, k) == pcc(~T, ~U, ~P, ~f, p, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : U32}, PC.lt0(k, hk))

# the mask cell over the production wrapper
def PCL(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, +n: U32, +d: Nat, +p: P, +k: U32, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>) -> Type:
  {Laws.rd_at(U32, Laws.pc_m(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb)), k) == pcc(~T, ~U, ~P, ~f, p, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : U32}

def pco_fin(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, +d: Nat, +n: U32, +p: P, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, +k: U32, hk: {U32.is_lt(k, n) == True{} : Bool},
  w: &o: Array<U32> -> {Laws.pc_m(T, U, K.Kernel.pred_count.go(~T, ~U, ~P, ~f, U32.to_nat(n), 0, 0, p, Array.new(U32, d, 0), Array.get(T, a, 0), Array.get(U32, va, 0), Array.get(U, b, 0), Array.get(U32, vb, 0))) == o : Array<U32>} & PCORes(~T, ~U, ~P, ~f, p, d, a, va, b, vb, o, Laws.addn(0, U32.to_nat(n))))
  -> PCL(~T, ~U, ~P, ~f, n, d, p, k, a, va, b, vb):
  (o, eq, wo, spec) = w
  %Equal.sym(Array<U32>, Laws.pc_m(T, U, K.Kernel.pred_count.go(~T, ~U, ~P, ~f, U32.to_nat(n), 0, 0, p, Array.new(U32, d, 0), Array.get(T, a, 0), Array.get(U32, va, 0), Array.get(U, b, 0), Array.get(U32, vb, 0))), o, eq) : {Laws.rd_at(U32, _, k) == pcc(~T, ~U, ~P, ~f, p, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : U32}
  %Equal.sym(U32, Laws.rd_at(U32, o, k), Laws.rdN(U32, d, o, k), Laws.rd_at_wf(U32, d, o, k, wo)) : {_ == pcc(~T, ~U, ~P, ~f, p, Laws.rd_at(T, a, k), Laws.rd_at(U32, va, k), Laws.rd_at(U, b, k), Laws.rd_at(U32, vb, k)) : U32}
  spec(k, lt_addn0(n, k, hk))

# Kernel.pred_count(n, d, p, a, va, b, vb): m[k] == (va[k] & vb[k]) != 0 ? f(p, a[k], b[k]) : 0 for k < n
def pco_cell(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, +d: Nat, +n: U32, +p: P, a: Array<T>, va: Array<U32>, b: Array<U>, vb: Array<U32>, +k: U32, fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, hk: {U32.is_lt(k, n) == True{} : Bool})
  -> PCL(~T, ~U, ~P, ~f, n, d, p, k, a, va, b, vb):
  pco_fin(~T, ~U, ~P, ~f, d, n, p, a, va, b, vb, k, hk, pco_go(~T, ~U, ~P, ~f, U32.to_nat(n), 0, 0, p, d, a, va, b, vb, Array.new(U32, d, 0), Laws.wf_new(U32, d, 0), B.room_from(d, n, fits))(pcohyp0(~T, ~U, ~P, ~f, p, d, a, va, b, vb, Array.new(U32, d, 0))))

def Laws.pred_count_cell(d, n, lit, a, va, b, vb, k, fits, hk):
  pco_cell(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), d, n, lit, a, va, b, vb, k, fits, hk)

# ---- Kernel.pred_count hands its operands back, and its count is the running sum of the words ---------

# the running modulo-2^32 sum of the predicate words from row j on (the count's spec over the inputs)
def PSum(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, fl: Nat, +j: U32, +acc: U32, +p: P, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -res: U32) -> Type:
  match fl:
    case 0n:
      {res == acc : U32}
    case 1n+q:
      &w: U32 -> {w == pcc(~T, ~U, ~P, ~f, p, Laws.rd_at(T, a, j), Laws.rd_at(U32, va, j), Laws.rd_at(U, b, j), Laws.rd_at(U32, vb, j)) : U32} & PSum(~T, ~U, ~P, ~f, q, U32.inc(j), U32.add(acc, w), p, a, va, b, vb, res)

# the loop's record IS (its mask, its count, the four operands), and its count satisfies PSum
def PCQ(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, fl: Nat, +j: U32, +cnt: U32, +p: P, -out: Array<U32>, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -ra: Array<T> & T, -rva: Array<U32> & U32, -rb: Array<U> & U, -rvb: Array<U32> & U32) -> Type:
  {K.Kernel.pred_count.go(~T, ~U, ~P, ~f, fl, j, cnt, p, out, ra, rva, rb, rvb) == K.PC{Laws.pc_m(T, U, K.Kernel.pred_count.go(~T, ~U, ~P, ~f, fl, j, cnt, p, out, ra, rva, rb, rvb)), Laws.pc_k(T, U, K.Kernel.pred_count.go(~T, ~U, ~P, ~f, fl, j, cnt, p, out, ra, rva, rb, rvb)), a, va, b, vb} : K.PC<T, U>} & PSum(~T, ~U, ~P, ~f, fl, j, cnt, p, a, va, b, vb, Laws.pc_k(T, U, K.Kernel.pred_count.go(~T, ~U, ~P, ~f, fl, j, cnt, p, out, ra, rva, rb, rvb)))

def pcq_s5(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, q: Nat, +j: U32, +cnt: U32, +p: P, -out: Array<U32>, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, +x: T, +wa: U32, +y: U, +wb: U32,
  ev: {pcc(~T, ~U, ~P, ~f, p, x, wa, y, wb) == pcc(~T, ~U, ~P, ~f, p, Laws.rd_at(T, a, j), Laws.rd_at(U32, va, j), Laws.rd_at(U, b, j), Laws.rd_at(U32, vb, j)) : U32},
  w: PCQ(~T, ~U, ~P, ~f, q, U32.inc(j), U32.add(cnt, pcc(~T, ~U, ~P, ~f, p, x, wa, y, wb)), p, Array.set(U32, out, j, pcc(~T, ~U, ~P, ~f, p, x, wa, y, wb)), a, va, b, vb, Array.get(T, a, U32.inc(j)), Array.get(U32, va, U32.inc(j)), Array.get(U, b, U32.inc(j)), Array.get(U32, vb, U32.inc(j))))
  -> PCQ(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, out, a, va, b, vb, (a, x), (va, wa), (b, y), (vb, wb)):
  (e, ps) = w
  (e, (pcc(~T, ~U, ~P, ~f, p, x, wa, y, wb), ev, ps))

def pcq_s4(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, q: Nat, +j: U32, +cnt: U32, +p: P, out: Array<U32>, a: Array<T>, va: Array<U32>, b: Array<U>, -vb: Array<U32>, +x: T, +ex: {x == Laws.rd_at(T, a, j) : T}, +wa: U32, +ewa: {wa == Laws.rd_at(U32, va, j) : U32}, +y: U, +ey: {y == Laws.rd_at(U, b, j) : U},
  ih: @a2: Array<T> -> @va2: Array<U32> -> @b2: Array<U> -> @vb2: Array<U32> -> @cnt3: U32 -> @c: Array<U32> -> PCQ(~T, ~U, ~P, ~f, q, U32.inc(j), cnt3, p, c, a2, va2, b2, vb2, Array.get(T, a2, U32.inc(j)), Array.get(U32, va2, U32.inc(j)), Array.get(U, b2, U32.inc(j)), Array.get(U32, vb2, U32.inc(j))),
  w: &vb2: Array<U32> -> &wb: U32 -> {vb2 == vb : Array<U32>} & {Array.get(U32, vb, j) == (vb, wb) : Array<U32> & U32} & {wb == Laws.rd_at(U32, vb, j) : U32})
  -> PCQ(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, out, a, va, b, vb, (a, x), (va, wa), (b, y), Array.get(U32, vb, j)):
  (vb2, +wb, +evb, e1, ewb) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, vb, j), (vb, wb), e1) : PCQ(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, out, a, va, b, vb, (a, x), (va, wa), (b, y), _)
  %evb : PCQ(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, out, a, va, b, _, (a, x), (va, wa), (b, y), (_, wb))
  pcq_s5(~T, ~U, ~P, ~f, q, j, cnt, p, out, a, va, b, vb2, x, wa, y, wb,
    pcc_eq(~T, ~U, ~P, ~f, p, j, a, va, b, vb2, x, wa, y, wb, ex, ewa, ey, Equal.trans(U32, wb, Laws.rd_at(U32, vb, j), Laws.rd_at(U32, vb2, j), ewb, Equal.sym(U32, Laws.rd_at(U32, vb2, j), Laws.rd_at(U32, vb, j), Equal.cong(Array<U32>, U32, r => Laws.rd_at(U32, r, j), vb2, vb, evb)))),
    ih(a, va, b, vb2, U32.add(cnt, pcc(~T, ~U, ~P, ~f, p, x, wa, y, wb)), Array.set(U32, out, j, pcc(~T, ~U, ~P, ~f, p, x, wa, y, wb))))

def pcq_s3(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, q: Nat, +j: U32, +cnt: U32, +p: P, out: Array<U32>, a: Array<T>, va: Array<U32>, -b: Array<U>, vb: Array<U32>, +x: T, +ex: {x == Laws.rd_at(T, a, j) : T}, +wa: U32, +ewa: {wa == Laws.rd_at(U32, va, j) : U32},
  ih: @a2: Array<T> -> @va2: Array<U32> -> @b2: Array<U> -> @vb2: Array<U32> -> @cnt3: U32 -> @c: Array<U32> -> PCQ(~T, ~U, ~P, ~f, q, U32.inc(j), cnt3, p, c, a2, va2, b2, vb2, Array.get(T, a2, U32.inc(j)), Array.get(U32, va2, U32.inc(j)), Array.get(U, b2, U32.inc(j)), Array.get(U32, vb2, U32.inc(j))),
  w: &b2: Array<U> -> &y: U -> {b2 == b : Array<U>} & {Array.get(U, b, j) == (b, y) : Array<U> & U} & {y == Laws.rd_at(U, b, j) : U})
  -> PCQ(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, out, a, va, b, vb, (a, x), (va, wa), Array.get(U, b, j), Array.get(U32, vb, j)):
  (b2, +y, +eb, e1, ey) = w
  %Equal.sym(Array<U> & U, Array.get(U, b, j), (b, y), e1) : PCQ(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, out, a, va, b, vb, (a, x), (va, wa), _, Array.get(U32, vb, j))
  %eb : PCQ(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, out, a, va, _, vb, (a, x), (va, wa), (_, y), Array.get(U32, vb, j))
  pcq_s4(~T, ~U, ~P, ~f, q, j, cnt, p, out, a, va, b2, vb, x, ex, wa, ewa, y, Equal.trans(U, y, Laws.rd_at(U, b, j), Laws.rd_at(U, b2, j), ey, Equal.sym(U, Laws.rd_at(U, b2, j), Laws.rd_at(U, b, j), Equal.cong(Array<U>, U, r => Laws.rd_at(U, r, j), b2, b, eb))), ih, PC.get_w(U32, vb, j))

def pcq_s2(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, q: Nat, +j: U32, +cnt: U32, +p: P, out: Array<U32>, a: Array<T>, -va: Array<U32>, b: Array<U>, vb: Array<U32>, +x: T, +ex: {x == Laws.rd_at(T, a, j) : T},
  ih: @a2: Array<T> -> @va2: Array<U32> -> @b2: Array<U> -> @vb2: Array<U32> -> @cnt3: U32 -> @c: Array<U32> -> PCQ(~T, ~U, ~P, ~f, q, U32.inc(j), cnt3, p, c, a2, va2, b2, vb2, Array.get(T, a2, U32.inc(j)), Array.get(U32, va2, U32.inc(j)), Array.get(U, b2, U32.inc(j)), Array.get(U32, vb2, U32.inc(j))),
  w: &va2: Array<U32> -> &wa: U32 -> {va2 == va : Array<U32>} & {Array.get(U32, va, j) == (va, wa) : Array<U32> & U32} & {wa == Laws.rd_at(U32, va, j) : U32})
  -> PCQ(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, out, a, va, b, vb, (a, x), Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j)):
  (va2, +wa, +eva, e1, ewa) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, va, j), (va, wa), e1) : PCQ(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, out, a, va, b, vb, (a, x), _, Array.get(U, b, j), Array.get(U32, vb, j))
  %eva : PCQ(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, out, a, _, b, vb, (a, x), (_, wa), Array.get(U, b, j), Array.get(U32, vb, j))
  pcq_s3(~T, ~U, ~P, ~f, q, j, cnt, p, out, a, va2, b, vb, x, ex, wa, Equal.trans(U32, wa, Laws.rd_at(U32, va, j), Laws.rd_at(U32, va2, j), ewa, Equal.sym(U32, Laws.rd_at(U32, va2, j), Laws.rd_at(U32, va, j), Equal.cong(Array<U32>, U32, r => Laws.rd_at(U32, r, j), va2, va, eva))), ih, PC.get_w(U, b, j))

def pcq_s1(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, q: Nat, +j: U32, +cnt: U32, +p: P, out: Array<U32>, -a: Array<T>, va: Array<U32>, b: Array<U>, vb: Array<U32>,
  ih: @a2: Array<T> -> @va2: Array<U32> -> @b2: Array<U> -> @vb2: Array<U32> -> @cnt3: U32 -> @c: Array<U32> -> PCQ(~T, ~U, ~P, ~f, q, U32.inc(j), cnt3, p, c, a2, va2, b2, vb2, Array.get(T, a2, U32.inc(j)), Array.get(U32, va2, U32.inc(j)), Array.get(U, b2, U32.inc(j)), Array.get(U32, vb2, U32.inc(j))),
  w: &a2: Array<T> -> &x: T -> {a2 == a : Array<T>} & {Array.get(T, a, j) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, j) : T})
  -> PCQ(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, out, a, va, b, vb, Array.get(T, a, j), Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j)):
  (a2, +x, +ea, e1, ex) = w
  %Equal.sym(Array<T> & T, Array.get(T, a, j), (a, x), e1) : PCQ(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, out, a, va, b, vb, _, Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j))
  %ea : PCQ(~T, ~U, ~P, ~f, 1n+q, j, cnt, p, out, _, va, b, vb, (_, x), Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j))
  pcq_s2(~T, ~U, ~P, ~f, q, j, cnt, p, out, a2, va, b, vb, x, Equal.trans(T, x, Laws.rd_at(T, a, j), Laws.rd_at(T, a2, j), ex, Equal.sym(T, Laws.rd_at(T, a2, j), Laws.rd_at(T, a, j), Equal.cong(Array<T>, T, r => Laws.rd_at(T, r, j), a2, a, ea))), ih, PC.get_w(U32, va, j))

def pcq_zero(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, +j: U32, +cnt: U32, +p: P, -out: Array<U32>, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>,
  wa: &a2: Array<T> -> &x: T -> {a2 == a : Array<T>} & {Array.get(T, a, j) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, j) : T},
  wva: &va2: Array<U32> -> &x2: U32 -> {va2 == va : Array<U32>} & {Array.get(U32, va, j) == (va, x2) : Array<U32> & U32} & {x2 == Laws.rd_at(U32, va, j) : U32},
  wb: &b2: Array<U> -> &y: U -> {b2 == b : Array<U>} & {Array.get(U, b, j) == (b, y) : Array<U> & U} & {y == Laws.rd_at(U, b, j) : U},
  wvb: &vb2: Array<U32> -> &y2: U32 -> {vb2 == vb : Array<U32>} & {Array.get(U32, vb, j) == (vb, y2) : Array<U32> & U32} & {y2 == Laws.rd_at(U32, vb, j) : U32})
  -> PCQ(~T, ~U, ~P, ~f, 0n, j, cnt, p, out, a, va, b, vb, Array.get(T, a, j), Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j)):
  (a2, +x, ea, e1, ex) = wa
  (va2, +x2, eva, e2, ex2) = wva
  (b2, +y, eb, e3, ey) = wb
  (vb2, +y2, evb, e4, ey2) = wvb
  %Equal.sym(Array<T> & T, Array.get(T, a, j), (a, x), e1) : PCQ(~T, ~U, ~P, ~f, 0n, j, cnt, p, out, a, va, b, vb, _, Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j))
  %Equal.sym(Array<U32> & U32, Array.get(U32, va, j), (va, x2), e2) : PCQ(~T, ~U, ~P, ~f, 0n, j, cnt, p, out, a, va, b, vb, (a, x), _, Array.get(U, b, j), Array.get(U32, vb, j))
  %Equal.sym(Array<U> & U, Array.get(U, b, j), (b, y), e3) : PCQ(~T, ~U, ~P, ~f, 0n, j, cnt, p, out, a, va, b, vb, (a, x), (va, x2), _, Array.get(U32, vb, j))
  %Equal.sym(Array<U32> & U32, Array.get(U32, vb, j), (vb, y2), e4) : PCQ(~T, ~U, ~P, ~f, 0n, j, cnt, p, out, a, va, b, vb, (a, x), (va, x2), (b, y), _)
  ({==}, {==})

def pcq_go(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, fl: Nat, +j: U32, +cnt: U32, +p: P, out: Array<U32>, a: Array<T>, va: Array<U32>, b: Array<U>, vb: Array<U32>)
  -> PCQ(~T, ~U, ~P, ~f, fl, j, cnt, p, out, a, va, b, vb, Array.get(T, a, j), Array.get(U32, va, j), Array.get(U, b, j), Array.get(U32, vb, j)):
  match fl:
    case 0n:
      pcq_zero(~T, ~U, ~P, ~f, j, cnt, p, out, a, va, b, vb, PC.get_w(T, a, j), PC.get_w(U32, va, j), PC.get_w(U, b, j), PC.get_w(U32, vb, j))
    case 1n++q:
      pcq_s1(~T, ~U, ~P, ~f, q, j, cnt, p, out, a, va, b, vb, a2 => va2 => b2 => vb2 => cnt3 => c => pcq_go(~T, ~U, ~P, ~f, q, U32.inc(j), cnt3, p, c, a2, va2, b2, vb2), PC.get_w(T, a, j))

def pcq_keep(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, +n: U32, +d: Nat, +p: P, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>,
  w: PCQ(~T, ~U, ~P, ~f, U32.to_nat(n), 0, 0, p, Array.new(U32, d, 0), a, va, b, vb, Array.get(T, a, 0), Array.get(U32, va, 0), Array.get(U, b, 0), Array.get(U32, vb, 0)))
  -> {K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb) == K.PC{Laws.pc_m(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb)), Laws.pc_k(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb)), a, va, b, vb} : K.PC<T, U>}:
  (e, ps) = w
  e

def Laws.pred_count_keeps(d, n, lit, a, va, b, vb):
  pcq_keep(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, a, va, b, vb, pcq_go(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), U32.to_nat(n), 0, 0, lit, Array.new(U32, d, 0), a, va, b, vb))

# ---- the count is popcount of the mask ---------------------------------------------------------------

# the next f indices from j are below m (Laws.Room with the bound m in place of 2^d)
def Below(+m: U32, j: U32, f: Nat) -> Type:
  match f:
    case 0n:
      Unit
    case 1n+q:
      {U32.is_lt(j, m) == True{} : Bool} & Below(m, U32.inc(j), q)

def below_step(+m: U32, +j: U32, +q: Nat, b: Bool, s: B.IncSpecU(b, j), ih: @j2: U32 -> {Nat.is_le(Nat.add(U32.to_nat(j2), q), U32.to_nat(m)) == True{} : Bool} -> Below(m, j2, q))
  -> {Nat.is_le(Nat.add(U32.to_nat(j), 1n+q), U32.to_nat(m)) == True{} : Bool} -> Below(m, U32.inc(j), q):
  match b:
    case True{}:
      %Equal.sym(Nat, Nat.add(U32.to_nat(j), 1n+q), 1n+Nat.add(U32.to_nat(j), q), B.add_succ(U32.to_nat(j), q)) : {Nat.is_le(_, U32.to_nat(m)) == True{} : Bool} -> Below(m, U32.inc(j), q)
      %s : {Nat.is_le(Nat.add(_, q), U32.to_nat(m)) == True{} : Bool} -> Below(m, U32.inc(j), q)
      ih(U32.inc(j))
    case False{}:
      h => Empty.absurd(Below(m, U32.inc(j), q), s(m)(B.gt_of_lt_u(j, m, B.lt_of_nat_u(j, m, B.lt_of_le_add(U32.to_nat(j), q, U32.to_nat(m), h)))))

def below_step_fin(+m: U32, +j: U32, +q: Nat, w: &b: Bool -> B.IncSpecU(b, j), ih: @j2: U32 -> {Nat.is_le(Nat.add(U32.to_nat(j2), q), U32.to_nat(m)) == True{} : Bool} -> Below(m, j2, q))
  -> {Nat.is_le(Nat.add(U32.to_nat(j), 1n+q), U32.to_nat(m)) == True{} : Bool} -> Below(m, U32.inc(j), q):
  (b, s) = w
  below_step(m, j, q, b, s, ih)

def below_of(f: Nat, +m: U32, +j: U32) -> {Nat.is_le(Nat.add(U32.to_nat(j), f), U32.to_nat(m)) == True{} : Bool} -> Below(m, j, f):
  match f:
    case 0n:
      h => Unit{}
    case 1n++q:
      +h => (B.lt_of_nat_u(j, m, B.lt_of_le_add(U32.to_nat(j), q, U32.to_nat(m), h)), below_step_fin(m, j, q, B.inc_nat_u(j), j2 => below_of(q, m, j2))(h))

def u32_le_refl(n: U32) -> {U32.is_le(n, n) == True{} : Bool}:
  match n:
    case U32{+x}:
      %Equal.sym(Cmp, Word.cmp(32n, x, x), EQ{}, L.word_cmp_refl(32n, x)) : {Cmp.is_le(_) == True{} : Bool}
      {==}

# the first to_nat(n) indices from 0 are below n
def below_from(+n: U32) -> Below(n, 0, U32.to_nat(n)):
  below_of(U32.to_nat(n), n, 0)(B.le_nat_u(n, n, u32_le_refl(n)))

# the FSum of the fused mask: each step's word (PSum) is the mask's cell (the cell theorem, on clones)
def FSA(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, fl: Nat, +j: U32, +acc: U32, +res: U32, +n: U32, +d: Nat, +p: P, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>) -> Type:
  Laws.FSum(fl, j, acc, Laws.pc_m(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb)), res)

def pcl_back(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, +n: U32, +d: Nat, +p: P, +k: U32, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -a1: Array<T>, -va1: Array<U32>, -b1: Array<U>, -vb1: Array<U32>,
  ea: {a1 == a : Array<T>}, eva: {va1 == va : Array<U32>}, eb: {b1 == b : Array<U>}, evb: {vb1 == vb : Array<U32>}, h: PCL(~T, ~U, ~P, ~f, n, d, p, k, a1, va1, b1, vb1)) -> PCL(~T, ~U, ~P, ~f, n, d, p, k, a, va, b, vb):
  %evb : PCL(~T, ~U, ~P, ~f, n, d, p, k, a, va, b, _)
  %eb : PCL(~T, ~U, ~P, ~f, n, d, p, k, a, va, _, vb1)
  %eva : PCL(~T, ~U, ~P, ~f, n, d, p, k, a, _, b1, vb1)
  %ea : PCL(~T, ~U, ~P, ~f, n, d, p, k, _, va1, b1, vb1)
  h

def fsa_back(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, fl: Nat, +j: U32, +acc: U32, -res: U32, +n: U32, +d: Nat, +p: P, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -a1: Array<T>, -va1: Array<U32>, -b1: Array<U>, -vb1: Array<U32>,
  ea: {a1 == a : Array<T>}, eva: {va1 == va : Array<U32>}, eb: {b1 == b : Array<U>}, evb: {vb1 == vb : Array<U32>}, h: FSA(~T, ~U, ~P, ~f, fl, j, acc, res, n, d, p, a1, va1, b1, vb1)) -> FSA(~T, ~U, ~P, ~f, fl, j, acc, res, n, d, p, a, va, b, vb):
  %evb : FSA(~T, ~U, ~P, ~f, fl, j, acc, res, n, d, p, a, va, b, _)
  %eb : FSA(~T, ~U, ~P, ~f, fl, j, acc, res, n, d, p, a, va, _, vb1)
  %eva : FSA(~T, ~U, ~P, ~f, fl, j, acc, res, n, d, p, a, _, b1, vb1)
  %ea : FSA(~T, ~U, ~P, ~f, fl, j, acc, res, n, d, p, _, va1, b1, vb1)
  h

def psum_to(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, fl: Nat, +j: U32, +acc: U32, +p: P, -res: U32, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -a1: Array<T>, -va1: Array<U32>, -b1: Array<U>, -vb1: Array<U32>,
  ea: {a1 == a : Array<T>}, eva: {va1 == va : Array<U32>}, eb: {b1 == b : Array<U>}, evb: {vb1 == vb : Array<U32>}, h: PSum(~T, ~U, ~P, ~f, fl, j, acc, p, a, va, b, vb, res)) -> PSum(~T, ~U, ~P, ~f, fl, j, acc, p, a1, va1, b1, vb1, res):
  %Equal.sym(Array<U32>, vb1, vb, evb) : PSum(~T, ~U, ~P, ~f, fl, j, acc, p, a1, va1, b1, _, res)
  %Equal.sym(Array<U>, b1, b, eb) : PSum(~T, ~U, ~P, ~f, fl, j, acc, p, a1, va1, _, vb, res)
  %Equal.sym(Array<U32>, va1, va, eva) : PSum(~T, ~U, ~P, ~f, fl, j, acc, p, a1, _, b, vb, res)
  %Equal.sym(Array<T>, a1, a, ea) : PSum(~T, ~U, ~P, ~f, fl, j, acc, p, _, va, b, vb, res)
  h

def fs_step(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, +q: Nat, +j: U32, +acc: U32, -res: U32, +n: U32, +d: Nat, +p: P, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>,
  below: Below(n, j, 1n+q), ps: PSum(~T, ~U, ~P, ~f, 1n+q, j, acc, p, a, va, b, vb, res),
  ih: @a2: Array<T> -> @va2: Array<U32> -> @b2: Array<U> -> @vb2: Array<U32> -> @acc2: U32 -> Below(n, U32.inc(j), q) -> PSum(~T, ~U, ~P, ~f, q, U32.inc(j), acc2, p, a2, va2, b2, vb2, res) -> FSA(~T, ~U, ~P, ~f, q, U32.inc(j), acc2, res, n, d, p, a2, va2, b2, vb2),
  wa: &a1: Array<T> -> &a2: Array<T> -> {a1 == a : Array<T>} & {a2 == a : Array<T>}, wva: &va1: Array<U32> -> &va2: Array<U32> -> {va1 == va : Array<U32>} & {va2 == va : Array<U32>},
  wb: &b1: Array<U> -> &b2: Array<U> -> {b1 == b : Array<U>} & {b2 == b : Array<U>}, wvb: &vb1: Array<U32> -> &vb2: Array<U32> -> {vb1 == vb : Array<U32>} & {vb2 == vb : Array<U32>})
  -> FSA(~T, ~U, ~P, ~f, 1n+q, j, acc, res, n, d, p, a, va, b, vb):
  (hj, below2) = below
  (+w, ew, ps2) = ps
  (a1, a2, ea1, +ea2) = wa
  (va1, va2, eva1, +eva2) = wva
  (b1, b2, eb1, +eb2) = wb
  (vb1, vb2, evb1, +evb2) = wvb
  (w, Equal.trans(U32, w, pcc(~T, ~U, ~P, ~f, p, Laws.rd_at(T, a, j), Laws.rd_at(U32, va, j), Laws.rd_at(U, b, j), Laws.rd_at(U32, vb, j)), Laws.rd_at(U32, Laws.pc_m(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb)), j), ew,
      Equal.sym(U32, Laws.rd_at(U32, Laws.pc_m(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb)), j), pcc(~T, ~U, ~P, ~f, p, Laws.rd_at(T, a, j), Laws.rd_at(U32, va, j), Laws.rd_at(U, b, j), Laws.rd_at(U32, vb, j)),
        pcl_back(~T, ~U, ~P, ~f, n, d, p, j, a, va, b, vb, a1, va1, b1, vb1, ea1, eva1, eb1, evb1, pco_cell(~T, ~U, ~P, ~f, d, n, p, a1, va1, b1, vb1, j, fits, hj)))),
    fsa_back(~T, ~U, ~P, ~f, q, U32.inc(j), U32.add(acc, w), res, n, d, p, a, va, b, vb, a2, va2, b2, vb2, ea2, eva2, eb2, evb2,
      ih(a2, va2, b2, vb2, U32.add(acc, w), below2, psum_to(~T, ~U, ~P, ~f, q, U32.inc(j), U32.add(acc, w), p, res, a, va, b, vb, a2, va2, b2, vb2, ea2, eva2, eb2, evb2, ps2))))

def fs_go(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, fl: Nat, +j: U32, +acc: U32, -res: U32, +n: U32, +d: Nat, +p: P, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, a: Array<T>, va: Array<U32>, b: Array<U>, vb: Array<U32>,
  below: Below(n, j, fl), ps: PSum(~T, ~U, ~P, ~f, fl, j, acc, p, a, va, b, vb, res)) -> FSA(~T, ~U, ~P, ~f, fl, j, acc, res, n, d, p, a, va, b, vb):
  match fl:
    case 0n:
      ps
    case 1n++q:
      fs_step(~T, ~U, ~P, ~f, q, j, acc, res, n, d, p, fits, a, va, b, vb, below, ps, a2 => va2 => b2 => vb2 => acc2 => bl => ps3 => fs_go(~T, ~U, ~P, ~f, q, U32.inc(j), acc2, res, n, d, p, fits, a2, va2, b2, vb2, bl, ps3), PC.clone_eq(T, a), PC.clone_eq(U32, va), PC.clone_eq(U, b), PC.clone_eq(U32, vb))

# two FSum chains over one array from one accumulator end at one result
def fsum_uniq(f: Nat, +i: U32, +acc: U32, -a: Array<U32>, -r1: U32, -r2: U32, h1: Laws.FSum(f, i, acc, a, r1), h2: Laws.FSum(f, i, acc, a, r2)) -> {r1 == r2 : U32}:
  match f:
    case 0n:
      Equal.trans(U32, r1, acc, r2, h1, Equal.sym(U32, r2, acc, h2))
    case 1n++q:
      (+x1, ex1, t1) = h1
      (+x2, ex2, t2) = h2
      fsum_uniq(q, U32.inc(i), U32.add(acc, x1), a, r1, r2, t1, (%Equal.trans(U32, x2, Laws.rd_at(U32, a, i), x1, ex2, Equal.sym(U32, x1, Laws.rd_at(U32, a, i), ex1)) : Laws.FSum(q, U32.inc(i), U32.add(acc, _), a, r2); t2))

# the count against popcount: PSum from the loop (pcq_go), FSum of the mask from it (fs_go), popcount's
# own FSum (popcount_sum), one result (fsum_uniq); each run on its own clone of the operands
def PCK(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, +n: U32, +d: Nat, +p: P, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>) -> Type:
  {Laws.pc_k(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb)) == Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, Laws.pc_m(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb)))) : U32}

def pck_back(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, +n: U32, +d: Nat, +p: P, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -a1: Array<T>, -va1: Array<U32>, -b1: Array<U>, -vb1: Array<U32>,
  ea: {a1 == a : Array<T>}, eva: {va1 == va : Array<U32>}, eb: {b1 == b : Array<U>}, evb: {vb1 == vb : Array<U32>}, h: Laws.FSum(U32.to_nat(n), 0, 0, Laws.pc_m(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a1, va1, b1, vb1)), Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, Laws.pc_m(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a1, va1, b1, vb1))))))
  -> Laws.FSum(U32.to_nat(n), 0, 0, Laws.pc_m(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb)), Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, Laws.pc_m(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb))))):
  %evb : Laws.FSum(U32.to_nat(n), 0, 0, Laws.pc_m(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, b, _)), Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, Laws.pc_m(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, b, _)))))
  %eb : Laws.FSum(U32.to_nat(n), 0, 0, Laws.pc_m(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, _, vb1)), Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, Laws.pc_m(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, _, vb1)))))
  %eva : Laws.FSum(U32.to_nat(n), 0, 0, Laws.pc_m(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, _, b1, vb1)), Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, Laws.pc_m(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, _, b1, vb1)))))
  %ea : Laws.FSum(U32.to_nat(n), 0, 0, Laws.pc_m(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, _, va1, b1, vb1)), Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, Laws.pc_m(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, _, va1, b1, vb1)))))
  h

def pck_k2(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, +n: U32, +d: Nat, +p: P, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>,
  hf: FSA(~T, ~U, ~P, ~f, U32.to_nat(n), 0, 0, Laws.pc_k(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb)), n, d, p, a, va, b, vb),
  hp: Laws.FSum(U32.to_nat(n), 0, 0, Laws.pc_m(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb)), Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, Laws.pc_m(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb))))))
  -> PCK(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb):
  fsum_uniq(U32.to_nat(n), 0, 0, Laws.pc_m(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb)), Laws.pc_k(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb)), Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, Laws.pc_m(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb)))), hf, hp)

# PSum over the loop's own count, as a goal over the four operands
def PSR(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, +n: U32, +d: Nat, +p: P, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>) -> Type:
  PSum(~T, ~U, ~P, ~f, U32.to_nat(n), 0, 0, p, a, va, b, vb, Laws.pc_k(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb)))

# the PSum part of PCQ
def pcq_ps(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, +n: U32, +d: Nat, +p: P, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>,
  w: PCQ(~T, ~U, ~P, ~f, U32.to_nat(n), 0, 0, p, Array.new(U32, d, 0), a, va, b, vb, Array.get(T, a, 0), Array.get(U32, va, 0), Array.get(U, b, 0), Array.get(U32, vb, 0)))
  -> PSR(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb):
  (e, ps) = w
  ps

def psr_back(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, +n: U32, +d: Nat, +p: P, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>, -a1: Array<T>, -va1: Array<U32>, -b1: Array<U>, -vb1: Array<U32>,
  ea: {a1 == a : Array<T>}, eva: {va1 == va : Array<U32>}, eb: {b1 == b : Array<U>}, evb: {vb1 == vb : Array<U32>}, h: PSR(~T, ~U, ~P, ~f, n, d, p, a1, va1, b1, vb1)) -> PSR(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb):
  %evb : PSR(~T, ~U, ~P, ~f, n, d, p, a, va, b, _)
  %eb : PSR(~T, ~U, ~P, ~f, n, d, p, a, va, _, vb1)
  %eva : PSR(~T, ~U, ~P, ~f, n, d, p, a, _, b1, vb1)
  %ea : PSR(~T, ~U, ~P, ~f, n, d, p, _, va1, b1, vb1)
  h

def pck_fin(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, +n: U32, +d: Nat, +p: P, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, -a: Array<T>, -va: Array<U32>, -b: Array<U>, -vb: Array<U32>,
  wa: &a1: Array<T> -> &a2: Array<T> -> &a3: Array<T> -> {a1 == a : Array<T>} & {a2 == a : Array<T>} & {a3 == a : Array<T>},
  wva: &va1: Array<U32> -> &va2: Array<U32> -> &va3: Array<U32> -> {va1 == va : Array<U32>} & {va2 == va : Array<U32>} & {va3 == va : Array<U32>},
  wb: &b1: Array<U> -> &b2: Array<U> -> &b3: Array<U> -> {b1 == b : Array<U>} & {b2 == b : Array<U>} & {b3 == b : Array<U>},
  wvb: &vb1: Array<U32> -> &vb2: Array<U32> -> &vb3: Array<U32> -> {vb1 == vb : Array<U32>} & {vb2 == vb : Array<U32>} & {vb3 == vb : Array<U32>})
  -> PCK(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb):
  (a1, a2, a3, ea1, +ea2, ea3) = wa
  (va1, va2, va3, eva1, +eva2, eva3) = wva
  (b1, b2, b3, eb1, +eb2, eb3) = wb
  (vb1, vb2, vb3, evb1, +evb2, evb3) = wvb
  pck_k2(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb,
    fsa_back(~T, ~U, ~P, ~f, U32.to_nat(n), 0, 0, Laws.pc_k(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb)), n, d, p, a, va, b, vb, a2, va2, b2, vb2, ea2, eva2, eb2, evb2,
      fs_go(~T, ~U, ~P, ~f, U32.to_nat(n), 0, 0, Laws.pc_k(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb)), n, d, p, fits, a2, va2, b2, vb2, below_from(n),
        psum_to(~T, ~U, ~P, ~f, U32.to_nat(n), 0, 0, p, Laws.pc_k(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb)), a, va, b, vb, a2, va2, b2, vb2, ea2, eva2, eb2, evb2,
          psr_back(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb, a1, va1, b1, vb1, ea1, eva1, eb1, evb1,
            pcq_ps(~T, ~U, ~P, ~f, n, d, p, a1, va1, b1, vb1, pcq_go(~T, ~U, ~P, ~f, U32.to_nat(n), 0, 0, p, Array.new(U32, d, 0), a1, va1, b1, vb1)))))),
    pck_back(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb, a3, va3, b3, vb3, ea3, eva3, eb3, evb3, Laws.popcount_sum(n, Laws.pc_m(T, U, K.Kernel.pred_count(~T, ~U, ~P, ~f, n, d, p, a3, va3, b3, vb3)))))

def pc_count(~T: Data, ~U: Data, ~P: Data, ~f: P -> T -> U -> U32, +n: U32, +d: Nat, +p: P, a: Array<T>, va: Array<U32>, b: Array<U>, vb: Array<U32>, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool})
  -> PCK(~T, ~U, ~P, ~f, n, d, p, a, va, b, vb):
  pck_fin(~T, ~U, ~P, ~f, n, d, p, fits, a, va, b, vb, clone3(T, a), clone3(U32, va), clone3(U, b), clone3(U32, vb))

def Laws.pred_count_count(d, n, lit, a, va, b, vb, fits):
  pc_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, lit, a, va, b, vb, fits)

# ---- Kernel.compact3 IS three Kernel.compact_keep runs and popcount's fold, one mask (simulation) ----------

def C3S(~A: Data, ~B: Data, ~C: Data, fl: Nat, +i: U32, +k: U32, -o1: Array<A>, -o2: Array<B>, -o3: Array<C>, -a1: Array<A>, -a2: Array<B>, -a3: Array<C>, -m: Array<U32>, -rm: Array<U32> & U32, -r1: Array<A> & A, -r2: Array<B> & B, -r3: Array<C> & C) -> Type:
  {K.Kernel.compact3.go(~A, ~B, ~C, fl, i, k, o1, o2, o3, rm, r1, r2, r3) == K.C3{Pair.fst(Array<A>, Array<U32>, K.Kernel.compact_keep.go(~A, fl, i, k, (a1, o1), rm)), Pair.fst(Array<B>, Array<U32>, K.Kernel.compact_keep.go(~B, fl, i, k, (a2, o2), rm)), Pair.fst(Array<C>, Array<U32>, K.Kernel.compact_keep.go(~C, fl, i, k, (a3, o3), rm)), m, a1, a2, a3, Pair.snd(Array<U32>, U32, K.Kernel.fold.go(~U32, ~U32, ~(acc => x => U32.add(acc, x)), fl, i, k, rm))} : K.C3<A, B, C>}

# one step of both sides after the mask word bit is read: the compact_keep step reads a_j[i] (s_j) itself
def C3U(~A: Data, ~B: Data, ~C: Data, q: Nat, +i: U32, +k: U32, +bit: U32, -o1: Array<A>, -o2: Array<B>, -o3: Array<C>, -a1: Array<A>, -a2: Array<B>, -a3: Array<C>, -m: Array<U32>, -r1: Array<A> & A, -r2: Array<B> & B, -r3: Array<C> & C, -s1: Array<A> & A, -s2: Array<B> & B, -s3: Array<C> & C) -> Type:
  {K.Kernel.compact3.go(~A, ~B, ~C, 1n+q, i, k, o1, o2, o3, (m, bit), r1, r2, r3) == K.C3{Pair.fst(Array<A>, Array<U32>, K.Kernel.compact_keep.go(~A, q, U32.inc(i), U32.add(k, bit), K.Kernel.compact.put(~A, o1, k, s1), Array.get(U32, m, U32.inc(i)))), Pair.fst(Array<B>, Array<U32>, K.Kernel.compact_keep.go(~B, q, U32.inc(i), U32.add(k, bit), K.Kernel.compact.put(~B, o2, k, s2), Array.get(U32, m, U32.inc(i)))), Pair.fst(Array<C>, Array<U32>, K.Kernel.compact_keep.go(~C, q, U32.inc(i), U32.add(k, bit), K.Kernel.compact.put(~C, o3, k, s3), Array.get(U32, m, U32.inc(i)))), m, a1, a2, a3, Pair.snd(Array<U32>, U32, K.Kernel.fold.go(~U32, ~U32, ~(acc => x => U32.add(acc, x)), q, U32.inc(i), U32.add(k, bit), Array.get(U32, m, U32.inc(i))))} : K.C3<A, B, C>}

def c3_s4(~A: Data, ~B: Data, ~C: Data, q: Nat, +i: U32, +k: U32, +bit: U32, o1: Array<A>, o2: Array<B>, o3: Array<C>, a1: Array<A>, a2: Array<B>, -a3: Array<C>, m: Array<U32>, +x1: A, +x2: B,
  ih: @b1: Array<A> -> @b2: Array<B> -> @b3: Array<C> -> @m2: Array<U32> -> @c1: Array<A> -> @c2: Array<B> -> @c3: Array<C> -> C3S(~A, ~B, ~C, q, U32.inc(i), U32.add(k, bit), c1, c2, c3, b1, b2, b3, m2, Array.get(U32, m2, U32.inc(i)), Array.get(A, b1, U32.inc(i)), Array.get(B, b2, U32.inc(i)), Array.get(C, b3, U32.inc(i))),
  w: &b: Array<C> -> &x: C -> {b == a3 : Array<C>} & {Array.get(C, a3, i) == (a3, x) : Array<C> & C} & {x == Laws.rd_at(C, a3, i) : C})
  -> C3U(~A, ~B, ~C, q, i, k, bit, o1, o2, o3, a1, a2, a3, m, (a1, x1), (a2, x2), Array.get(C, a3, i), (a1, x1), (a2, x2), Array.get(C, a3, i)):
  (b3, +x3, +eb, e1, ex) = w
  %Equal.sym(Array<C> & C, Array.get(C, a3, i), (a3, x3), e1) : C3U(~A, ~B, ~C, q, i, k, bit, o1, o2, o3, a1, a2, a3, m, (a1, x1), (a2, x2), _, (a1, x1), (a2, x2), _)
  %eb : C3U(~A, ~B, ~C, q, i, k, bit, o1, o2, o3, a1, a2, _, m, (a1, x1), (a2, x2), (_, x3), (a1, x1), (a2, x2), (_, x3))
  ih(a1, a2, b3, m, Array.set(A, o1, k, x1), Array.set(B, o2, k, x2), Array.set(C, o3, k, x3))

def c3_s3(~A: Data, ~B: Data, ~C: Data, q: Nat, +i: U32, +k: U32, +bit: U32, o1: Array<A>, o2: Array<B>, o3: Array<C>, a1: Array<A>, -a2: Array<B>, a3: Array<C>, m: Array<U32>, +x1: A,
  ih: @b1: Array<A> -> @b2: Array<B> -> @b3: Array<C> -> @m2: Array<U32> -> @c1: Array<A> -> @c2: Array<B> -> @c3: Array<C> -> C3S(~A, ~B, ~C, q, U32.inc(i), U32.add(k, bit), c1, c2, c3, b1, b2, b3, m2, Array.get(U32, m2, U32.inc(i)), Array.get(A, b1, U32.inc(i)), Array.get(B, b2, U32.inc(i)), Array.get(C, b3, U32.inc(i))),
  w: &b: Array<B> -> &x: B -> {b == a2 : Array<B>} & {Array.get(B, a2, i) == (a2, x) : Array<B> & B} & {x == Laws.rd_at(B, a2, i) : B})
  -> C3U(~A, ~B, ~C, q, i, k, bit, o1, o2, o3, a1, a2, a3, m, (a1, x1), Array.get(B, a2, i), Array.get(C, a3, i), (a1, x1), Array.get(B, a2, i), Array.get(C, a3, i)):
  (b2, +x2, +eb, e1, ex) = w
  %Equal.sym(Array<B> & B, Array.get(B, a2, i), (a2, x2), e1) : C3U(~A, ~B, ~C, q, i, k, bit, o1, o2, o3, a1, a2, a3, m, (a1, x1), _, Array.get(C, a3, i), (a1, x1), _, Array.get(C, a3, i))
  %eb : C3U(~A, ~B, ~C, q, i, k, bit, o1, o2, o3, a1, _, a3, m, (a1, x1), (_, x2), Array.get(C, a3, i), (a1, x1), (_, x2), Array.get(C, a3, i))
  c3_s4(~A, ~B, ~C, q, i, k, bit, o1, o2, o3, a1, b2, a3, m, x1, x2, ih, PC.get_w(C, a3, i))

def c3_s2(~A: Data, ~B: Data, ~C: Data, q: Nat, +i: U32, +k: U32, +bit: U32, o1: Array<A>, o2: Array<B>, o3: Array<C>, -a1: Array<A>, a2: Array<B>, a3: Array<C>, m: Array<U32>,
  ih: @b1: Array<A> -> @b2: Array<B> -> @b3: Array<C> -> @m2: Array<U32> -> @c1: Array<A> -> @c2: Array<B> -> @c3: Array<C> -> C3S(~A, ~B, ~C, q, U32.inc(i), U32.add(k, bit), c1, c2, c3, b1, b2, b3, m2, Array.get(U32, m2, U32.inc(i)), Array.get(A, b1, U32.inc(i)), Array.get(B, b2, U32.inc(i)), Array.get(C, b3, U32.inc(i))),
  w: &b: Array<A> -> &x: A -> {b == a1 : Array<A>} & {Array.get(A, a1, i) == (a1, x) : Array<A> & A} & {x == Laws.rd_at(A, a1, i) : A})
  -> C3U(~A, ~B, ~C, q, i, k, bit, o1, o2, o3, a1, a2, a3, m, Array.get(A, a1, i), Array.get(B, a2, i), Array.get(C, a3, i), Array.get(A, a1, i), Array.get(B, a2, i), Array.get(C, a3, i)):
  (b1, +x1, +eb, e1, ex) = w
  %Equal.sym(Array<A> & A, Array.get(A, a1, i), (a1, x1), e1) : C3U(~A, ~B, ~C, q, i, k, bit, o1, o2, o3, a1, a2, a3, m, _, Array.get(B, a2, i), Array.get(C, a3, i), _, Array.get(B, a2, i), Array.get(C, a3, i))
  %eb : C3U(~A, ~B, ~C, q, i, k, bit, o1, o2, o3, _, a2, a3, m, (_, x1), Array.get(B, a2, i), Array.get(C, a3, i), (_, x1), Array.get(B, a2, i), Array.get(C, a3, i))
  c3_s3(~A, ~B, ~C, q, i, k, bit, o1, o2, o3, b1, a2, a3, m, x1, ih, PC.get_w(B, a2, i))

def c3_s1(~A: Data, ~B: Data, ~C: Data, q: Nat, +i: U32, +k: U32, o1: Array<A>, o2: Array<B>, o3: Array<C>, a1: Array<A>, a2: Array<B>, a3: Array<C>, -m: Array<U32>,
  ih: @bit: U32 -> @b1: Array<A> -> @b2: Array<B> -> @b3: Array<C> -> @m2: Array<U32> -> @c1: Array<A> -> @c2: Array<B> -> @c3: Array<C> -> C3S(~A, ~B, ~C, q, U32.inc(i), U32.add(k, bit), c1, c2, c3, b1, b2, b3, m2, Array.get(U32, m2, U32.inc(i)), Array.get(A, b1, U32.inc(i)), Array.get(B, b2, U32.inc(i)), Array.get(C, b3, U32.inc(i))),
  w: &m3: Array<U32> -> &x: U32 -> {m3 == m : Array<U32>} & {Array.get(U32, m, i) == (m, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, m, i) : U32})
  -> C3S(~A, ~B, ~C, 1n+q, i, k, o1, o2, o3, a1, a2, a3, m, Array.get(U32, m, i), Array.get(A, a1, i), Array.get(B, a2, i), Array.get(C, a3, i)):
  (m2, +bit, +em, e1, ex) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, m, i), (m, bit), e1) : C3S(~A, ~B, ~C, 1n+q, i, k, o1, o2, o3, a1, a2, a3, m, _, Array.get(A, a1, i), Array.get(B, a2, i), Array.get(C, a3, i))
  %em : C3S(~A, ~B, ~C, 1n+q, i, k, o1, o2, o3, a1, a2, a3, _, (_, bit), Array.get(A, a1, i), Array.get(B, a2, i), Array.get(C, a3, i))
  c3_s2(~A, ~B, ~C, q, i, k, bit, o1, o2, o3, a1, a2, a3, m2, ih(bit), PC.get_w(A, a1, i))

def c3_zero(~A: Data, ~B: Data, ~C: Data, +i: U32, +k: U32, -o1: Array<A>, -o2: Array<B>, -o3: Array<C>, -a1: Array<A>, -a2: Array<B>, -a3: Array<C>, -m: Array<U32>,
  wm: &m3: Array<U32> -> &x: U32 -> {m3 == m : Array<U32>} & {Array.get(U32, m, i) == (m, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, m, i) : U32},
  w1: &b1: Array<A> -> &x1: A -> {b1 == a1 : Array<A>} & {Array.get(A, a1, i) == (a1, x1) : Array<A> & A} & {x1 == Laws.rd_at(A, a1, i) : A},
  w2: &b2: Array<B> -> &x2: B -> {b2 == a2 : Array<B>} & {Array.get(B, a2, i) == (a2, x2) : Array<B> & B} & {x2 == Laws.rd_at(B, a2, i) : B},
  w3: &b3: Array<C> -> &x3: C -> {b3 == a3 : Array<C>} & {Array.get(C, a3, i) == (a3, x3) : Array<C> & C} & {x3 == Laws.rd_at(C, a3, i) : C})
  -> C3S(~A, ~B, ~C, 0n, i, k, o1, o2, o3, a1, a2, a3, m, Array.get(U32, m, i), Array.get(A, a1, i), Array.get(B, a2, i), Array.get(C, a3, i)):
  (m2, +bit, em, e0, ex) = wm
  (b1, +x1, eb1, e1, ex1) = w1
  (b2, +x2, eb2, e2, ex2) = w2
  (b3, +x3, eb3, e3, ex3) = w3
  %Equal.sym(Array<U32> & U32, Array.get(U32, m, i), (m, bit), e0) : C3S(~A, ~B, ~C, 0n, i, k, o1, o2, o3, a1, a2, a3, m, _, Array.get(A, a1, i), Array.get(B, a2, i), Array.get(C, a3, i))
  %Equal.sym(Array<A> & A, Array.get(A, a1, i), (a1, x1), e1) : C3S(~A, ~B, ~C, 0n, i, k, o1, o2, o3, a1, a2, a3, m, (m, bit), _, Array.get(B, a2, i), Array.get(C, a3, i))
  %Equal.sym(Array<B> & B, Array.get(B, a2, i), (a2, x2), e2) : C3S(~A, ~B, ~C, 0n, i, k, o1, o2, o3, a1, a2, a3, m, (m, bit), (a1, x1), _, Array.get(C, a3, i))
  %Equal.sym(Array<C> & C, Array.get(C, a3, i), (a3, x3), e3) : C3S(~A, ~B, ~C, 0n, i, k, o1, o2, o3, a1, a2, a3, m, (m, bit), (a1, x1), (a2, x2), _)
  {==}

def c3_sim(~A: Data, ~B: Data, ~C: Data, fl: Nat, +i: U32, +k: U32, o1: Array<A>, o2: Array<B>, o3: Array<C>, a1: Array<A>, a2: Array<B>, a3: Array<C>, m: Array<U32>)
  -> C3S(~A, ~B, ~C, fl, i, k, o1, o2, o3, a1, a2, a3, m, Array.get(U32, m, i), Array.get(A, a1, i), Array.get(B, a2, i), Array.get(C, a3, i)):
  match fl:
    case 0n:
      c3_zero(~A, ~B, ~C, i, k, o1, o2, o3, a1, a2, a3, m, PC.get_w(U32, m, i), PC.get_w(A, a1, i), PC.get_w(B, a2, i), PC.get_w(C, a3, i))
    case 1n++q:
      c3_s1(~A, ~B, ~C, q, i, k, o1, o2, o3, a1, a2, a3, m, bit => b1 => b2 => b3 => m2 => c1 => c2 => c3 => c3_sim(~A, ~B, ~C, q, U32.inc(i), U32.add(k, bit), c1, c2, c3, b1, b2, b3, m2), PC.get_w(U32, m, i))

def Laws.compact3_unfused(d, n, m, a1, a2, a3, z1, z2, z3):
  c3_sim(~U32, ~U32, ~F32, U32.to_nat(n), 0, 0, Array.new(U32, d, z1), Array.new(U32, d, z2), Array.new(F32, d, z3), a1, a2, a3, m)


# ---- compact3's outputs: compact_contents per column, one mask, one cursor ------------------------------

# four clones of one array
def clone4_k(-T: Data, -a: Array<T>, -p: Array<T>, -q: Array<T>, +ep: {p == a : Array<T>}, +eq: {q == a : Array<T>},
  wp: &a1: Array<T> -> &a2: Array<T> -> {a1 == p : Array<T>} & {a2 == p : Array<T>}, wq: &a3: Array<T> -> &a4: Array<T> -> {a3 == q : Array<T>} & {a4 == q : Array<T>})
  -> &a1: Array<T> -> &a2: Array<T> -> &a3: Array<T> -> &a4: Array<T> -> {a1 == a : Array<T>} & {a2 == a : Array<T>} & {a3 == a : Array<T>} & {a4 == a : Array<T>}:
  (a1, a2, e1, e2) = wp
  (a3, a4, e3, e4) = wq
  (a1, a2, a3, a4, Equal.trans(Array<T>, a1, p, a, e1, ep), Equal.trans(Array<T>, a2, p, a, e2, ep), Equal.trans(Array<T>, a3, q, a, e3, eq), Equal.trans(Array<T>, a4, q, a, e4, eq))

def clone4_j(-T: Data, -a: Array<T>, w: &p: Array<T> -> &q: Array<T> -> {p == a : Array<T>} & {q == a : Array<T>})
  -> &a1: Array<T> -> &a2: Array<T> -> &a3: Array<T> -> &a4: Array<T> -> {a1 == a : Array<T>} & {a2 == a : Array<T>} & {a3 == a : Array<T>} & {a4 == a : Array<T>}:
  (p, q, +ep, +eq) = w
  clone4_k(T, a, p, q, ep, eq, PC.clone_eq(T, p), PC.clone_eq(T, q))

def clone4(-T: Data, a: Array<T>) -> &a1: Array<T> -> &a2: Array<T> -> &a3: Array<T> -> &a4: Array<T> -> {a1 == a : Array<T>} & {a2 == a : Array<T>} & {a3 == a : Array<T>} & {a4 == a : Array<T>}:
  clone4_j(T, a, PC.clone_eq(T, a))

# a CRoom chain, three and four times
def croom3_k(+f: Nat, +i: U32, +k: U32, +d: Nat, -mask: Array<U32>, w: Laws.CRoom(f, i, k, d, mask) & Laws.CRoom(f, i, k, d, mask)) -> Laws.CRoom(f, i, k, d, mask) & Laws.CRoom(f, i, k, d, mask) & Laws.CRoom(f, i, k, d, mask):
  (r1, r) = w
  (r1, PC.croom_dup(f, i, k, d, mask, r))

def croom3(+f: Nat, +i: U32, +k: U32, +d: Nat, -mask: Array<U32>, room: Laws.CRoom(f, i, k, d, mask)) -> Laws.CRoom(f, i, k, d, mask) & Laws.CRoom(f, i, k, d, mask) & Laws.CRoom(f, i, k, d, mask):
  croom3_k(f, i, k, d, mask, PC.croom_dup(f, i, k, d, mask, room))

def croom4_k(+f: Nat, +i: U32, +k: U32, +d: Nat, -mask: Array<U32>, w: Laws.CRoom(f, i, k, d, mask) & Laws.CRoom(f, i, k, d, mask)) -> Laws.CRoom(f, i, k, d, mask) & Laws.CRoom(f, i, k, d, mask) & Laws.CRoom(f, i, k, d, mask) & Laws.CRoom(f, i, k, d, mask):
  (r1, r) = w
  (r1, croom3(f, i, k, d, mask, r))

def croom4(+f: Nat, +i: U32, +k: U32, +d: Nat, -mask: Array<U32>, room: Laws.CRoom(f, i, k, d, mask)) -> Laws.CRoom(f, i, k, d, mask) & Laws.CRoom(f, i, k, d, mask) & Laws.CRoom(f, i, k, d, mask) & Laws.CRoom(f, i, k, d, mask):
  croom4_k(f, i, k, d, mask, PC.croom_dup(f, i, k, d, mask, room))

# compact_contents for one column, on clones of the column and of the mask, restated to the originals
def CS1(+n: U32, +d: Nat, -m: Array<U32>, -a: Array<U32>, +z: U32) -> Type:
  Laws.CSpec(U32, U32.to_nat(n), 0, 0, d, a, m, Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a, m, z)))

def cs1_of(+n: U32, +d: Nat, -m: Array<U32>, -a: Array<U32>, +z: U32, m2: Array<U32>, a2: Array<U32>, +em: {m2 == m : Array<U32>}, ea: {a2 == a : Array<U32>}, room: Laws.CRoom(U32.to_nat(n), 0, 0, d, m)) -> CS1(n, d, m, a, z):
  %em : CS1(n, d, _, a, z)
  %ea : CS1(n, d, m2, _, z)
  Laws.compact_contents(d, n, a2, m2, z, (%Equal.sym(Array<U32>, m2, m, em) : Laws.CRoom(U32.to_nat(n), 0, 0, d, _); room))

def C3E(+n: U32, +d: Nat, -m: Array<U32>, -a1: Array<U32>, -a2: Array<U32>, -a3: Array<U32>, +z1: U32, +z2: U32, +z3: U32) -> Type:
  {K.Kernel.compact3(~U32, ~U32, ~U32, n, d, m, a1, a2, a3, z1, z2, z3) == K.C3{Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a1, m, z1)), Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a2, m, z2)), Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a3, m, z3)), m, a1, a2, a3, Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, m))} : K.C3<U32, U32, U32>}

def c3e_back(+n: U32, +d: Nat, -m: Array<U32>, -a1: Array<U32>, -a2: Array<U32>, -a3: Array<U32>, +z1: U32, +z2: U32, +z3: U32, -m1: Array<U32>, -b1: Array<U32>, -b2: Array<U32>, -b3: Array<U32>,
  em: {m1 == m : Array<U32>}, e1: {b1 == a1 : Array<U32>}, e2: {b2 == a2 : Array<U32>}, e3: {b3 == a3 : Array<U32>}, h: C3E(n, d, m1, b1, b2, b3, z1, z2, z3)) -> C3E(n, d, m, a1, a2, a3, z1, z2, z3):
  %em : C3E(n, d, _, a1, a2, a3, z1, z2, z3)
  %e3 : C3E(n, d, m1, a1, a2, _, z1, z2, z3)
  %e2 : C3E(n, d, m1, a1, _, b3, z1, z2, z3)
  %e1 : C3E(n, d, m1, _, b2, b3, z1, z2, z3)
  h

def c3c_r(+n: U32, +d: Nat, -m: Array<U32>, -a1: Array<U32>, -a2: Array<U32>, -a3: Array<U32>, +z1: U32, +z2: U32, +z3: U32, m2: Array<U32>, m3: Array<U32>, m4: Array<U32>, c1: Array<U32>, c2: Array<U32>, c3: Array<U32>,
  +em2: {m2 == m : Array<U32>}, +em3: {m3 == m : Array<U32>}, +em4: {m4 == m : Array<U32>}, ec1: {c1 == a1 : Array<U32>}, ec2: {c2 == a2 : Array<U32>}, ec3: {c3 == a3 : Array<U32>},
  rooms: Laws.CRoom(U32.to_nat(n), 0, 0, d, m) & Laws.CRoom(U32.to_nat(n), 0, 0, d, m) & Laws.CRoom(U32.to_nat(n), 0, 0, d, m))
  -> CS1(n, d, m, a1, z1) & CS1(n, d, m, a2, z2) & CS1(n, d, m, a3, z3):
  (r1, r2, r3) = rooms
  (cs1_of(n, d, m, a1, z1, m2, c1, em2, ec1, r1), cs1_of(n, d, m, a2, z2, m3, c2, em3, ec2, r2), cs1_of(n, d, m, a3, z3, m4, c3, em4, ec3, r3))

def c3c_k(+n: U32, +d: Nat, -m: Array<U32>, -a1: Array<U32>, -a2: Array<U32>, -a3: Array<U32>, +z1: U32, +z2: U32, +z3: U32, room: Laws.CRoom(U32.to_nat(n), 0, 0, d, m),
  wm: &m1: Array<U32> -> &m2: Array<U32> -> &m3: Array<U32> -> &m4: Array<U32> -> {m1 == m : Array<U32>} & {m2 == m : Array<U32>} & {m3 == m : Array<U32>} & {m4 == m : Array<U32>},
  w1: &b1: Array<U32> -> &c1: Array<U32> -> {b1 == a1 : Array<U32>} & {c1 == a1 : Array<U32>}, w2: &b2: Array<U32> -> &c2: Array<U32> -> {b2 == a2 : Array<U32>} & {c2 == a2 : Array<U32>}, w3: &b3: Array<U32> -> &c3: Array<U32> -> {b3 == a3 : Array<U32>} & {c3 == a3 : Array<U32>})
  -> Laws.CSpec(U32, U32.to_nat(n), 0, 0, d, a1, m, Laws.c3_o1(U32, U32, U32, K.Kernel.compact3(~U32, ~U32, ~U32, n, d, m, a1, a2, a3, z1, z2, z3))) & Laws.CSpec(U32, U32.to_nat(n), 0, 0, d, a2, m, Laws.c3_o2(U32, U32, U32, K.Kernel.compact3(~U32, ~U32, ~U32, n, d, m, a1, a2, a3, z1, z2, z3))) & Laws.CSpec(U32, U32.to_nat(n), 0, 0, d, a3, m, Laws.c3_o3(U32, U32, U32, K.Kernel.compact3(~U32, ~U32, ~U32, n, d, m, a1, a2, a3, z1, z2, z3))):
  (m1, m2, m3, m4, em1, em2, em3, em4) = wm
  (b1, c1, eb1, ec1) = w1
  (b2, c2, eb2, ec2) = w2
  (b3, c3, eb3, ec3) = w3
  %Equal.sym(K.C3<U32, U32, U32>, K.Kernel.compact3(~U32, ~U32, ~U32, n, d, m, a1, a2, a3, z1, z2, z3), K.C3{Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a1, m, z1)), Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a2, m, z2)), Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a3, m, z3)), m, a1, a2, a3, Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, m))}, c3e_back(n, d, m, a1, a2, a3, z1, z2, z3, m1, b1, b2, b3, em1, eb1, eb2, eb3, c3_sim(~U32, ~U32, ~U32, U32.to_nat(n), 0, 0, Array.new(U32, d, z1), Array.new(U32, d, z2), Array.new(U32, d, z3), b1, b2, b3, m1))) : Laws.CSpec(U32, U32.to_nat(n), 0, 0, d, a1, m, Laws.c3_o1(U32, U32, U32, _)) & Laws.CSpec(U32, U32.to_nat(n), 0, 0, d, a2, m, Laws.c3_o2(U32, U32, U32, _)) & Laws.CSpec(U32, U32.to_nat(n), 0, 0, d, a3, m, Laws.c3_o3(U32, U32, U32, _))
  c3c_r(n, d, m, a1, a2, a3, z1, z2, z3, m2, m3, m4, c1, c2, c3, em2, em3, em4, ec1, ec2, ec3, croom3(U32.to_nat(n), 0, 0, d, m, room))

def Laws.compact3_contents(d, n, m, a1, a2, a3, z1, z2, z3, room):
  c3c_k(n, d, m, a1, a2, a3, z1, z2, z3, room, clone4(U32, m), PC.clone_eq(U32, a1), PC.clone_eq(U32, a2), PC.clone_eq(U32, a3))

# ---- Kernel.compact4 IS four Kernel.compact_keep runs and popcount's fold, one mask (simulation) ----------

def C4S(~A: Data, ~B: Data, ~C: Data, ~D: Data, fl: Nat, +i: U32, +k: U32, -o1: Array<A>, -o2: Array<B>, -o3: Array<C>, -o4: Array<D>, -a1: Array<A>, -a2: Array<B>, -a3: Array<C>, -a4: Array<D>, -m: Array<U32>, -rm: Array<U32> & U32, -r1: Array<A> & A, -r2: Array<B> & B, -r3: Array<C> & C, -r4: Array<D> & D) -> Type:
  {K.Kernel.compact4.go(~A, ~B, ~C, ~D, fl, i, k, o1, o2, o3, o4, rm, r1, r2, r3, r4) == K.C4{Pair.fst(Array<A>, Array<U32>, K.Kernel.compact_keep.go(~A, fl, i, k, (a1, o1), rm)), Pair.fst(Array<B>, Array<U32>, K.Kernel.compact_keep.go(~B, fl, i, k, (a2, o2), rm)), Pair.fst(Array<C>, Array<U32>, K.Kernel.compact_keep.go(~C, fl, i, k, (a3, o3), rm)), Pair.fst(Array<D>, Array<U32>, K.Kernel.compact_keep.go(~D, fl, i, k, (a4, o4), rm)), m, a1, a2, a3, a4, Pair.snd(Array<U32>, U32, K.Kernel.fold.go(~U32, ~U32, ~(acc => x => U32.add(acc, x)), fl, i, k, rm))} : K.C4<A, B, C, D>}

def C4U(~A: Data, ~B: Data, ~C: Data, ~D: Data, q: Nat, +i: U32, +k: U32, +bit: U32, -o1: Array<A>, -o2: Array<B>, -o3: Array<C>, -o4: Array<D>, -a1: Array<A>, -a2: Array<B>, -a3: Array<C>, -a4: Array<D>, -m: Array<U32>, -r1: Array<A> & A, -r2: Array<B> & B, -r3: Array<C> & C, -r4: Array<D> & D, -s1: Array<A> & A, -s2: Array<B> & B, -s3: Array<C> & C, -s4: Array<D> & D) -> Type:
  {K.Kernel.compact4.go(~A, ~B, ~C, ~D, 1n+q, i, k, o1, o2, o3, o4, (m, bit), r1, r2, r3, r4) == K.C4{Pair.fst(Array<A>, Array<U32>, K.Kernel.compact_keep.go(~A, q, U32.inc(i), U32.add(k, bit), K.Kernel.compact.put(~A, o1, k, s1), Array.get(U32, m, U32.inc(i)))), Pair.fst(Array<B>, Array<U32>, K.Kernel.compact_keep.go(~B, q, U32.inc(i), U32.add(k, bit), K.Kernel.compact.put(~B, o2, k, s2), Array.get(U32, m, U32.inc(i)))), Pair.fst(Array<C>, Array<U32>, K.Kernel.compact_keep.go(~C, q, U32.inc(i), U32.add(k, bit), K.Kernel.compact.put(~C, o3, k, s3), Array.get(U32, m, U32.inc(i)))), Pair.fst(Array<D>, Array<U32>, K.Kernel.compact_keep.go(~D, q, U32.inc(i), U32.add(k, bit), K.Kernel.compact.put(~D, o4, k, s4), Array.get(U32, m, U32.inc(i)))), m, a1, a2, a3, a4, Pair.snd(Array<U32>, U32, K.Kernel.fold.go(~U32, ~U32, ~(acc => x => U32.add(acc, x)), q, U32.inc(i), U32.add(k, bit), Array.get(U32, m, U32.inc(i))))} : K.C4<A, B, C, D>}

def c4_s5(~A: Data, ~B: Data, ~C: Data, ~D: Data, q: Nat, +i: U32, +k: U32, +bit: U32, o1: Array<A>, o2: Array<B>, o3: Array<C>, o4: Array<D>, a1: Array<A>, a2: Array<B>, a3: Array<C>, -a4: Array<D>, m: Array<U32>, +x1: A, +x2: B, +x3: C,
  ih: @b1: Array<A> -> @b2: Array<B> -> @b3: Array<C> -> @b4: Array<D> -> @m2: Array<U32> -> @c1: Array<A> -> @c2: Array<B> -> @c3: Array<C> -> @c4: Array<D> -> C4S(~A, ~B, ~C, ~D, q, U32.inc(i), U32.add(k, bit), c1, c2, c3, c4, b1, b2, b3, b4, m2, Array.get(U32, m2, U32.inc(i)), Array.get(A, b1, U32.inc(i)), Array.get(B, b2, U32.inc(i)), Array.get(C, b3, U32.inc(i)), Array.get(D, b4, U32.inc(i))),
  w: &b: Array<D> -> &x: D -> {b == a4 : Array<D>} & {Array.get(D, a4, i) == (a4, x) : Array<D> & D} & {x == Laws.rd_at(D, a4, i) : D})
  -> C4U(~A, ~B, ~C, ~D, q, i, k, bit, o1, o2, o3, o4, a1, a2, a3, a4, m, (a1, x1), (a2, x2), (a3, x3), Array.get(D, a4, i), (a1, x1), (a2, x2), (a3, x3), Array.get(D, a4, i)):
  (b4, +x4, +eb, e1, ex) = w
  %Equal.sym(Array<D> & D, Array.get(D, a4, i), (a4, x4), e1) : C4U(~A, ~B, ~C, ~D, q, i, k, bit, o1, o2, o3, o4, a1, a2, a3, a4, m, (a1, x1), (a2, x2), (a3, x3), _, (a1, x1), (a2, x2), (a3, x3), _)
  %eb : C4U(~A, ~B, ~C, ~D, q, i, k, bit, o1, o2, o3, o4, a1, a2, a3, _, m, (a1, x1), (a2, x2), (a3, x3), (_, x4), (a1, x1), (a2, x2), (a3, x3), (_, x4))
  ih(a1, a2, a3, b4, m, Array.set(A, o1, k, x1), Array.set(B, o2, k, x2), Array.set(C, o3, k, x3), Array.set(D, o4, k, x4))

def c4_s4(~A: Data, ~B: Data, ~C: Data, ~D: Data, q: Nat, +i: U32, +k: U32, +bit: U32, o1: Array<A>, o2: Array<B>, o3: Array<C>, o4: Array<D>, a1: Array<A>, a2: Array<B>, -a3: Array<C>, a4: Array<D>, m: Array<U32>, +x1: A, +x2: B,
  ih: @b1: Array<A> -> @b2: Array<B> -> @b3: Array<C> -> @b4: Array<D> -> @m2: Array<U32> -> @c1: Array<A> -> @c2: Array<B> -> @c3: Array<C> -> @c4: Array<D> -> C4S(~A, ~B, ~C, ~D, q, U32.inc(i), U32.add(k, bit), c1, c2, c3, c4, b1, b2, b3, b4, m2, Array.get(U32, m2, U32.inc(i)), Array.get(A, b1, U32.inc(i)), Array.get(B, b2, U32.inc(i)), Array.get(C, b3, U32.inc(i)), Array.get(D, b4, U32.inc(i))),
  w: &b: Array<C> -> &x: C -> {b == a3 : Array<C>} & {Array.get(C, a3, i) == (a3, x) : Array<C> & C} & {x == Laws.rd_at(C, a3, i) : C})
  -> C4U(~A, ~B, ~C, ~D, q, i, k, bit, o1, o2, o3, o4, a1, a2, a3, a4, m, (a1, x1), (a2, x2), Array.get(C, a3, i), Array.get(D, a4, i), (a1, x1), (a2, x2), Array.get(C, a3, i), Array.get(D, a4, i)):
  (b3, +x3, +eb, e1, ex) = w
  %Equal.sym(Array<C> & C, Array.get(C, a3, i), (a3, x3), e1) : C4U(~A, ~B, ~C, ~D, q, i, k, bit, o1, o2, o3, o4, a1, a2, a3, a4, m, (a1, x1), (a2, x2), _, Array.get(D, a4, i), (a1, x1), (a2, x2), _, Array.get(D, a4, i))
  %eb : C4U(~A, ~B, ~C, ~D, q, i, k, bit, o1, o2, o3, o4, a1, a2, _, a4, m, (a1, x1), (a2, x2), (_, x3), Array.get(D, a4, i), (a1, x1), (a2, x2), (_, x3), Array.get(D, a4, i))
  c4_s5(~A, ~B, ~C, ~D, q, i, k, bit, o1, o2, o3, o4, a1, a2, b3, a4, m, x1, x2, x3, ih, PC.get_w(D, a4, i))

def c4_s3(~A: Data, ~B: Data, ~C: Data, ~D: Data, q: Nat, +i: U32, +k: U32, +bit: U32, o1: Array<A>, o2: Array<B>, o3: Array<C>, o4: Array<D>, a1: Array<A>, -a2: Array<B>, a3: Array<C>, a4: Array<D>, m: Array<U32>, +x1: A,
  ih: @b1: Array<A> -> @b2: Array<B> -> @b3: Array<C> -> @b4: Array<D> -> @m2: Array<U32> -> @c1: Array<A> -> @c2: Array<B> -> @c3: Array<C> -> @c4: Array<D> -> C4S(~A, ~B, ~C, ~D, q, U32.inc(i), U32.add(k, bit), c1, c2, c3, c4, b1, b2, b3, b4, m2, Array.get(U32, m2, U32.inc(i)), Array.get(A, b1, U32.inc(i)), Array.get(B, b2, U32.inc(i)), Array.get(C, b3, U32.inc(i)), Array.get(D, b4, U32.inc(i))),
  w: &b: Array<B> -> &x: B -> {b == a2 : Array<B>} & {Array.get(B, a2, i) == (a2, x) : Array<B> & B} & {x == Laws.rd_at(B, a2, i) : B})
  -> C4U(~A, ~B, ~C, ~D, q, i, k, bit, o1, o2, o3, o4, a1, a2, a3, a4, m, (a1, x1), Array.get(B, a2, i), Array.get(C, a3, i), Array.get(D, a4, i), (a1, x1), Array.get(B, a2, i), Array.get(C, a3, i), Array.get(D, a4, i)):
  (b2, +x2, +eb, e1, ex) = w
  %Equal.sym(Array<B> & B, Array.get(B, a2, i), (a2, x2), e1) : C4U(~A, ~B, ~C, ~D, q, i, k, bit, o1, o2, o3, o4, a1, a2, a3, a4, m, (a1, x1), _, Array.get(C, a3, i), Array.get(D, a4, i), (a1, x1), _, Array.get(C, a3, i), Array.get(D, a4, i))
  %eb : C4U(~A, ~B, ~C, ~D, q, i, k, bit, o1, o2, o3, o4, a1, _, a3, a4, m, (a1, x1), (_, x2), Array.get(C, a3, i), Array.get(D, a4, i), (a1, x1), (_, x2), Array.get(C, a3, i), Array.get(D, a4, i))
  c4_s4(~A, ~B, ~C, ~D, q, i, k, bit, o1, o2, o3, o4, a1, b2, a3, a4, m, x1, x2, ih, PC.get_w(C, a3, i))

def c4_s2(~A: Data, ~B: Data, ~C: Data, ~D: Data, q: Nat, +i: U32, +k: U32, +bit: U32, o1: Array<A>, o2: Array<B>, o3: Array<C>, o4: Array<D>, -a1: Array<A>, a2: Array<B>, a3: Array<C>, a4: Array<D>, m: Array<U32>,
  ih: @b1: Array<A> -> @b2: Array<B> -> @b3: Array<C> -> @b4: Array<D> -> @m2: Array<U32> -> @c1: Array<A> -> @c2: Array<B> -> @c3: Array<C> -> @c4: Array<D> -> C4S(~A, ~B, ~C, ~D, q, U32.inc(i), U32.add(k, bit), c1, c2, c3, c4, b1, b2, b3, b4, m2, Array.get(U32, m2, U32.inc(i)), Array.get(A, b1, U32.inc(i)), Array.get(B, b2, U32.inc(i)), Array.get(C, b3, U32.inc(i)), Array.get(D, b4, U32.inc(i))),
  w: &b: Array<A> -> &x: A -> {b == a1 : Array<A>} & {Array.get(A, a1, i) == (a1, x) : Array<A> & A} & {x == Laws.rd_at(A, a1, i) : A})
  -> C4U(~A, ~B, ~C, ~D, q, i, k, bit, o1, o2, o3, o4, a1, a2, a3, a4, m, Array.get(A, a1, i), Array.get(B, a2, i), Array.get(C, a3, i), Array.get(D, a4, i), Array.get(A, a1, i), Array.get(B, a2, i), Array.get(C, a3, i), Array.get(D, a4, i)):
  (b1, +x1, +eb, e1, ex) = w
  %Equal.sym(Array<A> & A, Array.get(A, a1, i), (a1, x1), e1) : C4U(~A, ~B, ~C, ~D, q, i, k, bit, o1, o2, o3, o4, a1, a2, a3, a4, m, _, Array.get(B, a2, i), Array.get(C, a3, i), Array.get(D, a4, i), _, Array.get(B, a2, i), Array.get(C, a3, i), Array.get(D, a4, i))
  %eb : C4U(~A, ~B, ~C, ~D, q, i, k, bit, o1, o2, o3, o4, _, a2, a3, a4, m, (_, x1), Array.get(B, a2, i), Array.get(C, a3, i), Array.get(D, a4, i), (_, x1), Array.get(B, a2, i), Array.get(C, a3, i), Array.get(D, a4, i))
  c4_s3(~A, ~B, ~C, ~D, q, i, k, bit, o1, o2, o3, o4, b1, a2, a3, a4, m, x1, ih, PC.get_w(B, a2, i))

def c4_s1(~A: Data, ~B: Data, ~C: Data, ~D: Data, q: Nat, +i: U32, +k: U32, o1: Array<A>, o2: Array<B>, o3: Array<C>, o4: Array<D>, a1: Array<A>, a2: Array<B>, a3: Array<C>, a4: Array<D>, -m: Array<U32>,
  ih: @bit: U32 -> @b1: Array<A> -> @b2: Array<B> -> @b3: Array<C> -> @b4: Array<D> -> @m2: Array<U32> -> @c1: Array<A> -> @c2: Array<B> -> @c3: Array<C> -> @c4: Array<D> -> C4S(~A, ~B, ~C, ~D, q, U32.inc(i), U32.add(k, bit), c1, c2, c3, c4, b1, b2, b3, b4, m2, Array.get(U32, m2, U32.inc(i)), Array.get(A, b1, U32.inc(i)), Array.get(B, b2, U32.inc(i)), Array.get(C, b3, U32.inc(i)), Array.get(D, b4, U32.inc(i))),
  w: &m3: Array<U32> -> &x: U32 -> {m3 == m : Array<U32>} & {Array.get(U32, m, i) == (m, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, m, i) : U32})
  -> C4S(~A, ~B, ~C, ~D, 1n+q, i, k, o1, o2, o3, o4, a1, a2, a3, a4, m, Array.get(U32, m, i), Array.get(A, a1, i), Array.get(B, a2, i), Array.get(C, a3, i), Array.get(D, a4, i)):
  (m2, +bit, +em, e1, ex) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, m, i), (m, bit), e1) : C4S(~A, ~B, ~C, ~D, 1n+q, i, k, o1, o2, o3, o4, a1, a2, a3, a4, m, _, Array.get(A, a1, i), Array.get(B, a2, i), Array.get(C, a3, i), Array.get(D, a4, i))
  %em : C4S(~A, ~B, ~C, ~D, 1n+q, i, k, o1, o2, o3, o4, a1, a2, a3, a4, _, (_, bit), Array.get(A, a1, i), Array.get(B, a2, i), Array.get(C, a3, i), Array.get(D, a4, i))
  c4_s2(~A, ~B, ~C, ~D, q, i, k, bit, o1, o2, o3, o4, a1, a2, a3, a4, m2, ih(bit), PC.get_w(A, a1, i))

def c4_zero(~A: Data, ~B: Data, ~C: Data, ~D: Data, +i: U32, +k: U32, -o1: Array<A>, -o2: Array<B>, -o3: Array<C>, -o4: Array<D>, -a1: Array<A>, -a2: Array<B>, -a3: Array<C>, -a4: Array<D>, -m: Array<U32>,
  wm: &m3: Array<U32> -> &x: U32 -> {m3 == m : Array<U32>} & {Array.get(U32, m, i) == (m, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, m, i) : U32},
  w1: &b1: Array<A> -> &x1: A -> {b1 == a1 : Array<A>} & {Array.get(A, a1, i) == (a1, x1) : Array<A> & A} & {x1 == Laws.rd_at(A, a1, i) : A},
  w2: &b2: Array<B> -> &x2: B -> {b2 == a2 : Array<B>} & {Array.get(B, a2, i) == (a2, x2) : Array<B> & B} & {x2 == Laws.rd_at(B, a2, i) : B},
  w3: &b3: Array<C> -> &x3: C -> {b3 == a3 : Array<C>} & {Array.get(C, a3, i) == (a3, x3) : Array<C> & C} & {x3 == Laws.rd_at(C, a3, i) : C},
  w4: &b4: Array<D> -> &x4: D -> {b4 == a4 : Array<D>} & {Array.get(D, a4, i) == (a4, x4) : Array<D> & D} & {x4 == Laws.rd_at(D, a4, i) : D})
  -> C4S(~A, ~B, ~C, ~D, 0n, i, k, o1, o2, o3, o4, a1, a2, a3, a4, m, Array.get(U32, m, i), Array.get(A, a1, i), Array.get(B, a2, i), Array.get(C, a3, i), Array.get(D, a4, i)):
  (m2, +bit, em, e0, ex) = wm
  (b1, +x1, eb1, e1, ex1) = w1
  (b2, +x2, eb2, e2, ex2) = w2
  (b3, +x3, eb3, e3, ex3) = w3
  (b4, +x4, eb4, e4, ex4) = w4
  %Equal.sym(Array<U32> & U32, Array.get(U32, m, i), (m, bit), e0) : C4S(~A, ~B, ~C, ~D, 0n, i, k, o1, o2, o3, o4, a1, a2, a3, a4, m, _, Array.get(A, a1, i), Array.get(B, a2, i), Array.get(C, a3, i), Array.get(D, a4, i))
  %Equal.sym(Array<A> & A, Array.get(A, a1, i), (a1, x1), e1) : C4S(~A, ~B, ~C, ~D, 0n, i, k, o1, o2, o3, o4, a1, a2, a3, a4, m, (m, bit), _, Array.get(B, a2, i), Array.get(C, a3, i), Array.get(D, a4, i))
  %Equal.sym(Array<B> & B, Array.get(B, a2, i), (a2, x2), e2) : C4S(~A, ~B, ~C, ~D, 0n, i, k, o1, o2, o3, o4, a1, a2, a3, a4, m, (m, bit), (a1, x1), _, Array.get(C, a3, i), Array.get(D, a4, i))
  %Equal.sym(Array<C> & C, Array.get(C, a3, i), (a3, x3), e3) : C4S(~A, ~B, ~C, ~D, 0n, i, k, o1, o2, o3, o4, a1, a2, a3, a4, m, (m, bit), (a1, x1), (a2, x2), _, Array.get(D, a4, i))
  %Equal.sym(Array<D> & D, Array.get(D, a4, i), (a4, x4), e4) : C4S(~A, ~B, ~C, ~D, 0n, i, k, o1, o2, o3, o4, a1, a2, a3, a4, m, (m, bit), (a1, x1), (a2, x2), (a3, x3), _)
  {==}

def c4_sim(~A: Data, ~B: Data, ~C: Data, ~D: Data, fl: Nat, +i: U32, +k: U32, o1: Array<A>, o2: Array<B>, o3: Array<C>, o4: Array<D>, a1: Array<A>, a2: Array<B>, a3: Array<C>, a4: Array<D>, m: Array<U32>)
  -> C4S(~A, ~B, ~C, ~D, fl, i, k, o1, o2, o3, o4, a1, a2, a3, a4, m, Array.get(U32, m, i), Array.get(A, a1, i), Array.get(B, a2, i), Array.get(C, a3, i), Array.get(D, a4, i)):
  match fl:
    case 0n:
      c4_zero(~A, ~B, ~C, ~D, i, k, o1, o2, o3, o4, a1, a2, a3, a4, m, PC.get_w(U32, m, i), PC.get_w(A, a1, i), PC.get_w(B, a2, i), PC.get_w(C, a3, i), PC.get_w(D, a4, i))
    case 1n++q:
      c4_s1(~A, ~B, ~C, ~D, q, i, k, o1, o2, o3, o4, a1, a2, a3, a4, m, bit => b1 => b2 => b3 => b4 => m2 => c1 => c2 => c3 => c4 => c4_sim(~A, ~B, ~C, ~D, q, U32.inc(i), U32.add(k, bit), c1, c2, c3, c4, b1, b2, b3, b4, m2), PC.get_w(U32, m, i))

# ---- compact4's outputs: compact_contents per column -----------------------------------------------------

def C4E(+n: U32, +d: Nat, -m: Array<U32>, -a1: Array<U32>, -a2: Array<U32>, -a3: Array<U32>, -a4: Array<U32>, +z1: U32, +z2: U32, +z3: U32, +z4: U32) -> Type:
  {K.Kernel.compact4(~U32, ~U32, ~U32, ~U32, n, d, m, a1, a2, a3, a4, z1, z2, z3, z4) == K.C4{Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a1, m, z1)), Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a2, m, z2)), Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a3, m, z3)), Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a4, m, z4)), m, a1, a2, a3, a4, Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, m))} : K.C4<U32, U32, U32, U32>}

def c4e_back(+n: U32, +d: Nat, -m: Array<U32>, -a1: Array<U32>, -a2: Array<U32>, -a3: Array<U32>, -a4: Array<U32>, +z1: U32, +z2: U32, +z3: U32, +z4: U32, -m1: Array<U32>, -b1: Array<U32>, -b2: Array<U32>, -b3: Array<U32>, -b4: Array<U32>,
  em: {m1 == m : Array<U32>}, e1: {b1 == a1 : Array<U32>}, e2: {b2 == a2 : Array<U32>}, e3: {b3 == a3 : Array<U32>}, e4: {b4 == a4 : Array<U32>}, h: C4E(n, d, m1, b1, b2, b3, b4, z1, z2, z3, z4)) -> C4E(n, d, m, a1, a2, a3, a4, z1, z2, z3, z4):
  %em : C4E(n, d, _, a1, a2, a3, a4, z1, z2, z3, z4)
  %e4 : C4E(n, d, m1, a1, a2, a3, _, z1, z2, z3, z4)
  %e3 : C4E(n, d, m1, a1, a2, _, b4, z1, z2, z3, z4)
  %e2 : C4E(n, d, m1, a1, _, b3, b4, z1, z2, z3, z4)
  %e1 : C4E(n, d, m1, _, b2, b3, b4, z1, z2, z3, z4)
  h

def c4c_r(+n: U32, +d: Nat, -m: Array<U32>, -a1: Array<U32>, -a2: Array<U32>, -a3: Array<U32>, -a4: Array<U32>, +z1: U32, +z2: U32, +z3: U32, +z4: U32, m2: Array<U32>, m3: Array<U32>, m4: Array<U32>, m5: Array<U32>, c1: Array<U32>, c2: Array<U32>, c3: Array<U32>, c4: Array<U32>,
  +em2: {m2 == m : Array<U32>}, +em3: {m3 == m : Array<U32>}, +em4: {m4 == m : Array<U32>}, +em5: {m5 == m : Array<U32>}, ec1: {c1 == a1 : Array<U32>}, ec2: {c2 == a2 : Array<U32>}, ec3: {c3 == a3 : Array<U32>}, ec4: {c4 == a4 : Array<U32>},
  rooms: Laws.CRoom(U32.to_nat(n), 0, 0, d, m) & Laws.CRoom(U32.to_nat(n), 0, 0, d, m) & Laws.CRoom(U32.to_nat(n), 0, 0, d, m) & Laws.CRoom(U32.to_nat(n), 0, 0, d, m))
  -> CS1(n, d, m, a1, z1) & CS1(n, d, m, a2, z2) & CS1(n, d, m, a3, z3) & CS1(n, d, m, a4, z4):
  (r1, r2, r3, r4) = rooms
  (cs1_of(n, d, m, a1, z1, m2, c1, em2, ec1, r1), cs1_of(n, d, m, a2, z2, m3, c2, em3, ec2, r2), cs1_of(n, d, m, a3, z3, m4, c3, em4, ec3, r3), cs1_of(n, d, m, a4, z4, m5, c4, em5, ec4, r4))

def c4c_m(+n: U32, +d: Nat, -m: Array<U32>, -a1: Array<U32>, -a2: Array<U32>, -a3: Array<U32>, -a4: Array<U32>, +z1: U32, +z2: U32, +z3: U32, +z4: U32, room: Laws.CRoom(U32.to_nat(n), 0, 0, d, m),
  m1: Array<U32>, em1: {m1 == m : Array<U32>}, -mr: Array<U32>, +emr: {mr == m : Array<U32>},
  wm: &m2: Array<U32> -> &m3: Array<U32> -> &m4: Array<U32> -> &m5: Array<U32> -> {m2 == mr : Array<U32>} & {m3 == mr : Array<U32>} & {m4 == mr : Array<U32>} & {m5 == mr : Array<U32>},
  w1: &b1: Array<U32> -> &c1: Array<U32> -> {b1 == a1 : Array<U32>} & {c1 == a1 : Array<U32>}, w2: &b2: Array<U32> -> &c2: Array<U32> -> {b2 == a2 : Array<U32>} & {c2 == a2 : Array<U32>},
  w3: &b3: Array<U32> -> &c3: Array<U32> -> {b3 == a3 : Array<U32>} & {c3 == a3 : Array<U32>}, w4: &b4: Array<U32> -> &c4: Array<U32> -> {b4 == a4 : Array<U32>} & {c4 == a4 : Array<U32>})
  -> Laws.CSpec(U32, U32.to_nat(n), 0, 0, d, a1, m, Laws.c4_o1(U32, U32, U32, U32, K.Kernel.compact4(~U32, ~U32, ~U32, ~U32, n, d, m, a1, a2, a3, a4, z1, z2, z3, z4))) & Laws.CSpec(U32, U32.to_nat(n), 0, 0, d, a2, m, Laws.c4_o2(U32, U32, U32, U32, K.Kernel.compact4(~U32, ~U32, ~U32, ~U32, n, d, m, a1, a2, a3, a4, z1, z2, z3, z4))) & Laws.CSpec(U32, U32.to_nat(n), 0, 0, d, a3, m, Laws.c4_o3(U32, U32, U32, U32, K.Kernel.compact4(~U32, ~U32, ~U32, ~U32, n, d, m, a1, a2, a3, a4, z1, z2, z3, z4))) & Laws.CSpec(U32, U32.to_nat(n), 0, 0, d, a4, m, Laws.c4_o4(U32, U32, U32, U32, K.Kernel.compact4(~U32, ~U32, ~U32, ~U32, n, d, m, a1, a2, a3, a4, z1, z2, z3, z4))):
  (m2, m3, m4, m5, em2, em3, em4, em5) = wm
  (b1, c1, eb1, ec1) = w1
  (b2, c2, eb2, ec2) = w2
  (b3, c3, eb3, ec3) = w3
  (b4, c4, eb4, ec4) = w4
  %Equal.sym(K.C4<U32, U32, U32, U32>, K.Kernel.compact4(~U32, ~U32, ~U32, ~U32, n, d, m, a1, a2, a3, a4, z1, z2, z3, z4), K.C4{Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a1, m, z1)), Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a2, m, z2)), Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a3, m, z3)), Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, d, a4, m, z4)), m, a1, a2, a3, a4, Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, m))}, c4e_back(n, d, m, a1, a2, a3, a4, z1, z2, z3, z4, m1, b1, b2, b3, b4, em1, eb1, eb2, eb3, eb4, c4_sim(~U32, ~U32, ~U32, ~U32, U32.to_nat(n), 0, 0, Array.new(U32, d, z1), Array.new(U32, d, z2), Array.new(U32, d, z3), Array.new(U32, d, z4), b1, b2, b3, b4, m1))) : Laws.CSpec(U32, U32.to_nat(n), 0, 0, d, a1, m, Laws.c4_o1(U32, U32, U32, U32, _)) & Laws.CSpec(U32, U32.to_nat(n), 0, 0, d, a2, m, Laws.c4_o2(U32, U32, U32, U32, _)) & Laws.CSpec(U32, U32.to_nat(n), 0, 0, d, a3, m, Laws.c4_o3(U32, U32, U32, U32, _)) & Laws.CSpec(U32, U32.to_nat(n), 0, 0, d, a4, m, Laws.c4_o4(U32, U32, U32, U32, _))
  c4c_r(n, d, m, a1, a2, a3, a4, z1, z2, z3, z4, m2, m3, m4, m5, c1, c2, c3, c4, Equal.trans(Array<U32>, m2, mr, m, em2, emr), Equal.trans(Array<U32>, m3, mr, m, em3, emr), Equal.trans(Array<U32>, m4, mr, m, em4, emr), Equal.trans(Array<U32>, m5, mr, m, em5, emr), ec1, ec2, ec3, ec4, croom4(U32.to_nat(n), 0, 0, d, m, room))

def c4c_k(+n: U32, +d: Nat, -m: Array<U32>, -a1: Array<U32>, -a2: Array<U32>, -a3: Array<U32>, -a4: Array<U32>, +z1: U32, +z2: U32, +z3: U32, +z4: U32, room: Laws.CRoom(U32.to_nat(n), 0, 0, d, m),
  wm: &m1: Array<U32> -> &mr: Array<U32> -> {m1 == m : Array<U32>} & {mr == m : Array<U32>},
  w1: &b1: Array<U32> -> &c1: Array<U32> -> {b1 == a1 : Array<U32>} & {c1 == a1 : Array<U32>}, w2: &b2: Array<U32> -> &c2: Array<U32> -> {b2 == a2 : Array<U32>} & {c2 == a2 : Array<U32>},
  w3: &b3: Array<U32> -> &c3: Array<U32> -> {b3 == a3 : Array<U32>} & {c3 == a3 : Array<U32>}, w4: &b4: Array<U32> -> &c4: Array<U32> -> {b4 == a4 : Array<U32>} & {c4 == a4 : Array<U32>})
  -> Laws.CSpec(U32, U32.to_nat(n), 0, 0, d, a1, m, Laws.c4_o1(U32, U32, U32, U32, K.Kernel.compact4(~U32, ~U32, ~U32, ~U32, n, d, m, a1, a2, a3, a4, z1, z2, z3, z4))) & Laws.CSpec(U32, U32.to_nat(n), 0, 0, d, a2, m, Laws.c4_o2(U32, U32, U32, U32, K.Kernel.compact4(~U32, ~U32, ~U32, ~U32, n, d, m, a1, a2, a3, a4, z1, z2, z3, z4))) & Laws.CSpec(U32, U32.to_nat(n), 0, 0, d, a3, m, Laws.c4_o3(U32, U32, U32, U32, K.Kernel.compact4(~U32, ~U32, ~U32, ~U32, n, d, m, a1, a2, a3, a4, z1, z2, z3, z4))) & Laws.CSpec(U32, U32.to_nat(n), 0, 0, d, a4, m, Laws.c4_o4(U32, U32, U32, U32, K.Kernel.compact4(~U32, ~U32, ~U32, ~U32, n, d, m, a1, a2, a3, a4, z1, z2, z3, z4))):
  (m1, mr, em1, emr) = wm
  c4c_m(n, d, m, a1, a2, a3, a4, z1, z2, z3, z4, room, m1, em1, mr, emr, clone4(U32, mr), w1, w2, w3, w4)

def Laws.compact4_contents(d, n, m, a1, a2, a3, a4, z1, z2, z3, z4, room):
  c4c_k(n, d, m, a1, a2, a3, a4, z1, z2, z3, z4, room, PC.clone_eq(U32, m), PC.clone_eq(U32, a1), PC.clone_eq(U32, a2), PC.clone_eq(U32, a3), PC.clone_eq(U32, a4))

def Laws.compact4_unfused(d, n, m, a1, a2, a3, a4, z1, z2, z3, z4):
  c4_sim(~U32, ~U32, ~F32, ~U32, U32.to_nat(n), 0, 0, Array.new(U32, d, z1), Array.new(U32, d, z2), Array.new(F32, d, z3), Array.new(U32, d, z4), a1, a2, a3, a4, m)
