# PROOF_inplace.bend -- proofs of LAWS.bend section 15 (M5 part 4, P1), the in-place kernels:
# Kernel.mask_data (Eval.fix: null slots back to the default) and Kernel.choose (fill_null /
# when: a[i] := m[i] ? a[i] : b[i]), their cell theorems, and the Str column verbs over them
# (Eval.fix on a CStr column, Eval.fill, the storage of Eval.when).
#
# Shape: an in-place loop overwrites its input slot by slot, so "every row so far" cannot be
# carried as one affine forall across the writes (the write facts would be needed for the rows
# below, the rows above and the next read). Instead the loop lemma is a SINGLE-POSITION
# induction (the ckeep idiom of PROOF_contents): for one position pos it carries the current
# cell cur at pos (a Data value with its equation) and answers what the remaining run leaves
# there: cur when pos is already behind the loop (pos < i), else the kernel's choice at pos.
# Each step uses the write facts once (at pos) and splits pos against the write index i
# (below, equal, above; the "above" case needs is_lt(pos, inc i) == False, a Nat lemma).
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
import ./PROOF_strs.bend as PST
import ./PROOF_append.bend as PA

# ---- order facts for the position split ------------------------------------------------------------

# not LT and not EQ is GT
def cmp_gt_of(c: Cmp, h1: {Cmp.is_lt(c) == False{} : Bool}, h2: {Cmp.is_eq(c) == False{} : Bool}) -> {c == GT{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == GT{} : Cmp}, L.true_false(h1))
    case EQ{}:
      Empty.absurd({EQ{} == GT{} : Cmp}, L.true_false(h2))
    case GT{}:
      {==}

# nothing is below 0
def nat_not_lt_zero(p: Nat) -> {Cmp.is_lt(Nat.cmp(p, 0n)) == False{} : Bool}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      {==}

# a > b gives NOT a < 1 + b
def nat_gt_succ(a: Nat, b: Nat, h: {Nat.cmp(a, b) == GT{} : Cmp}) -> {Cmp.is_lt(Nat.cmp(a, 1n+b)) == False{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Cmp.is_lt(Nat.cmp(0n, 1n)) == False{} : Bool}, B.eq_gt(h))
    case 0n 1n+q:
      Empty.absurd({Cmp.is_lt(Nat.cmp(0n, 2n+q)) == False{} : Bool}, B.lt_gt(h))
    case 1n+p 0n:
      nat_not_lt_zero(p)
    case 1n+p 1n+q:
      nat_gt_succ(p, q, h)

# the Nat value of inc i for i below 2^d: one more (i is not the maximal word)
def inc_nat_d_k(bb: Bool, +i: U32, +d: Nat, s: B.IncSpecU(bb, i), hi: {U32.is_lt(i, U32.shln(1, d)) == True{} : Bool}) -> {U32.to_nat(U32.inc(i)) == 1n+U32.to_nat(i) : Nat}:
  match bb:
    case True{}:
      s
    case False{}:
      Empty.absurd({U32.to_nat(U32.inc(i)) == 1n+U32.to_nat(i) : Nat}, s(U32.shln(1, d))(B.gt_of_lt_u(i, U32.shln(1, d), hi)))

def inc_nat_d_fin(+i: U32, +d: Nat, w: &bb: Bool -> B.IncSpecU(bb, i), hi: {U32.is_lt(i, U32.shln(1, d)) == True{} : Bool}) -> {U32.to_nat(U32.inc(i)) == 1n+U32.to_nat(i) : Nat}:
  (bb, s) = w
  inc_nat_d_k(bb, i, d, s, hi)

def inc_nat_d(+i: U32, +d: Nat, hi: {U32.is_lt(i, U32.shln(1, d)) == True{} : Bool}) -> {U32.to_nat(U32.inc(i)) == 1n+U32.to_nat(i) : Nat}:
  inc_nat_d_fin(i, d, B.inc_nat_u(i), hi)

# pos neither below nor equal to i (below 2^d): pos is not below inc i either
def not_lt_inc(+pos: U32, +i: U32, +d: Nat, hi: {U32.is_lt(i, U32.shln(1, d)) == True{} : Bool}, h1: {U32.is_lt(pos, i) == False{} : Bool}, h2: {U32.is_eq(pos, i) == False{} : Bool}) -> {U32.is_lt(pos, U32.inc(i)) == False{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(pos, U32.inc(i)), Nat.cmp(U32.to_nat(pos), U32.to_nat(U32.inc(i))), B.cmp_nat_u(pos, U32.inc(i))) : {Cmp.is_lt(_) == False{} : Bool}
  %Equal.sym(Nat, U32.to_nat(U32.inc(i)), 1n+U32.to_nat(i), inc_nat_d(i, d, hi)) : {Cmp.is_lt(Nat.cmp(U32.to_nat(pos), _)) == False{} : Bool}
  nat_gt_succ(U32.to_nat(pos), U32.to_nat(i), cmp_gt_of(Nat.cmp(U32.to_nat(pos), U32.to_nat(i)), (%B.cmp_nat_u(pos, i) : {Cmp.is_lt(_) == False{} : Bool}; h1), (%B.cmp_nat_u(pos, i) : {Cmp.is_eq(_) == False{} : Bool}; h2)))

# is_eq(pos, i) == False refutes i == pos
def eq_false_ne(+pos: U32, +i: U32, h2: {U32.is_eq(pos, i) == False{} : Bool}) -> {i == pos : U32} -> Empty:
  e => L.true_false(Equal.trans(Bool, True{}, U32.is_eq(pos, i), False{}, Equal.sym(Bool, U32.is_eq(pos, i), True{}, (%Equal.sym(U32, i, pos, e) : {U32.is_eq(pos, _) == True{} : Bool}; PST.u32_eq_refl(pos))), h2))

# ---- Kernel.mask_data (in place): the cell at pos of the output of the remaining run ------------------

# the remaining run from counter i with the pending reads ra (a[i]) and rm (m[i]): the output (well
# formed) holds at pos the current cell cur when pos is behind the loop (pos < i), else cur where
# the mask word at pos is set and z where it is 0
def MDG(~T: Data, f: Nat, +i: U32, +z: T, +d: Nat, -m0: Array<U32>, -ra: Array<T> & T, -rm: Array<U32> & U32, +pos: U32, +cur: T) -> Type:
  &o: Array<T> -> &mb: Array<U32> -> {K.Kernel.mask_data.go(~T, f, i, z, ra, rm) == (o, mb) : Array<T> & Array<U32>} & {mb == m0 : Array<U32>} & Laws.WFArray(T, d, o) & {Laws.rdN(T, d, o, pos) == Bool.pick(T, U32.is_lt(pos, i), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, z)) : T}

# ... after the step's write (the array c) with the next reads pending
def MDC(~T: Data, p: Nat, +i: U32, +z: T, +d: Nat, -m0: Array<U32>, -c: Array<T>, -m2: Array<U32>, +pos: U32, +cur: T) -> Type:
  &o: Array<T> -> &mb: Array<U32> -> {K.Kernel.mask_data.go(~T, p, U32.inc(i), z, Array.get(T, c, U32.inc(i)), Array.get(U32, m2, U32.inc(i))) == (o, mb) : Array<T> & Array<U32>} & {mb == m0 : Array<U32>} & Laws.WFArray(T, d, o) & {Laws.rdN(T, d, o, pos) == Bool.pick(T, U32.is_lt(pos, i), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, z)) : T}

# the induction hypothesis: the remaining run from inc i on any array a3 (well formed, cell cur2 at
# pos) and any copy m3 of the mask
def MDIH(~T: Data, p: Nat, +i: U32, +z: T, +d: Nat, -m0: Array<U32>, +pos: U32) -> Type:
  @a3: Array<T> -> @m3: Array<U32> -> {m3 == m0 : Array<U32>} -> Laws.WFArray(T, d, a3) -> @cur2: T -> {Laws.rdN(T, d, a3, pos) == cur2 : T} -> Laws.Room(d, U32.inc(i), p) -> {U32.is_lt(pos, Laws.addn(U32.inc(i), p)) == True{} : Bool} -> {U32.is_lt(pos, U32.shln(1, d)) == True{} : Bool} -> MDG(~T, p, U32.inc(i), z, d, m0, Array.get(T, a3, U32.inc(i)), Array.get(U32, m3, U32.inc(i)), pos, cur2)


# the remaining run's answer at pos (the IH, from inc i) restated to the step's claim (from i): pos < i,
# the cell stays cur
def md_pick_lt(~T: Data, +pos: U32, +i: U32, +z: T, -m0: Array<U32>, +cur: T, +e1: {U32.is_lt(pos, i) == True{} : Bool}, +lt2: {U32.is_lt(pos, U32.inc(i)) == True{} : Bool}) -> {Bool.pick(T, U32.is_lt(pos, U32.inc(i)), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, z)) == Bool.pick(T, U32.is_lt(pos, i), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, z)) : T}:
  %Equal.sym(Bool, U32.is_lt(pos, i), True{}, e1) : {Bool.pick(T, U32.is_lt(pos, U32.inc(i)), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, z)) == Bool.pick(T, _, cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, z)) : T}
  %Equal.sym(Bool, U32.is_lt(pos, U32.inc(i)), True{}, lt2) : {Bool.pick(T, _, cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, z)) == cur : T}
  {==}

# pos == i: the cell becomes the written value pick(w != 0, x, z), w the mask word at pos, x = cur
def md_pick_eq(~T: Data, +pos: U32, +i: U32, +z: T, -m0: Array<U32>, +cur: T, +x: T, +w: U32, +e1: {U32.is_lt(pos, i) == False{} : Bool}, +lt2: {U32.is_lt(pos, U32.inc(i)) == True{} : Bool}, +ew: {w == Laws.rd_at(U32, m0, pos) : U32}, +ecx: {x == cur : T})
  -> {Bool.pick(T, U32.is_lt(pos, U32.inc(i)), Bool.pick(T, U32.is_ne(w, 0), x, z), Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), Bool.pick(T, U32.is_ne(w, 0), x, z), z)) == Bool.pick(T, U32.is_lt(pos, i), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, z)) : T}:
  %Equal.sym(Bool, U32.is_lt(pos, i), False{}, e1) : {Bool.pick(T, U32.is_lt(pos, U32.inc(i)), Bool.pick(T, U32.is_ne(w, 0), x, z), Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), Bool.pick(T, U32.is_ne(w, 0), x, z), z)) == Bool.pick(T, _, cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, z)) : T}
  %Equal.sym(Bool, U32.is_lt(pos, U32.inc(i)), True{}, lt2) : {Bool.pick(T, _, Bool.pick(T, U32.is_ne(w, 0), x, z), Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), Bool.pick(T, U32.is_ne(w, 0), x, z), z)) == Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, z) : T}
  %ew : {Bool.pick(T, U32.is_ne(w, 0), x, z) == Bool.pick(T, U32.is_ne(_, 0), cur, z) : T}
  %ecx : {Bool.pick(T, U32.is_ne(w, 0), x, z) == Bool.pick(T, U32.is_ne(w, 0), _, z) : T}
  {==}

# pos above i: untouched now, decided by the rows to come
def md_pick_gt(~T: Data, +pos: U32, +i: U32, +z: T, -m0: Array<U32>, +cur: T, +e1: {U32.is_lt(pos, i) == False{} : Bool}, +nlt2: {U32.is_lt(pos, U32.inc(i)) == False{} : Bool}) -> {Bool.pick(T, U32.is_lt(pos, U32.inc(i)), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, z)) == Bool.pick(T, U32.is_lt(pos, i), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, z)) : T}:
  %Equal.sym(Bool, U32.is_lt(pos, i), False{}, e1) : {Bool.pick(T, U32.is_lt(pos, U32.inc(i)), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, z)) == Bool.pick(T, _, cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, z)) : T}
  %Equal.sym(Bool, U32.is_lt(pos, U32.inc(i)), False{}, nlt2) : {Bool.pick(T, _, cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, z)) == Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, z) : T}
  {==}

# the IH's witness with its cell equation composed with a pick equation
def md_restate(~T: Data, p: Nat, +i: U32, +z: T, +d: Nat, -m0: Array<U32>, -c: Array<T>, -m2: Array<U32>, +pos: U32, +cur: T, +cur2: T,
  pe: {Bool.pick(T, U32.is_lt(pos, U32.inc(i)), cur2, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur2, z)) == Bool.pick(T, U32.is_lt(pos, i), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, z)) : T},
  w: MDG(~T, p, U32.inc(i), z, d, m0, Array.get(T, c, U32.inc(i)), Array.get(U32, m2, U32.inc(i)), pos, cur2))
  -> MDC(~T, p, i, z, d, m0, c, m2, pos, cur):
  (o, mb, eq, emb, wo, cell) = w
  (o, mb, eq, emb, wo, Equal.trans(T, Laws.rdN(T, d, o, pos), Bool.pick(T, U32.is_lt(pos, U32.inc(i)), cur2, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur2, z)), Bool.pick(T, U32.is_lt(pos, i), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, z)), cell, pe))

# pos == i: the written cell is read back at pos (same_at_refl through pos == i), and it is
# pick(w != 0, x, z) with x the old cell (= cur through cv)
def md_case_eq(~T: Data, p: Nat, +i: U32, +z: T, +d: Nat, -m0: Array<U32>, -a2: Array<T>, c: Array<T>, m2: Array<U32>, +em3: {m2 == m0 : Array<U32>}, +pos: U32, +cur: T, +x: T, +w: U32, +ex: {x == Laws.rd_at(T, a2, i) : T}, +ew: {w == Laws.rd_at(U32, m0, i) : U32}, +hcur: {Laws.rdN(T, d, a2, pos) == cur : T}, +hi: {U32.is_lt(i, U32.shln(1, d)) == True{} : Bool}, room2: Laws.Room(d, U32.inc(i), p), +hpos2: {U32.is_lt(pos, Laws.addn(U32.inc(i), p)) == True{} : Bool}, +hpd: {U32.is_lt(pos, U32.shln(1, d)) == True{} : Bool},
  +e1: {U32.is_lt(pos, i) == False{} : Bool}, wc: Laws.WFArray(T, d, c),
  fj: @j: U32 -> {Laws.rdN(T, d, c, j) == Bool.pick(T, Laws.same_at(d, i, j), Bool.pick(T, U32.is_ne(w, 0), x, z), Laws.rdN(T, d, a2, j)) : T}, cv: @j: U32 -> {Laws.rd_at(T, a2, j) == Laws.rdN(T, d, a2, j) : T},
  ih: MDIH(~T, p, i, z, d, m0, pos), +epi: {pos == i : U32})
  -> MDC(~T, p, i, z, d, m0, c, m2, pos, cur):
  md_restate(~T, p, i, z, d, m0, c, m2, pos, cur, Bool.pick(T, U32.is_ne(w, 0), x, z), md_pick_eq(~T, pos, i, z, m0, cur, x, w, e1, (%Equal.sym(U32, pos, i, epi) : {U32.is_lt(_, U32.inc(i)) == True{} : Bool}; PC.lt_inc_u(i, d, hi)), Equal.trans(U32, w, Laws.rd_at(U32, m0, i), Laws.rd_at(U32, m0, pos), ew, Equal.cong(U32, U32, q => Laws.rd_at(U32, m0, q), i, pos, Equal.sym(U32, pos, i, epi))), Equal.trans(T, x, Laws.rd_at(T, a2, i), cur, ex, Equal.trans(T, Laws.rd_at(T, a2, i), Laws.rdN(T, d, a2, i), cur, cv(i), Equal.trans(T, Laws.rdN(T, d, a2, i), Laws.rdN(T, d, a2, pos), cur, Equal.cong(U32, T, q => Laws.rdN(T, d, a2, q), i, pos, Equal.sym(U32, pos, i, epi)), hcur)))), ih(c, m2, em3, wc, Bool.pick(T, U32.is_ne(w, 0), x, z), (%Equal.sym(T, Laws.rdN(T, d, c, pos), Bool.pick(T, Laws.same_at(d, i, pos), Bool.pick(T, U32.is_ne(w, 0), x, z), Laws.rdN(T, d, a2, pos)), fj(pos)) : {_ == Bool.pick(T, U32.is_ne(w, 0), x, z) : T}; %Equal.sym(Bool, Laws.same_at(d, i, pos), True{}, (%Equal.sym(U32, pos, i, epi) : {Laws.same_at(d, i, _) == True{} : Bool}; PC.same_at_refl(d, i))) : {Bool.pick(T, _, Bool.pick(T, U32.is_ne(w, 0), x, z), Laws.rdN(T, d, a2, pos)) == Bool.pick(T, U32.is_ne(w, 0), x, z) : T}; {==}), room2, hpos2, hpd))

# the step's three cases, the two decisions as parameters: pos < i, pos == i, pos above i
def md_cases(~T: Data, b1: Bool, b2: Bool, p: Nat, +i: U32, +z: T, +d: Nat, -m0: Array<U32>, -a2: Array<T>, c: Array<T>, m2: Array<U32>, +em3: {m2 == m0 : Array<U32>}, +pos: U32, +cur: T, +x: T, +w: U32, +ex: {x == Laws.rd_at(T, a2, i) : T}, +ew: {w == Laws.rd_at(U32, m0, i) : U32}, +hcur: {Laws.rdN(T, d, a2, pos) == cur : T}, +hi: {U32.is_lt(i, U32.shln(1, d)) == True{} : Bool}, room2: Laws.Room(d, U32.inc(i), p), +hpos2: {U32.is_lt(pos, Laws.addn(U32.inc(i), p)) == True{} : Bool}, +hpd: {U32.is_lt(pos, U32.shln(1, d)) == True{} : Bool},
  +e1: {U32.is_lt(pos, i) == b1 : Bool}, +e2: {U32.is_eq(pos, i) == b2 : Bool}, wc: Laws.WFArray(T, d, c),
  fj: @j: U32 -> {Laws.rdN(T, d, c, j) == Bool.pick(T, Laws.same_at(d, i, j), Bool.pick(T, U32.is_ne(w, 0), x, z), Laws.rdN(T, d, a2, j)) : T}, cv: @j: U32 -> {Laws.rd_at(T, a2, j) == Laws.rdN(T, d, a2, j) : T},
  ih: MDIH(~T, p, i, z, d, m0, pos))
  -> MDC(~T, p, i, z, d, m0, c, m2, pos, cur):
  match b1 b2:
    case True{} _:
      md_restate(~T, p, i, z, d, m0, c, m2, pos, cur, cur, md_pick_lt(~T, pos, i, z, m0, cur, e1, PC.lt_trans_u(pos, i, U32.inc(i), e1, PC.lt_inc_u(i, d, hi))), ih(c, m2, em3, wc, cur, (%Equal.sym(T, Laws.rdN(T, d, c, pos), Bool.pick(T, Laws.same_at(d, i, pos), Bool.pick(T, U32.is_ne(w, 0), x, z), Laws.rdN(T, d, a2, pos)), fj(pos)) : {_ == cur : T}; %Equal.sym(Bool, Laws.same_at(d, i, pos), False{}, PC.same_false_lt(d, i, pos, hi, e1)) : {Bool.pick(T, _, Bool.pick(T, U32.is_ne(w, 0), x, z), Laws.rdN(T, d, a2, pos)) == cur : T}; hcur), room2, hpos2, hpd))
    case False{} True{}:
      md_case_eq(~T, p, i, z, d, m0, a2, c, m2, em3, pos, cur, x, w, ex, ew, hcur, hi, room2, hpos2, hpd, e1, wc, fj, cv, ih, PST.u32_eq(pos, i, e2))
    case False{} False{}:
      md_restate(~T, p, i, z, d, m0, c, m2, pos, cur, cur, md_pick_gt(~T, pos, i, z, m0, cur, e1, not_lt_inc(pos, i, d, hi, e1, e2)), ih(c, m2, em3, wc, cur, (%Equal.sym(T, Laws.rdN(T, d, c, pos), Bool.pick(T, Laws.same_at(d, i, pos), Bool.pick(T, U32.is_ne(w, 0), x, z), Laws.rdN(T, d, a2, pos)), fj(pos)) : {_ == cur : T}; %Equal.sym(Bool, Laws.same_at(d, i, pos), False{}, PC.same_false(d, i, pos, hi, hpd, eq_false_ne(pos, i, e2))) : {Bool.pick(T, _, Bool.pick(T, U32.is_ne(w, 0), x, z), Laws.rdN(T, d, a2, pos)) == cur : T}; hcur), room2, hpos2, hpd))

# the write computed: Array.set(a2, i, y) == c replaces the call; the counter bound moved to inc i
def md_step3(~T: Data, +p: Nat, +i: U32, +z: T, +d: Nat, -m0: Array<U32>, -a2: Array<T>, m2: Array<U32>, +em3: {m2 == m0 : Array<U32>}, +pos: U32, +cur: T, +x: T, +w: U32, +ex: {x == Laws.rd_at(T, a2, i) : T}, +ew: {w == Laws.rd_at(U32, m0, i) : U32}, +hcur: {Laws.rdN(T, d, a2, pos) == cur : T}, +hi: {U32.is_lt(i, U32.shln(1, d)) == True{} : Bool}, room2: Laws.Room(d, U32.inc(i), p), +hpos: {U32.is_lt(pos, Laws.addn(i, 1n+p)) == True{} : Bool}, +hpd: {U32.is_lt(pos, U32.shln(1, d)) == True{} : Bool},
  ih: MDIH(~T, p, i, z, d, m0, pos),
  ws: &c: Array<T> -> {Array.set(T, a2, i, Bool.pick(T, U32.is_ne(w, 0), x, z)) == c : Array<T>} & Laws.WFArray(T, d, c) & (@j: U32 -> {Laws.rdN(T, d, c, j) == Bool.pick(T, Laws.same_at(d, i, j), Bool.pick(T, U32.is_ne(w, 0), x, z), Laws.rdN(T, d, a2, j)) : T}) & (@j: U32 -> {Laws.rd_at(T, a2, j) == Laws.rdN(T, d, a2, j) : T}))
  -> MDC(~T, p, i, z, d, m0, Array.set(T, a2, i, Bool.pick(T, U32.is_ne(w, 0), x, z)), m2, pos, cur):
  (c, ec, wc, fj, cv) = ws
  %Equal.sym(Array<T>, Array.set(T, a2, i, Bool.pick(T, U32.is_ne(w, 0), x, z)), c, ec) : MDC(~T, p, i, z, d, m0, _, m2, pos, cur)
  md_cases(~T, U32.is_lt(pos, i), U32.is_eq(pos, i), p, i, z, d, m0, a2, c, m2, em3, pos, cur, x, w, ex, ew, hcur, hi, room2, (%Equal.sym(U32, Laws.addn(U32.inc(i), p), U32.inc(Laws.addn(i, p)), PC.addn_inc(i, p)) : {U32.is_lt(pos, _) == True{} : Bool}; hpos), hpd, {==}, {==}, wc, fj, cv, ih)

# the mask word read: Array.get(m, i) == (m, w), then the copy m2 of m everywhere
def md_step2(~T: Data, +p: Nat, +i: U32, +z: T, +d: Nat, -m0: Array<U32>, a2: Array<T>, -m: Array<U32>, +em: {m == m0 : Array<U32>}, wf: Laws.WFArray(T, d, a2), +pos: U32, +cur: T, +x: T, +ex: {x == Laws.rd_at(T, a2, i) : T}, +hcur: {Laws.rdN(T, d, a2, pos) == cur : T}, +hi: {U32.is_lt(i, U32.shln(1, d)) == True{} : Bool}, room2: Laws.Room(d, U32.inc(i), p), +hpos: {U32.is_lt(pos, Laws.addn(i, 1n+p)) == True{} : Bool}, +hpd: {U32.is_lt(pos, U32.shln(1, d)) == True{} : Bool},
  ih: MDIH(~T, p, i, z, d, m0, pos),
  wm: &m2: Array<U32> -> &w: U32 -> {m2 == m : Array<U32>} & {Array.get(U32, m, i) == (m, w) : Array<U32> & U32} & {w == Laws.rd_at(U32, m, i) : U32})
  -> MDG(~T, 1n+p, i, z, d, m0, (a2, x), Array.get(U32, m, i), pos, cur):
  (m2, +w, +em2, e1, ew) = wm
  %Equal.sym(Array<U32> & U32, Array.get(U32, m, i), (m, w), e1) : MDG(~T, 1n+p, i, z, d, m0, (a2, x), _, pos, cur)
  %em2 : MDG(~T, 1n+p, i, z, d, m0, (a2, x), (_, w), pos, cur)
  md_step3(~T, p, i, z, d, m0, a2, m2, Equal.trans(Array<U32>, m2, m, m0, em2, em), pos, cur, x, w, ex, Equal.trans(U32, w, Laws.rd_at(U32, m, i), Laws.rd_at(U32, m0, i), ew, Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, i), m, m0, em)), hcur, hi, room2, hpos, hpd, ih, PC.set_other_w(T, d, a2, i, Bool.pick(T, U32.is_ne(w, 0), x, z), wf))

# the cell read: Array.get(a, i) == (a, x), then the copy a2 of a everywhere
def md_step1(~T: Data, +p: Nat, +i: U32, +z: T, +d: Nat, -m0: Array<U32>, -a: Array<T>, m: Array<U32>, +em: {m == m0 : Array<U32>}, wf: Laws.WFArray(T, d, a), +pos: U32, +cur: T, +hcur: {Laws.rdN(T, d, a, pos) == cur : T}, room: Laws.Room(d, i, 1n+p), +hpos: {U32.is_lt(pos, Laws.addn(i, 1n+p)) == True{} : Bool}, +hpd: {U32.is_lt(pos, U32.shln(1, d)) == True{} : Bool},
  ih: MDIH(~T, p, i, z, d, m0, pos),
  wa: &b: Array<T> -> &x: T -> {b == a : Array<T>} & {Array.get(T, a, i) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, i) : T})
  -> MDG(~T, 1n+p, i, z, d, m0, Array.get(T, a, i), Array.get(U32, m, i), pos, cur):
  (+hi, room2) = room
  (a2, +x, +ea, e1, ex) = wa
  %Equal.sym(Array<T> & T, Array.get(T, a, i), (a, x), e1) : MDG(~T, 1n+p, i, z, d, m0, _, Array.get(U32, m, i), pos, cur)
  %ea : MDG(~T, 1n+p, i, z, d, m0, (_, x), Array.get(U32, m, i), pos, cur)
  md_step2(~T, p, i, z, d, m0, a2, m, em, (%Equal.sym(Array<T>, a2, a, ea) : Laws.WFArray(T, d, _); wf), pos, cur, x, Equal.trans(T, x, Laws.rd_at(T, a, i), Laws.rd_at(T, a2, i), ex, Equal.cong(Array<T>, T, q => Laws.rd_at(T, q, i), a, a2, Equal.sym(Array<T>, a2, a, ea))), Equal.trans(T, Laws.rdN(T, d, a2, pos), Laws.rdN(T, d, a, pos), cur, Equal.cong(Array<T>, T, q => Laws.rdN(T, d, q, pos), a2, a, ea), hcur), hi, room2, hpos, hpd, ih, PC.get_w(U32, m, i))

# no step left: the array as it is; pos is behind the loop (pos < addn(i, 0) = i)
def md_zero2(~T: Data, +i: U32, +z: T, +d: Nat, -m0: Array<U32>, -a: Array<T>, a2: Array<T>, -m: Array<U32>, +em: {m == m0 : Array<U32>}, +ea: {a2 == a : Array<T>}, +x: T, wf: Laws.WFArray(T, d, a), +pos: U32, +cur: T, +hcur: {Laws.rdN(T, d, a, pos) == cur : T}, +hpos: {U32.is_lt(pos, i) == True{} : Bool},
  wm: &m2: Array<U32> -> &w: U32 -> {m2 == m : Array<U32>} & {Array.get(U32, m, i) == (m, w) : Array<U32> & U32} & {w == Laws.rd_at(U32, m, i) : U32})
  -> MDG(~T, 0n, i, z, d, m0, (a, x), Array.get(U32, m, i), pos, cur):
  (m2, +w, +em2, e1, ew) = wm
  %Equal.sym(Array<U32> & U32, Array.get(U32, m, i), (m, w), e1) : MDG(~T, 0n, i, z, d, m0, (a, x), _, pos, cur)
  %ea : MDG(~T, 0n, i, z, d, m0, (_, x), (m, w), pos, cur)
  %em2 : MDG(~T, 0n, i, z, d, m0, (a2, x), (_, w), pos, cur)
  (a2, m2, {==}, Equal.trans(Array<U32>, m2, m, m0, em2, em), (%Equal.sym(Array<T>, a2, a, ea) : Laws.WFArray(T, d, _); wf), (%Equal.sym(Bool, U32.is_lt(pos, i), True{}, hpos) : {Laws.rdN(T, d, a2, pos) == Bool.pick(T, _, cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, z)) : T}; %Equal.sym(Array<T>, a2, a, ea) : {Laws.rdN(T, d, _, pos) == cur : T}; hcur))

def md_zero(~T: Data, +i: U32, +z: T, +d: Nat, -m0: Array<U32>, -a: Array<T>, m: Array<U32>, +em: {m == m0 : Array<U32>}, wf: Laws.WFArray(T, d, a), +pos: U32, +cur: T, +hcur: {Laws.rdN(T, d, a, pos) == cur : T}, +hpos: {U32.is_lt(pos, i) == True{} : Bool},
  wa: &b: Array<T> -> &x: T -> {b == a : Array<T>} & {Array.get(T, a, i) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, i) : T})
  -> MDG(~T, 0n, i, z, d, m0, Array.get(T, a, i), Array.get(U32, m, i), pos, cur):
  (a2, +x, +ea, e1, ex) = wa
  %Equal.sym(Array<T> & T, Array.get(T, a, i), (a, x), e1) : MDG(~T, 0n, i, z, d, m0, _, Array.get(U32, m, i), pos, cur)
  md_zero2(~T, i, z, d, m0, a, a2, m, em, ea, x, wf, pos, cur, hcur, hpos, PC.get_w(U32, m, i))

# Kernel.mask_data.go with f steps left at counter i on a well-formed array whose cell at pos is cur,
# the mask a copy of m0, the next f write indices below 2^d, pos below addn(i, f) and below 2^d
def md_go(~T: Data, f: Nat, +i: U32, +z: T, +d: Nat, -m0: Array<U32>, a: Array<T>, m: Array<U32>, +em: {m == m0 : Array<U32>}, wf: Laws.WFArray(T, d, a), +pos: U32, +cur: T, +hcur: {Laws.rdN(T, d, a, pos) == cur : T}, room: Laws.Room(d, i, f), +hpos: {U32.is_lt(pos, Laws.addn(i, f)) == True{} : Bool}, +hpd: {U32.is_lt(pos, U32.shln(1, d)) == True{} : Bool})
  -> MDG(~T, f, i, z, d, m0, Array.get(T, a, i), Array.get(U32, m, i), pos, cur):
  match f:
    case 0n:
      md_zero(~T, i, z, d, m0, a, m, em, wf, pos, cur, hcur, hpos, PC.get_w(T, a, i))
    case 1n++p:
      md_step1(~T, p, i, z, d, m0, a, m, em, wf, pos, cur, hcur, room, hpos, hpd, a3 => m3 => em3 => wf3 => cur2 => hcur2 => room2 => hpos2 => hpd2 => md_go(~T, p, U32.inc(i), z, d, m0, a3, m3, em3, wf3, pos, cur2, hcur2, room2, hpos2, hpd2), PC.get_w(T, a, i))

# nothing is below 0: the position is never behind the loop at its start
def lt0_false_k(c: Cmp, +pos: U32, e: {U32.cmp(pos, 0) == c : Cmp}) -> {U32.is_lt(pos, 0) == False{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({U32.is_lt(pos, 0) == False{} : Bool}, PC.lt0(pos, (%Equal.sym(Cmp, U32.cmp(pos, 0), LT{}, e) : {Cmp.is_lt(_) == True{} : Bool}; {==})))
    case EQ{}:
      %Equal.sym(Cmp, U32.cmp(pos, 0), EQ{}, e) : {Cmp.is_lt(_) == False{} : Bool}
      {==}
    case GT{}:
      %Equal.sym(Cmp, U32.cmp(pos, 0), GT{}, e) : {Cmp.is_lt(_) == False{} : Bool}
      {==}

def lt0_false(+pos: U32) -> {U32.is_lt(pos, 0) == False{} : Bool}:
  lt0_false_k(U32.cmp(pos, 0), pos, {==})
# ---- Kernel.mask_data(n, a, m, z): the cell at pos < n (template; the law is the U32 instance) --------

# the kernel's answer as a witness
def MDW(~T: Data, +n: U32, +d: Nat, -a: Array<T>, -m: Array<U32>, +z: T, +pos: U32) -> Type:
  &o: Array<T> -> &mb: Array<U32> -> {K.Kernel.mask_data(~T, n, a, m, z) == (o, mb) : Array<T> & Array<U32>} & {mb == m : Array<U32>} & Laws.WFArray(T, d, o) & {Laws.rdN(T, d, o, pos) == Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m, pos), 0), Laws.rd_at(T, a, pos), z) : T}

def md_fin(~T: Data, +n: U32, +d: Nat, -a: Array<T>, -m: Array<U32>, +z: T, +pos: U32, +cur: T, +ecur: {cur == Laws.rd_at(T, a, pos) : T}, +hpos: {U32.is_lt(pos, n) == True{} : Bool},
  w: MDG(~T, U32.to_nat(n), 0, z, d, m, Array.get(T, a, 0), Array.get(U32, m, 0), pos, cur)) -> MDW(~T, n, d, a, m, z, pos):
  (o, mb, eq, emb, wo, cell) = w
  (o, mb, eq, emb, wo, Equal.trans(T, Laws.rdN(T, d, o, pos), Bool.pick(T, U32.is_lt(pos, 0), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m, pos), 0), cur, z)), Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m, pos), 0), Laws.rd_at(T, a, pos), z), cell, (%ecur : {Bool.pick(T, U32.is_lt(pos, 0), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m, pos), 0), cur, z)) == Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m, pos), 0), _, z) : T}; %Equal.sym(Bool, U32.is_lt(pos, 0), False{}, lt0_false(pos)) : {Bool.pick(T, _, cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m, pos), 0), cur, z)) == Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m, pos), 0), cur, z) : T}; {==})))

# the loop from counter 0 on the copy a3 of the input, whose cell at pos is the Data value x
def md_cur3(~T: Data, +n: U32, +d: Nat, -a: Array<T>, -a2: Array<T>, a3: Array<T>, m: Array<U32>, +z: T, +pos: U32, +ea: {a2 == a : Array<T>}, +ea3: {a3 == a2 : Array<T>}, +x: T, +ex: {x == Laws.rd_at(T, a2, pos) : T}, wf2: Laws.WFArray(T, d, a2), cv: @k: U32 -> {Laws.rd_at(T, a, k) == Laws.rdN(T, d, a, k) : T}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hpos: {U32.is_lt(pos, n) == True{} : Bool})
  -> MDW(~T, n, d, a2, m, z, pos):
  %ea3 : MDW(~T, n, d, _, m, z, pos)
  md_fin(~T, n, d, a3, m, z, pos, x, Equal.trans(T, x, Laws.rd_at(T, a2, pos), Laws.rd_at(T, a3, pos), ex, Equal.cong(Array<T>, T, q => Laws.rd_at(T, q, pos), a2, a3, Equal.sym(Array<T>, a3, a2, ea3))), hpos, md_go(~T, U32.to_nat(n), 0, z, d, m, a3, m, {==}, (%Equal.sym(Array<T>, a3, a2, ea3) : Laws.WFArray(T, d, _); wf2), pos, x, Equal.trans(T, Laws.rdN(T, d, a3, pos), Laws.rdN(T, d, a, pos), x, Equal.cong(Array<T>, T, q => Laws.rdN(T, d, q, pos), a3, a, Equal.trans(Array<T>, a3, a2, a, ea3, ea)), Equal.trans(T, Laws.rdN(T, d, a, pos), Laws.rd_at(T, a, pos), x, Equal.sym(T, Laws.rd_at(T, a, pos), Laws.rdN(T, d, a, pos), cv(pos)), Equal.trans(T, Laws.rd_at(T, a, pos), Laws.rd_at(T, a2, pos), x, Equal.cong(Array<T>, T, q => Laws.rd_at(T, q, pos), a, a2, Equal.sym(Array<T>, a2, a, ea)), Equal.sym(T, x, Laws.rd_at(T, a2, pos), ex)))), B.room_from(d, n, fits), (%Equal.sym(U32, Laws.addn(0, U32.to_nat(n)), n, B.addn_to_nat(n)) : {U32.is_lt(pos, _) == True{} : Bool}; hpos), PST.lt_le_trans_u(pos, n, U32.shln(1, d), hpos, fits)))


# the cell at pos as a Data value x (get_w on the copy a2; the copy a3 carries on), its model
# equation through rd_all's forall over the original
def md_cur2(~T: Data, +n: U32, +d: Nat, -a: Array<T>, -a2: Array<T>, m: Array<U32>, +z: T, +pos: U32, +ea: {a2 == a : Array<T>}, wf2: Laws.WFArray(T, d, a2), cv: @k: U32 -> {Laws.rd_at(T, a, k) == Laws.rdN(T, d, a, k) : T}, fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hpos: {U32.is_lt(pos, n) == True{} : Bool},
  w: &a3: Array<T> -> &x: T -> {a3 == a2 : Array<T>} & {Array.get(T, a2, pos) == (a2, x) : Array<T> & T} & {x == Laws.rd_at(T, a2, pos) : T})
  -> MDW(~T, n, d, a2, m, z, pos):
  (a3, +x, +ea3, e1, ex) = w
  md_cur3(~T, n, d, a, a2, a3, m, z, pos, ea, ea3, x, ex, wf2, cv, fits, hpos)


def md_cur(~T: Data, +n: U32, +d: Nat, -a: Array<T>, m: Array<U32>, +z: T, +pos: U32, fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hpos: {U32.is_lt(pos, n) == True{} : Bool},
  w: &a2: Array<T> -> {a2 == a : Array<T>} & Laws.WFArray(T, d, a2) & (@k: U32 -> {Laws.rd_at(T, a, k) == Laws.rdN(T, d, a, k) : T}))
  -> MDW(~T, n, d, a, m, z, pos):
  (a2, +ea, wf2, cv) = w
  %ea : MDW(~T, n, d, _, m, z, pos)
  md_cur2(~T, n, d, a, a2, m, z, pos, ea, wf2, cv, fits, hpos, PC.get_w(T, a2, pos))

def mask_data_w(~T: Data, +n: U32, +d: Nat, a: Array<T>, m: Array<U32>, +z: T, +pos: U32, wf: Laws.WFArray(T, d, a), fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hpos: {U32.is_lt(pos, n) == True{} : Bool}) -> MDW(~T, n, d, a, m, z, pos):
  md_cur(~T, n, d, a, m, z, pos, fits, hpos, PST.rd_all(T, d, a, wf))


# ---- Kernel.mask_data hands the mask back ---------------------------------------------------------------

def MDM(~T: Data, f: Nat, +i: U32, +z: T, -ra: Array<T> & T, -m: Array<U32>) -> Type:
  {Pair.snd(Array<T>, Array<U32>, K.Kernel.mask_data.go(~T, f, i, z, ra, Array.get(U32, m, i))) == m : Array<U32>}

def mdm_step2(~T: Data, p: Nat, +i: U32, +z: T, a2: Array<T>, -m: Array<U32>, +x: T,
  ih: @c: Array<T> -> @m3: Array<U32> -> MDM(~T, p, U32.inc(i), z, Array.get(T, c, U32.inc(i)), m3),
  wm: &m2: Array<U32> -> &w: U32 -> {m2 == m : Array<U32>} & {Array.get(U32, m, i) == (m, w) : Array<U32> & U32} & {w == Laws.rd_at(U32, m, i) : U32})
  -> MDM(~T, 1n+p, i, z, (a2, x), m):
  (m2, +w, em2, e1, ew) = wm
  %Equal.sym(Array<U32> & U32, Array.get(U32, m, i), (m, w), e1) : {Pair.snd(Array<T>, Array<U32>, K.Kernel.mask_data.go(~T, 1n+p, i, z, (a2, x), _)) == m : Array<U32>}
  %em2 : {Pair.snd(Array<T>, Array<U32>, K.Kernel.mask_data.go(~T, 1n+p, i, z, (a2, x), (_, w))) == _ : Array<U32>}
  ih(Array.set(T, a2, i, Bool.pick(T, U32.is_ne(w, 0), x, z)), m2)

def mdm_step1(~T: Data, p: Nat, +i: U32, +z: T, -a: Array<T>, m: Array<U32>,
  ih: @c: Array<T> -> @m3: Array<U32> -> MDM(~T, p, U32.inc(i), z, Array.get(T, c, U32.inc(i)), m3),
  wa: &b: Array<T> -> &x: T -> {b == a : Array<T>} & {Array.get(T, a, i) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, i) : T})
  -> MDM(~T, 1n+p, i, z, Array.get(T, a, i), m):
  (a2, +x, ea, e1, ex) = wa
  %Equal.sym(Array<T> & T, Array.get(T, a, i), (a, x), e1) : MDM(~T, 1n+p, i, z, _, m)
  %ea : MDM(~T, 1n+p, i, z, (_, x), m)
  mdm_step2(~T, p, i, z, a2, m, x, ih, PC.get_w(U32, m, i))

def mdm_zero2(~T: Data, +i: U32, +z: T, -a: Array<T>, +x: T, -m: Array<U32>,
  wm: &m2: Array<U32> -> &w: U32 -> {m2 == m : Array<U32>} & {Array.get(U32, m, i) == (m, w) : Array<U32> & U32} & {w == Laws.rd_at(U32, m, i) : U32})
  -> MDM(~T, 0n, i, z, (a, x), m):
  (m2, +w, em2, e1, ew) = wm
  %Equal.sym(Array<U32> & U32, Array.get(U32, m, i), (m, w), e1) : {Pair.snd(Array<T>, Array<U32>, K.Kernel.mask_data.go(~T, 0n, i, z, (a, x), _)) == m : Array<U32>}
  {==}

def mdm_zero(~T: Data, +i: U32, +z: T, -a: Array<T>, m: Array<U32>,
  wa: &b: Array<T> -> &x: T -> {b == a : Array<T>} & {Array.get(T, a, i) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, i) : T})
  -> MDM(~T, 0n, i, z, Array.get(T, a, i), m):
  (a2, +x, ea, e1, ex) = wa
  %Equal.sym(Array<T> & T, Array.get(T, a, i), (a, x), e1) : MDM(~T, 0n, i, z, _, m)
  mdm_zero2(~T, i, z, a, x, m, PC.get_w(U32, m, i))

def mdm_go(~T: Data, f: Nat, +i: U32, +z: T, a: Array<T>, m: Array<U32>) -> MDM(~T, f, i, z, Array.get(T, a, i), m):
  match f:
    case 0n:
      mdm_zero(~T, i, z, a, m, PC.get_w(T, a, i))
    case 1n++p:
      mdm_step1(~T, p, i, z, a, m, c => m3 => mdm_go(~T, p, U32.inc(i), z, c, m3), PC.get_w(T, a, i))

# ---- the laws: Kernel.mask_data at the U32 instance ------------------------------------------------------

def md_cell_fin(+n: U32, +d: Nat, -a: Array<U32>, -m: Array<U32>, +z: U32, +pos: U32, w: MDW(~U32, n, d, a, m, z, pos))
  -> {Laws.rd_at(U32, Pair.fst(Array<U32>, Array<U32>, K.Kernel.mask_data(~U32, n, a, m, z)), pos) == Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, pos), 0), Laws.rd_at(U32, a, pos), z) : U32}:
  (o, mb, eq, emb, wo, cell) = w
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.mask_data(~U32, n, a, m, z), (o, mb), eq) : {Laws.rd_at(U32, Pair.fst(Array<U32>, Array<U32>, _), pos) == Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, pos), 0), Laws.rd_at(U32, a, pos), z) : U32}
  %Equal.sym(U32, Laws.rd_at(U32, o, pos), Laws.rdN(U32, d, o, pos), Laws.rd_at_wf(U32, d, o, pos, wo)) : {_ == Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, pos), 0), Laws.rd_at(U32, a, pos), z) : U32}
  cell

def Laws.mask_data_cell(n, d, a, m, z, pos, wf, fits, hpos):
  md_cell_fin(n, d, a, m, z, pos, mask_data_w(~U32, n, d, a, m, z, pos, wf, fits, hpos))

# the mask back without any hypothesis on the data array: the separate induction mdm_go (the MDW
# witness carries the same fact, but under the well-formedness and slot hypotheses)
def Laws.mask_data_keeps_mask(n, a, m, z):
  mdm_go(~U32, U32.to_nat(n), 0, z, a, m)

# ---- Kernel.choose (in place into a): the cell at pos of the output of the remaining run ----------------
#
# The same single-position induction as mask_data's; the "else" value is b's cell at pos (b is read
# every step and handed back: its model facts speak about the original b0).

def CHG(~T: Data, f: Nat, +i: U32, +d: Nat, -m0: Array<U32>, -b0: Array<T>, -ra: Array<T> & T, -rb: Array<T> & T, -rm: Array<U32> & U32, +pos: U32, +cur: T) -> Type:
  &mb: Array<U32> -> &o: Array<T> -> {K.Kernel.choose.go(~T, f, i, ra, rb, rm) == (mb, o) : Array<U32> & Array<T>} & {mb == m0 : Array<U32>} & Laws.WFArray(T, d, o) & {Laws.rdN(T, d, o, pos) == Bool.pick(T, U32.is_lt(pos, i), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, Laws.rd_at(T, b0, pos))) : T}

def CHC(~T: Data, p: Nat, +i: U32, +d: Nat, -m0: Array<U32>, -b0: Array<T>, -c: Array<T>, -b2: Array<T>, -m2: Array<U32>, +pos: U32, +cur: T) -> Type:
  &mb: Array<U32> -> &o: Array<T> -> {K.Kernel.choose.go(~T, p, U32.inc(i), Array.get(T, c, U32.inc(i)), Array.get(T, b2, U32.inc(i)), Array.get(U32, m2, U32.inc(i))) == (mb, o) : Array<U32> & Array<T>} & {mb == m0 : Array<U32>} & Laws.WFArray(T, d, o) & {Laws.rdN(T, d, o, pos) == Bool.pick(T, U32.is_lt(pos, i), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, Laws.rd_at(T, b0, pos))) : T}

def CHIH(~T: Data, p: Nat, +i: U32, +d: Nat, -m0: Array<U32>, -b0: Array<T>, +pos: U32) -> Type:
  @a3: Array<T> -> @b3: Array<T> -> @m3: Array<U32> -> {b3 == b0 : Array<T>} -> {m3 == m0 : Array<U32>} -> Laws.WFArray(T, d, a3) -> @cur2: T -> {Laws.rdN(T, d, a3, pos) == cur2 : T} -> Laws.Room(d, U32.inc(i), p) -> {U32.is_lt(pos, Laws.addn(U32.inc(i), p)) == True{} : Bool} -> {U32.is_lt(pos, U32.shln(1, d)) == True{} : Bool} -> CHG(~T, p, U32.inc(i), d, m0, b0, Array.get(T, a3, U32.inc(i)), Array.get(T, b3, U32.inc(i)), Array.get(U32, m3, U32.inc(i)), pos, cur2)

def ch_pick_lt(~T: Data, +pos: U32, +i: U32, -m0: Array<U32>, -b0: Array<T>, +cur: T, +e1: {U32.is_lt(pos, i) == True{} : Bool}, +lt2: {U32.is_lt(pos, U32.inc(i)) == True{} : Bool}) -> {Bool.pick(T, U32.is_lt(pos, U32.inc(i)), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, Laws.rd_at(T, b0, pos))) == Bool.pick(T, U32.is_lt(pos, i), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, Laws.rd_at(T, b0, pos))) : T}:
  %Equal.sym(Bool, U32.is_lt(pos, i), True{}, e1) : {Bool.pick(T, U32.is_lt(pos, U32.inc(i)), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, Laws.rd_at(T, b0, pos))) == Bool.pick(T, _, cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, Laws.rd_at(T, b0, pos))) : T}
  %Equal.sym(Bool, U32.is_lt(pos, U32.inc(i)), True{}, lt2) : {Bool.pick(T, _, cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, Laws.rd_at(T, b0, pos))) == cur : T}
  {==}

def ch_pick_eq(~T: Data, +pos: U32, +i: U32, -m0: Array<U32>, -b0: Array<T>, +cur: T, +x: T, +y: T, +w: U32, +e1: {U32.is_lt(pos, i) == False{} : Bool}, +lt2: {U32.is_lt(pos, U32.inc(i)) == True{} : Bool}, +ew: {w == Laws.rd_at(U32, m0, pos) : U32}, +ecx: {x == cur : T}, +ey: {y == Laws.rd_at(T, b0, pos) : T})
  -> {Bool.pick(T, U32.is_lt(pos, U32.inc(i)), Bool.pick(T, U32.is_ne(w, 0), x, y), Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), Bool.pick(T, U32.is_ne(w, 0), x, y), Laws.rd_at(T, b0, pos))) == Bool.pick(T, U32.is_lt(pos, i), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, Laws.rd_at(T, b0, pos))) : T}:
  %Equal.sym(Bool, U32.is_lt(pos, i), False{}, e1) : {Bool.pick(T, U32.is_lt(pos, U32.inc(i)), Bool.pick(T, U32.is_ne(w, 0), x, y), Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), Bool.pick(T, U32.is_ne(w, 0), x, y), Laws.rd_at(T, b0, pos))) == Bool.pick(T, _, cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, Laws.rd_at(T, b0, pos))) : T}
  %Equal.sym(Bool, U32.is_lt(pos, U32.inc(i)), True{}, lt2) : {Bool.pick(T, _, Bool.pick(T, U32.is_ne(w, 0), x, y), Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), Bool.pick(T, U32.is_ne(w, 0), x, y), Laws.rd_at(T, b0, pos))) == Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, Laws.rd_at(T, b0, pos)) : T}
  %ew : {Bool.pick(T, U32.is_ne(w, 0), x, y) == Bool.pick(T, U32.is_ne(_, 0), cur, Laws.rd_at(T, b0, pos)) : T}
  %ecx : {Bool.pick(T, U32.is_ne(w, 0), x, y) == Bool.pick(T, U32.is_ne(w, 0), _, Laws.rd_at(T, b0, pos)) : T}
  %ey : {Bool.pick(T, U32.is_ne(w, 0), x, y) == Bool.pick(T, U32.is_ne(w, 0), x, _) : T}
  {==}

def ch_pick_gt(~T: Data, +pos: U32, +i: U32, -m0: Array<U32>, -b0: Array<T>, +cur: T, +e1: {U32.is_lt(pos, i) == False{} : Bool}, +nlt2: {U32.is_lt(pos, U32.inc(i)) == False{} : Bool}) -> {Bool.pick(T, U32.is_lt(pos, U32.inc(i)), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, Laws.rd_at(T, b0, pos))) == Bool.pick(T, U32.is_lt(pos, i), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, Laws.rd_at(T, b0, pos))) : T}:
  %Equal.sym(Bool, U32.is_lt(pos, i), False{}, e1) : {Bool.pick(T, U32.is_lt(pos, U32.inc(i)), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, Laws.rd_at(T, b0, pos))) == Bool.pick(T, _, cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, Laws.rd_at(T, b0, pos))) : T}
  %Equal.sym(Bool, U32.is_lt(pos, U32.inc(i)), False{}, nlt2) : {Bool.pick(T, _, cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, Laws.rd_at(T, b0, pos))) == Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, Laws.rd_at(T, b0, pos)) : T}
  {==}

def ch_restate(~T: Data, p: Nat, +i: U32, +d: Nat, -m0: Array<U32>, -b0: Array<T>, -c: Array<T>, -b2: Array<T>, -m2: Array<U32>, +pos: U32, +cur: T, +cur2: T,
  pe: {Bool.pick(T, U32.is_lt(pos, U32.inc(i)), cur2, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur2, Laws.rd_at(T, b0, pos))) == Bool.pick(T, U32.is_lt(pos, i), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, Laws.rd_at(T, b0, pos))) : T},
  w: CHG(~T, p, U32.inc(i), d, m0, b0, Array.get(T, c, U32.inc(i)), Array.get(T, b2, U32.inc(i)), Array.get(U32, m2, U32.inc(i)), pos, cur2))
  -> CHC(~T, p, i, d, m0, b0, c, b2, m2, pos, cur):
  (mb, o, eq, emb, wo, cell) = w
  (mb, o, eq, emb, wo, Equal.trans(T, Laws.rdN(T, d, o, pos), Bool.pick(T, U32.is_lt(pos, U32.inc(i)), cur2, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur2, Laws.rd_at(T, b0, pos))), Bool.pick(T, U32.is_lt(pos, i), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, Laws.rd_at(T, b0, pos))), cell, pe))

# pos == i: the written cell pick(w != 0, x, y) is read back at pos; x = cur, y = b's cell at pos
def ch_case_eq(~T: Data, p: Nat, +i: U32, +d: Nat, -m0: Array<U32>, -b0: Array<T>, -a2: Array<T>, c: Array<T>, b2: Array<T>, m2: Array<U32>, +eb3: {b2 == b0 : Array<T>}, +em3: {m2 == m0 : Array<U32>}, +pos: U32, +cur: T, +x: T, +y: T, +w: U32, +ex: {x == Laws.rd_at(T, a2, i) : T}, +ey: {y == Laws.rd_at(T, b0, i) : T}, +ew: {w == Laws.rd_at(U32, m0, i) : U32}, +hcur: {Laws.rdN(T, d, a2, pos) == cur : T}, +hi: {U32.is_lt(i, U32.shln(1, d)) == True{} : Bool}, room2: Laws.Room(d, U32.inc(i), p), +hpos2: {U32.is_lt(pos, Laws.addn(U32.inc(i), p)) == True{} : Bool}, +hpd: {U32.is_lt(pos, U32.shln(1, d)) == True{} : Bool},
  +e1: {U32.is_lt(pos, i) == False{} : Bool}, wc: Laws.WFArray(T, d, c),
  fj: @j: U32 -> {Laws.rdN(T, d, c, j) == Bool.pick(T, Laws.same_at(d, i, j), Bool.pick(T, U32.is_ne(w, 0), x, y), Laws.rdN(T, d, a2, j)) : T}, cv: @j: U32 -> {Laws.rd_at(T, a2, j) == Laws.rdN(T, d, a2, j) : T},
  ih: CHIH(~T, p, i, d, m0, b0, pos), +epi: {pos == i : U32})
  -> CHC(~T, p, i, d, m0, b0, c, b2, m2, pos, cur):
  ch_restate(~T, p, i, d, m0, b0, c, b2, m2, pos, cur, Bool.pick(T, U32.is_ne(w, 0), x, y), ch_pick_eq(~T, pos, i, m0, b0, cur, x, y, w, e1, (%Equal.sym(U32, pos, i, epi) : {U32.is_lt(_, U32.inc(i)) == True{} : Bool}; PC.lt_inc_u(i, d, hi)), Equal.trans(U32, w, Laws.rd_at(U32, m0, i), Laws.rd_at(U32, m0, pos), ew, Equal.cong(U32, U32, q => Laws.rd_at(U32, m0, q), i, pos, Equal.sym(U32, pos, i, epi))), Equal.trans(T, x, Laws.rd_at(T, a2, i), cur, ex, Equal.trans(T, Laws.rd_at(T, a2, i), Laws.rdN(T, d, a2, i), cur, cv(i), Equal.trans(T, Laws.rdN(T, d, a2, i), Laws.rdN(T, d, a2, pos), cur, Equal.cong(U32, T, q => Laws.rdN(T, d, a2, q), i, pos, Equal.sym(U32, pos, i, epi)), hcur))), Equal.trans(T, y, Laws.rd_at(T, b0, i), Laws.rd_at(T, b0, pos), ey, Equal.cong(U32, T, q => Laws.rd_at(T, b0, q), i, pos, Equal.sym(U32, pos, i, epi)))), ih(c, b2, m2, eb3, em3, wc, Bool.pick(T, U32.is_ne(w, 0), x, y), (%Equal.sym(T, Laws.rdN(T, d, c, pos), Bool.pick(T, Laws.same_at(d, i, pos), Bool.pick(T, U32.is_ne(w, 0), x, y), Laws.rdN(T, d, a2, pos)), fj(pos)) : {_ == Bool.pick(T, U32.is_ne(w, 0), x, y) : T}; %Equal.sym(Bool, Laws.same_at(d, i, pos), True{}, (%Equal.sym(U32, pos, i, epi) : {Laws.same_at(d, i, _) == True{} : Bool}; PC.same_at_refl(d, i))) : {Bool.pick(T, _, Bool.pick(T, U32.is_ne(w, 0), x, y), Laws.rdN(T, d, a2, pos)) == Bool.pick(T, U32.is_ne(w, 0), x, y) : T}; {==}), room2, hpos2, hpd))

def ch_cases(~T: Data, b1: Bool, bq: Bool, p: Nat, +i: U32, +d: Nat, -m0: Array<U32>, -b0: Array<T>, -a2: Array<T>, c: Array<T>, b2: Array<T>, m2: Array<U32>, +eb3: {b2 == b0 : Array<T>}, +em3: {m2 == m0 : Array<U32>}, +pos: U32, +cur: T, +x: T, +y: T, +w: U32, +ex: {x == Laws.rd_at(T, a2, i) : T}, +ey: {y == Laws.rd_at(T, b0, i) : T}, +ew: {w == Laws.rd_at(U32, m0, i) : U32}, +hcur: {Laws.rdN(T, d, a2, pos) == cur : T}, +hi: {U32.is_lt(i, U32.shln(1, d)) == True{} : Bool}, room2: Laws.Room(d, U32.inc(i), p), +hpos2: {U32.is_lt(pos, Laws.addn(U32.inc(i), p)) == True{} : Bool}, +hpd: {U32.is_lt(pos, U32.shln(1, d)) == True{} : Bool},
  +e1: {U32.is_lt(pos, i) == b1 : Bool}, +e2: {U32.is_eq(pos, i) == bq : Bool}, wc: Laws.WFArray(T, d, c),
  fj: @j: U32 -> {Laws.rdN(T, d, c, j) == Bool.pick(T, Laws.same_at(d, i, j), Bool.pick(T, U32.is_ne(w, 0), x, y), Laws.rdN(T, d, a2, j)) : T}, cv: @j: U32 -> {Laws.rd_at(T, a2, j) == Laws.rdN(T, d, a2, j) : T},
  ih: CHIH(~T, p, i, d, m0, b0, pos))
  -> CHC(~T, p, i, d, m0, b0, c, b2, m2, pos, cur):
  match b1 bq:
    case True{} _:
      ch_restate(~T, p, i, d, m0, b0, c, b2, m2, pos, cur, cur, ch_pick_lt(~T, pos, i, m0, b0, cur, e1, PC.lt_trans_u(pos, i, U32.inc(i), e1, PC.lt_inc_u(i, d, hi))), ih(c, b2, m2, eb3, em3, wc, cur, (%Equal.sym(T, Laws.rdN(T, d, c, pos), Bool.pick(T, Laws.same_at(d, i, pos), Bool.pick(T, U32.is_ne(w, 0), x, y), Laws.rdN(T, d, a2, pos)), fj(pos)) : {_ == cur : T}; %Equal.sym(Bool, Laws.same_at(d, i, pos), False{}, PC.same_false_lt(d, i, pos, hi, e1)) : {Bool.pick(T, _, Bool.pick(T, U32.is_ne(w, 0), x, y), Laws.rdN(T, d, a2, pos)) == cur : T}; hcur), room2, hpos2, hpd))
    case False{} True{}:
      ch_case_eq(~T, p, i, d, m0, b0, a2, c, b2, m2, eb3, em3, pos, cur, x, y, w, ex, ey, ew, hcur, hi, room2, hpos2, hpd, e1, wc, fj, cv, ih, PST.u32_eq(pos, i, e2))
    case False{} False{}:
      ch_restate(~T, p, i, d, m0, b0, c, b2, m2, pos, cur, cur, ch_pick_gt(~T, pos, i, m0, b0, cur, e1, not_lt_inc(pos, i, d, hi, e1, e2)), ih(c, b2, m2, eb3, em3, wc, cur, (%Equal.sym(T, Laws.rdN(T, d, c, pos), Bool.pick(T, Laws.same_at(d, i, pos), Bool.pick(T, U32.is_ne(w, 0), x, y), Laws.rdN(T, d, a2, pos)), fj(pos)) : {_ == cur : T}; %Equal.sym(Bool, Laws.same_at(d, i, pos), False{}, PC.same_false(d, i, pos, hi, hpd, eq_false_ne(pos, i, e2))) : {Bool.pick(T, _, Bool.pick(T, U32.is_ne(w, 0), x, y), Laws.rdN(T, d, a2, pos)) == cur : T}; hcur), room2, hpos2, hpd))

# the write computed
def ch_step4(~T: Data, +p: Nat, +i: U32, +d: Nat, -m0: Array<U32>, -b0: Array<T>, -a2: Array<T>, b2: Array<T>, m2: Array<U32>, +eb3: {b2 == b0 : Array<T>}, +em3: {m2 == m0 : Array<U32>}, +pos: U32, +cur: T, +x: T, +y: T, +w: U32, +ex: {x == Laws.rd_at(T, a2, i) : T}, +ey: {y == Laws.rd_at(T, b0, i) : T}, +ew: {w == Laws.rd_at(U32, m0, i) : U32}, +hcur: {Laws.rdN(T, d, a2, pos) == cur : T}, +hi: {U32.is_lt(i, U32.shln(1, d)) == True{} : Bool}, room2: Laws.Room(d, U32.inc(i), p), +hpos: {U32.is_lt(pos, Laws.addn(i, 1n+p)) == True{} : Bool}, +hpd: {U32.is_lt(pos, U32.shln(1, d)) == True{} : Bool},
  ih: CHIH(~T, p, i, d, m0, b0, pos),
  ws: &c: Array<T> -> {Array.set(T, a2, i, Bool.pick(T, U32.is_ne(w, 0), x, y)) == c : Array<T>} & Laws.WFArray(T, d, c) & (@j: U32 -> {Laws.rdN(T, d, c, j) == Bool.pick(T, Laws.same_at(d, i, j), Bool.pick(T, U32.is_ne(w, 0), x, y), Laws.rdN(T, d, a2, j)) : T}) & (@j: U32 -> {Laws.rd_at(T, a2, j) == Laws.rdN(T, d, a2, j) : T}))
  -> CHC(~T, p, i, d, m0, b0, Array.set(T, a2, i, Bool.pick(T, U32.is_ne(w, 0), x, y)), b2, m2, pos, cur):
  (c, ec, wc, fj, cv) = ws
  %Equal.sym(Array<T>, Array.set(T, a2, i, Bool.pick(T, U32.is_ne(w, 0), x, y)), c, ec) : CHC(~T, p, i, d, m0, b0, _, b2, m2, pos, cur)
  ch_cases(~T, U32.is_lt(pos, i), U32.is_eq(pos, i), p, i, d, m0, b0, a2, c, b2, m2, eb3, em3, pos, cur, x, y, w, ex, ey, ew, hcur, hi, room2, (%Equal.sym(U32, Laws.addn(U32.inc(i), p), U32.inc(Laws.addn(i, p)), PC.addn_inc(i, p)) : {U32.is_lt(pos, _) == True{} : Bool}; hpos), hpd, {==}, {==}, wc, fj, cv, ih)

# the mask word read
def ch_step3(~T: Data, +p: Nat, +i: U32, +d: Nat, -m0: Array<U32>, -b0: Array<T>, a2: Array<T>, b2: Array<T>, -m: Array<U32>, +eb3: {b2 == b0 : Array<T>}, +em: {m == m0 : Array<U32>}, wf: Laws.WFArray(T, d, a2), +pos: U32, +cur: T, +x: T, +y: T, +ex: {x == Laws.rd_at(T, a2, i) : T}, +ey: {y == Laws.rd_at(T, b0, i) : T}, +hcur: {Laws.rdN(T, d, a2, pos) == cur : T}, +hi: {U32.is_lt(i, U32.shln(1, d)) == True{} : Bool}, room2: Laws.Room(d, U32.inc(i), p), +hpos: {U32.is_lt(pos, Laws.addn(i, 1n+p)) == True{} : Bool}, +hpd: {U32.is_lt(pos, U32.shln(1, d)) == True{} : Bool},
  ih: CHIH(~T, p, i, d, m0, b0, pos),
  wm: &m2: Array<U32> -> &w: U32 -> {m2 == m : Array<U32>} & {Array.get(U32, m, i) == (m, w) : Array<U32> & U32} & {w == Laws.rd_at(U32, m, i) : U32})
  -> CHG(~T, 1n+p, i, d, m0, b0, (a2, x), (b2, y), Array.get(U32, m, i), pos, cur):
  (m2, +w, +em2, e1, ew) = wm
  %Equal.sym(Array<U32> & U32, Array.get(U32, m, i), (m, w), e1) : CHG(~T, 1n+p, i, d, m0, b0, (a2, x), (b2, y), _, pos, cur)
  %em2 : CHG(~T, 1n+p, i, d, m0, b0, (a2, x), (b2, y), (_, w), pos, cur)
  ch_step4(~T, p, i, d, m0, b0, a2, b2, m2, eb3, Equal.trans(Array<U32>, m2, m, m0, em2, em), pos, cur, x, y, w, ex, ey, Equal.trans(U32, w, Laws.rd_at(U32, m, i), Laws.rd_at(U32, m0, i), ew, Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, i), m, m0, em)), hcur, hi, room2, hpos, hpd, ih, PC.set_other_w(T, d, a2, i, Bool.pick(T, U32.is_ne(w, 0), x, y), wf))

# b's cell read
def ch_step2(~T: Data, +p: Nat, +i: U32, +d: Nat, -m0: Array<U32>, -b0: Array<T>, a2: Array<T>, -b: Array<T>, m: Array<U32>, +eb: {b == b0 : Array<T>}, +em: {m == m0 : Array<U32>}, wf: Laws.WFArray(T, d, a2), +pos: U32, +cur: T, +x: T, +ex: {x == Laws.rd_at(T, a2, i) : T}, +hcur: {Laws.rdN(T, d, a2, pos) == cur : T}, +hi: {U32.is_lt(i, U32.shln(1, d)) == True{} : Bool}, room2: Laws.Room(d, U32.inc(i), p), +hpos: {U32.is_lt(pos, Laws.addn(i, 1n+p)) == True{} : Bool}, +hpd: {U32.is_lt(pos, U32.shln(1, d)) == True{} : Bool},
  ih: CHIH(~T, p, i, d, m0, b0, pos),
  wb: &b2: Array<T> -> &y: T -> {b2 == b : Array<T>} & {Array.get(T, b, i) == (b, y) : Array<T> & T} & {y == Laws.rd_at(T, b, i) : T})
  -> CHG(~T, 1n+p, i, d, m0, b0, (a2, x), Array.get(T, b, i), Array.get(U32, m, i), pos, cur):
  (b2, +y, +eb2, e1, ey) = wb
  %Equal.sym(Array<T> & T, Array.get(T, b, i), (b, y), e1) : CHG(~T, 1n+p, i, d, m0, b0, (a2, x), _, Array.get(U32, m, i), pos, cur)
  %eb2 : CHG(~T, 1n+p, i, d, m0, b0, (a2, x), (_, y), Array.get(U32, m, i), pos, cur)
  ch_step3(~T, p, i, d, m0, b0, a2, b2, m, Equal.trans(Array<T>, b2, b, b0, eb2, eb), em, wf, pos, cur, x, y, ex, Equal.trans(T, y, Laws.rd_at(T, b, i), Laws.rd_at(T, b0, i), ey, Equal.cong(Array<T>, T, q => Laws.rd_at(T, q, i), b, b0, eb)), hcur, hi, room2, hpos, hpd, ih, PC.get_w(U32, m, i))

# a's cell read
def ch_step1(~T: Data, +p: Nat, +i: U32, +d: Nat, -m0: Array<U32>, -b0: Array<T>, -a: Array<T>, b: Array<T>, m: Array<U32>, +eb: {b == b0 : Array<T>}, +em: {m == m0 : Array<U32>}, wf: Laws.WFArray(T, d, a), +pos: U32, +cur: T, +hcur: {Laws.rdN(T, d, a, pos) == cur : T}, room: Laws.Room(d, i, 1n+p), +hpos: {U32.is_lt(pos, Laws.addn(i, 1n+p)) == True{} : Bool}, +hpd: {U32.is_lt(pos, U32.shln(1, d)) == True{} : Bool},
  ih: CHIH(~T, p, i, d, m0, b0, pos),
  wa: &a3: Array<T> -> &x: T -> {a3 == a : Array<T>} & {Array.get(T, a, i) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, i) : T})
  -> CHG(~T, 1n+p, i, d, m0, b0, Array.get(T, a, i), Array.get(T, b, i), Array.get(U32, m, i), pos, cur):
  (+hi, room2) = room
  (a2, +x, +ea, e1, ex) = wa
  %Equal.sym(Array<T> & T, Array.get(T, a, i), (a, x), e1) : CHG(~T, 1n+p, i, d, m0, b0, _, Array.get(T, b, i), Array.get(U32, m, i), pos, cur)
  %ea : CHG(~T, 1n+p, i, d, m0, b0, (_, x), Array.get(T, b, i), Array.get(U32, m, i), pos, cur)
  ch_step2(~T, p, i, d, m0, b0, a2, b, m, eb, em, (%Equal.sym(Array<T>, a2, a, ea) : Laws.WFArray(T, d, _); wf), pos, cur, x, Equal.trans(T, x, Laws.rd_at(T, a, i), Laws.rd_at(T, a2, i), ex, Equal.cong(Array<T>, T, q => Laws.rd_at(T, q, i), a, a2, Equal.sym(Array<T>, a2, a, ea))), Equal.trans(T, Laws.rdN(T, d, a2, pos), Laws.rdN(T, d, a, pos), cur, Equal.cong(Array<T>, T, q => Laws.rdN(T, d, q, pos), a2, a, ea), hcur), hi, room2, hpos, hpd, ih, PC.get_w(T, b, i))

# no step left: the array as it is (pos is behind the loop)
def ch_zero3(~T: Data, +i: U32, +d: Nat, -m0: Array<U32>, -b0: Array<T>, -a: Array<T>, a2: Array<T>, -b: Array<T>, +y: T, -m: Array<U32>, +em: {m == m0 : Array<U32>}, +ea: {a2 == a : Array<T>}, +x: T, wf: Laws.WFArray(T, d, a), +pos: U32, +cur: T, +hcur: {Laws.rdN(T, d, a, pos) == cur : T}, +hpos: {U32.is_lt(pos, i) == True{} : Bool},
  wm: &m2: Array<U32> -> &w: U32 -> {m2 == m : Array<U32>} & {Array.get(U32, m, i) == (m, w) : Array<U32> & U32} & {w == Laws.rd_at(U32, m, i) : U32})
  -> CHG(~T, 0n, i, d, m0, b0, (a, x), (b, y), Array.get(U32, m, i), pos, cur):
  (m2, +w, +em2, e1, ew) = wm
  %Equal.sym(Array<U32> & U32, Array.get(U32, m, i), (m, w), e1) : CHG(~T, 0n, i, d, m0, b0, (a, x), (b, y), _, pos, cur)
  %ea : CHG(~T, 0n, i, d, m0, b0, (_, x), (b, y), (m, w), pos, cur)
  %em2 : CHG(~T, 0n, i, d, m0, b0, (a2, x), (b, y), (_, w), pos, cur)
  (m2, a2, {==}, Equal.trans(Array<U32>, m2, m, m0, em2, em), (%Equal.sym(Array<T>, a2, a, ea) : Laws.WFArray(T, d, _); wf), (%Equal.sym(Bool, U32.is_lt(pos, i), True{}, hpos) : {Laws.rdN(T, d, a2, pos) == Bool.pick(T, _, cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m0, pos), 0), cur, Laws.rd_at(T, b0, pos))) : T}; %Equal.sym(Array<T>, a2, a, ea) : {Laws.rdN(T, d, _, pos) == cur : T}; hcur))

def ch_zero2(~T: Data, +i: U32, +d: Nat, -m0: Array<U32>, -b0: Array<T>, -a: Array<T>, a2: Array<T>, -b: Array<T>, m: Array<U32>, +em: {m == m0 : Array<U32>}, +ea: {a2 == a : Array<T>}, +x: T, wf: Laws.WFArray(T, d, a), +pos: U32, +cur: T, +hcur: {Laws.rdN(T, d, a, pos) == cur : T}, +hpos: {U32.is_lt(pos, i) == True{} : Bool},
  wb: &b2: Array<T> -> &y: T -> {b2 == b : Array<T>} & {Array.get(T, b, i) == (b, y) : Array<T> & T} & {y == Laws.rd_at(T, b, i) : T})
  -> CHG(~T, 0n, i, d, m0, b0, (a, x), Array.get(T, b, i), Array.get(U32, m, i), pos, cur):
  (b2, +y, eb2, e1, ey) = wb
  %Equal.sym(Array<T> & T, Array.get(T, b, i), (b, y), e1) : CHG(~T, 0n, i, d, m0, b0, (a, x), _, Array.get(U32, m, i), pos, cur)
  ch_zero3(~T, i, d, m0, b0, a, a2, b, y, m, em, ea, x, wf, pos, cur, hcur, hpos, PC.get_w(U32, m, i))

def ch_zero(~T: Data, +i: U32, +d: Nat, -m0: Array<U32>, -b0: Array<T>, -a: Array<T>, b: Array<T>, m: Array<U32>, +em: {m == m0 : Array<U32>}, wf: Laws.WFArray(T, d, a), +pos: U32, +cur: T, +hcur: {Laws.rdN(T, d, a, pos) == cur : T}, +hpos: {U32.is_lt(pos, i) == True{} : Bool},
  wa: &a3: Array<T> -> &x: T -> {a3 == a : Array<T>} & {Array.get(T, a, i) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, i) : T})
  -> CHG(~T, 0n, i, d, m0, b0, Array.get(T, a, i), Array.get(T, b, i), Array.get(U32, m, i), pos, cur):
  (a2, +x, +ea, e1, ex) = wa
  %Equal.sym(Array<T> & T, Array.get(T, a, i), (a, x), e1) : CHG(~T, 0n, i, d, m0, b0, _, Array.get(T, b, i), Array.get(U32, m, i), pos, cur)
  ch_zero2(~T, i, d, m0, b0, a, a2, b, m, em, ea, x, wf, pos, cur, hcur, hpos, PC.get_w(T, b, i))

# Kernel.choose.go with f steps left at counter i (a well formed, its cell at pos cur; b, m copies of
# b0, m0; the next f write indices below 2^d; pos below addn(i, f) and below 2^d)
def ch_go(~T: Data, f: Nat, +i: U32, +d: Nat, -m0: Array<U32>, -b0: Array<T>, a: Array<T>, b: Array<T>, m: Array<U32>, +eb: {b == b0 : Array<T>}, +em: {m == m0 : Array<U32>}, wf: Laws.WFArray(T, d, a), +pos: U32, +cur: T, +hcur: {Laws.rdN(T, d, a, pos) == cur : T}, room: Laws.Room(d, i, f), +hpos: {U32.is_lt(pos, Laws.addn(i, f)) == True{} : Bool}, +hpd: {U32.is_lt(pos, U32.shln(1, d)) == True{} : Bool})
  -> CHG(~T, f, i, d, m0, b0, Array.get(T, a, i), Array.get(T, b, i), Array.get(U32, m, i), pos, cur):
  match f:
    case 0n:
      ch_zero(~T, i, d, m0, b0, a, b, m, em, wf, pos, cur, hcur, hpos, PC.get_w(T, a, i))
    case 1n++p:
      ch_step1(~T, p, i, d, m0, b0, a, b, m, eb, em, wf, pos, cur, hcur, room, hpos, hpd, a3 => b3 => m3 => eb3 => em3 => wf3 => cur2 => hcur2 => room2 => hpos2 => hpd2 => ch_go(~T, p, U32.inc(i), d, m0, b0, a3, b3, m3, eb3, em3, wf3, pos, cur2, hcur2, room2, hpos2, hpd2), PC.get_w(T, a, i))

# ---- Kernel.choose(n, m, a, b): the cell at pos < n (template; the law is the U32 instance) --------------

def CHW(~T: Data, +n: U32, +d: Nat, -m: Array<U32>, -a: Array<T>, -b: Array<T>, +pos: U32) -> Type:
  &mb: Array<U32> -> &o: Array<T> -> {K.Kernel.choose(~T, n, m, a, b) == (mb, o) : Array<U32> & Array<T>} & {mb == m : Array<U32>} & Laws.WFArray(T, d, o) & {Laws.rdN(T, d, o, pos) == Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m, pos), 0), Laws.rd_at(T, a, pos), Laws.rd_at(T, b, pos)) : T}

def ch_fin(~T: Data, +n: U32, +d: Nat, -m: Array<U32>, -a: Array<T>, -b: Array<T>, +pos: U32, +cur: T, +ecur: {cur == Laws.rd_at(T, a, pos) : T},
  w: CHG(~T, U32.to_nat(n), 0, d, m, b, Array.get(T, a, 0), Array.get(T, b, 0), Array.get(U32, m, 0), pos, cur)) -> CHW(~T, n, d, m, a, b, pos):
  (mb, o, eq, emb, wo, cell) = w
  (mb, o, eq, emb, wo, Equal.trans(T, Laws.rdN(T, d, o, pos), Bool.pick(T, U32.is_lt(pos, 0), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m, pos), 0), cur, Laws.rd_at(T, b, pos))), Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m, pos), 0), Laws.rd_at(T, a, pos), Laws.rd_at(T, b, pos)), cell, (%ecur : {Bool.pick(T, U32.is_lt(pos, 0), cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m, pos), 0), cur, Laws.rd_at(T, b, pos))) == Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m, pos), 0), _, Laws.rd_at(T, b, pos)) : T}; %Equal.sym(Bool, U32.is_lt(pos, 0), False{}, lt0_false(pos)) : {Bool.pick(T, _, cur, Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m, pos), 0), cur, Laws.rd_at(T, b, pos))) == Bool.pick(T, U32.is_ne(Laws.rd_at(U32, m, pos), 0), cur, Laws.rd_at(T, b, pos)) : T}; {==})))

def ch_cur3(~T: Data, +n: U32, +d: Nat, -m: Array<U32>, -a: Array<T>, -a2: Array<T>, a3: Array<T>, b: Array<T>, m2: Array<U32>, +em2: {m2 == m : Array<U32>}, +pos: U32, +ea: {a2 == a : Array<T>}, +ea3: {a3 == a2 : Array<T>}, +x: T, +ex: {x == Laws.rd_at(T, a2, pos) : T}, wf2: Laws.WFArray(T, d, a2), cv: @k: U32 -> {Laws.rd_at(T, a, k) == Laws.rdN(T, d, a, k) : T}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hpos: {U32.is_lt(pos, n) == True{} : Bool})
  -> CHW(~T, n, d, m, a2, b, pos):
  %ea3 : CHW(~T, n, d, m, _, b, pos)
  %em2 : CHW(~T, n, d, _, a3, b, pos)
  ch_fin(~T, n, d, m2, a3, b, pos, x, Equal.trans(T, x, Laws.rd_at(T, a2, pos), Laws.rd_at(T, a3, pos), ex, Equal.cong(Array<T>, T, q => Laws.rd_at(T, q, pos), a2, a3, Equal.sym(Array<T>, a3, a2, ea3))), ch_go(~T, U32.to_nat(n), 0, d, m2, b, a3, b, m2, {==}, {==}, (%Equal.sym(Array<T>, a3, a2, ea3) : Laws.WFArray(T, d, _); wf2), pos, x, Equal.trans(T, Laws.rdN(T, d, a3, pos), Laws.rdN(T, d, a, pos), x, Equal.cong(Array<T>, T, q => Laws.rdN(T, d, q, pos), a3, a, Equal.trans(Array<T>, a3, a2, a, ea3, ea)), Equal.trans(T, Laws.rdN(T, d, a, pos), Laws.rd_at(T, a, pos), x, Equal.sym(T, Laws.rd_at(T, a, pos), Laws.rdN(T, d, a, pos), cv(pos)), Equal.trans(T, Laws.rd_at(T, a, pos), Laws.rd_at(T, a2, pos), x, Equal.cong(Array<T>, T, q => Laws.rd_at(T, q, pos), a, a2, Equal.sym(Array<T>, a2, a, ea)), Equal.sym(T, x, Laws.rd_at(T, a2, pos), ex)))), B.room_from(d, n, fits), (%Equal.sym(U32, Laws.addn(0, U32.to_nat(n)), n, B.addn_to_nat(n)) : {U32.is_lt(pos, _) == True{} : Bool}; hpos), PST.lt_le_trans_u(pos, n, U32.shln(1, d), hpos, fits)))

def ch_cur2(~T: Data, +n: U32, +d: Nat, -m: Array<U32>, -a: Array<T>, -a2: Array<T>, b: Array<T>, m2: Array<U32>, +em2: {m2 == m : Array<U32>}, +pos: U32, +ea: {a2 == a : Array<T>}, wf2: Laws.WFArray(T, d, a2), cv: @k: U32 -> {Laws.rd_at(T, a, k) == Laws.rdN(T, d, a, k) : T}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hpos: {U32.is_lt(pos, n) == True{} : Bool},
  w: &a3: Array<T> -> &x: T -> {a3 == a2 : Array<T>} & {Array.get(T, a2, pos) == (a2, x) : Array<T> & T} & {x == Laws.rd_at(T, a2, pos) : T})
  -> CHW(~T, n, d, m, a2, b, pos):
  (a3, +x, +ea3, e1, ex) = w
  ch_cur3(~T, n, d, m, a, a2, a3, b, m2, em2, pos, ea, ea3, x, ex, wf2, cv, fits, hpos)

def ch_cur(~T: Data, +n: U32, +d: Nat, -m: Array<U32>, -a: Array<T>, b: Array<T>, m2: Array<U32>, +em2: {m2 == m : Array<U32>}, +pos: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hpos: {U32.is_lt(pos, n) == True{} : Bool},
  w: &a2: Array<T> -> {a2 == a : Array<T>} & Laws.WFArray(T, d, a2) & (@k: U32 -> {Laws.rd_at(T, a, k) == Laws.rdN(T, d, a, k) : T}))
  -> CHW(~T, n, d, m, a, b, pos):
  (a2, +ea, wf2, cv) = w
  %ea : CHW(~T, n, d, m, _, b, pos)
  ch_cur2(~T, n, d, m, a, a2, b, m2, em2, pos, ea, wf2, cv, fits, hpos, PC.get_w(T, a2, pos))

# the mask is cloned once (clone_eq) so that the law's statement keeps the original m in its model
# terms while a copy runs through the kernel
def choose_w2(~T: Data, +n: U32, +d: Nat, -m: Array<U32>, a: Array<T>, b: Array<T>, +pos: U32, wf: Laws.WFArray(T, d, a), +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hpos: {U32.is_lt(pos, n) == True{} : Bool},
  w: &m1: Array<U32> -> &m2: Array<U32> -> {m1 == m : Array<U32>} & {m2 == m : Array<U32>}) -> CHW(~T, n, d, m, a, b, pos):
  (m1, m2, +em1, em2) = w
  ch_cur(~T, n, d, m, a, b, m1, em1, pos, fits, hpos, PST.rd_all(T, d, a, wf))

def choose_w(~T: Data, +n: U32, +d: Nat, m: Array<U32>, a: Array<T>, b: Array<T>, +pos: U32, wf: Laws.WFArray(T, d, a), +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hpos: {U32.is_lt(pos, n) == True{} : Bool}) -> CHW(~T, n, d, m, a, b, pos):
  choose_w2(~T, n, d, m, a, b, pos, wf, fits, hpos, PC.clone_eq(U32, m))

# ---- Kernel.choose hands the mask back ---------------------------------------------------------------------

def CHM(~T: Data, f: Nat, +i: U32, -ra: Array<T> & T, -rb: Array<T> & T, -m: Array<U32>) -> Type:
  {Pair.fst(Array<U32>, Array<T>, K.Kernel.choose.go(~T, f, i, ra, rb, Array.get(U32, m, i))) == m : Array<U32>}

def chm_step3(~T: Data, p: Nat, +i: U32, a2: Array<T>, b2: Array<T>, -m: Array<U32>, +x: T, +y: T,
  ih: @c: Array<T> -> @b3: Array<T> -> @m3: Array<U32> -> CHM(~T, p, U32.inc(i), Array.get(T, c, U32.inc(i)), Array.get(T, b3, U32.inc(i)), m3),
  wm: &m2: Array<U32> -> &w: U32 -> {m2 == m : Array<U32>} & {Array.get(U32, m, i) == (m, w) : Array<U32> & U32} & {w == Laws.rd_at(U32, m, i) : U32})
  -> CHM(~T, 1n+p, i, (a2, x), (b2, y), m):
  (m2, +w, em2, e1, ew) = wm
  %Equal.sym(Array<U32> & U32, Array.get(U32, m, i), (m, w), e1) : {Pair.fst(Array<U32>, Array<T>, K.Kernel.choose.go(~T, 1n+p, i, (a2, x), (b2, y), _)) == m : Array<U32>}
  %em2 : {Pair.fst(Array<U32>, Array<T>, K.Kernel.choose.go(~T, 1n+p, i, (a2, x), (b2, y), (_, w))) == _ : Array<U32>}
  ih(Array.set(T, a2, i, Bool.pick(T, U32.is_ne(w, 0), x, y)), b2, m2)

def chm_step2(~T: Data, p: Nat, +i: U32, a2: Array<T>, -b: Array<T>, m: Array<U32>, +x: T,
  ih: @c: Array<T> -> @b3: Array<T> -> @m3: Array<U32> -> CHM(~T, p, U32.inc(i), Array.get(T, c, U32.inc(i)), Array.get(T, b3, U32.inc(i)), m3),
  wb: &b2: Array<T> -> &y: T -> {b2 == b : Array<T>} & {Array.get(T, b, i) == (b, y) : Array<T> & T} & {y == Laws.rd_at(T, b, i) : T})
  -> CHM(~T, 1n+p, i, (a2, x), Array.get(T, b, i), m):
  (b2, +y, eb2, e1, ey) = wb
  %Equal.sym(Array<T> & T, Array.get(T, b, i), (b, y), e1) : CHM(~T, 1n+p, i, (a2, x), _, m)
  %eb2 : CHM(~T, 1n+p, i, (a2, x), (_, y), m)
  chm_step3(~T, p, i, a2, b2, m, x, y, ih, PC.get_w(U32, m, i))

def chm_step1(~T: Data, p: Nat, +i: U32, -a: Array<T>, b: Array<T>, m: Array<U32>,
  ih: @c: Array<T> -> @b3: Array<T> -> @m3: Array<U32> -> CHM(~T, p, U32.inc(i), Array.get(T, c, U32.inc(i)), Array.get(T, b3, U32.inc(i)), m3),
  wa: &a3: Array<T> -> &x: T -> {a3 == a : Array<T>} & {Array.get(T, a, i) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, i) : T})
  -> CHM(~T, 1n+p, i, Array.get(T, a, i), Array.get(T, b, i), m):
  (a2, +x, ea, e1, ex) = wa
  %Equal.sym(Array<T> & T, Array.get(T, a, i), (a, x), e1) : CHM(~T, 1n+p, i, _, Array.get(T, b, i), m)
  %ea : CHM(~T, 1n+p, i, (_, x), Array.get(T, b, i), m)
  chm_step2(~T, p, i, a2, b, m, x, ih, PC.get_w(T, b, i))

def chm_zero3(~T: Data, +i: U32, -a: Array<T>, -b: Array<T>, -m: Array<U32>, +x: T, +y: T,
  wm: &m2: Array<U32> -> &w: U32 -> {m2 == m : Array<U32>} & {Array.get(U32, m, i) == (m, w) : Array<U32> & U32} & {w == Laws.rd_at(U32, m, i) : U32})
  -> CHM(~T, 0n, i, (a, x), (b, y), m):
  (m2, +w, em2, e1, ew) = wm
  %Equal.sym(Array<U32> & U32, Array.get(U32, m, i), (m, w), e1) : {Pair.fst(Array<U32>, Array<T>, K.Kernel.choose.go(~T, 0n, i, (a, x), (b, y), _)) == m : Array<U32>}
  {==}

def chm_zero2(~T: Data, +i: U32, -a: Array<T>, -b: Array<T>, m: Array<U32>, +x: T,
  wb: &b2: Array<T> -> &y: T -> {b2 == b : Array<T>} & {Array.get(T, b, i) == (b, y) : Array<T> & T} & {y == Laws.rd_at(T, b, i) : T})
  -> CHM(~T, 0n, i, (a, x), Array.get(T, b, i), m):
  (b2, +y, eb2, e1, ey) = wb
  %Equal.sym(Array<T> & T, Array.get(T, b, i), (b, y), e1) : CHM(~T, 0n, i, (a, x), _, m)
  chm_zero3(~T, i, a, b, m, x, y, PC.get_w(U32, m, i))

def chm_zero(~T: Data, +i: U32, -a: Array<T>, b: Array<T>, m: Array<U32>,
  wa: &a3: Array<T> -> &x: T -> {a3 == a : Array<T>} & {Array.get(T, a, i) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, i) : T})
  -> CHM(~T, 0n, i, Array.get(T, a, i), Array.get(T, b, i), m):
  (a2, +x, ea, e1, ex) = wa
  %Equal.sym(Array<T> & T, Array.get(T, a, i), (a, x), e1) : CHM(~T, 0n, i, _, Array.get(T, b, i), m)
  chm_zero2(~T, i, a, b, m, x, PC.get_w(T, b, i))

def chm_go(~T: Data, f: Nat, +i: U32, a: Array<T>, b: Array<T>, m: Array<U32>) -> CHM(~T, f, i, Array.get(T, a, i), Array.get(T, b, i), m):
  match f:
    case 0n:
      chm_zero(~T, i, a, b, m, PC.get_w(T, a, i))
    case 1n++p:
      chm_step1(~T, p, i, a, b, m, c => b3 => m3 => chm_go(~T, p, U32.inc(i), c, b3, m3), PC.get_w(T, a, i))

# ---- the laws: Kernel.choose at the U32 instance -----------------------------------------------------------

def ch_cell_fin(+n: U32, +d: Nat, -m: Array<U32>, -a: Array<U32>, -b: Array<U32>, +pos: U32, w: CHW(~U32, n, d, m, a, b, pos))
  -> {Laws.rd_at(U32, Pair.snd(Array<U32>, Array<U32>, K.Kernel.choose(~U32, n, m, a, b)), pos) == Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, pos), 0), Laws.rd_at(U32, a, pos), Laws.rd_at(U32, b, pos)) : U32}:
  (mb, o, eq, emb, wo, cell) = w
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.choose(~U32, n, m, a, b), (mb, o), eq) : {Laws.rd_at(U32, Pair.snd(Array<U32>, Array<U32>, _), pos) == Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, pos), 0), Laws.rd_at(U32, a, pos), Laws.rd_at(U32, b, pos)) : U32}
  %Equal.sym(U32, Laws.rd_at(U32, o, pos), Laws.rdN(U32, d, o, pos), Laws.rd_at_wf(U32, d, o, pos, wo)) : {_ == Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, pos), 0), Laws.rd_at(U32, a, pos), Laws.rd_at(U32, b, pos)) : U32}
  cell

def Laws.choose_cell(n, d, m, a, b, pos, wf, fits, hpos):
  ch_cell_fin(n, d, m, a, b, pos, choose_w(~U32, n, d, m, a, b, pos, wf, fits, hpos))

def Laws.choose_keeps_mask(n, m, a, b):
  chm_go(~U32, U32.to_nat(n), 0, a, b, m)

# ---- Laws.fix_cell: Eval.fix keeps every cell -----------------------------------------------------------
#
# With a mask, Eval.fix runs Kernel.mask_data over the data (mask_data_w: the mask back, the data's
# cell at i the old one where the mask word is set and the default where it is 0). The mask word at
# i is read off the returned mask (get_w) as a Data word w, both sides' tests become is_ne(w, 0),
# and a case split on it closes the pick algebra: set, the data cell is the old one; 0, both null.

def fix_pick_bool(b: Bool, +w: U32, -x: Array<U32>, +i: U32, +eb: {U32.is_ne(w, 0) == b : Bool}) -> {Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SBool{U32.is_ne(Bool.pick(U32, U32.is_ne(w, 0), Laws.rd_at(U32, x, i), 0), 0)}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SBool{U32.is_ne(Laws.rd_at(U32, x, i), 0)}, D.SNull{}) : D.Scalar}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_ne(w, 0), True{}, eb) : {Bool.pick(D.Scalar, _, D.SBool{U32.is_ne(Bool.pick(U32, _, Laws.rd_at(U32, x, i), 0), 0)}, D.SNull{}) == Bool.pick(D.Scalar, _, D.SBool{U32.is_ne(Laws.rd_at(U32, x, i), 0)}, D.SNull{}) : D.Scalar}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_ne(w, 0), False{}, eb) : {Bool.pick(D.Scalar, _, D.SBool{U32.is_ne(Bool.pick(U32, _, Laws.rd_at(U32, x, i), 0), 0)}, D.SNull{}) == Bool.pick(D.Scalar, _, D.SBool{U32.is_ne(Laws.rd_at(U32, x, i), 0)}, D.SNull{}) : D.Scalar}
      {==}

def fix_pick_u32(b: Bool, +w: U32, -x: Array<U32>, +i: U32, +eb: {U32.is_ne(w, 0) == b : Bool}) -> {Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SU32{Bool.pick(U32, U32.is_ne(w, 0), Laws.rd_at(U32, x, i), 0)}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SU32{Laws.rd_at(U32, x, i)}, D.SNull{}) : D.Scalar}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_ne(w, 0), True{}, eb) : {Bool.pick(D.Scalar, _, D.SU32{Bool.pick(U32, _, Laws.rd_at(U32, x, i), 0)}, D.SNull{}) == Bool.pick(D.Scalar, _, D.SU32{Laws.rd_at(U32, x, i)}, D.SNull{}) : D.Scalar}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_ne(w, 0), False{}, eb) : {Bool.pick(D.Scalar, _, D.SU32{Bool.pick(U32, _, Laws.rd_at(U32, x, i), 0)}, D.SNull{}) == Bool.pick(D.Scalar, _, D.SU32{Laws.rd_at(U32, x, i)}, D.SNull{}) : D.Scalar}
      {==}

def fix_pick_i32(b: Bool, +w: U32, -x: Array<U32>, +i: U32, +eb: {U32.is_ne(w, 0) == b : Bool}) -> {Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SI32{D.I32{Bool.pick(U32, U32.is_ne(w, 0), Laws.rd_at(U32, x, i), 0)}}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SI32{D.I32{Laws.rd_at(U32, x, i)}}, D.SNull{}) : D.Scalar}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_ne(w, 0), True{}, eb) : {Bool.pick(D.Scalar, _, D.SI32{D.I32{Bool.pick(U32, _, Laws.rd_at(U32, x, i), 0)}}, D.SNull{}) == Bool.pick(D.Scalar, _, D.SI32{D.I32{Laws.rd_at(U32, x, i)}}, D.SNull{}) : D.Scalar}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_ne(w, 0), False{}, eb) : {Bool.pick(D.Scalar, _, D.SI32{D.I32{Bool.pick(U32, _, Laws.rd_at(U32, x, i), 0)}}, D.SNull{}) == Bool.pick(D.Scalar, _, D.SI32{D.I32{Laws.rd_at(U32, x, i)}}, D.SNull{}) : D.Scalar}
      {==}

def fix_pick_f32(b: Bool, +w: U32, -x: Array<F32>, +i: U32, +eb: {U32.is_ne(w, 0) == b : Bool}) -> {Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SF32{Bool.pick(F32, U32.is_ne(w, 0), Laws.rd_at(F32, x, i), 0.0)}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SF32{Laws.rd_at(F32, x, i)}, D.SNull{}) : D.Scalar}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_ne(w, 0), True{}, eb) : {Bool.pick(D.Scalar, _, D.SF32{Bool.pick(F32, _, Laws.rd_at(F32, x, i), 0.0)}, D.SNull{}) == Bool.pick(D.Scalar, _, D.SF32{Laws.rd_at(F32, x, i)}, D.SNull{}) : D.Scalar}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_ne(w, 0), False{}, eb) : {Bool.pick(D.Scalar, _, D.SF32{Bool.pick(F32, _, Laws.rd_at(F32, x, i), 0.0)}, D.SNull{}) == Bool.pick(D.Scalar, _, D.SF32{Laws.rd_at(F32, x, i)}, D.SNull{}) : D.Scalar}
      {==}

def fix_pick_raw(b: Bool, +w: U32, -x: Array<String>, +i: U32, +eb: {U32.is_ne(w, 0) == b : Bool}) -> {Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SStr{Bool.pick(String, U32.is_ne(w, 0), Laws.rd_at(String, x, i), "")}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SStr{Laws.rd_at(String, x, i)}, D.SNull{}) : D.Scalar}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_ne(w, 0), True{}, eb) : {Bool.pick(D.Scalar, _, D.SStr{Bool.pick(String, _, Laws.rd_at(String, x, i), "")}, D.SNull{}) == Bool.pick(D.Scalar, _, D.SStr{Laws.rd_at(String, x, i)}, D.SNull{}) : D.Scalar}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_ne(w, 0), False{}, eb) : {Bool.pick(D.Scalar, _, D.SStr{Bool.pick(String, _, Laws.rd_at(String, x, i), "")}, D.SNull{}) == Bool.pick(D.Scalar, _, D.SStr{Laws.rd_at(String, x, i)}, D.SNull{}) : D.Scalar}
      {==}

def fix_pick_dict(b: Bool, +w: U32, -x: Array<U32>, -dict: ST.Dict, +i: U32, +eb: {U32.is_ne(w, 0) == b : Bool}) -> {Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SStr{Laws.dentry(dict, Bool.pick(U32, U32.is_ne(w, 0), Laws.rd_at(U32, x, i), 0))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SStr{Laws.dentry(dict, Laws.rd_at(U32, x, i))}, D.SNull{}) : D.Scalar}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_ne(w, 0), True{}, eb) : {Bool.pick(D.Scalar, _, D.SStr{Laws.dentry(dict, Bool.pick(U32, _, Laws.rd_at(U32, x, i), 0))}, D.SNull{}) == Bool.pick(D.Scalar, _, D.SStr{Laws.dentry(dict, Laws.rd_at(U32, x, i))}, D.SNull{}) : D.Scalar}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_ne(w, 0), False{}, eb) : {Bool.pick(D.Scalar, _, D.SStr{Laws.dentry(dict, Bool.pick(U32, _, Laws.rd_at(U32, x, i), 0))}, D.SNull{}) == Bool.pick(D.Scalar, _, D.SStr{Laws.dentry(dict, Laws.rd_at(U32, x, i))}, D.SNull{}) : D.Scalar}
      {==}

# the mask word at i read off the returned mask mb (== m): w with w == rd_at(m, i)
def MaskRead(-m: Array<U32>, -mb: Array<U32>, +i: U32) -> Type:
  &mb2: Array<U32> -> &w: U32 -> {mb2 == mb : Array<U32>} & {w == Laws.rd_at(U32, m, i) : U32} & {w == Laws.rd_at(U32, mb2, i) : U32}

def mask_read_j(-m: Array<U32>, -mb: Array<U32>, +i: U32, +emb: {mb == m : Array<U32>}, mb2: Array<U32>, +w: U32, +emb2: {mb2 == mb : Array<U32>}, +ew: {w == Laws.rd_at(U32, mb, i) : U32}) -> MaskRead(m, mb, i):
  (mb2, w, emb2, Equal.trans(U32, w, Laws.rd_at(U32, mb, i), Laws.rd_at(U32, m, i), ew, Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, i), mb, m, emb)), Equal.trans(U32, w, Laws.rd_at(U32, mb, i), Laws.rd_at(U32, mb2, i), ew, Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, i), mb, mb2, Equal.sym(Array<U32>, mb2, mb, emb2))))

def mask_read_k(-m: Array<U32>, -mb: Array<U32>, +i: U32, +emb: {mb == m : Array<U32>}, w: &mb2: Array<U32> -> &w: U32 -> {mb2 == mb : Array<U32>} & {Array.get(U32, mb, i) == (mb, w) : Array<U32> & U32} & {w == Laws.rd_at(U32, mb, i) : U32}) -> MaskRead(m, mb, i):
  (mb2, +w, +emb2, e1, ew) = w
  mask_read_j(m, mb, i, emb, mb2, w, emb2, ew)

def mask_read(-m: Array<U32>, mb: Array<U32>, +i: U32, +emb: {mb == m : Array<U32>}) -> MaskRead(m, mb, i):
  mask_read_k(m, mb, i, emb, PC.get_w(U32, mb, i))

# ---- the word columns (Bool / U32 / I32: Eval.fix.w over Column.mk_w) --------------------------------------

def fixc_bool_k(+n: U32, +d: Nat, -m: Array<U32>, -x: Array<U32>, +i: U32, o: Array<U32>, -mb: Array<U32>, wo: Laws.WFArray(U32, d, o), +cell: {Laws.rdN(U32, d, o, i) == Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, i), 0), Laws.rd_at(U32, x, i), 0) : U32}, w: MaskRead(m, mb, i))
  -> {Laws.ccell(C.CBool{n, d, C.Mask{mb}, o}, i) == Laws.ccell(C.CBool{n, d, C.Mask{m}, x}, i) : D.Scalar}:
  (mb2, +w, +emb2, +ewm, ew2) = w
  %emb2 : {Laws.ccell(C.CBool{n, d, C.Mask{_}, o}, i) == Laws.ccell(C.CBool{n, d, C.Mask{m}, x}, i) : D.Scalar}
  %Equal.sym(U32, Laws.rd_at(U32, o, i), Laws.rdN(U32, d, o, i), Laws.rd_at_wf(U32, d, o, i, wo)) : {Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mb2, i), 0), D.SBool{U32.is_ne(_, 0)}, D.SNull{}) == Laws.ccell(C.CBool{n, d, C.Mask{m}, x}, i) : D.Scalar}
  %Equal.sym(U32, Laws.rdN(U32, d, o, i), Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, i), 0), Laws.rd_at(U32, x, i), 0), cell) : {Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mb2, i), 0), D.SBool{U32.is_ne(_, 0)}, D.SNull{}) == Laws.ccell(C.CBool{n, d, C.Mask{m}, x}, i) : D.Scalar}
  %ew2 : {Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SBool{U32.is_ne(Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, i), 0), Laws.rd_at(U32, x, i), 0), 0)}, D.SNull{}) == Laws.ccell(C.CBool{n, d, C.Mask{m}, x}, i) : D.Scalar}
  %ewm : {Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SBool{U32.is_ne(Bool.pick(U32, U32.is_ne(_, 0), Laws.rd_at(U32, x, i), 0), 0)}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SBool{U32.is_ne(Laws.rd_at(U32, x, i), 0)}, D.SNull{}) : D.Scalar}
  fix_pick_bool(U32.is_ne(w, 0), w, x, i, {==})

def fixc_bool(+n: U32, +d: Nat, -m: Array<U32>, -x: Array<U32>, +i: U32, w: MDW(~U32, n, d, x, m, 0, i)) -> {Laws.ccell(V.Eval.fix.w2(D.TBool{}, n, d, K.Kernel.mask_data(~U32, n, x, m, 0)), i) == Laws.ccell(C.CBool{n, d, C.Mask{m}, x}, i) : D.Scalar}:
  (o, mb, eq, +emb, wo, cell) = w
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.mask_data(~U32, n, x, m, 0), (o, mb), eq) : {Laws.ccell(V.Eval.fix.w2(D.TBool{}, n, d, _), i) == Laws.ccell(C.CBool{n, d, C.Mask{m}, x}, i) : D.Scalar}
  fixc_bool_k(n, d, m, x, i, o, mb, wo, cell, mask_read(m, mb, i, emb))

def fixc_u32_k(+n: U32, +d: Nat, -m: Array<U32>, -x: Array<U32>, +i: U32, o: Array<U32>, -mb: Array<U32>, wo: Laws.WFArray(U32, d, o), +cell: {Laws.rdN(U32, d, o, i) == Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, i), 0), Laws.rd_at(U32, x, i), 0) : U32}, w: MaskRead(m, mb, i))
  -> {Laws.ccell(C.CU32{n, d, C.Mask{mb}, o}, i) == Laws.ccell(C.CU32{n, d, C.Mask{m}, x}, i) : D.Scalar}:
  (mb2, +w, +emb2, +ewm, ew2) = w
  %emb2 : {Laws.ccell(C.CU32{n, d, C.Mask{_}, o}, i) == Laws.ccell(C.CU32{n, d, C.Mask{m}, x}, i) : D.Scalar}
  %Equal.sym(U32, Laws.rd_at(U32, o, i), Laws.rdN(U32, d, o, i), Laws.rd_at_wf(U32, d, o, i, wo)) : {Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mb2, i), 0), D.SU32{_}, D.SNull{}) == Laws.ccell(C.CU32{n, d, C.Mask{m}, x}, i) : D.Scalar}
  %Equal.sym(U32, Laws.rdN(U32, d, o, i), Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, i), 0), Laws.rd_at(U32, x, i), 0), cell) : {Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mb2, i), 0), D.SU32{_}, D.SNull{}) == Laws.ccell(C.CU32{n, d, C.Mask{m}, x}, i) : D.Scalar}
  %ew2 : {Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SU32{Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, i), 0), Laws.rd_at(U32, x, i), 0)}, D.SNull{}) == Laws.ccell(C.CU32{n, d, C.Mask{m}, x}, i) : D.Scalar}
  %ewm : {Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SU32{Bool.pick(U32, U32.is_ne(_, 0), Laws.rd_at(U32, x, i), 0)}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SU32{Laws.rd_at(U32, x, i)}, D.SNull{}) : D.Scalar}
  fix_pick_u32(U32.is_ne(w, 0), w, x, i, {==})

def fixc_u32(+n: U32, +d: Nat, -m: Array<U32>, -x: Array<U32>, +i: U32, w: MDW(~U32, n, d, x, m, 0, i)) -> {Laws.ccell(V.Eval.fix.w2(D.TU32{}, n, d, K.Kernel.mask_data(~U32, n, x, m, 0)), i) == Laws.ccell(C.CU32{n, d, C.Mask{m}, x}, i) : D.Scalar}:
  (o, mb, eq, +emb, wo, cell) = w
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.mask_data(~U32, n, x, m, 0), (o, mb), eq) : {Laws.ccell(V.Eval.fix.w2(D.TU32{}, n, d, _), i) == Laws.ccell(C.CU32{n, d, C.Mask{m}, x}, i) : D.Scalar}
  fixc_u32_k(n, d, m, x, i, o, mb, wo, cell, mask_read(m, mb, i, emb))

def fixc_i32_k(+n: U32, +d: Nat, -m: Array<U32>, -x: Array<U32>, +i: U32, o: Array<U32>, -mb: Array<U32>, wo: Laws.WFArray(U32, d, o), +cell: {Laws.rdN(U32, d, o, i) == Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, i), 0), Laws.rd_at(U32, x, i), 0) : U32}, w: MaskRead(m, mb, i))
  -> {Laws.ccell(C.CI32{n, d, C.Mask{mb}, o}, i) == Laws.ccell(C.CI32{n, d, C.Mask{m}, x}, i) : D.Scalar}:
  (mb2, +w, +emb2, +ewm, ew2) = w
  %emb2 : {Laws.ccell(C.CI32{n, d, C.Mask{_}, o}, i) == Laws.ccell(C.CI32{n, d, C.Mask{m}, x}, i) : D.Scalar}
  %Equal.sym(U32, Laws.rd_at(U32, o, i), Laws.rdN(U32, d, o, i), Laws.rd_at_wf(U32, d, o, i, wo)) : {Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mb2, i), 0), D.SI32{D.I32{_}}, D.SNull{}) == Laws.ccell(C.CI32{n, d, C.Mask{m}, x}, i) : D.Scalar}
  %Equal.sym(U32, Laws.rdN(U32, d, o, i), Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, i), 0), Laws.rd_at(U32, x, i), 0), cell) : {Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mb2, i), 0), D.SI32{D.I32{_}}, D.SNull{}) == Laws.ccell(C.CI32{n, d, C.Mask{m}, x}, i) : D.Scalar}
  %ew2 : {Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SI32{D.I32{Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, i), 0), Laws.rd_at(U32, x, i), 0)}}, D.SNull{}) == Laws.ccell(C.CI32{n, d, C.Mask{m}, x}, i) : D.Scalar}
  %ewm : {Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SI32{D.I32{Bool.pick(U32, U32.is_ne(_, 0), Laws.rd_at(U32, x, i), 0)}}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SI32{D.I32{Laws.rd_at(U32, x, i)}}, D.SNull{}) : D.Scalar}
  fix_pick_i32(U32.is_ne(w, 0), w, x, i, {==})

def fixc_i32(+n: U32, +d: Nat, -m: Array<U32>, -x: Array<U32>, +i: U32, w: MDW(~U32, n, d, x, m, 0, i)) -> {Laws.ccell(V.Eval.fix.w2(D.TI32{}, n, d, K.Kernel.mask_data(~U32, n, x, m, 0)), i) == Laws.ccell(C.CI32{n, d, C.Mask{m}, x}, i) : D.Scalar}:
  (o, mb, eq, +emb, wo, cell) = w
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.mask_data(~U32, n, x, m, 0), (o, mb), eq) : {Laws.ccell(V.Eval.fix.w2(D.TI32{}, n, d, _), i) == Laws.ccell(C.CI32{n, d, C.Mask{m}, x}, i) : D.Scalar}
  fixc_i32_k(n, d, m, x, i, o, mb, wo, cell, mask_read(m, mb, i, emb))

# ---- F32 (Eval.fix.f / .f2) ------------------------------------------------------------------------------------

def fixc_f32_k(+n: U32, +d: Nat, -m: Array<U32>, -x: Array<F32>, +i: U32, o: Array<F32>, -mb: Array<U32>, wo: Laws.WFArray(F32, d, o), +cell: {Laws.rdN(F32, d, o, i) == Bool.pick(F32, U32.is_ne(Laws.rd_at(U32, m, i), 0), Laws.rd_at(F32, x, i), 0.0) : F32}, w: MaskRead(m, mb, i))
  -> {Laws.ccell(C.CF32{n, d, C.Mask{mb}, o}, i) == Laws.ccell(C.CF32{n, d, C.Mask{m}, x}, i) : D.Scalar}:
  (mb2, +w, +emb2, +ewm, ew2) = w
  %emb2 : {Laws.ccell(C.CF32{n, d, C.Mask{_}, o}, i) == Laws.ccell(C.CF32{n, d, C.Mask{m}, x}, i) : D.Scalar}
  %Equal.sym(F32, Laws.rd_at(F32, o, i), Laws.rdN(F32, d, o, i), Laws.rd_at_wf(F32, d, o, i, wo)) : {Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mb2, i), 0), D.SF32{_}, D.SNull{}) == Laws.ccell(C.CF32{n, d, C.Mask{m}, x}, i) : D.Scalar}
  %Equal.sym(F32, Laws.rdN(F32, d, o, i), Bool.pick(F32, U32.is_ne(Laws.rd_at(U32, m, i), 0), Laws.rd_at(F32, x, i), 0.0), cell) : {Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mb2, i), 0), D.SF32{_}, D.SNull{}) == Laws.ccell(C.CF32{n, d, C.Mask{m}, x}, i) : D.Scalar}
  %ew2 : {Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SF32{Bool.pick(F32, U32.is_ne(Laws.rd_at(U32, m, i), 0), Laws.rd_at(F32, x, i), 0.0)}, D.SNull{}) == Laws.ccell(C.CF32{n, d, C.Mask{m}, x}, i) : D.Scalar}
  %ewm : {Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SF32{Bool.pick(F32, U32.is_ne(_, 0), Laws.rd_at(F32, x, i), 0.0)}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SF32{Laws.rd_at(F32, x, i)}, D.SNull{}) : D.Scalar}
  fix_pick_f32(U32.is_ne(w, 0), w, x, i, {==})

def fixc_f32(+n: U32, +d: Nat, -m: Array<U32>, -x: Array<F32>, +i: U32, w: MDW(~F32, n, d, x, m, 0.0, i)) -> {Laws.ccell(V.Eval.fix.f2(n, d, K.Kernel.mask_data(~F32, n, x, m, 0.0)), i) == Laws.ccell(C.CF32{n, d, C.Mask{m}, x}, i) : D.Scalar}:
  (o, mb, eq, +emb, wo, cell) = w
  %Equal.sym(Array<F32> & Array<U32>, K.Kernel.mask_data(~F32, n, x, m, 0.0), (o, mb), eq) : {Laws.ccell(V.Eval.fix.f2(n, d, _), i) == Laws.ccell(C.CF32{n, d, C.Mask{m}, x}, i) : D.Scalar}
  fixc_f32_k(n, d, m, x, i, o, mb, wo, cell, mask_read(m, mb, i, emb))

# ---- Str: Eval.fix.s / .s2 over Strs.fix (Raw: the strings; Dictionary: the codes, the dictionary along) ----

def fixc_raw_k(+n: U32, +d: Nat, -m: Array<U32>, -x: Array<String>, +i: U32, o: Array<String>, -mb: Array<U32>, wo: Laws.WFArray(String, d, o), +cell: {Laws.rdN(String, d, o, i) == Bool.pick(String, U32.is_ne(Laws.rd_at(U32, m, i), 0), Laws.rd_at(String, x, i), "") : String}, w: MaskRead(m, mb, i))
  -> {Laws.ccell(C.CStr{n, d, C.Mask{mb}, ST.SRaw{o}}, i) == Laws.ccell(C.CStr{n, d, C.Mask{m}, ST.SRaw{x}}, i) : D.Scalar}:
  (mb2, +w, +emb2, +ewm, ew2) = w
  %emb2 : {Laws.ccell(C.CStr{n, d, C.Mask{_}, ST.SRaw{o}}, i) == Laws.ccell(C.CStr{n, d, C.Mask{m}, ST.SRaw{x}}, i) : D.Scalar}
  %Equal.sym(String, Laws.rd_at(String, o, i), Laws.rdN(String, d, o, i), Laws.rd_at_wf(String, d, o, i, wo)) : {Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mb2, i), 0), D.SStr{_}, D.SNull{}) == Laws.ccell(C.CStr{n, d, C.Mask{m}, ST.SRaw{x}}, i) : D.Scalar}
  %Equal.sym(String, Laws.rdN(String, d, o, i), Bool.pick(String, U32.is_ne(Laws.rd_at(U32, m, i), 0), Laws.rd_at(String, x, i), ""), cell) : {Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mb2, i), 0), D.SStr{_}, D.SNull{}) == Laws.ccell(C.CStr{n, d, C.Mask{m}, ST.SRaw{x}}, i) : D.Scalar}
  %ew2 : {Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Bool.pick(String, U32.is_ne(Laws.rd_at(U32, m, i), 0), Laws.rd_at(String, x, i), "")}, D.SNull{}) == Laws.ccell(C.CStr{n, d, C.Mask{m}, ST.SRaw{x}}, i) : D.Scalar}
  %ewm : {Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SStr{Bool.pick(String, U32.is_ne(_, 0), Laws.rd_at(String, x, i), "")}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.rd_at(String, x, i)}, D.SNull{}) : D.Scalar}
  fix_pick_raw(U32.is_ne(w, 0), w, x, i, {==})

def fixc_raw(+n: U32, +d: Nat, -m: Array<U32>, -x: Array<String>, +i: U32, w: MDW(~String, n, d, x, m, "", i)) -> {Laws.ccell(V.Eval.fix.s2(n, d, ST.Strs.out.r(K.Kernel.mask_data(~String, n, x, m, ""))), i) == Laws.ccell(C.CStr{n, d, C.Mask{m}, ST.SRaw{x}}, i) : D.Scalar}:
  (o, mb, eq, +emb, wo, cell) = w
  %Equal.sym(Array<String> & Array<U32>, K.Kernel.mask_data(~String, n, x, m, ""), (o, mb), eq) : {Laws.ccell(V.Eval.fix.s2(n, d, ST.Strs.out.r(_)), i) == Laws.ccell(C.CStr{n, d, C.Mask{m}, ST.SRaw{x}}, i) : D.Scalar}
  fixc_raw_k(n, d, m, x, i, o, mb, wo, cell, mask_read(m, mb, i, emb))

def fixc_dict_k(+n: U32, +d: Nat, -m: Array<U32>, -x: Array<U32>, dict: ST.Dict, +i: U32, o: Array<U32>, -mb: Array<U32>, wo: Laws.WFArray(U32, d, o), +cell: {Laws.rdN(U32, d, o, i) == Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, i), 0), Laws.rd_at(U32, x, i), 0) : U32}, w: MaskRead(m, mb, i))
  -> {Laws.ccell(C.CStr{n, d, C.Mask{mb}, ST.SDict{o, dict}}, i) == Laws.ccell(C.CStr{n, d, C.Mask{m}, ST.SDict{x, dict}}, i) : D.Scalar}:
  (mb2, +w, +emb2, +ewm, ew2) = w
  %emb2 : {Laws.ccell(C.CStr{n, d, C.Mask{_}, ST.SDict{o, dict}}, i) == Laws.ccell(C.CStr{n, d, C.Mask{m}, ST.SDict{x, dict}}, i) : D.Scalar}
  %Equal.sym(U32, Laws.rd_at(U32, o, i), Laws.rdN(U32, d, o, i), Laws.rd_at_wf(U32, d, o, i, wo)) : {Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mb2, i), 0), D.SStr{Laws.dentry(dict, _)}, D.SNull{}) == Laws.ccell(C.CStr{n, d, C.Mask{m}, ST.SDict{x, dict}}, i) : D.Scalar}
  %Equal.sym(U32, Laws.rdN(U32, d, o, i), Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, i), 0), Laws.rd_at(U32, x, i), 0), cell) : {Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mb2, i), 0), D.SStr{Laws.dentry(dict, _)}, D.SNull{}) == Laws.ccell(C.CStr{n, d, C.Mask{m}, ST.SDict{x, dict}}, i) : D.Scalar}
  %ew2 : {Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.dentry(dict, Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, m, i), 0), Laws.rd_at(U32, x, i), 0))}, D.SNull{}) == Laws.ccell(C.CStr{n, d, C.Mask{m}, ST.SDict{x, dict}}, i) : D.Scalar}
  %ewm : {Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SStr{Laws.dentry(dict, Bool.pick(U32, U32.is_ne(_, 0), Laws.rd_at(U32, x, i), 0))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.dentry(dict, Laws.rd_at(U32, x, i))}, D.SNull{}) : D.Scalar}
  fix_pick_dict(U32.is_ne(w, 0), w, x, dict, i, {==})

def fixc_dict(+n: U32, +d: Nat, -m: Array<U32>, -x: Array<U32>, dict: ST.Dict, +i: U32, w: MDW(~U32, n, d, x, m, 0, i)) -> {Laws.ccell(V.Eval.fix.s2(n, d, ST.Strs.out.d(dict, K.Kernel.mask_data(~U32, n, x, m, 0))), i) == Laws.ccell(C.CStr{n, d, C.Mask{m}, ST.SDict{x, dict}}, i) : D.Scalar}:
  (o, mb, eq, +emb, wo, cell) = w
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.mask_data(~U32, n, x, m, 0), (o, mb), eq) : {Laws.ccell(V.Eval.fix.s2(n, d, ST.Strs.out.d(dict, _)), i) == Laws.ccell(C.CStr{n, d, C.Mask{m}, ST.SDict{x, dict}}, i) : D.Scalar}
  fixc_dict_k(n, d, m, x, dict, i, o, mb, wo, cell, mask_read(m, mb, i, emb))

def fixc_str(+n: U32, +d: Nat, m: Array<U32>, x: ST.Strs, +i: U32, hyp: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool} & {U32.is_lt(i, n) == True{} : Bool} & Laws.WFStrData(d, x)) -> {Laws.ccell(V.Eval.fix.s2(n, d, ST.Strs.fix(n, x, m)), i) == Laws.ccell(C.CStr{n, d, C.Mask{m}, x}, i) : D.Scalar}:
  match x:
    case ST.SRaw{a}:
      (+fits, +hi, wf) = hyp
      fixc_raw(n, d, m, a, i, mask_data_w(~String, n, d, a, m, "", i, wf, fits, hi))
    case ST.SDict{codes, dict}:
      (+fits, +hi, wf) = hyp
      fixc_dict(n, d, m, codes, dict, i, mask_data_w(~U32, n, d, codes, m, 0, i, wf, fits, hi))

# ---- per column kind: the valid-everywhere column is untouched; a mask runs the kernel --------------------

def fixc_wb(+n: U32, +d: Nat, v: C.Valid, x: Array<U32>, +i: U32, hyp: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool} & {U32.is_lt(i, n) == True{} : Bool} & Laws.WFArray(U32, d, x)) -> {Laws.ccell(V.Eval.fix.w(D.TBool{}, n, d, v, x), i) == Laws.ccell(C.CBool{n, d, v, x}, i) : D.Scalar}:
  match v:
    case C.AllValid{}:
      {==}
    case C.Mask{m}:
      (+fits, +hi, wf) = hyp
      fixc_bool(n, d, m, x, i, mask_data_w(~U32, n, d, x, m, 0, i, wf, fits, hi))

def fixc_wu(+n: U32, +d: Nat, v: C.Valid, x: Array<U32>, +i: U32, hyp: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool} & {U32.is_lt(i, n) == True{} : Bool} & Laws.WFArray(U32, d, x)) -> {Laws.ccell(V.Eval.fix.w(D.TU32{}, n, d, v, x), i) == Laws.ccell(C.CU32{n, d, v, x}, i) : D.Scalar}:
  match v:
    case C.AllValid{}:
      {==}
    case C.Mask{m}:
      (+fits, +hi, wf) = hyp
      fixc_u32(n, d, m, x, i, mask_data_w(~U32, n, d, x, m, 0, i, wf, fits, hi))

def fixc_wi(+n: U32, +d: Nat, v: C.Valid, x: Array<U32>, +i: U32, hyp: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool} & {U32.is_lt(i, n) == True{} : Bool} & Laws.WFArray(U32, d, x)) -> {Laws.ccell(V.Eval.fix.w(D.TI32{}, n, d, v, x), i) == Laws.ccell(C.CI32{n, d, v, x}, i) : D.Scalar}:
  match v:
    case C.AllValid{}:
      {==}
    case C.Mask{m}:
      (+fits, +hi, wf) = hyp
      fixc_i32(n, d, m, x, i, mask_data_w(~U32, n, d, x, m, 0, i, wf, fits, hi))

def fixc_f(+n: U32, +d: Nat, v: C.Valid, x: Array<F32>, +i: U32, hyp: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool} & {U32.is_lt(i, n) == True{} : Bool} & Laws.WFArray(F32, d, x)) -> {Laws.ccell(V.Eval.fix.f(n, d, v, x), i) == Laws.ccell(C.CF32{n, d, v, x}, i) : D.Scalar}:
  match v:
    case C.AllValid{}:
      {==}
    case C.Mask{m}:
      (+fits, +hi, wf) = hyp
      fixc_f32(n, d, m, x, i, mask_data_w(~F32, n, d, x, m, 0.0, i, wf, fits, hi))

def fixc_s(+n: U32, +d: Nat, v: C.Valid, x: ST.Strs, +i: U32, hyp: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool} & {U32.is_lt(i, n) == True{} : Bool} & Laws.WFStrData(d, x)) -> {Laws.ccell(V.Eval.fix.s(n, d, v, x), i) == Laws.ccell(C.CStr{n, d, v, x}, i) : D.Scalar}:
  match v:
    case C.AllValid{}:
      {==}
    case C.Mask{m}:
      fixc_str(n, d, m, x, i, hyp)

def Laws.fix_cell(c, i, hyp):
  match c:
    case C.CBool{+n, +d, v, x}:
      fixc_wb(n, d, v, x, i, hyp)
    case C.CU32{+n, +d, v, x}:
      fixc_wu(n, d, v, x, i, hyp)
    case C.CI32{+n, +d, v, x}:
      fixc_wi(n, d, v, x, i, hyp)
    case C.CF32{+n, +d, v, x}:
      fixc_f(n, d, v, x, i, hyp)
    case C.CStr{+n, +d, v, x}:
      fixc_s(n, d, v, x, i, hyp)

# ---- Laws.fill_str_cell: Eval.fill on two Str columns ----------------------------------------------------
#
# Eval.fill.str decodes both sides (any pair but two Dictionaries) and runs Eval.fill.t: valid-
# everywhere a is kept as it is; with a mask, Kernel.choose picks a's cell where the mask word is
# set and b's where it is 0 (choose_w), and the validity is AllValid (b valid everywhere) or the OR
# of the two masks (mask_or_cell). The mask words at i are read off the returned mask as Data words
# (mask_read / get_w) so the pick algebra is closed by a case split on them (both 0/1: Mask01).

# Strs.decode as a well-formed array whose rows below n read as the cells (DecodeW with the shape)
def DecodeWF(-s: ST.Strs, +n: U32, +d: Nat) -> Type:
  &o: Array<String> -> {ST.Strs.decode(n, d, s) == o : Array<String>} & Laws.WFArray(String, d, o) & (@i: U32 -> {U32.is_lt(i, n) == True{} : Bool} -> {Laws.rd_at(String, o, i) == Laws.scell(s, i) : String})

def decode_wf_dict_k(+n: U32, +d: Nat, -codes: Array<U32>, +k: U32, +dd: Nat, -strs: Array<String>, +b: Nat, -slots: Array<ST.SSlot>, +tag: U32, -o: Array<String>, pm: Array<U32>, spec: @i: U32 -> {U32.is_lt(i, n) == True{} : Bool} -> {Laws.rdN(String, d, o, i) == Laws.rd_at(String, strs, Laws.rd_at(U32, codes, i)) : String},
  w: &o2: Array<String> -> {o2 == o : Array<String>} & Laws.WFArray(String, d, o2) & (@i: U32 -> {Laws.rd_at(String, o, i) == Laws.rdN(String, d, o, i) : String}))
  -> &o3: Array<String> -> {ST.Strs.fst(~String, (o, pm)) == o3 : Array<String>} & Laws.WFArray(String, d, o3) & (@i: U32 -> {U32.is_lt(i, n) == True{} : Bool} -> {Laws.rd_at(String, o3, i) == Laws.scell(ST.SDict{codes, ST.Dict{k, dd, strs, b, slots, tag}}, i) : String}):
  (o2, +e2, w2, cv) = w
  (o2, Equal.sym(Array<String>, o2, o, e2), w2, +i => hi => Equal.trans(String, Laws.rd_at(String, o2, i), Laws.rd_at(String, o, i), Laws.rd_at(String, strs, Laws.rd_at(U32, codes, i)), Equal.cong(Array<String>, String, q => Laws.rd_at(String, q, i), o2, o, e2), Equal.trans(String, Laws.rd_at(String, o, i), Laws.rdN(String, d, o, i), Laws.rd_at(String, strs, Laws.rd_at(U32, codes, i)), cv(i), spec(i, hi))))

def decode_wf_dict(+n: U32, +d: Nat, -codes: Array<U32>, +k: U32, +dd: Nat, -strs: Array<String>, +b: Nat, -slots: Array<ST.SSlot>, +tag: U32, w: PST.TGW(~String, d, n, strs, codes, "")) -> DecodeWF(ST.SDict{codes, ST.Dict{k, dd, strs, b, slots, tag}}, n, d):
  (o, pm, eq, epm, wo, spec) = w
  %Equal.sym(Array<String> & Array<U32>, K.Kernel.gather(~String, n, d, strs, codes, ""), (o, pm), eq) : &o3: Array<String> -> {ST.Strs.fst(~String, _) == o3 : Array<String>} & Laws.WFArray(String, d, o3) & (@i: U32 -> {U32.is_lt(i, n) == True{} : Bool} -> {Laws.rd_at(String, o3, i) == Laws.scell(ST.SDict{codes, ST.Dict{k, dd, strs, b, slots, tag}}, i) : String})
  decode_wf_dict_k(n, d, codes, k, dd, strs, b, slots, tag, o, pm, spec, PST.rd_all(String, d, o, wo))

def decode_wf_d(+n: U32, +d: Nat, codes: Array<U32>, dict: ST.Dict, fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}) -> DecodeWF(ST.SDict{codes, dict}, n, d):
  match dict:
    case ST.Dict{+k, +dd, strs, +b, slots, +tag}:
      decode_wf_dict(n, d, codes, k, dd, strs, b, slots, tag, PST.tgather_w(~String, d, n, strs, codes, "", fits))

def decode_wf(+n: U32, +d: Nat, s: ST.Strs, fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, wfs: Laws.WFStrData(d, s)) -> DecodeWF(s, n, d):
  match s:
    case ST.SRaw{a}:
      (a, {==}, wfs, +i => hi => {==})
    case ST.SDict{codes, dict}:
      decode_wf_d(n, d, codes, dict, fits)

# ---- the pick algebra of the Raw branch ---------------------------------------------------------------------

# b valid everywhere: the chosen string is a's where a's mask word is set, b's otherwise
def fill_pick_av(bw: Bool, -xa: ST.Strs, -xb: ST.Strs, +i: U32, +w: U32, +eb: {U32.is_ne(w, 0) == bw : Bool}) -> {D.SStr{Bool.pick(String, U32.is_ne(w, 0), Laws.scell(xa, i), Laws.scell(xb, i))} == Bool.pick(D.Scalar, U32.is_ne(w, 0), Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), D.SStr{Laws.scell(xb, i)}) : D.Scalar}:
  match bw:
    case True{}:
      %Equal.sym(Bool, U32.is_ne(w, 0), True{}, eb) : {D.SStr{Bool.pick(String, _, Laws.scell(xa, i), Laws.scell(xb, i))} == Bool.pick(D.Scalar, _, Bool.pick(D.Scalar, _, D.SStr{Laws.scell(xa, i)}, D.SNull{}), D.SStr{Laws.scell(xb, i)}) : D.Scalar}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_ne(w, 0), False{}, eb) : {D.SStr{Bool.pick(String, _, Laws.scell(xa, i), Laws.scell(xb, i))} == Bool.pick(D.Scalar, _, Bool.pick(D.Scalar, _, D.SStr{Laws.scell(xa, i)}, D.SNull{}), D.SStr{Laws.scell(xb, i)}) : D.Scalar}
      {==}

# both masked (words w, wb in {0, 1}): the OR of the words is the result's mask word
def fill_pick_mk(cw: Bool, cwb: Bool, -xa: ST.Strs, -xb: ST.Strs, +i: U32, +w: U32, +wb: U32, sw: PC.Bit01(cw, w), swb: PC.Bit01(cwb, wb))
  -> {Bool.pick(D.Scalar, U32.is_ne(U32.or(w, wb), 0), D.SStr{Bool.pick(String, U32.is_ne(w, 0), Laws.scell(xa, i), Laws.scell(xb, i))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(w, 0), Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(wb, 0), D.SStr{Laws.scell(xb, i)}, D.SNull{})) : D.Scalar}:
  match cw cwb:
    case True{} True{}:
      %Equal.sym(U32, w, 1, sw) : {Bool.pick(D.Scalar, U32.is_ne(U32.or(_, wb), 0), D.SStr{Bool.pick(String, U32.is_ne(_, 0), Laws.scell(xa, i), Laws.scell(xb, i))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(_, 0), Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(wb, 0), D.SStr{Laws.scell(xb, i)}, D.SNull{})) : D.Scalar}
      %Equal.sym(U32, wb, 1, swb) : {Bool.pick(D.Scalar, U32.is_ne(U32.or(1, _), 0), D.SStr{Bool.pick(String, U32.is_ne(1, 0), Laws.scell(xa, i), Laws.scell(xb, i))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(1, 0), Bool.pick(D.Scalar, U32.is_ne(1, 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.scell(xb, i)}, D.SNull{})) : D.Scalar}
      {==}
    case True{} False{}:
      %Equal.sym(U32, w, 1, sw) : {Bool.pick(D.Scalar, U32.is_ne(U32.or(_, wb), 0), D.SStr{Bool.pick(String, U32.is_ne(_, 0), Laws.scell(xa, i), Laws.scell(xb, i))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(_, 0), Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(wb, 0), D.SStr{Laws.scell(xb, i)}, D.SNull{})) : D.Scalar}
      %Equal.sym(U32, wb, 0, swb) : {Bool.pick(D.Scalar, U32.is_ne(U32.or(1, _), 0), D.SStr{Bool.pick(String, U32.is_ne(1, 0), Laws.scell(xa, i), Laws.scell(xb, i))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(1, 0), Bool.pick(D.Scalar, U32.is_ne(1, 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.scell(xb, i)}, D.SNull{})) : D.Scalar}
      {==}
    case False{} True{}:
      %Equal.sym(U32, w, 0, sw) : {Bool.pick(D.Scalar, U32.is_ne(U32.or(_, wb), 0), D.SStr{Bool.pick(String, U32.is_ne(_, 0), Laws.scell(xa, i), Laws.scell(xb, i))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(_, 0), Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(wb, 0), D.SStr{Laws.scell(xb, i)}, D.SNull{})) : D.Scalar}
      %Equal.sym(U32, wb, 1, swb) : {Bool.pick(D.Scalar, U32.is_ne(U32.or(0, _), 0), D.SStr{Bool.pick(String, U32.is_ne(0, 0), Laws.scell(xa, i), Laws.scell(xb, i))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(0, 0), Bool.pick(D.Scalar, U32.is_ne(0, 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.scell(xb, i)}, D.SNull{})) : D.Scalar}
      {==}
    case False{} False{}:
      %Equal.sym(U32, w, 0, sw) : {Bool.pick(D.Scalar, U32.is_ne(U32.or(_, wb), 0), D.SStr{Bool.pick(String, U32.is_ne(_, 0), Laws.scell(xa, i), Laws.scell(xb, i))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(_, 0), Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(wb, 0), D.SStr{Laws.scell(xb, i)}, D.SNull{})) : D.Scalar}
      %Equal.sym(U32, wb, 0, swb) : {Bool.pick(D.Scalar, U32.is_ne(U32.or(0, _), 0), D.SStr{Bool.pick(String, U32.is_ne(0, 0), Laws.scell(xa, i), Laws.scell(xb, i))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(0, 0), Bool.pick(D.Scalar, U32.is_ne(0, 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.scell(xb, i)}, D.SNull{})) : D.Scalar}
      {==}

def fill_pick_mk_k(-xa: ST.Strs, -xb: ST.Strs, +i: U32, +w: U32, +wb: U32, w1: &cw: Bool -> PC.Bit01(cw, w), w2: &cwb: Bool -> PC.Bit01(cwb, wb))
  -> {Bool.pick(D.Scalar, U32.is_ne(U32.or(w, wb), 0), D.SStr{Bool.pick(String, U32.is_ne(w, 0), Laws.scell(xa, i), Laws.scell(xb, i))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(w, 0), Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(wb, 0), D.SStr{Laws.scell(xb, i)}, D.SNull{})) : D.Scalar}:
  (cw, sw) = w1
  (cwb, swb) = w2
  fill_pick_mk(cw, cwb, xa, xb, i, w, wb, sw, swb)

def fill_pick_mk_w(-xa: ST.Strs, -xb: ST.Strs, +i: U32, +w: U32, +wb: U32, hw: {U32.is_le(w, 1) == True{} : Bool}, hwb: {U32.is_le(wb, 1) == True{} : Bool})
  -> {Bool.pick(D.Scalar, U32.is_ne(U32.or(w, wb), 0), D.SStr{Bool.pick(String, U32.is_ne(w, 0), Laws.scell(xa, i), Laws.scell(xb, i))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(w, 0), Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(wb, 0), D.SStr{Laws.scell(xb, i)}, D.SNull{})) : D.Scalar}:
  fill_pick_mk_k(xa, xb, i, w, wb, PC.le1_cases(w, hw), PC.le1_cases(wb, hwb))

# ---- the Raw branch -----------------------------------------------------------------------------------------

# the goal over the decoded arrays A (a's rows, written in place) and B (b's rows)
def FRaw(+n: U32, +d: Nat, -va: C.Valid, -xa: ST.Strs, +n2: U32, +d2: Nat, -vb: C.Valid, -xb: ST.Strs, -A: Array<String>, -B: Array<String>, +i: U32) -> Type:
  &c: C.Column -> {V.Eval.fill.s(n, d, V.Eval.fill.t(~String, n, d, va, vb, A, B)) == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, Laws.vbit(va, i), Laws.ccell(C.CStr{n, d, va, xa}, i), Laws.ccell(C.CStr{n2, d2, vb, xb}, i)) : D.Scalar}


# ... after the choose (a masked): its result pair r, then the pair (mb, o) in place
def FRaw1(+n: U32, +d: Nat, -ma: Array<U32>, -xa: ST.Strs, +n2: U32, +d2: Nat, -vb: C.Valid, -xb: ST.Strs, -r: Array<U32> & Array<String>, +i: U32) -> Type:
  &c: C.Column -> {V.Eval.fill.s(n, d, V.Eval.fill.t2(~String, n, d, vb, r)) == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.ccell(C.CStr{n, d, C.Mask{ma}, xa}, i), Laws.ccell(C.CStr{n2, d2, vb, xb}, i)) : D.Scalar}

def FRaw2(+n: U32, +d: Nat, -ma: Array<U32>, -xa: ST.Strs, +n2: U32, +d2: Nat, -vb: C.Valid, -xb: ST.Strs, -mb: Array<U32>, -o: Array<String>, +i: U32) -> Type:
  &c: C.Column -> {V.Eval.fill.s(n, d, V.Eval.fill.t2(~String, n, d, vb, (mb, o))) == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.ccell(C.CStr{n, d, C.Mask{ma}, xa}, i), Laws.ccell(C.CStr{n2, d2, vb, xb}, i)) : D.Scalar}

# a masked, b valid everywhere: the result is valid everywhere, its row the chosen string
def fill_raw_mk_av(+n: U32, +d: Nat, -ma: Array<U32>, -xa: ST.Strs, +n2: U32, +d2: Nat, -xb: ST.Strs, -A: Array<String>, -B: Array<String>, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool},
  fA: @j: U32 -> {U32.is_lt(j, n) == True{} : Bool} -> {Laws.rd_at(String, A, j) == Laws.scell(xa, j) : String}, fB: @j: U32 -> {U32.is_lt(j, n) == True{} : Bool} -> {Laws.rd_at(String, B, j) == Laws.scell(xb, j) : String},
  -mb: Array<U32>, -o: Array<String>, +cell: {Laws.rdN(String, d, o, i) == Bool.pick(String, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.rd_at(String, A, i), Laws.rd_at(String, B, i)) : String},
  +w: U32, +ewm: {w == Laws.rd_at(U32, ma, i) : U32},
  wo2: &o2: Array<String> -> {o2 == o : Array<String>} & Laws.WFArray(String, d, o2) & (@k: U32 -> {Laws.rd_at(String, o, k) == Laws.rdN(String, d, o, k) : String}))
  -> FRaw2(n, d, ma, xa, n2, d2, C.AllValid{}, xb, mb, o, i):
  (o2, +eo2, wo3, cv) = wo2
  (C.CStr{n, d, C.AllValid{}, ST.SRaw{o2}}, (%Equal.sym(Array<String>, o2, o, eo2) : {V.Eval.fill.s(n, d, V.Eval.fill.t2(~String, n, d, C.AllValid{}, (mb, o))) == Done{C.CStr{n, d, C.AllValid{}, ST.SRaw{_}}} : E.ResT(C.Column)}; {==}),
    (%Equal.sym(Array<String>, o2, o, eo2) : {D.SStr{Laws.rd_at(String, _, i)} == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), D.SStr{Laws.scell(xb, i)}) : D.Scalar};
     %Equal.sym(String, Laws.rd_at(String, o, i), Laws.rdN(String, d, o, i), cv(i)) : {D.SStr{_} == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), D.SStr{Laws.scell(xb, i)}) : D.Scalar};
     %Equal.sym(String, Laws.rdN(String, d, o, i), Bool.pick(String, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.rd_at(String, A, i), Laws.rd_at(String, B, i)), cell) : {D.SStr{_} == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), D.SStr{Laws.scell(xb, i)}) : D.Scalar};
     %Equal.sym(String, Laws.rd_at(String, A, i), Laws.scell(xa, i), fA(i, hi)) : {D.SStr{Bool.pick(String, U32.is_ne(Laws.rd_at(U32, ma, i), 0), _, Laws.rd_at(String, B, i))} == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), D.SStr{Laws.scell(xb, i)}) : D.Scalar};
     %Equal.sym(String, Laws.rd_at(String, B, i), Laws.scell(xb, i), fB(i, hi)) : {D.SStr{Bool.pick(String, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.scell(xa, i), _)} == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), D.SStr{Laws.scell(xb, i)}) : D.Scalar};
     %ewm : {D.SStr{Bool.pick(String, U32.is_ne(_, 0), Laws.scell(xa, i), Laws.scell(xb, i))} == Bool.pick(D.Scalar, U32.is_ne(_, 0), Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), D.SStr{Laws.scell(xb, i)}) : D.Scalar};
     fill_pick_av(U32.is_ne(w, 0), xa, xb, i, w, {==})))

# a masked, b masked: the result's mask is the OR of the masks (mask_or_cell on the second copies),
# its row the chosen string; both words are Data (w off the returned mask, wb off b's mask)
def fill_raw_mk_mk3(+n: U32, +d: Nat, -ma: Array<U32>, -xa: ST.Strs, +n2: U32, +d2: Nat, -mbb: Array<U32>, -xb: ST.Strs, -A: Array<String>, -B: Array<String>, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool},
  fA: @j: U32 -> {U32.is_lt(j, n) == True{} : Bool} -> {Laws.rd_at(String, A, j) == Laws.scell(xa, j) : String}, fB: @j: U32 -> {U32.is_lt(j, n) == True{} : Bool} -> {Laws.rd_at(String, B, j) == Laws.scell(xb, j) : String},
  -o: Array<String>, +cell: {Laws.rdN(String, d, o, i) == Bool.pick(String, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.rd_at(String, A, i), Laws.rd_at(String, B, i)) : String},
  +w: U32, +ewm: {w == Laws.rd_at(U32, ma, i) : U32}, +hw: {U32.is_le(w, 1) == True{} : Bool}, +wb: U32, +ewb: {wb == Laws.rd_at(U32, mbb, i) : U32}, +hwb: {U32.is_le(wb, 1) == True{} : Bool},
  mb3: Array<U32>, mb4: Array<U32>, mbb3: Array<U32>, mbb4: Array<U32>, +e43: {mb4 == mb3 : Array<U32>}, +eb43: {mbb4 == mbb3 : Array<U32>}, +ew4: {w == Laws.rd_at(U32, mb4, i) : U32}, +ewb4: {wb == Laws.rd_at(U32, mbb4, i) : U32},
  wo2: &o2: Array<String> -> {o2 == o : Array<String>} & Laws.WFArray(String, d, o2) & (@k: U32 -> {Laws.rd_at(String, o, k) == Laws.rdN(String, d, o, k) : String}))
  -> &c: C.Column -> {Done{C.CStr{n, d, C.Mask{K.Kernel.mask_or(n, d, mb3, mbb3)}, ST.SRaw{o}}} == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.ccell(C.CStr{n, d, C.Mask{ma}, xa}, i), Laws.ccell(C.CStr{n2, d2, C.Mask{mbb}, xb}, i)) : D.Scalar}:
  (o2, +eo2, wo3, cv) = wo2
  (C.CStr{n, d, C.Mask{K.Kernel.mask_or(n, d, mb3, mbb3)}, ST.SRaw{o2}}, (%Equal.sym(Array<String>, o2, o, eo2) : {Done{C.CStr{n, d, C.Mask{K.Kernel.mask_or(n, d, mb3, mbb3)}, ST.SRaw{o}}} == Done{C.CStr{n, d, C.Mask{K.Kernel.mask_or(n, d, mb3, mbb3)}, ST.SRaw{_}}} : E.ResT(C.Column)}; {==}),
    (%e43 : {Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, K.Kernel.mask_or(n, d, _, mbb3), i), 0), D.SStr{Laws.rd_at(String, o2, i)}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mbb, i), 0), D.SStr{Laws.scell(xb, i)}, D.SNull{})) : D.Scalar};
     %eb43 : {Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, K.Kernel.mask_or(n, d, mb4, _), i), 0), D.SStr{Laws.rd_at(String, o2, i)}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mbb, i), 0), D.SStr{Laws.scell(xb, i)}, D.SNull{})) : D.Scalar};
     %Equal.sym(U32, Laws.rd_at(U32, K.Kernel.mask_or(n, d, mb4, mbb4), i), U32.or(Laws.rd_at(U32, mb4, i), Laws.rd_at(U32, mbb4, i)), Laws.mask_or_cell(d, n, mb4, mbb4, i, fits, hi)) : {Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.rd_at(String, o2, i)}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mbb, i), 0), D.SStr{Laws.scell(xb, i)}, D.SNull{})) : D.Scalar};
     %ew4 : {Bool.pick(D.Scalar, U32.is_ne(U32.or(_, Laws.rd_at(U32, mbb4, i)), 0), D.SStr{Laws.rd_at(String, o2, i)}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mbb, i), 0), D.SStr{Laws.scell(xb, i)}, D.SNull{})) : D.Scalar};
     %ewb4 : {Bool.pick(D.Scalar, U32.is_ne(U32.or(w, _), 0), D.SStr{Laws.rd_at(String, o2, i)}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mbb, i), 0), D.SStr{Laws.scell(xb, i)}, D.SNull{})) : D.Scalar};
     %Equal.sym(Array<String>, o2, o, eo2) : {Bool.pick(D.Scalar, U32.is_ne(U32.or(w, wb), 0), D.SStr{Laws.rd_at(String, _, i)}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mbb, i), 0), D.SStr{Laws.scell(xb, i)}, D.SNull{})) : D.Scalar};
     %Equal.sym(String, Laws.rd_at(String, o, i), Laws.rdN(String, d, o, i), cv(i)) : {Bool.pick(D.Scalar, U32.is_ne(U32.or(w, wb), 0), D.SStr{_}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mbb, i), 0), D.SStr{Laws.scell(xb, i)}, D.SNull{})) : D.Scalar};
     %Equal.sym(String, Laws.rdN(String, d, o, i), Bool.pick(String, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.rd_at(String, A, i), Laws.rd_at(String, B, i)), cell) : {Bool.pick(D.Scalar, U32.is_ne(U32.or(w, wb), 0), D.SStr{_}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mbb, i), 0), D.SStr{Laws.scell(xb, i)}, D.SNull{})) : D.Scalar};
     %Equal.sym(String, Laws.rd_at(String, A, i), Laws.scell(xa, i), fA(i, hi)) : {Bool.pick(D.Scalar, U32.is_ne(U32.or(w, wb), 0), D.SStr{Bool.pick(String, U32.is_ne(Laws.rd_at(U32, ma, i), 0), _, Laws.rd_at(String, B, i))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mbb, i), 0), D.SStr{Laws.scell(xb, i)}, D.SNull{})) : D.Scalar};
     %Equal.sym(String, Laws.rd_at(String, B, i), Laws.scell(xb, i), fB(i, hi)) : {Bool.pick(D.Scalar, U32.is_ne(U32.or(w, wb), 0), D.SStr{Bool.pick(String, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.scell(xa, i), _)}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mbb, i), 0), D.SStr{Laws.scell(xb, i)}, D.SNull{})) : D.Scalar};
     %ewm : {Bool.pick(D.Scalar, U32.is_ne(U32.or(w, wb), 0), D.SStr{Bool.pick(String, U32.is_ne(_, 0), Laws.scell(xa, i), Laws.scell(xb, i))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(_, 0), Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mbb, i), 0), D.SStr{Laws.scell(xb, i)}, D.SNull{})) : D.Scalar};
     %ewb : {Bool.pick(D.Scalar, U32.is_ne(U32.or(w, wb), 0), D.SStr{Bool.pick(String, U32.is_ne(w, 0), Laws.scell(xa, i), Laws.scell(xb, i))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(w, 0), Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SStr{Laws.scell(xa, i)}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.scell(xb, i)}, D.SNull{})) : D.Scalar};
     fill_pick_mk_w(xa, xb, i, w, wb, hw, hwb)))

# the two masks cloned (the production term keeps one copy each; mask_or_cell consumes the other)
def fill_raw_mk_mk2(+n: U32, +d: Nat, -ma: Array<U32>, -xa: ST.Strs, +n2: U32, +d2: Nat, -mbb: Array<U32>, -xb: ST.Strs, -A: Array<String>, -B: Array<String>, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool},
  fA: @j: U32 -> {U32.is_lt(j, n) == True{} : Bool} -> {Laws.rd_at(String, A, j) == Laws.scell(xa, j) : String}, fB: @j: U32 -> {U32.is_lt(j, n) == True{} : Bool} -> {Laws.rd_at(String, B, j) == Laws.scell(xb, j) : String},
  -o: Array<String>, +cell: {Laws.rdN(String, d, o, i) == Bool.pick(String, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.rd_at(String, A, i), Laws.rd_at(String, B, i)) : String},
  +w: U32, +ewm: {w == Laws.rd_at(U32, ma, i) : U32}, +hw: {U32.is_le(w, 1) == True{} : Bool}, +wb: U32, +ewb: {wb == Laws.rd_at(U32, mbb, i) : U32}, +hwb: {U32.is_le(wb, 1) == True{} : Bool},
  -mb2: Array<U32>, -mbb2: Array<U32>, +ew2: {w == Laws.rd_at(U32, mb2, i) : U32}, +ewb2: {wb == Laws.rd_at(U32, mbb2, i) : U32},
  wo2: &o2: Array<String> -> {o2 == o : Array<String>} & Laws.WFArray(String, d, o2) & (@k: U32 -> {Laws.rd_at(String, o, k) == Laws.rdN(String, d, o, k) : String}),
  wm: &mb3: Array<U32> -> &mb4: Array<U32> -> {mb3 == mb2 : Array<U32>} & {mb4 == mb2 : Array<U32>},
  wmb: &mbb3: Array<U32> -> &mbb4: Array<U32> -> {mbb3 == mbb2 : Array<U32>} & {mbb4 == mbb2 : Array<U32>})
  -> &c: C.Column -> {Done{C.CStr{n, d, C.Mask{K.Kernel.mask_or(n, d, mb2, mbb2)}, ST.SRaw{o}}} == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.ccell(C.CStr{n, d, C.Mask{ma}, xa}, i), Laws.ccell(C.CStr{n2, d2, C.Mask{mbb}, xb}, i)) : D.Scalar}:
  (mb3, mb4, +e3, +e4) = wm
  (mbb3, mbb4, +eb3, +eb4) = wmb
  %e3 : &c: C.Column -> {Done{C.CStr{n, d, C.Mask{K.Kernel.mask_or(n, d, _, mbb2)}, ST.SRaw{o}}} == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.ccell(C.CStr{n, d, C.Mask{ma}, xa}, i), Laws.ccell(C.CStr{n2, d2, C.Mask{mbb}, xb}, i)) : D.Scalar}
  %eb3 : &c: C.Column -> {Done{C.CStr{n, d, C.Mask{K.Kernel.mask_or(n, d, mb3, _)}, ST.SRaw{o}}} == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.ccell(C.CStr{n, d, C.Mask{ma}, xa}, i), Laws.ccell(C.CStr{n2, d2, C.Mask{mbb}, xb}, i)) : D.Scalar}
  fill_raw_mk_mk3(n, d, ma, xa, n2, d2, mbb, xb, A, B, i, hi, fits, fA, fB, o, cell, w, ewm, hw, wb, ewb, hwb, mb3, mb4, mbb3, mbb4, Equal.trans(Array<U32>, mb4, mb2, mb3, e4, Equal.sym(Array<U32>, mb3, mb2, e3)), Equal.trans(Array<U32>, mbb4, mbb2, mbb3, eb4, Equal.sym(Array<U32>, mbb3, mbb2, eb3)), Equal.trans(U32, w, Laws.rd_at(U32, mb2, i), Laws.rd_at(U32, mb4, i), ew2, Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, i), mb2, mb4, Equal.sym(Array<U32>, mb4, mb2, e4))), Equal.trans(U32, wb, Laws.rd_at(U32, mbb2, i), Laws.rd_at(U32, mbb4, i), ewb2, Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, i), mbb2, mbb4, Equal.sym(Array<U32>, mbb4, mbb2, eb4))), wo2)

def fill_raw_mk_mk1(+n: U32, +d: Nat, -ma: Array<U32>, -xa: ST.Strs, +n2: U32, +d2: Nat, -mbb: Array<U32>, -xb: ST.Strs, -A: Array<String>, -B: Array<String>, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool},
  fA: @j: U32 -> {U32.is_lt(j, n) == True{} : Bool} -> {Laws.rd_at(String, A, j) == Laws.scell(xa, j) : String}, fB: @j: U32 -> {U32.is_lt(j, n) == True{} : Bool} -> {Laws.rd_at(String, B, j) == Laws.scell(xb, j) : String},
  -o: Array<String>, +cell: {Laws.rdN(String, d, o, i) == Bool.pick(String, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.rd_at(String, A, i), Laws.rd_at(String, B, i)) : String},
  +w: U32, +ewm: {w == Laws.rd_at(U32, ma, i) : U32}, +hw: {U32.is_le(w, 1) == True{} : Bool}, +wb: U32, +ewb: {wb == Laws.rd_at(U32, mbb, i) : U32}, +hwb0: {U32.is_le(Laws.rd_at(U32, mbb, i), 1) == True{} : Bool},
  mb2: Array<U32>, mbb2: Array<U32>, +ew2: {w == Laws.rd_at(U32, mb2, i) : U32}, +embb2: {mbb2 == mbb : Array<U32>},
  wo2: &o2: Array<String> -> {o2 == o : Array<String>} & Laws.WFArray(String, d, o2) & (@k: U32 -> {Laws.rd_at(String, o, k) == Laws.rdN(String, d, o, k) : String}))
  -> &c: C.Column -> {Done{C.CStr{n, d, C.Mask{K.Kernel.mask_or(n, d, mb2, mbb2)}, ST.SRaw{o}}} == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.ccell(C.CStr{n, d, C.Mask{ma}, xa}, i), Laws.ccell(C.CStr{n2, d2, C.Mask{mbb}, xb}, i)) : D.Scalar}:
  fill_raw_mk_mk2(n, d, ma, xa, n2, d2, mbb, xb, A, B, i, hi, fits, fA, fB, o, cell, w, ewm, hw, wb, ewb, (%Equal.sym(U32, wb, Laws.rd_at(U32, mbb, i), ewb) : {U32.is_le(_, 1) == True{} : Bool}; hwb0), mb2, mbb2, ew2, Equal.trans(U32, wb, Laws.rd_at(U32, mbb, i), Laws.rd_at(U32, mbb2, i), ewb, Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, i), mbb, mbb2, Equal.sym(Array<U32>, mbb2, mbb, embb2))), wo2, PC.clone_eq(U32, mb2), PC.clone_eq(U32, mbb2))

# b's mask word read (get_w); b's mask copy replaces the original in the production term
def fill_raw_mk_mk(+n: U32, +d: Nat, -ma: Array<U32>, -xa: ST.Strs, +n2: U32, +d2: Nat, -mbb: Array<U32>, -xb: ST.Strs, -A: Array<String>, -B: Array<String>, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool},
  fA: @j: U32 -> {U32.is_lt(j, n) == True{} : Bool} -> {Laws.rd_at(String, A, j) == Laws.scell(xa, j) : String}, fB: @j: U32 -> {U32.is_lt(j, n) == True{} : Bool} -> {Laws.rd_at(String, B, j) == Laws.scell(xb, j) : String},
  -o: Array<String>, +cell: {Laws.rdN(String, d, o, i) == Bool.pick(String, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.rd_at(String, A, i), Laws.rd_at(String, B, i)) : String},
  +w: U32, +ewm: {w == Laws.rd_at(U32, ma, i) : U32}, +hw: {U32.is_le(w, 1) == True{} : Bool}, +hwb0: {U32.is_le(Laws.rd_at(U32, mbb, i), 1) == True{} : Bool},
  mb2: Array<U32>, +ew2: {w == Laws.rd_at(U32, mb2, i) : U32},
  wo2: &o2: Array<String> -> {o2 == o : Array<String>} & Laws.WFArray(String, d, o2) & (@k: U32 -> {Laws.rd_at(String, o, k) == Laws.rdN(String, d, o, k) : String}),
  wb: &mbb2: Array<U32> -> &wbv: U32 -> {mbb2 == mbb : Array<U32>} & {Array.get(U32, mbb, i) == (mbb, wbv) : Array<U32> & U32} & {wbv == Laws.rd_at(U32, mbb, i) : U32})
  -> FRaw2(n, d, ma, xa, n2, d2, C.Mask{mbb}, xb, mb2, o, i):
  (mbb2, +wbv, +embb2, e1, ewbv) = wb
  %embb2 : &c: C.Column -> {Done{C.CStr{n, d, C.Mask{K.Kernel.mask_or(n, d, mb2, _)}, ST.SRaw{o}}} == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.ccell(C.CStr{n, d, C.Mask{ma}, xa}, i), Laws.ccell(C.CStr{n2, d2, C.Mask{mbb}, xb}, i)) : D.Scalar}
  fill_raw_mk_mk1(n, d, ma, xa, n2, d2, mbb, xb, A, B, i, hi, fits, fA, fB, o, cell, w, ewm, hw, wbv, ewbv, hwb0, mb2, mbb2, ew2, embb2, wo2)

# the mask word of a read off the returned mask; the output read back (rd_all); then by b's validity
def fill_raw_mk1(+n: U32, +d: Nat, -ma: Array<U32>, -xa: ST.Strs, +n2: U32, +d2: Nat, vb: C.Valid, -xb: ST.Strs, -A: Array<String>, -B: Array<String>, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +m01a: {U32.is_le(Laws.rd_at(U32, ma, i), 1) == True{} : Bool}, m01b: Laws.Mask01(vb, i),
  fA: @j: U32 -> {U32.is_lt(j, n) == True{} : Bool} -> {Laws.rd_at(String, A, j) == Laws.scell(xa, j) : String}, fB: @j: U32 -> {U32.is_lt(j, n) == True{} : Bool} -> {Laws.rd_at(String, B, j) == Laws.scell(xb, j) : String},
  mb2: Array<U32>, o: Array<String>, wo: Laws.WFArray(String, d, o), +cell: {Laws.rdN(String, d, o, i) == Bool.pick(String, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.rd_at(String, A, i), Laws.rd_at(String, B, i)) : String},
  +w: U32, +ewm: {w == Laws.rd_at(U32, ma, i) : U32}, +ew2: {w == Laws.rd_at(U32, mb2, i) : U32})
  -> FRaw2(n, d, ma, xa, n2, d2, vb, xb, mb2, o, i):
  match vb:
    case C.AllValid{}:
      fill_raw_mk_av(n, d, ma, xa, n2, d2, xb, A, B, i, hi, fA, fB, mb2, o, cell, w, ewm, PST.rd_all(String, d, o, wo))
    case C.Mask{mbb}:
      fill_raw_mk_mk(n, d, ma, xa, n2, d2, mbb, xb, A, B, i, hi, fits, fA, fB, o, cell, w, ewm, (%Equal.sym(U32, w, Laws.rd_at(U32, ma, i), ewm) : {U32.is_le(_, 1) == True{} : Bool}; m01a), m01b, mb2, ew2, PST.rd_all(String, d, o, wo), PC.get_w(U32, mbb, i))

def fill_raw_mk0(+n: U32, +d: Nat, -ma: Array<U32>, -xa: ST.Strs, +n2: U32, +d2: Nat, vb: C.Valid, -xb: ST.Strs, -A: Array<String>, -B: Array<String>, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +m01a: {U32.is_le(Laws.rd_at(U32, ma, i), 1) == True{} : Bool}, m01b: Laws.Mask01(vb, i),
  fA: @j: U32 -> {U32.is_lt(j, n) == True{} : Bool} -> {Laws.rd_at(String, A, j) == Laws.scell(xa, j) : String}, fB: @j: U32 -> {U32.is_lt(j, n) == True{} : Bool} -> {Laws.rd_at(String, B, j) == Laws.scell(xb, j) : String},
  -mb: Array<U32>, o: Array<String>, wo: Laws.WFArray(String, d, o), +cell: {Laws.rdN(String, d, o, i) == Bool.pick(String, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.rd_at(String, A, i), Laws.rd_at(String, B, i)) : String},
  wr: MaskRead(ma, mb, i))
  -> FRaw2(n, d, ma, xa, n2, d2, vb, xb, mb, o, i):
  (mb2, +w, +emb2, +ewm, ew2) = wr
  %emb2 : FRaw2(n, d, ma, xa, n2, d2, vb, xb, _, o, i)
  fill_raw_mk1(n, d, ma, xa, n2, d2, vb, xb, A, B, i, hi, fits, m01a, m01b, fA, fB, mb2, o, wo, cell, w, ewm, ew2)

# the choose computed: its result pair replaces the call
def fill_raw_mk(+n: U32, +d: Nat, -ma: Array<U32>, -xa: ST.Strs, +n2: U32, +d2: Nat, vb: C.Valid, -xb: ST.Strs, -A: Array<String>, -B: Array<String>, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +m01a: {U32.is_le(Laws.rd_at(U32, ma, i), 1) == True{} : Bool}, m01b: Laws.Mask01(vb, i),
  fA: @j: U32 -> {U32.is_lt(j, n) == True{} : Bool} -> {Laws.rd_at(String, A, j) == Laws.scell(xa, j) : String}, fB: @j: U32 -> {U32.is_lt(j, n) == True{} : Bool} -> {Laws.rd_at(String, B, j) == Laws.scell(xb, j) : String},
  w: CHW(~String, n, d, ma, A, B, i))
  -> FRaw(n, d, C.Mask{ma}, xa, n2, d2, vb, xb, A, B, i):
  (mb, o, eq, +emb, wo, cell) = w
  %Equal.sym(Array<U32> & Array<String>, K.Kernel.choose(~String, n, ma, A, B), (mb, o), eq) : FRaw1(n, d, ma, xa, n2, d2, vb, xb, _, i)
  fill_raw_mk0(n, d, ma, xa, n2, d2, vb, xb, A, B, i, hi, fits, m01a, m01b, fA, fB, mb, o, wo, cell, mask_read(ma, mb, i, emb))

# the Raw branch: a valid everywhere is kept as it is (row i a's cell); a masked runs the choose
def fill_raw(+n: U32, +d: Nat, va: C.Valid, -xa: ST.Strs, +n2: U32, +d2: Nat, vb: C.Valid, -xb: ST.Strs, A: Array<String>, B: Array<String>, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, wfA: Laws.WFArray(String, d, A), m01a: Laws.Mask01(va, i), m01b: Laws.Mask01(vb, i),
  fA: @j: U32 -> {U32.is_lt(j, n) == True{} : Bool} -> {Laws.rd_at(String, A, j) == Laws.scell(xa, j) : String}, fB: @j: U32 -> {U32.is_lt(j, n) == True{} : Bool} -> {Laws.rd_at(String, B, j) == Laws.scell(xb, j) : String})
  -> FRaw(n, d, va, xa, n2, d2, vb, xb, A, B, i):
  match va:
    case C.AllValid{}:
      (C.CStr{n, d, C.AllValid{}, ST.SRaw{A}}, {==}, (%fA(i, hi) : {D.SStr{Laws.rd_at(String, A, i)} == D.SStr{_} : D.Scalar}; {==}))
    case C.Mask{ma}:
      fill_raw_mk(n, d, ma, xa, n2, d2, vb, xb, A, B, i, hi, fits, m01a, m01b, fA, fB, choose_w(~String, n, d, ma, A, B, i, wfA, fits, hi))

# the decodes computed: their arrays replace the calls
def fill_raw_dec(+n: U32, +d: Nat, va: C.Valid, -xa: ST.Strs, +n2: U32, +d2: Nat, vb: C.Valid, -xb: ST.Strs, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, m01a: Laws.Mask01(va, i), m01b: Laws.Mask01(vb, i), wa: DecodeWF(xa, n, d), wb: PA.DecodeW(xb, n, d))
  -> &c: C.Column -> {V.Eval.fill.s(n, d, V.Eval.fill.t(~String, n, d, va, vb, ST.Strs.decode(n, d, xa), ST.Strs.decode(n, d, xb))) == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, Laws.vbit(va, i), Laws.ccell(C.CStr{n, d, va, xa}, i), Laws.ccell(C.CStr{n2, d2, vb, xb}, i)) : D.Scalar}:
  (A, eA, wfA, fA) = wa
  (B, eB, fB) = wb
  %Equal.sym(Array<String>, ST.Strs.decode(n, d, xa), A, eA) : FRaw(n, d, va, xa, n2, d2, vb, xb, _, ST.Strs.decode(n, d, xb), i)
  %Equal.sym(Array<String>, ST.Strs.decode(n, d, xb), B, eB) : FRaw(n, d, va, xa, n2, d2, vb, xb, A, _, i)
  fill_raw(n, d, va, xa, n2, d2, vb, xb, A, B, i, hi, fits, wfA, m01a, m01b, fA, fB)

# ---- the Dictionary branch of fill_null ---------------------------------------------------------------------
#
# Two Dictionaries: b's entries are merged into a's (dict_merge_spec), b's codes re-coded through the
# map (Eval.zd.map = a gather), then Eval.fill.t chooses the codes of a (kept: Keep) and the re-coded
# ones (named by EncRows). The two row facts are prepared as Data equalities over the final arrays
# (KA: a's code at i keeps its entry in the extended dictionary; EB: the re-coded code at i names b's
# entry), reading the codes off clones (get_w) as in Strs.append's proof; the choose / validity part
# is the Raw branch's with these two facts in place of the decoded rows.

# a's row: a's code in the extended entry array is the old entry (through Keep)
def KA(-strs2: Array<String>, -ca1: Array<U32>, -dca: ST.Dict, -ca: Array<U32>, +i: U32) -> Type:
  {Laws.rd_at(String, strs2, Laws.rd_at(U32, ca1, i)) == Laws.dentry(dca, Laws.rd_at(U32, ca, i)) : String}

# b's row: the re-coded code in the extended entry array is b's entry
def EB(-strs2: Array<String>, -M: Array<U32>, -strsb: Array<String>, -cb: Array<U32>, +i: U32) -> Type:
  {Laws.rd_at(String, strs2, Laws.rd_at(U32, M, i)) == Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i)) : String}

# the pick algebra, b valid everywhere
def fd_pick_av(bw: Bool, -strs2: Array<String>, -ca1: Array<U32>, -M: Array<U32>, -dca: ST.Dict, -ca: Array<U32>, -strsb: Array<String>, -cb: Array<U32>, +i: U32, +w: U32, +eb: {U32.is_ne(w, 0) == bw : Bool}, ka: KA(strs2, ca1, dca, ca, i), ebb: EB(strs2, M, strsb, cb, i))
  -> {D.SStr{Laws.rd_at(String, strs2, Bool.pick(U32, U32.is_ne(w, 0), Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)))} == Bool.pick(D.Scalar, U32.is_ne(w, 0), Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}) : D.Scalar}:
  match bw:
    case True{}:
      %Equal.sym(Bool, U32.is_ne(w, 0), True{}, eb) : {D.SStr{Laws.rd_at(String, strs2, Bool.pick(U32, _, Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)))} == Bool.pick(D.Scalar, _, Bool.pick(D.Scalar, _, D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}) : D.Scalar}
      %Equal.sym(String, Laws.rd_at(String, strs2, Laws.rd_at(U32, ca1, i)), Laws.dentry(dca, Laws.rd_at(U32, ca, i)), ka) : {D.SStr{_} == D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))} : D.Scalar}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_ne(w, 0), False{}, eb) : {D.SStr{Laws.rd_at(String, strs2, Bool.pick(U32, _, Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)))} == Bool.pick(D.Scalar, _, Bool.pick(D.Scalar, _, D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}) : D.Scalar}
      %Equal.sym(String, Laws.rd_at(String, strs2, Laws.rd_at(U32, M, i)), Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i)), ebb) : {D.SStr{_} == D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))} : D.Scalar}
      {==}

# the pick algebra, both masked (w, wb in {0, 1})
def fd_pick_mk(cw: Bool, cwb: Bool, -strs2: Array<String>, -ca1: Array<U32>, -M: Array<U32>, -dca: ST.Dict, -ca: Array<U32>, -strsb: Array<String>, -cb: Array<U32>, +i: U32, +w: U32, +wb: U32, sw: PC.Bit01(cw, w), swb: PC.Bit01(cwb, wb), ka: KA(strs2, ca1, dca, ca, i), ebb: EB(strs2, M, strsb, cb, i))
  -> {Bool.pick(D.Scalar, U32.is_ne(U32.or(w, wb), 0), D.SStr{Laws.rd_at(String, strs2, Bool.pick(U32, U32.is_ne(w, 0), Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(w, 0), Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(wb, 0), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}, D.SNull{})) : D.Scalar}:
  match cw cwb:
    case True{} True{}:
      %Equal.sym(U32, w, 1, sw) : {Bool.pick(D.Scalar, U32.is_ne(U32.or(_, wb), 0), D.SStr{Laws.rd_at(String, strs2, Bool.pick(U32, U32.is_ne(_, 0), Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(_, 0), Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(wb, 0), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}, D.SNull{})) : D.Scalar}
      %Equal.sym(U32, wb, 1, swb) : {Bool.pick(D.Scalar, U32.is_ne(U32.or(1, _), 0), D.SStr{Laws.rd_at(String, strs2, Bool.pick(U32, U32.is_ne(1, 0), Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(1, 0), Bool.pick(D.Scalar, U32.is_ne(1, 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}, D.SNull{})) : D.Scalar}
      %Equal.sym(String, Laws.rd_at(String, strs2, Laws.rd_at(U32, ca1, i)), Laws.dentry(dca, Laws.rd_at(U32, ca, i)), ka) : {D.SStr{_} == D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))} : D.Scalar}
      {==}
    case True{} False{}:
      %Equal.sym(U32, w, 1, sw) : {Bool.pick(D.Scalar, U32.is_ne(U32.or(_, wb), 0), D.SStr{Laws.rd_at(String, strs2, Bool.pick(U32, U32.is_ne(_, 0), Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(_, 0), Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(wb, 0), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}, D.SNull{})) : D.Scalar}
      %Equal.sym(U32, wb, 0, swb) : {Bool.pick(D.Scalar, U32.is_ne(U32.or(1, _), 0), D.SStr{Laws.rd_at(String, strs2, Bool.pick(U32, U32.is_ne(1, 0), Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(1, 0), Bool.pick(D.Scalar, U32.is_ne(1, 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}, D.SNull{})) : D.Scalar}
      %Equal.sym(String, Laws.rd_at(String, strs2, Laws.rd_at(U32, ca1, i)), Laws.dentry(dca, Laws.rd_at(U32, ca, i)), ka) : {D.SStr{_} == D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))} : D.Scalar}
      {==}
    case False{} True{}:
      %Equal.sym(U32, w, 0, sw) : {Bool.pick(D.Scalar, U32.is_ne(U32.or(_, wb), 0), D.SStr{Laws.rd_at(String, strs2, Bool.pick(U32, U32.is_ne(_, 0), Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(_, 0), Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(wb, 0), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}, D.SNull{})) : D.Scalar}
      %Equal.sym(U32, wb, 1, swb) : {Bool.pick(D.Scalar, U32.is_ne(U32.or(0, _), 0), D.SStr{Laws.rd_at(String, strs2, Bool.pick(U32, U32.is_ne(0, 0), Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(0, 0), Bool.pick(D.Scalar, U32.is_ne(0, 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}, D.SNull{})) : D.Scalar}
      %Equal.sym(String, Laws.rd_at(String, strs2, Laws.rd_at(U32, M, i)), Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i)), ebb) : {D.SStr{_} == D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))} : D.Scalar}
      {==}
    case False{} False{}:
      %Equal.sym(U32, w, 0, sw) : {Bool.pick(D.Scalar, U32.is_ne(U32.or(_, wb), 0), D.SStr{Laws.rd_at(String, strs2, Bool.pick(U32, U32.is_ne(_, 0), Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(_, 0), Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(wb, 0), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}, D.SNull{})) : D.Scalar}
      %Equal.sym(U32, wb, 0, swb) : {Bool.pick(D.Scalar, U32.is_ne(U32.or(0, _), 0), D.SStr{Laws.rd_at(String, strs2, Bool.pick(U32, U32.is_ne(0, 0), Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(0, 0), Bool.pick(D.Scalar, U32.is_ne(0, 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}, D.SNull{})) : D.Scalar}
      {==}

def fd_pick_mk_k(-strs2: Array<String>, -ca1: Array<U32>, -M: Array<U32>, -dca: ST.Dict, -ca: Array<U32>, -strsb: Array<String>, -cb: Array<U32>, +i: U32, +w: U32, +wb: U32, w1: &cw: Bool -> PC.Bit01(cw, w), w2: &cwb: Bool -> PC.Bit01(cwb, wb), ka: KA(strs2, ca1, dca, ca, i), ebb: EB(strs2, M, strsb, cb, i))
  -> {Bool.pick(D.Scalar, U32.is_ne(U32.or(w, wb), 0), D.SStr{Laws.rd_at(String, strs2, Bool.pick(U32, U32.is_ne(w, 0), Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(w, 0), Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(wb, 0), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}, D.SNull{})) : D.Scalar}:
  (cw, sw) = w1
  (cwb, swb) = w2
  fd_pick_mk(cw, cwb, strs2, ca1, M, dca, ca, strsb, cb, i, w, wb, sw, swb, ka, ebb)

def fd_pick_mk_w(-strs2: Array<String>, -ca1: Array<U32>, -M: Array<U32>, -dca: ST.Dict, -ca: Array<U32>, -strsb: Array<String>, -cb: Array<U32>, +i: U32, +w: U32, +wb: U32, hw: {U32.is_le(w, 1) == True{} : Bool}, hwb: {U32.is_le(wb, 1) == True{} : Bool}, ka: KA(strs2, ca1, dca, ca, i), ebb: EB(strs2, M, strsb, cb, i))
  -> {Bool.pick(D.Scalar, U32.is_ne(U32.or(w, wb), 0), D.SStr{Laws.rd_at(String, strs2, Bool.pick(U32, U32.is_ne(w, 0), Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(w, 0), Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(wb, 0), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}, D.SNull{})) : D.Scalar}:
  fd_pick_mk_k(strs2, ca1, M, dca, ca, strsb, cb, i, w, wb, PC.le1_cases(w, hw), PC.le1_cases(wb, hwb), ka, ebb)


# the goal over a's codes copy ca1 and the re-coded codes M, the extended dictionary D = Dict{k2, ..}
def FDict(+n: U32, +d: Nat, -va: C.Valid, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, -vb: C.Valid, -cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, -ca1: Array<U32>, -M: Array<U32>, +k2: U32, +dd2: Nat, -strs2: Array<String>, +b2: Nat, -slots2: Array<ST.SSlot>, +tag2: U32, +i: U32) -> Type:
  &c: C.Column -> {V.Eval.fill.sd2(n, d, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}, V.Eval.fill.t(~U32, n, d, va, vb, ca1, M)) == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, Laws.vbit(va, i), Laws.ccell(C.CStr{n, d, va, ST.SDict{ca, dca}}, i), Laws.ccell(C.CStr{n2, d2, vb, ST.SDict{cb, ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}}}, i)) : D.Scalar}

# ... a masked, the choose's result pair r in place, then (mb, o)
def FDict1(+n: U32, +d: Nat, -ma: Array<U32>, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, -vb: C.Valid, -cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, -r: Array<U32> & Array<U32>, +k2: U32, +dd2: Nat, -strs2: Array<String>, +b2: Nat, -slots2: Array<ST.SSlot>, +tag2: U32, +i: U32) -> Type:
  &c: C.Column -> {V.Eval.fill.sd2(n, d, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}, V.Eval.fill.t2(~U32, n, d, vb, r)) == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.ccell(C.CStr{n, d, C.Mask{ma}, ST.SDict{ca, dca}}, i), Laws.ccell(C.CStr{n2, d2, vb, ST.SDict{cb, ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}}}, i)) : D.Scalar}

def FDict2(+n: U32, +d: Nat, -ma: Array<U32>, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, -vb: C.Valid, -cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, -mb: Array<U32>, -o: Array<U32>, +k2: U32, +dd2: Nat, -strs2: Array<String>, +b2: Nat, -slots2: Array<ST.SSlot>, +tag2: U32, +i: U32) -> Type:
  &c: C.Column -> {V.Eval.fill.sd2(n, d, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}, V.Eval.fill.t2(~U32, n, d, vb, (mb, o))) == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.ccell(C.CStr{n, d, C.Mask{ma}, ST.SDict{ca, dca}}, i), Laws.ccell(C.CStr{n2, d2, vb, ST.SDict{cb, ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}}}, i)) : D.Scalar}

# a masked, b valid everywhere
def fd_mk_av(+n: U32, +d: Nat, -ma: Array<U32>, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, -cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, -ca1: Array<U32>, -M: Array<U32>, +k2: U32, +dd2: Nat, strs2: Array<String>, +b2: Nat, slots2: Array<ST.SSlot>, +tag2: U32, +i: U32,
  ka: KA(strs2, ca1, dca, ca, i), ebb: EB(strs2, M, strsb, cb, i),
  -mb: Array<U32>, -o: Array<U32>, +cell: {Laws.rdN(U32, d, o, i) == Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)) : U32},
  +w: U32, +ewm: {w == Laws.rd_at(U32, ma, i) : U32},
  wo2: &o2: Array<U32> -> {o2 == o : Array<U32>} & Laws.WFArray(U32, d, o2) & (@k: U32 -> {Laws.rd_at(U32, o, k) == Laws.rdN(U32, d, o, k) : U32}))
  -> FDict2(n, d, ma, ca, dca, n2, d2, C.AllValid{}, cb, kb, ddb, strsb, bb, slotsb, tagb, mb, o, k2, dd2, strs2, b2, slots2, tag2, i):
  (o2, +eo2, wo3, cv) = wo2
  (C.CStr{n, d, C.AllValid{}, ST.SDict{o2, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}}}, (%Equal.sym(Array<U32>, o2, o, eo2) : {V.Eval.fill.sd2(n, d, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}, V.Eval.fill.t2(~U32, n, d, C.AllValid{}, (mb, o))) == Done{C.CStr{n, d, C.AllValid{}, ST.SDict{_, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}}}} : E.ResT(C.Column)}; {==}),
    (%Equal.sym(Array<U32>, o2, o, eo2) : {D.SStr{Laws.rd_at(String, strs2, Laws.rd_at(U32, _, i))} == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}) : D.Scalar};
     %Equal.sym(U32, Laws.rd_at(U32, o, i), Laws.rdN(U32, d, o, i), cv(i)) : {D.SStr{Laws.rd_at(String, strs2, _)} == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}) : D.Scalar};
     %Equal.sym(U32, Laws.rdN(U32, d, o, i), Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)), cell) : {D.SStr{Laws.rd_at(String, strs2, _)} == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}) : D.Scalar};
     %ewm : {D.SStr{Laws.rd_at(String, strs2, Bool.pick(U32, U32.is_ne(_, 0), Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)))} == Bool.pick(D.Scalar, U32.is_ne(_, 0), Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}) : D.Scalar};
     fd_pick_av(U32.is_ne(w, 0), strs2, ca1, M, dca, ca, strsb, cb, i, w, {==}, ka, ebb)))

# a masked, b masked
def fd_mk_mk3(+n: U32, +d: Nat, -ma: Array<U32>, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, -mbb: Array<U32>, -cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, -ca1: Array<U32>, -M: Array<U32>, +k2: U32, +dd2: Nat, strs2: Array<String>, +b2: Nat, slots2: Array<ST.SSlot>, +tag2: U32, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool},
  ka: KA(strs2, ca1, dca, ca, i), ebb: EB(strs2, M, strsb, cb, i),
  -o: Array<U32>, +cell: {Laws.rdN(U32, d, o, i) == Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)) : U32},
  +w: U32, +ewm: {w == Laws.rd_at(U32, ma, i) : U32}, +hw: {U32.is_le(w, 1) == True{} : Bool}, +wb: U32, +ewb: {wb == Laws.rd_at(U32, mbb, i) : U32}, +hwb: {U32.is_le(wb, 1) == True{} : Bool},
  mb3: Array<U32>, mb4: Array<U32>, mbb3: Array<U32>, mbb4: Array<U32>, +e43: {mb4 == mb3 : Array<U32>}, +eb43: {mbb4 == mbb3 : Array<U32>}, +ew4: {w == Laws.rd_at(U32, mb4, i) : U32}, +ewb4: {wb == Laws.rd_at(U32, mbb4, i) : U32},
  wo2: &o2: Array<U32> -> {o2 == o : Array<U32>} & Laws.WFArray(U32, d, o2) & (@k: U32 -> {Laws.rd_at(U32, o, k) == Laws.rdN(U32, d, o, k) : U32}))
  -> &c: C.Column -> {Done{C.CStr{n, d, C.Mask{K.Kernel.mask_or(n, d, mb3, mbb3)}, ST.SDict{o, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}}}} == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.ccell(C.CStr{n, d, C.Mask{ma}, ST.SDict{ca, dca}}, i), Laws.ccell(C.CStr{n2, d2, C.Mask{mbb}, ST.SDict{cb, ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}}}, i)) : D.Scalar}:
  (o2, +eo2, wo3, cv) = wo2
  (C.CStr{n, d, C.Mask{K.Kernel.mask_or(n, d, mb3, mbb3)}, ST.SDict{o2, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}}}, (%Equal.sym(Array<U32>, o2, o, eo2) : {Done{C.CStr{n, d, C.Mask{K.Kernel.mask_or(n, d, mb3, mbb3)}, ST.SDict{o, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}}}} == Done{C.CStr{n, d, C.Mask{K.Kernel.mask_or(n, d, mb3, mbb3)}, ST.SDict{_, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}}}} : E.ResT(C.Column)}; {==}),
    (%e43 : {Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, K.Kernel.mask_or(n, d, _, mbb3), i), 0), D.SStr{Laws.rd_at(String, strs2, Laws.rd_at(U32, o2, i))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mbb, i), 0), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}, D.SNull{})) : D.Scalar};
     %eb43 : {Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, K.Kernel.mask_or(n, d, mb4, _), i), 0), D.SStr{Laws.rd_at(String, strs2, Laws.rd_at(U32, o2, i))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mbb, i), 0), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}, D.SNull{})) : D.Scalar};
     %Equal.sym(U32, Laws.rd_at(U32, K.Kernel.mask_or(n, d, mb4, mbb4), i), U32.or(Laws.rd_at(U32, mb4, i), Laws.rd_at(U32, mbb4, i)), Laws.mask_or_cell(d, n, mb4, mbb4, i, fits, hi)) : {Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.rd_at(String, strs2, Laws.rd_at(U32, o2, i))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mbb, i), 0), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}, D.SNull{})) : D.Scalar};
     %ew4 : {Bool.pick(D.Scalar, U32.is_ne(U32.or(_, Laws.rd_at(U32, mbb4, i)), 0), D.SStr{Laws.rd_at(String, strs2, Laws.rd_at(U32, o2, i))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mbb, i), 0), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}, D.SNull{})) : D.Scalar};
     %ewb4 : {Bool.pick(D.Scalar, U32.is_ne(U32.or(w, _), 0), D.SStr{Laws.rd_at(String, strs2, Laws.rd_at(U32, o2, i))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mbb, i), 0), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}, D.SNull{})) : D.Scalar};
     %Equal.sym(Array<U32>, o2, o, eo2) : {Bool.pick(D.Scalar, U32.is_ne(U32.or(w, wb), 0), D.SStr{Laws.rd_at(String, strs2, Laws.rd_at(U32, _, i))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mbb, i), 0), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}, D.SNull{})) : D.Scalar};
     %Equal.sym(U32, Laws.rd_at(U32, o, i), Laws.rdN(U32, d, o, i), cv(i)) : {Bool.pick(D.Scalar, U32.is_ne(U32.or(w, wb), 0), D.SStr{Laws.rd_at(String, strs2, _)}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mbb, i), 0), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}, D.SNull{})) : D.Scalar};
     %Equal.sym(U32, Laws.rdN(U32, d, o, i), Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)), cell) : {Bool.pick(D.Scalar, U32.is_ne(U32.or(w, wb), 0), D.SStr{Laws.rd_at(String, strs2, _)}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mbb, i), 0), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}, D.SNull{})) : D.Scalar};
     %ewm : {Bool.pick(D.Scalar, U32.is_ne(U32.or(w, wb), 0), D.SStr{Laws.rd_at(String, strs2, Bool.pick(U32, U32.is_ne(_, 0), Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(_, 0), Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, mbb, i), 0), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}, D.SNull{})) : D.Scalar};
     %ewb : {Bool.pick(D.Scalar, U32.is_ne(U32.or(w, wb), 0), D.SStr{Laws.rd_at(String, strs2, Bool.pick(U32, U32.is_ne(w, 0), Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)))}, D.SNull{}) == Bool.pick(D.Scalar, U32.is_ne(w, 0), Bool.pick(D.Scalar, U32.is_ne(w, 0), D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))}, D.SNull{}), Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i))}, D.SNull{})) : D.Scalar};
     fd_pick_mk_w(strs2, ca1, M, dca, ca, strsb, cb, i, w, wb, hw, hwb, ka, ebb)))

def fd_mk_mk2(+n: U32, +d: Nat, -ma: Array<U32>, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, -mbb: Array<U32>, -cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, -ca1: Array<U32>, -M: Array<U32>, +k2: U32, +dd2: Nat, strs2: Array<String>, +b2: Nat, slots2: Array<ST.SSlot>, +tag2: U32, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool},
  ka: KA(strs2, ca1, dca, ca, i), ebb: EB(strs2, M, strsb, cb, i),
  -o: Array<U32>, +cell: {Laws.rdN(U32, d, o, i) == Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)) : U32},
  +w: U32, +ewm: {w == Laws.rd_at(U32, ma, i) : U32}, +hw: {U32.is_le(w, 1) == True{} : Bool}, +wb: U32, +ewb: {wb == Laws.rd_at(U32, mbb, i) : U32}, +hwb: {U32.is_le(wb, 1) == True{} : Bool},
  -mb2: Array<U32>, -mbb2: Array<U32>, +ew2: {w == Laws.rd_at(U32, mb2, i) : U32}, +ewb2: {wb == Laws.rd_at(U32, mbb2, i) : U32},
  wo2: &o2: Array<U32> -> {o2 == o : Array<U32>} & Laws.WFArray(U32, d, o2) & (@k: U32 -> {Laws.rd_at(U32, o, k) == Laws.rdN(U32, d, o, k) : U32}),
  wm: &mb3: Array<U32> -> &mb4: Array<U32> -> {mb3 == mb2 : Array<U32>} & {mb4 == mb2 : Array<U32>},
  wmb: &mbb3: Array<U32> -> &mbb4: Array<U32> -> {mbb3 == mbb2 : Array<U32>} & {mbb4 == mbb2 : Array<U32>})
  -> &c: C.Column -> {Done{C.CStr{n, d, C.Mask{K.Kernel.mask_or(n, d, mb2, mbb2)}, ST.SDict{o, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}}}} == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.ccell(C.CStr{n, d, C.Mask{ma}, ST.SDict{ca, dca}}, i), Laws.ccell(C.CStr{n2, d2, C.Mask{mbb}, ST.SDict{cb, ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}}}, i)) : D.Scalar}:
  (mb3, mb4, +e3, +e4) = wm
  (mbb3, mbb4, +eb3, +eb4) = wmb
  %e3 : &c: C.Column -> {Done{C.CStr{n, d, C.Mask{K.Kernel.mask_or(n, d, _, mbb2)}, ST.SDict{o, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}}}} == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.ccell(C.CStr{n, d, C.Mask{ma}, ST.SDict{ca, dca}}, i), Laws.ccell(C.CStr{n2, d2, C.Mask{mbb}, ST.SDict{cb, ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}}}, i)) : D.Scalar}
  %eb3 : &c: C.Column -> {Done{C.CStr{n, d, C.Mask{K.Kernel.mask_or(n, d, mb3, _)}, ST.SDict{o, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}}}} == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.ccell(C.CStr{n, d, C.Mask{ma}, ST.SDict{ca, dca}}, i), Laws.ccell(C.CStr{n2, d2, C.Mask{mbb}, ST.SDict{cb, ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}}}, i)) : D.Scalar}
  fd_mk_mk3(n, d, ma, ca, dca, n2, d2, mbb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, M, k2, dd2, strs2, b2, slots2, tag2, i, hi, fits, ka, ebb, o, cell, w, ewm, hw, wb, ewb, hwb, mb3, mb4, mbb3, mbb4, Equal.trans(Array<U32>, mb4, mb2, mb3, e4, Equal.sym(Array<U32>, mb3, mb2, e3)), Equal.trans(Array<U32>, mbb4, mbb2, mbb3, eb4, Equal.sym(Array<U32>, mbb3, mbb2, eb3)), Equal.trans(U32, w, Laws.rd_at(U32, mb2, i), Laws.rd_at(U32, mb4, i), ew2, Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, i), mb2, mb4, Equal.sym(Array<U32>, mb4, mb2, e4))), Equal.trans(U32, wb, Laws.rd_at(U32, mbb2, i), Laws.rd_at(U32, mbb4, i), ewb2, Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, i), mbb2, mbb4, Equal.sym(Array<U32>, mbb4, mbb2, eb4))), wo2)

def fd_mk_mk1(+n: U32, +d: Nat, -ma: Array<U32>, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, -mbb: Array<U32>, -cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, -ca1: Array<U32>, -M: Array<U32>, +k2: U32, +dd2: Nat, strs2: Array<String>, +b2: Nat, slots2: Array<ST.SSlot>, +tag2: U32, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool},
  ka: KA(strs2, ca1, dca, ca, i), ebb: EB(strs2, M, strsb, cb, i),
  -o: Array<U32>, +cell: {Laws.rdN(U32, d, o, i) == Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)) : U32},
  +w: U32, +ewm: {w == Laws.rd_at(U32, ma, i) : U32}, +hw: {U32.is_le(w, 1) == True{} : Bool}, +wb: U32, +ewb: {wb == Laws.rd_at(U32, mbb, i) : U32}, +hwb0: {U32.is_le(Laws.rd_at(U32, mbb, i), 1) == True{} : Bool},
  mb2: Array<U32>, mbb2: Array<U32>, +ew2: {w == Laws.rd_at(U32, mb2, i) : U32}, +embb2: {mbb2 == mbb : Array<U32>},
  wo2: &o2: Array<U32> -> {o2 == o : Array<U32>} & Laws.WFArray(U32, d, o2) & (@k: U32 -> {Laws.rd_at(U32, o, k) == Laws.rdN(U32, d, o, k) : U32}))
  -> &c: C.Column -> {Done{C.CStr{n, d, C.Mask{K.Kernel.mask_or(n, d, mb2, mbb2)}, ST.SDict{o, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}}}} == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.ccell(C.CStr{n, d, C.Mask{ma}, ST.SDict{ca, dca}}, i), Laws.ccell(C.CStr{n2, d2, C.Mask{mbb}, ST.SDict{cb, ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}}}, i)) : D.Scalar}:
  fd_mk_mk2(n, d, ma, ca, dca, n2, d2, mbb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, M, k2, dd2, strs2, b2, slots2, tag2, i, hi, fits, ka, ebb, o, cell, w, ewm, hw, wb, ewb, (%Equal.sym(U32, wb, Laws.rd_at(U32, mbb, i), ewb) : {U32.is_le(_, 1) == True{} : Bool}; hwb0), mb2, mbb2, ew2, Equal.trans(U32, wb, Laws.rd_at(U32, mbb, i), Laws.rd_at(U32, mbb2, i), ewb, Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, i), mbb, mbb2, Equal.sym(Array<U32>, mbb2, mbb, embb2))), wo2, PC.clone_eq(U32, mb2), PC.clone_eq(U32, mbb2))

def fd_mk_mk(+n: U32, +d: Nat, -ma: Array<U32>, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, -mbb: Array<U32>, -cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, -ca1: Array<U32>, -M: Array<U32>, +k2: U32, +dd2: Nat, strs2: Array<String>, +b2: Nat, slots2: Array<ST.SSlot>, +tag2: U32, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool},
  ka: KA(strs2, ca1, dca, ca, i), ebb: EB(strs2, M, strsb, cb, i),
  -o: Array<U32>, +cell: {Laws.rdN(U32, d, o, i) == Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)) : U32},
  +w: U32, +ewm: {w == Laws.rd_at(U32, ma, i) : U32}, +hw: {U32.is_le(w, 1) == True{} : Bool}, +hwb0: {U32.is_le(Laws.rd_at(U32, mbb, i), 1) == True{} : Bool},
  mb2: Array<U32>, +ew2: {w == Laws.rd_at(U32, mb2, i) : U32},
  wo2: &o2: Array<U32> -> {o2 == o : Array<U32>} & Laws.WFArray(U32, d, o2) & (@k: U32 -> {Laws.rd_at(U32, o, k) == Laws.rdN(U32, d, o, k) : U32}),
  wb: &mbb2: Array<U32> -> &wbv: U32 -> {mbb2 == mbb : Array<U32>} & {Array.get(U32, mbb, i) == (mbb, wbv) : Array<U32> & U32} & {wbv == Laws.rd_at(U32, mbb, i) : U32})
  -> FDict2(n, d, ma, ca, dca, n2, d2, C.Mask{mbb}, cb, kb, ddb, strsb, bb, slotsb, tagb, mb2, o, k2, dd2, strs2, b2, slots2, tag2, i):
  (mbb2, +wbv, +embb2, e1, ewbv) = wb
  %embb2 : &c: C.Column -> {Done{C.CStr{n, d, C.Mask{K.Kernel.mask_or(n, d, mb2, _)}, ST.SDict{o, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}}}} == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.ccell(C.CStr{n, d, C.Mask{ma}, ST.SDict{ca, dca}}, i), Laws.ccell(C.CStr{n2, d2, C.Mask{mbb}, ST.SDict{cb, ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}}}, i)) : D.Scalar}
  fd_mk_mk1(n, d, ma, ca, dca, n2, d2, mbb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, M, k2, dd2, strs2, b2, slots2, tag2, i, hi, fits, ka, ebb, o, cell, w, ewm, hw, wbv, ewbv, hwb0, mb2, mbb2, ew2, embb2, wo2)

def fd_mk1(+n: U32, +d: Nat, -ma: Array<U32>, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, vb: C.Valid, -cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, -ca1: Array<U32>, -M: Array<U32>, +k2: U32, +dd2: Nat, strs2: Array<String>, +b2: Nat, slots2: Array<ST.SSlot>, +tag2: U32, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +m01a: {U32.is_le(Laws.rd_at(U32, ma, i), 1) == True{} : Bool}, m01b: Laws.Mask01(vb, i),
  ka: KA(strs2, ca1, dca, ca, i), ebb: EB(strs2, M, strsb, cb, i),
  mb2: Array<U32>, o: Array<U32>, wo: Laws.WFArray(U32, d, o), +cell: {Laws.rdN(U32, d, o, i) == Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)) : U32},
  +w: U32, +ewm: {w == Laws.rd_at(U32, ma, i) : U32}, +ew2: {w == Laws.rd_at(U32, mb2, i) : U32})
  -> FDict2(n, d, ma, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, mb2, o, k2, dd2, strs2, b2, slots2, tag2, i):
  match vb:
    case C.AllValid{}:
      fd_mk_av(n, d, ma, ca, dca, n2, d2, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, M, k2, dd2, strs2, b2, slots2, tag2, i, ka, ebb, mb2, o, cell, w, ewm, PST.rd_all(U32, d, o, wo))
    case C.Mask{mbb}:
      fd_mk_mk(n, d, ma, ca, dca, n2, d2, mbb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, M, k2, dd2, strs2, b2, slots2, tag2, i, hi, fits, ka, ebb, o, cell, w, ewm, (%Equal.sym(U32, w, Laws.rd_at(U32, ma, i), ewm) : {U32.is_le(_, 1) == True{} : Bool}; m01a), m01b, mb2, ew2, PST.rd_all(U32, d, o, wo), PC.get_w(U32, mbb, i))

def fd_mk0(+n: U32, +d: Nat, -ma: Array<U32>, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, vb: C.Valid, -cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, -ca1: Array<U32>, -M: Array<U32>, +k2: U32, +dd2: Nat, strs2: Array<String>, +b2: Nat, slots2: Array<ST.SSlot>, +tag2: U32, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +m01a: {U32.is_le(Laws.rd_at(U32, ma, i), 1) == True{} : Bool}, m01b: Laws.Mask01(vb, i),
  ka: KA(strs2, ca1, dca, ca, i), ebb: EB(strs2, M, strsb, cb, i),
  -mb: Array<U32>, o: Array<U32>, wo: Laws.WFArray(U32, d, o), +cell: {Laws.rdN(U32, d, o, i) == Bool.pick(U32, U32.is_ne(Laws.rd_at(U32, ma, i), 0), Laws.rd_at(U32, ca1, i), Laws.rd_at(U32, M, i)) : U32},
  wr: MaskRead(ma, mb, i))
  -> FDict2(n, d, ma, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, mb, o, k2, dd2, strs2, b2, slots2, tag2, i):
  (mb2, +w, +emb2, +ewm, ew2) = wr
  %emb2 : FDict2(n, d, ma, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, _, o, k2, dd2, strs2, b2, slots2, tag2, i)
  fd_mk1(n, d, ma, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, M, k2, dd2, strs2, b2, slots2, tag2, i, hi, fits, m01a, m01b, ka, ebb, mb2, o, wo, cell, w, ewm, ew2)

def fd_mk(+n: U32, +d: Nat, -ma: Array<U32>, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, vb: C.Valid, -cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, -ca1: Array<U32>, -M: Array<U32>, +k2: U32, +dd2: Nat, strs2: Array<String>, +b2: Nat, slots2: Array<ST.SSlot>, +tag2: U32, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +m01a: {U32.is_le(Laws.rd_at(U32, ma, i), 1) == True{} : Bool}, m01b: Laws.Mask01(vb, i),
  ka: KA(strs2, ca1, dca, ca, i), ebb: EB(strs2, M, strsb, cb, i),
  w: CHW(~U32, n, d, ma, ca1, M, i))
  -> FDict(n, d, C.Mask{ma}, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, M, k2, dd2, strs2, b2, slots2, tag2, i):
  (mb, o, eq, +emb, wo, cell) = w
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.choose(~U32, n, ma, ca1, M), (mb, o), eq) : FDict1(n, d, ma, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, _, k2, dd2, strs2, b2, slots2, tag2, i)
  fd_mk0(n, d, ma, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, M, k2, dd2, strs2, b2, slots2, tag2, i, hi, fits, m01a, m01b, ka, ebb, mb, o, wo, cell, mask_read(ma, mb, i, emb))

# the core: a valid everywhere keeps its codes (Keep), a masked runs the choose
def fd_core(+n: U32, +d: Nat, va: C.Valid, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, vb: C.Valid, -cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, ca1: Array<U32>, M: Array<U32>, +k2: U32, +dd2: Nat, strs2: Array<String>, +b2: Nat, slots2: Array<ST.SSlot>, +tag2: U32, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, wf1: Laws.WFArray(U32, d, ca1), m01a: Laws.Mask01(va, i), m01b: Laws.Mask01(vb, i),
  ka: KA(strs2, ca1, dca, ca, i), ebb: EB(strs2, M, strsb, cb, i))
  -> FDict(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, M, k2, dd2, strs2, b2, slots2, tag2, i):
  match va:
    case C.AllValid{}:
      (C.CStr{n, d, C.AllValid{}, ST.SDict{ca1, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}}}, {==}, (%Equal.sym(String, Laws.rd_at(String, strs2, Laws.rd_at(U32, ca1, i)), Laws.dentry(dca, Laws.rd_at(U32, ca, i)), ka) : {D.SStr{_} == D.SStr{Laws.dentry(dca, Laws.rd_at(U32, ca, i))} : D.Scalar}; {==}))
    case C.Mask{ma}:
      fd_mk(n, d, ma, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, M, k2, dd2, strs2, b2, slots2, tag2, i, hi, fits, m01a, m01b, ka, ebb, choose_w(~U32, n, d, ma, ca1, M, i, wf1, fits, hi))

# ---- the preamble: merge, the codes and the map read as Data, the gather ------------------------------------

# the goal before the gather: the map copy mp and b's codes copy cbp in the production term
def FDP(+n: U32, +d: Nat, -va: C.Valid, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, -vb: C.Valid, -cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, -ca1: Array<U32>, -mp: Array<U32>, -cbp: Array<U32>, -dst2: ST.Dict, +i: U32) -> Type:
  &c: C.Column -> {V.Eval.fill.sd2(n, d, dst2, V.Eval.fill.t(~U32, n, d, va, vb, ca1, V.Eval.zd.map(n, d, mp, cbp))) == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, Laws.vbit(va, i), Laws.ccell(C.CStr{n, d, va, ST.SDict{ca, dca}}, i), Laws.ccell(C.CStr{n2, d2, vb, ST.SDict{cb, ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}}}, i)) : D.Scalar}

# ... the gather's result pair in place
def FDP2(+n: U32, +d: Nat, -va: C.Valid, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, -vb: C.Valid, -cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, -ca1: Array<U32>, -r: Array<U32> & Array<U32>, -dst2: ST.Dict, +i: U32) -> Type:
  &c: C.Column -> {V.Eval.fill.sd2(n, d, dst2, V.Eval.fill.t(~U32, n, d, va, vb, ca1, V.Eval.zd.snd(r))) == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, Laws.vbit(va, i), Laws.ccell(C.CStr{n, d, va, ST.SDict{ca, dca}}, i), Laws.ccell(C.CStr{n2, d2, vb, ST.SDict{cb, ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}}}, i)) : D.Scalar}

# ... the re-coded array M in place
def FDP3(+n: U32, +d: Nat, -va: C.Valid, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, -vb: C.Valid, -cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, -ca1: Array<U32>, -M: Array<U32>, -dst2: ST.Dict, +i: U32) -> Type:
  &c: C.Column -> {V.Eval.fill.sd2(n, d, dst2, V.Eval.fill.t(~U32, n, d, va, vb, ca1, M)) == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, Laws.vbit(va, i), Laws.ccell(C.CStr{n, d, va, ST.SDict{ca, dca}}, i), Laws.ccell(C.CStr{n2, d2, vb, ST.SDict{cb, ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}}}, i)) : D.Scalar}

# EB from the chain: M's row i is the map's slot at b's code (the gather), which names b's entry
# (EncRows) in the extended entry array (WFDictE's entry clause)
def fd_eb(+kb: U32, +ddb: Nat, -strsb: Array<String>, -cb: Array<U32>, -cbp: Array<U32>, +k2: U32, -strs2: Array<String>, +es2: List<&2, String>, +n: U32, +d: Nat, -M: Array<U32>, -M2: Array<U32>, -m: Array<U32>, -mp: Array<U32>, +eM2: {M2 == M : Array<U32>}, +emp: {mp == m : Array<U32>}, +ecbp: {cbp == cb : Array<U32>}, +ek2: {U32.to_nat(k2) == List.length(&2, String, es2) : Nat}, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool},
  +c: U32, +ec: {c == Laws.rd_at(U32, cb, i) : U32}, +code: U32, +ecode: {code == Laws.rd_at(U32, m, c) : U32},
  cvM: @j: U32 -> {Laws.rd_at(U32, M, j) == Laws.rdN(U32, d, M, j) : U32},
  spec: @j: U32 -> {U32.is_lt(j, n) == True{} : Bool} -> {Laws.rdN(U32, d, M, j) == Laws.rd_at(U32, mp, Laws.rd_at(U32, cbp, j)) : U32},
  cvm: @j: U32 -> {Laws.rd_at(U32, m, j) == Laws.rdN(U32, ddb, m, j) : U32},
  rows: Laws.EncRows(kb, ddb, strsb, m, es2), hc: {U32.is_lt(Laws.rd_at(U32, cb, i), kb) == True{} : Bool},
  ent: @c2: U32 -> {U32.is_lt(c2, k2) == True{} : Bool} -> {Laws.rd_at(String, strs2, c2) == Laws.nthd(es2, c2) : String})
  -> EB(strs2, M2, strsb, cb, i):
  %Equal.sym(U32, Laws.rd_at(U32, M2, i), code, Equal.trans(U32, Laws.rd_at(U32, M2, i), Laws.rd_at(U32, M, i), code, Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, i), M2, M, eM2),
    Equal.trans(U32, Laws.rd_at(U32, M, i), Laws.rdN(U32, d, M, i), code, cvM(i),
      Equal.trans(U32, Laws.rdN(U32, d, M, i), Laws.rd_at(U32, mp, Laws.rd_at(U32, cbp, i)), code, spec(i, hi),
        Equal.trans(U32, Laws.rd_at(U32, mp, Laws.rd_at(U32, cbp, i)), Laws.rd_at(U32, m, c), code, Equal.trans(U32, Laws.rd_at(U32, mp, Laws.rd_at(U32, cbp, i)), Laws.rd_at(U32, m, Laws.rd_at(U32, cbp, i)), Laws.rd_at(U32, m, c), Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, Laws.rd_at(U32, cbp, i)), mp, m, emp), Equal.cong(U32, U32, q => Laws.rd_at(U32, m, q), Laws.rd_at(U32, cbp, i), c, Equal.trans(U32, Laws.rd_at(U32, cbp, i), Laws.rd_at(U32, cb, i), c, Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, i), cbp, cb, ecbp), Equal.sym(U32, c, Laws.rd_at(U32, cb, i), ec)))), Equal.sym(U32, code, Laws.rd_at(U32, m, c), ecode)))))) : {Laws.rd_at(String, strs2, _) == Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, i)) : String}
  %ec : {Laws.rd_at(String, strs2, code) == Laws.rd_at(String, strsb, _) : String}
  PA.sapp_right_fin(kb, ddb, strsb, k2, strs2, es2, ek2, c, code, ent, rows(c, (%Equal.sym(U32, c, Laws.rd_at(U32, cb, i), ec) : {U32.is_lt(_, kb) == True{} : Bool}; hc), code, Equal.trans(U32, code, Laws.rd_at(U32, m, c), Laws.rdN(U32, ddb, m, c), ecode, cvm(c))))

# KA from Keep at a's code c (Data): the extended dictionary keeps the old codes' entries
def fd_ka(-strs2: Array<String>, +k2: U32, +dd2: Nat, +b2: Nat, -slots2: Array<ST.SSlot>, +tag2: U32, -ca1: Array<U32>, -dca: ST.Dict, -ca: Array<U32>, +i: U32, +c: U32, +ec: {c == Laws.rd_at(U32, ca, i) : U32}, +ec1: {c == Laws.rd_at(U32, ca1, i) : U32}, hc: {U32.is_lt(Laws.rd_at(U32, ca, i), Laws.dk(dca)) == True{} : Bool},
  keep: @c2: U32 -> {U32.is_lt(c2, Laws.dk(dca)) == True{} : Bool} -> {Laws.dentry(ST.Dict{k2, dd2, strs2, b2, slots2, tag2}, c2) == Laws.dentry(dca, c2) : String})
  -> KA(strs2, ca1, dca, ca, i):
  %ec1 : {Laws.rd_at(String, strs2, _) == Laws.dentry(dca, Laws.rd_at(U32, ca, i)) : String}
  %ec : {Laws.rd_at(String, strs2, c) == Laws.dentry(dca, _) : String}
  keep(c, (%Equal.sym(U32, c, Laws.rd_at(U32, ca, i), ec) : {U32.is_lt(_, Laws.dk(dca)) == True{} : Bool}; hc))

def fd_pre9(+n: U32, +d: Nat, va: C.Valid, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, vb: C.Valid, -cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, ca1: Array<U32>, -M: Array<U32>, -cbp: Array<U32>, -m: Array<U32>, -mp: Array<U32>, +k2: U32, +dd2: Nat, strs2: Array<String>, +b2: Nat, slots2: Array<ST.SSlot>, +tag2: U32, +es2: List<&2, String>, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, wf1: Laws.WFArray(U32, d, ca1), m01a: Laws.Mask01(va, i), m01b: Laws.Mask01(vb, i),
  +emp: {mp == m : Array<U32>}, +ecbp: {cbp == cb : Array<U32>}, +ca_c: U32, +eca: {ca_c == Laws.rd_at(U32, ca, i) : U32}, +eca1: {ca_c == Laws.rd_at(U32, ca1, i) : U32}, hca: {U32.is_lt(Laws.rd_at(U32, ca, i), Laws.dk(dca)) == True{} : Bool},
  +c: U32, +ec: {c == Laws.rd_at(U32, cb, i) : U32}, +code: U32, +ecode: {code == Laws.rd_at(U32, m, c) : U32}, hc: {U32.is_lt(Laws.rd_at(U32, cb, i), kb) == True{} : Bool},
  spec: @j: U32 -> {U32.is_lt(j, n) == True{} : Bool} -> {Laws.rdN(U32, d, M, j) == Laws.rd_at(U32, mp, Laws.rd_at(U32, cbp, j)) : U32},
  cvm: @j: U32 -> {Laws.rd_at(U32, m, j) == Laws.rdN(U32, ddb, m, j) : U32},
  wf2: Laws.WFDictE(ST.Dict{k2, dd2, strs2, b2, slots2, tag2}, es2), keep: @c2: U32 -> {U32.is_lt(c2, Laws.dk(dca)) == True{} : Bool} -> {Laws.dentry(ST.Dict{k2, dd2, strs2, b2, slots2, tag2}, c2) == Laws.dentry(dca, c2) : String}, rows: Laws.EncRows(kb, ddb, strsb, m, es2),
  w: &M2: Array<U32> -> {M2 == M : Array<U32>} & Laws.WFArray(U32, d, M2) & (@j: U32 -> {Laws.rd_at(U32, M, j) == Laws.rdN(U32, d, M, j) : U32}))
  -> FDP3(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, M, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}, i):
  (+ek2, hle2, hpos2, h02, wfs2, ent, wfix2) = wf2
  (M2, +eM2, wM2, cvM) = w
  %eM2 : FDP3(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, _, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}, i)
  fd_core(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, M2, k2, dd2, strs2, b2, slots2, tag2, i, hi, fits, wf1, m01a, m01b, fd_ka(strs2, k2, dd2, b2, slots2, tag2, ca1, dca, ca, i, ca_c, eca, eca1, hca, keep), fd_eb(kb, ddb, strsb, cb, cbp, k2, strs2, es2, n, d, M, M2, m, mp, eM2, emp, ecbp, ek2, i, hi, c, ec, code, ecode, cvM, spec, cvm, rows, hc, ent))

# the extended dictionary taken apart (its entry clause); the gather's output read back (rd_all);
# EB and KA assembled; the core
def fd_pre8(+n: U32, +d: Nat, va: C.Valid, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, vb: C.Valid, -cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, ca1: Array<U32>, M: Array<U32>, -cbp: Array<U32>, -m: Array<U32>, -mp: Array<U32>, dst2: ST.Dict, +es2: List<&2, String>, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, wf1: Laws.WFArray(U32, d, ca1), m01a: Laws.Mask01(va, i), m01b: Laws.Mask01(vb, i),
  +emp: {mp == m : Array<U32>}, +ecbp: {cbp == cb : Array<U32>}, +ca_c: U32, +eca: {ca_c == Laws.rd_at(U32, ca, i) : U32}, +eca1: {ca_c == Laws.rd_at(U32, ca1, i) : U32}, hca: {U32.is_lt(Laws.rd_at(U32, ca, i), Laws.dk(dca)) == True{} : Bool},
  +c: U32, +ec: {c == Laws.rd_at(U32, cb, i) : U32}, +code: U32, +ecode: {code == Laws.rd_at(U32, m, c) : U32}, hc: {U32.is_lt(Laws.rd_at(U32, cb, i), kb) == True{} : Bool},
  wM: Laws.WFArray(U32, d, M), spec: @j: U32 -> {U32.is_lt(j, n) == True{} : Bool} -> {Laws.rdN(U32, d, M, j) == Laws.rd_at(U32, mp, Laws.rd_at(U32, cbp, j)) : U32},
  cvm: @j: U32 -> {Laws.rd_at(U32, m, j) == Laws.rdN(U32, ddb, m, j) : U32},
  wf2: Laws.WFDictE(dst2, es2), keep: @c2: U32 -> {U32.is_lt(c2, Laws.dk(dca)) == True{} : Bool} -> {Laws.dentry(dst2, c2) == Laws.dentry(dca, c2) : String}, rows: Laws.EncRows(kb, ddb, strsb, m, es2))
  -> FDP3(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, M, dst2, i):
  match dst2:
    case ST.Dict{+k2, +dd2, strs2, +b2, slots2, +tag2}:
      fd_pre9(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, M, cbp, m, mp, k2, dd2, strs2, b2, slots2, tag2, es2, i, hi, fits, wf1, m01a, m01b, emp, ecbp, ca_c, eca, eca1, hca, c, ec, code, ecode, hc, spec, cvm, wf2, keep, rows, PST.rd_all(U32, d, M, wM))

# the gather computed: its result pair replaces Eval.zd.map's call
def fd_pre7(+n: U32, +d: Nat, va: C.Valid, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, vb: C.Valid, -cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, ca1: Array<U32>, -cbp: Array<U32>, -m: Array<U32>, -mp: Array<U32>, dst2: ST.Dict, +es2: List<&2, String>, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, wf1: Laws.WFArray(U32, d, ca1), m01a: Laws.Mask01(va, i), m01b: Laws.Mask01(vb, i),
  +emp: {mp == m : Array<U32>}, +ecbp: {cbp == cb : Array<U32>}, +ca_c: U32, +eca: {ca_c == Laws.rd_at(U32, ca, i) : U32}, +eca1: {ca_c == Laws.rd_at(U32, ca1, i) : U32}, hca: {U32.is_lt(Laws.rd_at(U32, ca, i), Laws.dk(dca)) == True{} : Bool},
  +c: U32, +ec: {c == Laws.rd_at(U32, cb, i) : U32}, +code: U32, +ecode: {code == Laws.rd_at(U32, m, c) : U32}, hc: {U32.is_lt(Laws.rd_at(U32, cb, i), kb) == True{} : Bool},
  cvm: @j: U32 -> {Laws.rd_at(U32, m, j) == Laws.rdN(U32, ddb, m, j) : U32},
  wf2: Laws.WFDictE(dst2, es2), keep: @c2: U32 -> {U32.is_lt(c2, Laws.dk(dca)) == True{} : Bool} -> {Laws.dentry(dst2, c2) == Laws.dentry(dca, c2) : String}, rows: Laws.EncRows(kb, ddb, strsb, m, es2),
  w: PST.TGW(~U32, d, n, mp, cbp, 0))
  -> FDP(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, mp, cbp, dst2, i):
  (M, pm, eqg, epm, wM, spec) = w
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.gather(~U32, n, d, mp, cbp, 0), (M, pm), eqg) : FDP2(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, _, dst2, i)
  fd_pre8(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, M, cbp, m, mp, dst2, es2, i, hi, fits, wf1, m01a, m01b, emp, ecbp, ca_c, eca, eca1, hca, c, ec, code, ecode, hc, wM, spec, cvm, wf2, keep, rows)

# the map's slot at b's code read on the copy m3
def fd_pre6(+n: U32, +d: Nat, va: C.Valid, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, vb: C.Valid, -cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, ca1: Array<U32>, cbp: Array<U32>, -m: Array<U32>, mp: Array<U32>, -m3: Array<U32>, dst2: ST.Dict, +es2: List<&2, String>, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, wf1: Laws.WFArray(U32, d, ca1), m01a: Laws.Mask01(va, i), m01b: Laws.Mask01(vb, i),
  +emp: {mp == m : Array<U32>}, +em3: {m3 == m : Array<U32>}, +ecbp: {cbp == cb : Array<U32>}, +ca_c: U32, +eca: {ca_c == Laws.rd_at(U32, ca, i) : U32}, +eca1: {ca_c == Laws.rd_at(U32, ca1, i) : U32}, hca: {U32.is_lt(Laws.rd_at(U32, ca, i), Laws.dk(dca)) == True{} : Bool},
  +c: U32, +ec: {c == Laws.rd_at(U32, cb, i) : U32}, hc: {U32.is_lt(Laws.rd_at(U32, cb, i), kb) == True{} : Bool},
  cvm: @j: U32 -> {Laws.rd_at(U32, m, j) == Laws.rdN(U32, ddb, m, j) : U32},
  wf2: Laws.WFDictE(dst2, es2), keep: @c2: U32 -> {U32.is_lt(c2, Laws.dk(dca)) == True{} : Bool} -> {Laws.dentry(dst2, c2) == Laws.dentry(dca, c2) : String}, rows: Laws.EncRows(kb, ddb, strsb, m, es2),
  w: &m4: Array<U32> -> &code: U32 -> {m4 == m3 : Array<U32>} & {Array.get(U32, m3, c) == (m3, code) : Array<U32> & U32} & {code == Laws.rd_at(U32, m3, c) : U32})
  -> FDP(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, mp, cbp, dst2, i):
  (m4, +code, em4, e1, ecode3) = w
  fd_pre7(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, cbp, m, mp, dst2, es2, i, hi, fits, wf1, m01a, m01b, emp, ecbp, ca_c, eca, eca1, hca, c, ec, code, Equal.trans(U32, code, Laws.rd_at(U32, m3, c), Laws.rd_at(U32, m, c), ecode3, Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, c), m3, m, em3)), hc, cvm, wf2, keep, rows, PST.tgather_w(~U32, d, n, mp, cbp, 0, fits))

# the map's copy m2 cloned: mp feeds the gather, m3 is read
def fd_pre5(+n: U32, +d: Nat, va: C.Valid, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, vb: C.Valid, -cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, ca1: Array<U32>, cbp: Array<U32>, -m: Array<U32>, -m2: Array<U32>, dst2: ST.Dict, +es2: List<&2, String>, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, wf1: Laws.WFArray(U32, d, ca1), m01a: Laws.Mask01(va, i), m01b: Laws.Mask01(vb, i),
  +em2: {m2 == m : Array<U32>}, +ecbp: {cbp == cb : Array<U32>}, +ca_c: U32, +eca: {ca_c == Laws.rd_at(U32, ca, i) : U32}, +eca1: {ca_c == Laws.rd_at(U32, ca1, i) : U32}, hca: {U32.is_lt(Laws.rd_at(U32, ca, i), Laws.dk(dca)) == True{} : Bool},
  +c: U32, +ec: {c == Laws.rd_at(U32, cb, i) : U32}, hc: {U32.is_lt(Laws.rd_at(U32, cb, i), kb) == True{} : Bool},
  cvm: @j: U32 -> {Laws.rd_at(U32, m, j) == Laws.rdN(U32, ddb, m, j) : U32},
  wf2: Laws.WFDictE(dst2, es2), keep: @c2: U32 -> {U32.is_lt(c2, Laws.dk(dca)) == True{} : Bool} -> {Laws.dentry(dst2, c2) == Laws.dentry(dca, c2) : String}, rows: Laws.EncRows(kb, ddb, strsb, m, es2),
  w: &mp: Array<U32> -> &m3: Array<U32> -> {mp == m2 : Array<U32>} & {m3 == m2 : Array<U32>})
  -> FDP(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, m2, cbp, dst2, i):
  (mp, m3, +ep, +e3) = w
  %ep : FDP(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, _, cbp, dst2, i)
  fd_pre6(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, cbp, m, mp, m3, dst2, es2, i, hi, fits, wf1, m01a, m01b, Equal.trans(Array<U32>, mp, m2, m, ep, em2), Equal.trans(Array<U32>, m3, m2, m, e3, em2), ecbp, ca_c, eca, eca1, hca, c, ec, hc, cvm, wf2, keep, rows, PC.get_w(U32, m3, c))

# the map read back (rd_all)
def fd_pre4(+n: U32, +d: Nat, va: C.Valid, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, vb: C.Valid, -cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, ca1: Array<U32>, cbp: Array<U32>, -m: Array<U32>, dst2: ST.Dict, +es2: List<&2, String>, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, wf1: Laws.WFArray(U32, d, ca1), m01a: Laws.Mask01(va, i), m01b: Laws.Mask01(vb, i),
  +ecbp: {cbp == cb : Array<U32>}, +ca_c: U32, +eca: {ca_c == Laws.rd_at(U32, ca, i) : U32}, +eca1: {ca_c == Laws.rd_at(U32, ca1, i) : U32}, hca: {U32.is_lt(Laws.rd_at(U32, ca, i), Laws.dk(dca)) == True{} : Bool},
  +c: U32, +ec: {c == Laws.rd_at(U32, cb, i) : U32}, hc: {U32.is_lt(Laws.rd_at(U32, cb, i), kb) == True{} : Bool},
  wf2: Laws.WFDictE(dst2, es2), keep: @c2: U32 -> {U32.is_lt(c2, Laws.dk(dca)) == True{} : Bool} -> {Laws.dentry(dst2, c2) == Laws.dentry(dca, c2) : String}, rows: Laws.EncRows(kb, ddb, strsb, m, es2),
  w: &m2: Array<U32> -> {m2 == m : Array<U32>} & Laws.WFArray(U32, ddb, m2) & (@j: U32 -> {Laws.rd_at(U32, m, j) == Laws.rdN(U32, ddb, m, j) : U32}))
  -> FDP(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, m, cbp, dst2, i):
  (m2, +em2, wm2, cvm) = w
  %em2 : FDP(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, _, cbp, dst2, i)
  fd_pre5(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, cbp, m, m2, dst2, es2, i, hi, fits, wf1, m01a, m01b, em2, ecbp, ca_c, eca, eca1, hca, c, ec, hc, cvm, wf2, keep, rows, PC.clone_eq(U32, m2))

# b's code at i read on the copy cb2
def fd_pre3(+n: U32, +d: Nat, va: C.Valid, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, vb: C.Valid, -cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, ca1: Array<U32>, cbp: Array<U32>, -cb2: Array<U32>, m: Array<U32>, dst2: ST.Dict, +es2: List<&2, String>, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, wf1: Laws.WFArray(U32, d, ca1), m01a: Laws.Mask01(va, i), m01b: Laws.Mask01(vb, i),
  +ecbp: {cbp == cb : Array<U32>}, +ecb2: {cb2 == cb : Array<U32>}, +ca_c: U32, +eca: {ca_c == Laws.rd_at(U32, ca, i) : U32}, +eca1: {ca_c == Laws.rd_at(U32, ca1, i) : U32}, hca: {U32.is_lt(Laws.rd_at(U32, ca, i), Laws.dk(dca)) == True{} : Bool}, hc: {U32.is_lt(Laws.rd_at(U32, cb, i), kb) == True{} : Bool},
  wm: Laws.WFArray(U32, ddb, m), wf2: Laws.WFDictE(dst2, es2), keep: @c2: U32 -> {U32.is_lt(c2, Laws.dk(dca)) == True{} : Bool} -> {Laws.dentry(dst2, c2) == Laws.dentry(dca, c2) : String}, rows: Laws.EncRows(kb, ddb, strsb, m, es2),
  w: &cb3: Array<U32> -> &c: U32 -> {cb3 == cb2 : Array<U32>} & {Array.get(U32, cb2, i) == (cb2, c) : Array<U32> & U32} & {c == Laws.rd_at(U32, cb2, i) : U32})
  -> FDP(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, m, cbp, dst2, i):
  (cb3, +c, ecb3, e1, ec2) = w
  fd_pre4(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, cbp, m, dst2, es2, i, hi, fits, wf1, m01a, m01b, ecbp, ca_c, eca, eca1, hca, c, Equal.trans(U32, c, Laws.rd_at(U32, cb2, i), Laws.rd_at(U32, cb, i), ec2, Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, i), cb2, cb, ecb2)), hc, wf2, keep, rows, PST.rd_all(U32, ddb, m, wm))

# b's codes cloned: cbp feeds the gather, cb2 is read
def fd_pre2(+n: U32, +d: Nat, va: C.Valid, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, vb: C.Valid, -cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, ca1: Array<U32>, m: Array<U32>, dst2: ST.Dict, +es2: List<&2, String>, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, wf1: Laws.WFArray(U32, d, ca1), m01a: Laws.Mask01(va, i), m01b: Laws.Mask01(vb, i),
  +ca_c: U32, +eca: {ca_c == Laws.rd_at(U32, ca, i) : U32}, +eca1: {ca_c == Laws.rd_at(U32, ca1, i) : U32}, hca: {U32.is_lt(Laws.rd_at(U32, ca, i), Laws.dk(dca)) == True{} : Bool}, hc: {U32.is_lt(Laws.rd_at(U32, cb, i), kb) == True{} : Bool},
  wm: Laws.WFArray(U32, ddb, m), wf2: Laws.WFDictE(dst2, es2), keep: @c2: U32 -> {U32.is_lt(c2, Laws.dk(dca)) == True{} : Bool} -> {Laws.dentry(dst2, c2) == Laws.dentry(dca, c2) : String}, rows: Laws.EncRows(kb, ddb, strsb, m, es2),
  w: &cbp: Array<U32> -> &cb2: Array<U32> -> {cbp == cb : Array<U32>} & {cb2 == cb : Array<U32>})
  -> FDP(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, m, cb, dst2, i):
  (cbp, cb2, +ecbp, +ecb2) = w
  %ecbp : FDP(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, m, _, dst2, i)
  fd_pre3(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, cbp, cb2, m, dst2, es2, i, hi, fits, wf1, m01a, m01b, ecbp, ecb2, ca_c, eca, eca1, hca, hc, wm, wf2, keep, rows, PC.get_w(U32, cb2, i))

# a's code at i read on the copy ca2
def fd_pre1b(+n: U32, +d: Nat, va: C.Valid, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, vb: C.Valid, cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, ca1: Array<U32>, -ca2: Array<U32>, m: Array<U32>, dst2: ST.Dict, +es2: List<&2, String>, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, wf1: Laws.WFArray(U32, d, ca1), m01a: Laws.Mask01(va, i), m01b: Laws.Mask01(vb, i),
  +e1: {ca1 == ca : Array<U32>}, +e2: {ca2 == ca : Array<U32>}, hca: {U32.is_lt(Laws.rd_at(U32, ca, i), Laws.dk(dca)) == True{} : Bool}, hc: {U32.is_lt(Laws.rd_at(U32, cb, i), kb) == True{} : Bool},
  wm: Laws.WFArray(U32, ddb, m), wf2: Laws.WFDictE(dst2, es2), keep: @c2: U32 -> {U32.is_lt(c2, Laws.dk(dca)) == True{} : Bool} -> {Laws.dentry(dst2, c2) == Laws.dentry(dca, c2) : String}, rows: Laws.EncRows(kb, ddb, strsb, m, es2),
  +c: U32, +ec2: {c == Laws.rd_at(U32, ca2, i) : U32})
  -> FDP(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, m, cb, dst2, i):
  fd_pre2(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, m, dst2, es2, i, hi, fits, wf1, m01a, m01b, c, Equal.trans(U32, c, Laws.rd_at(U32, ca2, i), Laws.rd_at(U32, ca, i), ec2, Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, i), ca2, ca, e2)), Equal.trans(U32, c, Laws.rd_at(U32, ca2, i), Laws.rd_at(U32, ca1, i), ec2, Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, i), ca2, ca1, Equal.trans(Array<U32>, ca2, ca, ca1, e2, Equal.sym(Array<U32>, ca1, ca, e1)))), hca, hc, wm, wf2, keep, rows, PC.clone_eq(U32, cb))

def fd_pre1(+n: U32, +d: Nat, va: C.Valid, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, vb: C.Valid, cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, ca1: Array<U32>, -ca2: Array<U32>, m: Array<U32>, dst2: ST.Dict, +es2: List<&2, String>, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, wf1: Laws.WFArray(U32, d, ca1), m01a: Laws.Mask01(va, i), m01b: Laws.Mask01(vb, i),
  +e1: {ca1 == ca : Array<U32>}, +e2: {ca2 == ca : Array<U32>}, hca: {U32.is_lt(Laws.rd_at(U32, ca, i), Laws.dk(dca)) == True{} : Bool}, hc: {U32.is_lt(Laws.rd_at(U32, cb, i), kb) == True{} : Bool},
  wm: Laws.WFArray(U32, ddb, m), wf2: Laws.WFDictE(dst2, es2), keep: @c2: U32 -> {U32.is_lt(c2, Laws.dk(dca)) == True{} : Bool} -> {Laws.dentry(dst2, c2) == Laws.dentry(dca, c2) : String}, rows: Laws.EncRows(kb, ddb, strsb, m, es2),
  w: &ca3: Array<U32> -> &c: U32 -> {ca3 == ca2 : Array<U32>} & {Array.get(U32, ca2, i) == (ca2, c) : Array<U32> & U32} & {c == Laws.rd_at(U32, ca2, i) : U32})
  -> FDP(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, m, cb, dst2, i):
  (ca3, +c, eca3, ea1, ec2) = w
  fd_pre1b(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, ca2, m, dst2, es2, i, hi, fits, wf1, m01a, m01b, e1, e2, hca, hc, wm, wf2, keep, rows, c, ec2)
# a's codes cloned (well formed: the kernel writes into the first copy; the second is read)
def fd_pre0(+n: U32, +d: Nat, va: C.Valid, -ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, vb: C.Valid, cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, m: Array<U32>, dst2: ST.Dict, +es2: List<&2, String>, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, m01a: Laws.Mask01(va, i), m01b: Laws.Mask01(vb, i),
  hca: {U32.is_lt(Laws.rd_at(U32, ca, i), Laws.dk(dca)) == True{} : Bool}, hc: {U32.is_lt(Laws.rd_at(U32, cb, i), kb) == True{} : Bool},
  wm: Laws.WFArray(U32, ddb, m), wf2: Laws.WFDictE(dst2, es2), keep: @c2: U32 -> {U32.is_lt(c2, Laws.dk(dca)) == True{} : Bool} -> {Laws.dentry(dst2, c2) == Laws.dentry(dca, c2) : String}, rows: Laws.EncRows(kb, ddb, strsb, m, es2),
  w: &ca1: Array<U32> -> &ca2: Array<U32> -> {ca1 == ca : Array<U32>} & {ca2 == ca : Array<U32>} & Laws.WFArray(U32, d, ca1) & Laws.WFArray(U32, d, ca2))
  -> FDP(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca, m, cb, dst2, i):
  (ca1, ca2, +e1, +e2, wf1, wfa2) = w
  %e1 : FDP(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, _, m, cb, dst2, i)
  fd_pre1(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, ca1, ca2, m, dst2, es2, i, hi, fits, wf1, m01a, m01b, e1, e2, hca, hc, wm, wf2, keep, rows, PC.get_w(U32, ca2, i))

# the merge computed: its result triple replaces the call
def fd_merge(+n: U32, +d: Nat, va: C.Valid, ca: Array<U32>, -dca: ST.Dict, +n2: U32, +d2: Nat, vb: C.Valid, cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, +esa: List<&2, String>, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, wfc: Laws.WFArray(U32, d, ca), m01a: Laws.Mask01(va, i), m01b: Laws.Mask01(vb, i),
  hca: {U32.is_lt(Laws.rd_at(U32, ca, i), Laws.dk(dca)) == True{} : Bool}, hc: {U32.is_lt(Laws.rd_at(U32, cb, i), kb) == True{} : Bool},
  w: Laws.MergeW(ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}, dca, esa))
  -> &c: C.Column -> {V.Eval.fill.sd(n, d, va, vb, ca, cb, ST.Dict.merge(ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}, dca)) == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, Laws.vbit(va, i), Laws.ccell(C.CStr{n, d, va, ST.SDict{ca, dca}}, i), Laws.ccell(C.CStr{n2, d2, vb, ST.SDict{cb, ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}}}, i)) : D.Scalar}:
  (src2, dst2, m, +es2, eqm, esrc, ext, wm, wf2, keep, rows) = w
  %Equal.sym(ST.Dict & ST.Dict & Array<U32>, ST.Dict.merge(ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}, dca), (src2, dst2, m), eqm) : &c: C.Column -> {V.Eval.fill.sd(n, d, va, vb, ca, cb, _) == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, Laws.vbit(va, i), Laws.ccell(C.CStr{n, d, va, ST.SDict{ca, dca}}, i), Laws.ccell(C.CStr{n2, d2, vb, ST.SDict{cb, ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}}}, i)) : D.Scalar}
  fd_pre0(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, m, dst2, es2, i, hi, fits, m01a, m01b, hca, hc, wm, wf2, keep, rows, PC.clone_wf(U32, d, ca, wfc))

# a's dictionary's entry list taken apart; the merge theorem applied
def fd_dict(+n: U32, +d: Nat, va: C.Valid, ca: Array<U32>, dca: ST.Dict, +n2: U32, +d2: Nat, vb: C.Valid, cb: Array<U32>, +kb: U32, +ddb: Nat, strsb: Array<String>, +bb: Nat, slotsb: Array<ST.SSlot>, +tagb: U32, +i: U32, +hi: {U32.is_lt(i, n) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, wfc: Laws.WFArray(U32, d, ca), m01a: Laws.Mask01(va, i), m01b: Laws.Mask01(vb, i),
  wfd: Laws.WFDict(dca), fitsb: {U32.is_le(kb, U32.shln(1, ddb)) == True{} : Bool}, hca: {U32.is_lt(Laws.rd_at(U32, ca, i), Laws.dk(dca)) == True{} : Bool}, hc: {U32.is_lt(Laws.rd_at(U32, cb, i), kb) == True{} : Bool}, probes: Laws.MergeProbe(U32.to_nat(kb), 0, strsb, dca))
  -> Laws.FillW(n, d, va, ST.SDict{ca, dca}, n2, d2, vb, ST.SDict{cb, ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}}, i):
  (+esa, wfa) = wfd
  fd_merge(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, esa, i, hi, fits, wfc, m01a, m01b, hca, hc, Laws.dict_merge_spec(ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}, dca, esa, fitsb, wfa, probes))

# b's dictionary taken apart, the hypotheses taken apart
def fd_law(+n: U32, +d: Nat, va: C.Valid, ca: Array<U32>, dca: ST.Dict, +n2: U32, +d2: Nat, vb: C.Valid, cb: Array<U32>, dcb: ST.Dict, +i: U32, hyp: Laws.FillHyp(n, d, va, ST.SDict{ca, dca}, vb, ST.SDict{cb, dcb}, i))
  -> Laws.FillW(n, d, va, ST.SDict{ca, dca}, n2, d2, vb, ST.SDict{cb, dcb}, i):
  match dcb:
    case ST.Dict{+kb, +ddb, strsb, +bb, slotsb, +tagb}:
      (+fits, +hi, wfc, m01a, m01b, wfd, fitsb, hca, hc, probes) = hyp
      fd_dict(n, d, va, ca, dca, n2, d2, vb, cb, kb, ddb, strsb, bb, slotsb, tagb, i, hi, fits, wfc, m01a, m01b, wfd, fitsb, hca, hc, probes)

# the Raw branch's law shape: the decodes from the hypotheses
def fr_law(+n: U32, +d: Nat, va: C.Valid, xa: ST.Strs, +n2: U32, +d2: Nat, vb: C.Valid, xb: ST.Strs, +i: U32, +fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, +hi: {U32.is_lt(i, n) == True{} : Bool}, wfs: Laws.WFStrData(d, xa), m01a: Laws.Mask01(va, i), m01b: Laws.Mask01(vb, i))
  -> &c: C.Column -> {V.Eval.fill.s(n, d, V.Eval.fill.t(~String, n, d, va, vb, ST.Strs.decode(n, d, xa), ST.Strs.decode(n, d, xb))) == Done{c} : E.ResT(C.Column)} & {Laws.ccell(c, i) == Bool.pick(D.Scalar, Laws.vbit(va, i), Laws.ccell(C.CStr{n, d, va, xa}, i), Laws.ccell(C.CStr{n2, d2, vb, xb}, i)) : D.Scalar}:
  fill_raw_dec(n, d, va, xa, n2, d2, vb, xb, i, hi, fits, m01a, m01b, decode_wf(n, d, xa, fits, wfs), PA.decode_w(n, d, xb, fits))

def Laws.fill_str_cell(n, d, va, xa, n2, d2, vb, xb, i, hyp):
  match xa xb:
    case ST.SDict{ca, dca} ST.SDict{cb, dcb}:
      fd_law(n, d, va, ca, dca, n2, d2, vb, cb, dcb, i, hyp)
    case ST.SRaw{a} ST.SRaw{b}:
      (+fits, +hi, wfs, m01a, m01b, dh) = hyp
      fr_law(n, d, va, ST.SRaw{a}, n2, d2, vb, ST.SRaw{b}, i, fits, hi, wfs, m01a, m01b)
    case ST.SRaw{a} ST.SDict{cb, dcb}:
      (+fits, +hi, wfs, m01a, m01b, dh) = hyp
      fr_law(n, d, va, ST.SRaw{a}, n2, d2, vb, ST.SDict{cb, dcb}, i, fits, hi, wfs, m01a, m01b)
    case ST.SDict{ca, dca} ST.SRaw{b}:
      (+fits, +hi, wfs, m01a, m01b, dh) = hyp
      fr_law(n, d, va, ST.SDict{ca, dca}, n2, d2, vb, ST.SRaw{b}, i, fits, hi, wfs, m01a, m01b)
