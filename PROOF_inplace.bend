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
