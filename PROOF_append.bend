# PROOF_append.bend -- proofs of LAWS.bend section 15 (M5 part 4, P1): the concatenation
# kernel Kernel.append (= two Kernel.copy_into loops writing at off + i) and Strs.append
# (the Str storage of Cat.col / concat_vertical) in both storages.
#
# Shape: the copy loop is proven as a template over the cell type T (the law instances are
# U32 for the word buffers and the codes, String for a Raw column). The write index is the
# word w = off + i, which the loop increments through U32.add(off, U32.inc(i)) ==
# U32.inc(U32.add(off, i)) (add_inc_r, a Word.adc lemma); the per-row invariant records each
# written index below the current one (so the distinct-paths lemma applies without any
# monotonicity of U32.add), and the slots below off are kept (the left half survives the
# right copy). Laws.Room over w gives every write index below 2^d.
import Base
import ./src/dtype.bend as D
import ./src/err.bend as E
import ./src/kernels.bend as K
import ./src/column.bend as C
import ./src/strs.bend as ST
import ./src/table.bend as TB
import ./LAWS.bend as Laws
import ./PROOF_lib.bend as L
import ./PROOF_kernels.bend as PK
import ./PROOF_bits.bend as B
import ./PROOF_contents.bend as PC
import ./PROOF_strs.bend as PST

# ---- Word.adc: a carry in is one increment; adding an incremented word is incrementing the sum --------

def adc_carry(n: Nat, a: Word(n), b: Word(n)) -> {Word.adc(n, a, b, False{}, True{}) == Word.inc(n, Word.adc(n, a, b, False{}, False{})) : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n++p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          {==}
        case WCon{False{}, +at} WCon{True{}, +bt}:
          %Equal.sym(Word(p), Word.adc(p, at, bt, False{}, True{}), Word.inc(p, Word.adc(p, at, bt, False{}, False{})), adc_carry(p, at, bt)) : {WCon{False{}, _} == WCon{False{}, Word.inc(p, Word.adc(p, at, bt, False{}, False{}))} : Word(1n+p)}
          {==}
        case WCon{True{}, +at} WCon{False{}, +bt}:
          %Equal.sym(Word(p), Word.adc(p, at, bt, False{}, True{}), Word.inc(p, Word.adc(p, at, bt, False{}, False{})), adc_carry(p, at, bt)) : {WCon{False{}, _} == WCon{False{}, Word.inc(p, Word.adc(p, at, bt, False{}, False{}))} : Word(1n+p)}
          {==}
        case WCon{True{}, +at} WCon{True{}, +bt}:
          {==}

def adc_inc_r(n: Nat, a: Word(n), b: Word(n), c: Bool) -> {Word.adc(n, a, Word.inc(n, b), False{}, c) == Word.inc(n, Word.adc(n, a, b, False{}, c)) : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n++p:
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          {==}
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          %Equal.sym(Word(p), Word.adc(p, at, bt, False{}, True{}), Word.inc(p, Word.adc(p, at, bt, False{}, False{})), adc_carry(p, at, bt)) : {WCon{False{}, _} == WCon{False{}, Word.inc(p, Word.adc(p, at, bt, False{}, False{}))} : Word(1n+p)}
          {==}
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          %Equal.sym(Word(p), Word.adc(p, at, bt, False{}, True{}), Word.inc(p, Word.adc(p, at, bt, False{}, False{})), adc_carry(p, at, bt)) : {WCon{False{}, _} == WCon{False{}, Word.inc(p, Word.adc(p, at, bt, False{}, False{}))} : Word(1n+p)}
          {==}
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          {==}
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          %Equal.sym(Word(p), Word.adc(p, at, Word.inc(p, bt), False{}, False{}), Word.inc(p, Word.adc(p, at, bt, False{}, False{})), adc_inc_r(p, at, bt, False{})) : {WCon{False{}, _} == WCon{False{}, Word.inc(p, Word.adc(p, at, bt, False{}, False{}))} : Word(1n+p)}
          {==}
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          %Equal.sym(Word(p), Word.adc(p, at, Word.inc(p, bt), False{}, False{}), Word.inc(p, Word.adc(p, at, bt, False{}, False{})), adc_inc_r(p, at, bt, False{})) : {WCon{True{}, _} == WCon{True{}, Word.adc(p, at, bt, False{}, True{})} : Word(1n+p)}
          %Equal.sym(Word(p), Word.adc(p, at, bt, False{}, True{}), Word.inc(p, Word.adc(p, at, bt, False{}, False{})), adc_carry(p, at, bt)) : {WCon{True{}, Word.inc(p, Word.adc(p, at, bt, False{}, False{}))} == WCon{True{}, _} : Word(1n+p)}
          {==}
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          %Equal.sym(Word(p), Word.adc(p, at, Word.inc(p, bt), False{}, False{}), Word.inc(p, Word.adc(p, at, bt, False{}, False{})), adc_inc_r(p, at, bt, False{})) : {WCon{True{}, _} == WCon{True{}, Word.adc(p, at, bt, False{}, True{})} : Word(1n+p)}
          %Equal.sym(Word(p), Word.adc(p, at, bt, False{}, True{}), Word.inc(p, Word.adc(p, at, bt, False{}, False{})), adc_carry(p, at, bt)) : {WCon{True{}, Word.inc(p, Word.adc(p, at, bt, False{}, False{}))} == WCon{True{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          %Equal.sym(Word(p), Word.adc(p, at, Word.inc(p, bt), False{}, True{}), Word.inc(p, Word.adc(p, at, bt, False{}, True{})), adc_inc_r(p, at, bt, True{})) : {WCon{False{}, _} == WCon{False{}, Word.inc(p, Word.adc(p, at, bt, False{}, True{}))} : Word(1n+p)}
          {==}

# U32.add(x, U32.inc(y)) == U32.inc(U32.add(x, y)): the write index of Kernel.copy_into's next step
def add_inc_r(x: U32, y: U32) -> {U32.add(x, U32.inc(y)) == U32.inc(U32.add(x, y)) : U32}:
  match x y:
    case U32{a} U32{b}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.adc(32n, a, Word.inc(32n, b), False{}, False{}), Word.inc(32n, Word.adc(32n, a, b, False{}, False{})), adc_inc_r(32n, a, b, False{}))

# 0 + x == x
def adc_zero_l(n: Nat, x: Word(n)) -> {Word.adc(n, Word.zero(n), x, False{}, False{}) == x : Word(n)}:
  match n:
    case 0n:
      match x:
        case WNil{}:
          {==}
    case 1n++p:
      match x:
        case WCon{False{}, +t}:
          %Equal.sym(Word(p), Word.adc(p, Word.zero(p), t, False{}, False{}), t, adc_zero_l(p, t)) : {WCon{False{}, _} == WCon{False{}, t} : Word(1n+p)}
          {==}
        case WCon{True{}, +t}:
          %Equal.sym(Word(p), Word.adc(p, Word.zero(p), t, False{}, False{}), t, adc_zero_l(p, t)) : {WCon{True{}, _} == WCon{True{}, t} : Word(1n+p)}
          {==}

def u_add0_l(x: U32) -> {U32.add(0, x) == x : U32}:
  match x:
    case U32{a}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.adc(32n, Word.zero(32n), a, False{}, False{}), a, adc_zero_l(32n, a))

# ---- order helpers --------------------------------------------------------------------------------

# a <= b and b < c give a < c
def le_lt_u(+a: U32, +b: U32, +c: U32, h1: {U32.is_le(a, b) == True{} : Bool}, h2: {U32.is_lt(b, c) == True{} : Bool}) -> {U32.is_lt(a, c) == True{} : Bool}:
  B.lt_of_nat_u(a, c, PST.nat_le_lt_trans(U32.to_nat(a), U32.to_nat(b), U32.to_nat(c), B.le_nat_u(a, b, h1), PST.lt_nat_of_u(b, c, h2)))

def le_refl_u(+a: U32) -> {U32.is_le(a, a) == True{} : Bool}:
  PST.le_u_of_nat(a, a, PST.nat_le_refl(U32.to_nat(a)))

# a <= a + b
def nat_le_add_r(a: Nat, b: Nat) -> {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p _:
      nat_le_add_r(p, b)

# two writes of one cell at one index into equal arrays agree (template form of PROOF_strs' writes_eq)
def writes_eq_t(~T: Data, -x1: Array<T>, -x2: Array<T>, -c1: Array<T>, -c2: Array<T>, +k: U32, +s: T, +e21: {x2 == x1 : Array<T>}, +ec1: {Array.set(T, x1, k, s) == c1 : Array<T>}, ec2: {Array.set(T, x2, k, s) == c2 : Array<T>}) -> {c2 == c1 : Array<T>}:
  Equal.trans(Array<T>, c2, Array.set(T, x2, k, s), c1, Equal.sym(Array<T>, Array.set(T, x2, k, s), c2, ec2), Equal.trans(Array<T>, Array.set(T, x2, k, s), Array.set(T, x1, k, s), c1, Equal.cong(Array<T>, Array<T>, q => Array.set(T, q, k, s), x2, x1, e21), ec1))

# ---- the copy loop Kernel.copy_into.go as a template --------------------------------------------------

# every row k < i is written: the slot off + k (below the current write index w) holds a[k]
def CPHyp(~T: Data, +i: U32, +off: U32, +w: U32, +d: Nat, -a: Array<T>, -out: Array<T>) -> Type:
  @k: U32 -> {U32.is_lt(k, i) == True{} : Bool} -> {U32.is_lt(U32.add(off, k), w) == True{} : Bool} & {Laws.rdN(T, d, out, U32.add(off, k)) == Laws.rd_at(T, a, k) : T}

# the slots below off are untouched (out0 the array before the loop)
def CPLow(~T: Data, +off: U32, +d: Nat, -out0: Array<T>, -out: Array<T>) -> Type:
  @j: U32 -> {U32.is_lt(j, off) == True{} : Bool} -> {Laws.rdN(T, d, out, j) == Laws.rdN(T, d, out0, j) : T}

# the result: well formed, every k < bound at off + k, the slots below off kept
def CPRes(~T: Data, +off: U32, +d: Nat, -a: Array<T>, -out0: Array<T>, o: Array<T>, +bound: U32) -> Type:
  Laws.WFArray(T, d, o) & (@k: U32 -> {U32.is_lt(k, bound) == True{} : Bool} -> {Laws.rdN(T, d, o, U32.add(off, k)) == Laws.rd_at(T, a, k) : T}) & CPLow(~T, off, d, out0, o)

def CPGoal(~T: Data, f: Nat, +i: U32, +off: U32, +w: U32, +d: Nat, -a: Array<T>, -out0: Array<T>, -out: Array<T>, -r: Array<T> & T) -> Type:
  CPHyp(~T, i, off, w, d, a, out) -> CPLow(~T, off, d, out0, out) -> &o: Array<T> -> {K.Kernel.copy_into.go(~T, f, i, off, out, r) == o : Array<T>} & CPRes(~T, off, d, a, out0, o, Laws.addn(i, f))

# after one step: the write at index wi (= off + i, then w) of the cell x
def CPSet(~T: Data, p: Nat, +i: U32, +off: U32, +w: U32, +wi: U32, +d: Nat, -a: Array<T>, -out0: Array<T>, -out: Array<T>, +x: T) -> Type:
  CPHyp(~T, i, off, w, d, a, out) -> CPLow(~T, off, d, out0, out) -> &o: Array<T> -> {K.Kernel.copy_into.go(~T, p, U32.inc(i), off, Array.set(T, out, wi, x), Array.get(T, a, U32.inc(i))) == o : Array<T>} & CPRes(~T, off, d, a, out0, o, Laws.addn(i, 1n+p))

# ... with the written array c in place and the bound as a parameter
def CPC(~T: Data, p: Nat, +i: U32, +off: U32, +w: U32, +d: Nat, -a: Array<T>, -out0: Array<T>, -out: Array<T>, -c: Array<T>, +bound: U32) -> Type:
  CPHyp(~T, i, off, w, d, a, out) -> CPLow(~T, off, d, out0, out) -> &o: Array<T> -> {K.Kernel.copy_into.go(~T, p, U32.inc(i), off, c, Array.get(T, a, U32.inc(i))) == o : Array<T>} & CPRes(~T, off, d, a, out0, o, bound)

# the induction hypothesis of the loop
def CPIH(~T: Data, p: Nat, +i: U32, +off: U32, +w: U32, +d: Nat, -out0: Array<T>) -> Type:
  @a2: Array<T> -> @c: Array<T> -> Laws.WFArray(T, d, c) -> {U32.inc(w) == U32.add(off, U32.inc(i)) : U32} -> {U32.is_le(off, U32.inc(w)) == True{} : Bool} -> Laws.Room(d, U32.inc(w), p) -> CPGoal(~T, p, U32.inc(i), off, U32.inc(w), d, a2, out0, c, Array.get(T, a2, U32.inc(i)))

# the row invariant after the write at w: k < i untouched (its index is below w), k == i the cell
def cpnext_lt(~T: Data, +d: Nat, +i: U32, +off: U32, +w: U32, +k: U32, -a: Array<T>, -out: Array<T>, -c: Array<T>, +hw: {U32.is_lt(w, U32.shln(1, d)) == True{} : Bool}, +x: T,
  fj: @j: U32 -> {Laws.rdN(T, d, c, j) == Bool.pick(T, Laws.same_at(d, w, j), x, Laws.rdN(T, d, out, j)) : T}, old: {U32.is_lt(U32.add(off, k), w) == True{} : Bool} & {Laws.rdN(T, d, out, U32.add(off, k)) == Laws.rd_at(T, a, k) : T})
  -> {U32.is_lt(U32.add(off, k), U32.inc(w)) == True{} : Bool} & {Laws.rdN(T, d, c, U32.add(off, k)) == Laws.rd_at(T, a, k) : T}:
  (+lt, eq) = old
  (PC.lt_trans_u(U32.add(off, k), w, U32.inc(w), lt, PC.lt_inc_u(w, d, hw)), (%Equal.sym(T, Laws.rdN(T, d, c, U32.add(off, k)), Bool.pick(T, Laws.same_at(d, w, U32.add(off, k)), x, Laws.rdN(T, d, out, U32.add(off, k))), fj(U32.add(off, k))) : {_ == Laws.rd_at(T, a, k) : T}; %Equal.sym(Bool, Laws.same_at(d, w, U32.add(off, k)), False{}, PC.same_false_lt(d, w, U32.add(off, k), hw, lt)) : {Bool.pick(T, _, x, Laws.rdN(T, d, out, U32.add(off, k))) == Laws.rd_at(T, a, k) : T}; eq))

def cpnext_b(~T: Data, b: Bool, +d: Nat, +i: U32, +off: U32, +w: U32, +k: U32, -a: Array<T>, -out: Array<T>, -c: Array<T>, +hw: {U32.is_lt(w, U32.shln(1, d)) == True{} : Bool}, +ew: {w == U32.add(off, i) : U32}, +x: T, ex: {x == Laws.rd_at(T, a, i) : T}, g: CPHyp(~T, i, off, w, d, a, out),
  fj: @j: U32 -> {Laws.rdN(T, d, c, j) == Bool.pick(T, Laws.same_at(d, w, j), x, Laws.rdN(T, d, out, j)) : T}, s: PC.IncLtU(b, k, i))
  -> {U32.is_lt(U32.add(off, k), U32.inc(w)) == True{} : Bool} & {Laws.rdN(T, d, c, U32.add(off, k)) == Laws.rd_at(T, a, k) : T}:
  match b:
    case True{}:
      cpnext_lt(~T, d, i, off, w, k, a, out, c, hw, x, fj, g(k, s))
    case False{}:
      %Equal.sym(U32, k, i, s) : {U32.is_lt(U32.add(off, _), U32.inc(w)) == True{} : Bool} & {Laws.rdN(T, d, c, U32.add(off, _)) == Laws.rd_at(T, a, _) : T}
      %ew : {U32.is_lt(_, U32.inc(w)) == True{} : Bool} & {Laws.rdN(T, d, c, _) == Laws.rd_at(T, a, i) : T}
      (PC.lt_inc_u(w, d, hw), (%Equal.sym(T, Laws.rdN(T, d, c, w), Bool.pick(T, Laws.same_at(d, w, w), x, Laws.rdN(T, d, out, w)), fj(w)) : {_ == Laws.rd_at(T, a, i) : T}; %Equal.sym(Bool, Laws.same_at(d, w, w), True{}, PC.same_at_refl(d, w)) : {Bool.pick(T, _, x, Laws.rdN(T, d, out, w)) == Laws.rd_at(T, a, i) : T}; ex))

def cpnext_k(~T: Data, +d: Nat, +i: U32, +off: U32, +w: U32, +k: U32, -a: Array<T>, -out: Array<T>, -c: Array<T>, +hw: {U32.is_lt(w, U32.shln(1, d)) == True{} : Bool}, +ew: {w == U32.add(off, i) : U32}, +x: T, ex: {x == Laws.rd_at(T, a, i) : T}, g: CPHyp(~T, i, off, w, d, a, out),
  fj: @j: U32 -> {Laws.rdN(T, d, c, j) == Bool.pick(T, Laws.same_at(d, w, j), x, Laws.rdN(T, d, out, j)) : T}, s: &b: Bool -> PC.IncLtU(b, k, i))
  -> {U32.is_lt(U32.add(off, k), U32.inc(w)) == True{} : Bool} & {Laws.rdN(T, d, c, U32.add(off, k)) == Laws.rd_at(T, a, k) : T}:
  (b, s2) = s
  cpnext_b(~T, b, d, i, off, w, k, a, out, c, hw, ew, x, ex, g, fj, s2)

def cpnext(~T: Data, +d: Nat, +i: U32, +off: U32, +w: U32, -a: Array<T>, -out: Array<T>, -c: Array<T>, +hw: {U32.is_lt(w, U32.shln(1, d)) == True{} : Bool}, +ew: {w == U32.add(off, i) : U32}, +x: T, +ex: {x == Laws.rd_at(T, a, i) : T}, g: CPHyp(~T, i, off, w, d, a, out),
  fj: @j: U32 -> {Laws.rdN(T, d, c, j) == Bool.pick(T, Laws.same_at(d, w, j), x, Laws.rdN(T, d, out, j)) : T})
  -> CPHyp(~T, U32.inc(i), off, U32.inc(w), d, a, c):
  +k => hk => cpnext_k(~T, d, i, off, w, k, a, out, c, hw, ew, x, ex, g, fj, PC.inc_lt_u(k, i, hk))

# the slots below off after the write at w >= off: the write facts of the second copy (s2 -> c2,
# with s2 == s1 and c2 == c1) restated to the first
def cplow_next(~T: Data, +d: Nat, +off: U32, +w: U32, -out0: Array<T>, -s1: Array<T>, -s2: Array<T>, -c1: Array<T>, -c2: Array<T>, +e21: {s2 == s1 : Array<T>}, +e12: {c2 == c1 : Array<T>}, +hw: {U32.is_lt(w, U32.shln(1, d)) == True{} : Bool}, +hle: {U32.is_le(off, w) == True{} : Bool}, +x: T, low: CPLow(~T, off, d, out0, s1),
  fj2: @j: U32 -> {Laws.rdN(T, d, c2, j) == Bool.pick(T, Laws.same_at(d, w, j), x, Laws.rdN(T, d, s2, j)) : T})
  -> CPLow(~T, off, d, out0, c1):
  +j => +hj =>
    %e12 : {Laws.rdN(T, d, _, j) == Laws.rdN(T, d, out0, j) : T}
    %Equal.sym(T, Laws.rdN(T, d, c2, j), Bool.pick(T, Laws.same_at(d, w, j), x, Laws.rdN(T, d, s2, j)), fj2(j)) : {_ == Laws.rdN(T, d, out0, j) : T}
    %Equal.sym(Bool, Laws.same_at(d, w, j), False{}, PC.same_false_lt(d, w, j, hw, PST.lt_le_trans_u(j, off, w, hj, hle))) : {Bool.pick(T, _, x, Laws.rdN(T, d, s2, j)) == Laws.rdN(T, d, out0, j) : T}
    %Equal.sym(Array<T>, s2, s1, e21) : {Laws.rdN(T, d, _, j) == Laws.rdN(T, d, out0, j) : T}
    low(j, hj)

# the next iteration's arithmetic: inc(w) == off + inc(i) and off <= inc(w)
def cp_ew_next(+i: U32, +off: U32, +w: U32, +ew: {w == U32.add(off, i) : U32}) -> {U32.inc(w) == U32.add(off, U32.inc(i)) : U32}:
  Equal.trans(U32, U32.inc(w), U32.inc(U32.add(off, i)), U32.add(off, U32.inc(i)), Equal.cong(U32, U32, q => U32.inc(q), w, U32.add(off, i), ew), Equal.sym(U32, U32.add(off, U32.inc(i)), U32.inc(U32.add(off, i)), add_inc_r(off, i)))

def cp_le_next(+d: Nat, +off: U32, +w: U32, +hw: {U32.is_lt(w, U32.shln(1, d)) == True{} : Bool}, +hle: {U32.is_le(off, w) == True{} : Bool}) -> {U32.is_le(off, U32.inc(w)) == True{} : Bool}:
  PST.lt_le_u(off, U32.inc(w), le_lt_u(off, w, U32.inc(w), hle, PC.lt_inc_u(w, d, hw)))

# both writes computed: the loop continues on c1 with the two invariants
def cp_step5(~T: Data, p: Nat, +i: U32, +off: U32, +w: U32, +d: Nat, a: Array<T>, -out0: Array<T>, -s1: Array<T>, -s2: Array<T>, c1: Array<T>, -c2: Array<T>, +e21: {s2 == s1 : Array<T>}, +e12: {c2 == c1 : Array<T>}, +x: T, +ex: {x == Laws.rd_at(T, a, i) : T}, +hw: {U32.is_lt(w, U32.shln(1, d)) == True{} : Bool}, +ew: {w == U32.add(off, i) : U32}, +hle: {U32.is_le(off, w) == True{} : Bool}, room: Laws.Room(d, U32.inc(w), p),
  ih: CPIH(~T, p, i, off, w, d, out0), wc1: Laws.WFArray(T, d, c1),
  fj1: @j: U32 -> {Laws.rdN(T, d, c1, j) == Bool.pick(T, Laws.same_at(d, w, j), x, Laws.rdN(T, d, s1, j)) : T},
  fj2: @j: U32 -> {Laws.rdN(T, d, c2, j) == Bool.pick(T, Laws.same_at(d, w, j), x, Laws.rdN(T, d, s2, j)) : T})
  -> CPC(~T, p, i, off, w, d, a, out0, s1, c1, Laws.addn(U32.inc(i), p)):
  g => low => ih(a, c1, wc1, cp_ew_next(i, off, w, ew), cp_le_next(d, off, w, hw, hle), room)(cpnext(~T, d, i, off, w, a, s1, c1, hw, ew, x, ex, g, fj1))(cplow_next(~T, d, off, w, out0, s1, s2, c1, c2, e21, e12, hw, hle, x, low, fj2))

def cp_step4(~T: Data, p: Nat, +i: U32, +off: U32, +w: U32, +d: Nat, a: Array<T>, -out0: Array<T>, -s1: Array<T>, -s2: Array<T>, c1: Array<T>, +e21: {s2 == s1 : Array<T>}, +x: T, +ec1: {Array.set(T, s1, w, x) == c1 : Array<T>}, +ex: {x == Laws.rd_at(T, a, i) : T}, +hw: {U32.is_lt(w, U32.shln(1, d)) == True{} : Bool}, +ew: {w == U32.add(off, i) : U32}, +hle: {U32.is_le(off, w) == True{} : Bool}, room: Laws.Room(d, U32.inc(w), p),
  ih: CPIH(~T, p, i, off, w, d, out0), wc1: Laws.WFArray(T, d, c1),
  fj1: @j: U32 -> {Laws.rdN(T, d, c1, j) == Bool.pick(T, Laws.same_at(d, w, j), x, Laws.rdN(T, d, s1, j)) : T},
  w2: &c2: Array<T> -> {Array.set(T, s2, w, x) == c2 : Array<T>} & Laws.WFArray(T, d, c2) & (@j: U32 -> {Laws.rdN(T, d, c2, j) == Bool.pick(T, Laws.same_at(d, w, j), x, Laws.rdN(T, d, s2, j)) : T}) & (@j: U32 -> {Laws.rd_at(T, s2, j) == Laws.rdN(T, d, s2, j) : T}))
  -> CPC(~T, p, i, off, w, d, a, out0, s1, c1, Laws.addn(U32.inc(i), p)):
  (c2, ec2, wc2, fj2, cv2) = w2
  cp_step5(~T, p, i, off, w, d, a, out0, s1, s2, c1, c2, e21, writes_eq_t(~T, s1, s2, c1, c2, w, x, e21, ec1, ec2), x, ex, hw, ew, hle, room, ih, wc1, fj1, fj2)

# the first copy's write computed: Array.set(s1, w, x) == c1 replaces the call
def cp_step3(~T: Data, +p: Nat, +i: U32, +off: U32, +w: U32, +d: Nat, a: Array<T>, -out0: Array<T>, -s1: Array<T>, s2: Array<T>, +e21: {s2 == s1 : Array<T>}, wf2: Laws.WFArray(T, d, s2), +x: T, +ex: {x == Laws.rd_at(T, a, i) : T}, +hw: {U32.is_lt(w, U32.shln(1, d)) == True{} : Bool}, +ew: {w == U32.add(off, i) : U32}, +hle: {U32.is_le(off, w) == True{} : Bool}, room: Laws.Room(d, U32.inc(w), p),
  ih: CPIH(~T, p, i, off, w, d, out0),
  w1: &c1: Array<T> -> {Array.set(T, s1, w, x) == c1 : Array<T>} & Laws.WFArray(T, d, c1) & (@j: U32 -> {Laws.rdN(T, d, c1, j) == Bool.pick(T, Laws.same_at(d, w, j), x, Laws.rdN(T, d, s1, j)) : T}) & (@j: U32 -> {Laws.rd_at(T, s1, j) == Laws.rdN(T, d, s1, j) : T}))
  -> CPSet(~T, p, i, off, w, w, d, a, out0, s1, x):
  (c1, +ec1, wc1, fj1, cv1) = w1
  %Equal.sym(Array<T>, Array.set(T, s1, w, x), c1, ec1) : CPC(~T, p, i, off, w, d, a, out0, s1, _, Laws.addn(i, 1n+p))
  %PC.addn_inc(i, p) : CPC(~T, p, i, off, w, d, a, out0, s1, c1, _)
  cp_step4(~T, p, i, off, w, d, a, out0, s1, s2, c1, e21, x, ec1, ex, hw, ew, hle, room, ih, wc1, fj1, PC.set_other_w(T, d, s2, w, x, wf2))

# the output cloned (the write facts are needed twice: the rows and the low slots); the write index
# off + i is the word w
def cp_step2(~T: Data, p: Nat, +i: U32, +off: U32, +w: U32, +d: Nat, a: Array<T>, -out0: Array<T>, -out: Array<T>, +x: T, +ex: {x == Laws.rd_at(T, a, i) : T}, +hw: {U32.is_lt(w, U32.shln(1, d)) == True{} : Bool}, +ew: {w == U32.add(off, i) : U32}, +hle: {U32.is_le(off, w) == True{} : Bool}, room: Laws.Room(d, U32.inc(w), p),
  ih: CPIH(~T, p, i, off, w, d, out0),
  wc: &s1: Array<T> -> &s2: Array<T> -> {s1 == out : Array<T>} & {s2 == out : Array<T>} & Laws.WFArray(T, d, s1) & Laws.WFArray(T, d, s2))
  -> CPSet(~T, p, i, off, w, U32.add(off, i), d, a, out0, out, x):
  (s1, s2, +e1, +e2, wf1, wf2) = wc
  %e1 : CPSet(~T, p, i, off, w, U32.add(off, i), d, a, out0, _, x)
  %ew : CPSet(~T, p, i, off, w, _, d, a, out0, s1, x)
  cp_step3(~T, p, i, off, w, d, a, out0, s1, s2, Equal.trans(Array<T>, s2, out, s1, e2, Equal.sym(Array<T>, s1, out, e1)), wf2, x, ex, hw, ew, hle, room, ih, PC.set_other_w(T, d, s1, w, x, wf1))

# the read a[i] computed: Array.get(a, i) == (a, x), the copy a2 of a everywhere
def cp_step1(~T: Data, p: Nat, +i: U32, +off: U32, +w: U32, +d: Nat, -a: Array<T>, -out0: Array<T>, out: Array<T>, wf: Laws.WFArray(T, d, out), +ew: {w == U32.add(off, i) : U32}, +hle: {U32.is_le(off, w) == True{} : Bool}, room: Laws.Room(d, w, 1n+p),
  ih: CPIH(~T, p, i, off, w, d, out0),
  wr: &b: Array<T> -> &x: T -> {b == a : Array<T>} & {Array.get(T, a, i) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, i) : T})
  -> CPGoal(~T, 1n+p, i, off, w, d, a, out0, out, Array.get(T, a, i)):
  (+hw, room2) = room
  (a2, +x, +ea, e1, ex) = wr
  %Equal.sym(Array<T> & T, Array.get(T, a, i), (a, x), e1) : CPGoal(~T, 1n+p, i, off, w, d, a, out0, out, _)
  %ea : CPGoal(~T, 1n+p, i, off, w, d, _, out0, out, (_, x))
  cp_step2(~T, p, i, off, w, d, a2, out0, out, x, Equal.trans(T, x, Laws.rd_at(T, a, i), Laws.rd_at(T, a2, i), ex, Equal.cong(Array<T>, T, q => Laws.rd_at(T, q, i), a, a2, Equal.sym(Array<T>, a2, a, ea))), hw, ew, hle, room2, ih, PC.clone_wf(T, d, out, wf))

# the rows part of CPHyp (the index bound dropped)
def cp_rows_k(~T: Data, +i: U32, +off: U32, +w: U32, +d: Nat, -a: Array<T>, -out: Array<T>, +k: U32, h: {U32.is_lt(U32.add(off, k), w) == True{} : Bool} & {Laws.rdN(T, d, out, U32.add(off, k)) == Laws.rd_at(T, a, k) : T}) -> {Laws.rdN(T, d, out, U32.add(off, k)) == Laws.rd_at(T, a, k) : T}:
  (lt, eq) = h
  eq

def cp_rows(~T: Data, +i: U32, +off: U32, +w: U32, +d: Nat, -a: Array<T>, -out: Array<T>, g: CPHyp(~T, i, off, w, d, a, out)) -> @k: U32 -> {U32.is_lt(k, i) == True{} : Bool} -> {Laws.rdN(T, d, out, U32.add(off, k)) == Laws.rd_at(T, a, k) : T}:
  +k => hk => cp_rows_k(~T, i, off, w, d, a, out, k, g(k, hk))

def cp_zero(~T: Data, +i: U32, +off: U32, +w: U32, +d: Nat, -a: Array<T>, -out0: Array<T>, out: Array<T>, wf: Laws.WFArray(T, d, out),
  wr: &b: Array<T> -> &x: T -> {b == a : Array<T>} & {Array.get(T, a, i) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, i) : T})
  -> CPGoal(~T, 0n, i, off, w, d, a, out0, out, Array.get(T, a, i)):
  (a2, +x, ea, e1, ex) = wr
  %Equal.sym(Array<T> & T, Array.get(T, a, i), (a, x), e1) : CPGoal(~T, 0n, i, off, w, d, a, out0, out, _)
  g => low => (out, {==}, wf, cp_rows(~T, i, off, w, d, a, out, g), low)

# Kernel.copy_into.go with f steps left at counter i and write index w = off + i (>= off), the next f
# write indices below 2^d: afterwards every k < addn(i, f) holds a[k] at off + k and the slots below
# off are kept
def cp_go(~T: Data, f: Nat, +i: U32, +off: U32, +w: U32, +d: Nat, a: Array<T>, out: Array<T>, wf: Laws.WFArray(T, d, out), +ew: {w == U32.add(off, i) : U32}, +hle: {U32.is_le(off, w) == True{} : Bool}, room: Laws.Room(d, w, f), -out0: Array<T>) -> CPGoal(~T, f, i, off, w, d, a, out0, out, Array.get(T, a, i)):
  match f:
    case 0n:
      cp_zero(~T, i, off, w, d, a, out0, out, wf, PC.get_w(T, a, i))
    case 1n++p:
      cp_step1(~T, p, i, off, w, d, a, out0, out, wf, ew, hle, room, a2 => c => wc => ew2 => hle2 => room2 => cp_go(~T, p, U32.inc(i), off, U32.inc(w), d, a2, c, wc, ew2, hle2, room2, out0), PC.get_w(T, a, i))

# ---- Kernel.copy_into(n, off, out, a): the whole copy as a witness ------------------------------------------

def CPW(~T: Data, +n: U32, +off: U32, +d: Nat, -a: Array<T>, -out0: Array<T>) -> Type:
  &o: Array<T> -> {K.Kernel.copy_into(~T, n, off, out0, a) == o : Array<T>} & CPRes(~T, off, d, a, out0, o, n)

def cphyp0(~T: Data, +off: U32, +d: Nat, -a: Array<T>, -out: Array<T>) -> CPHyp(~T, 0, off, off, d, a, out):
  +k => hk => Empty.absurd({U32.is_lt(U32.add(off, k), off) == True{} : Bool} & {Laws.rdN(T, d, out, U32.add(off, k)) == Laws.rd_at(T, a, k) : T}, PC.lt0(k, hk))

def cplow0(~T: Data, +off: U32, +d: Nat, -out: Array<T>) -> CPLow(~T, off, d, out, out):
  +j => hj => {==}

def cp_fin(~T: Data, +n: U32, +off: U32, +d: Nat, -a: Array<T>, -out0: Array<T>, w: &o: Array<T> -> {K.Kernel.copy_into.go(~T, U32.to_nat(n), 0, off, out0, Array.get(T, a, 0)) == o : Array<T>} & CPRes(~T, off, d, a, out0, o, Laws.addn(0, U32.to_nat(n)))) -> CPW(~T, n, off, d, a, out0):
  %B.addn_to_nat(n) : &o: Array<T> -> {K.Kernel.copy_into(~T, n, off, out0, a) == o : Array<T>} & CPRes(~T, off, d, a, out0, o, _)
  w

# the copy of n rows of a at off into out (well formed, to_nat(off) + to_nat(n) <= 2^d)
def copy_into_w(~T: Data, +n: U32, +off: U32, +d: Nat, a: Array<T>, out: Array<T>, wf: Laws.WFArray(T, d, out), fits: {Nat.is_le(Nat.add(U32.to_nat(off), U32.to_nat(n)), U32.to_nat(U32.shln(1, d))) == True{} : Bool}) -> CPW(~T, n, off, d, a, out):
  cp_fin(~T, n, off, d, a, out, cp_go(~T, U32.to_nat(n), 0, off, off, d, a, out, wf, Equal.sym(U32, U32.add(off, 0), off, PC.u_add0(off)), le_refl_u(off), B.room_of(U32.to_nat(n), d, off)(fits), out)(cphyp0(~T, off, d, a, out))(cplow0(~T, off, d, out)))

# ---- Kernel.append: the two copies composed (template; Laws.append_cells is the U32 instance) --------

# the rows of a in the output of the second copy: the low slots kept, the first copy's rows at 0 + k
def app_left(~T: Data, +na: U32, +d: Nat, -a: Array<T>, -o1: Array<T>, -o2: Array<T>,
  rows1: @k: U32 -> {U32.is_lt(k, na) == True{} : Bool} -> {Laws.rdN(T, d, o1, U32.add(0, k)) == Laws.rd_at(T, a, k) : T},
  low2: CPLow(~T, na, d, o1, o2))
  -> @k: U32 -> {U32.is_lt(k, na) == True{} : Bool} -> {Laws.rdN(T, d, o2, k) == Laws.rd_at(T, a, k) : T}:
  +k => +hk => Equal.trans(T, Laws.rdN(T, d, o2, k), Laws.rdN(T, d, o1, k), Laws.rd_at(T, a, k), low2(k, hk), (%u_add0_l(k) : {Laws.rdN(T, d, o1, _) == Laws.rd_at(T, a, k) : T}; rows1(k, hk)))

# Kernel.append's answer as a template witness
def TAppendW(~T: Data, -a: Array<T>, -b: Array<T>, +na: U32, +nb: U32, +d: Nat, +z: T) -> Type:
  &o: Array<T> -> {K.Kernel.append(~T, na, nb, d, a, b, z) == o : Array<T>} & Laws.WFArray(T, d, o) & (@k: U32 -> {U32.is_lt(k, na) == True{} : Bool} -> {Laws.rdN(T, d, o, k) == Laws.rd_at(T, a, k) : T}) & (@k: U32 -> {U32.is_lt(k, nb) == True{} : Bool} -> {Laws.rdN(T, d, o, U32.add(na, k)) == Laws.rd_at(T, b, k) : T})

def append_w2(~T: Data, +na: U32, +nb: U32, +d: Nat, -a: Array<T>, -b: Array<T>, +z: T, -o1: Array<T>,
  rows1: @k: U32 -> {U32.is_lt(k, na) == True{} : Bool} -> {Laws.rdN(T, d, o1, U32.add(0, k)) == Laws.rd_at(T, a, k) : T},
  w2: CPW(~T, nb, na, d, b, o1))
  -> &o: Array<T> -> {K.Kernel.copy_into(~T, nb, na, o1, b) == o : Array<T>} & Laws.WFArray(T, d, o) & (@k: U32 -> {U32.is_lt(k, na) == True{} : Bool} -> {Laws.rdN(T, d, o, k) == Laws.rd_at(T, a, k) : T}) & (@k: U32 -> {U32.is_lt(k, nb) == True{} : Bool} -> {Laws.rdN(T, d, o, U32.add(na, k)) == Laws.rd_at(T, b, k) : T}):
  (o2, eq2, wo2, rows2, low2) = w2
  (o2, eq2, wo2, app_left(~T, na, d, a, o1, o2, rows1, low2), rows2)

def append_w1(~T: Data, +na: U32, +nb: U32, +d: Nat, -a: Array<T>, b: Array<T>, +z: T, fits: Laws.CatFits(na, nb, d), w1: CPW(~T, na, 0, d, a, Array.new(T, d, z))) -> TAppendW(~T, a, b, na, nb, d, z):
  (o1, eq1, wo1, rows1, low1) = w1
  %Equal.sym(Array<T>, K.Kernel.copy_into(~T, na, 0, Array.new(T, d, z), a), o1, eq1) : &o: Array<T> -> {K.Kernel.copy_into(~T, nb, na, _, b) == o : Array<T>} & Laws.WFArray(T, d, o) & (@k: U32 -> {U32.is_lt(k, na) == True{} : Bool} -> {Laws.rdN(T, d, o, k) == Laws.rd_at(T, a, k) : T}) & (@k: U32 -> {U32.is_lt(k, nb) == True{} : Bool} -> {Laws.rdN(T, d, o, U32.add(na, k)) == Laws.rd_at(T, b, k) : T})
  append_w2(~T, na, nb, d, a, b, z, o1, rows1, copy_into_w(~T, nb, na, d, b, o1, wo1, fits))

# na <= na + nb <= 2^d: the first copy's room
def cat_fits_left(+na: U32, +nb: U32, +d: Nat, fits: Laws.CatFits(na, nb, d)) -> {Nat.is_le(Nat.add(U32.to_nat(0), U32.to_nat(na)), U32.to_nat(U32.shln(1, d))) == True{} : Bool}:
  PST.nat_le_trans(U32.to_nat(na), Nat.add(U32.to_nat(na), U32.to_nat(nb)), U32.to_nat(U32.shln(1, d)), nat_le_add_r(U32.to_nat(na), U32.to_nat(nb)), fits)

def append_w(~T: Data, +na: U32, +nb: U32, +d: Nat, a: Array<T>, b: Array<T>, +z: T, +fits: {Nat.is_le(Nat.add(U32.to_nat(na), U32.to_nat(nb)), U32.to_nat(U32.shln(1, d))) == True{} : Bool}) -> TAppendW(~T, a, b, na, nb, d, z):
  append_w1(~T, na, nb, d, a, b, z, fits, copy_into_w(~T, na, 0, d, a, Array.new(T, d, z), Laws.wf_new(T, d, z), cat_fits_left(na, nb, d, fits)))

def Laws.append_cells(na, nb, d, a, b, z, fits):
  append_w(~U32, na, nb, d, a, b, z, fits)

# ---- rd_at of a well-formed array, twice: a copy whose every cell reads as the model of the original,
#      with two foralls (one per consumer) ------------------------------------------------------------

def RdAll2(~T: Data, +d: Nat, -o: Array<T>) -> Type:
  &o2: Array<T> -> {o2 == o : Array<T>} & Laws.WFArray(T, d, o2) & (@k: U32 -> {Laws.rd_at(T, o2, k) == Laws.rdN(T, d, o, k) : T}) & (@k: U32 -> {Laws.rd_at(T, o2, k) == Laws.rdN(T, d, o, k) : T})

def rd_all2_k(~T: Data, +d: Nat, -o: Array<T>, -o1: Array<T>, +e1: {o1 == o : Array<T>}, cv1: @k: U32 -> {Laws.rd_at(T, o, k) == Laws.rdN(T, d, o, k) : T},
  w: &o2: Array<T> -> {o2 == o1 : Array<T>} & Laws.WFArray(T, d, o2) & (@k: U32 -> {Laws.rd_at(T, o1, k) == Laws.rdN(T, d, o1, k) : T}))
  -> RdAll2(~T, d, o):
  (o2, +e2, w2, cv2) = w
  (o2, Equal.trans(Array<T>, o2, o1, o, e2, e1), w2, +k => Equal.trans(T, Laws.rd_at(T, o2, k), Laws.rd_at(T, o, k), Laws.rdN(T, d, o, k), Equal.cong(Array<T>, T, q => Laws.rd_at(T, q, k), o2, o, Equal.trans(Array<T>, o2, o1, o, e2, e1)), cv1(k)), +k => Equal.trans(T, Laws.rd_at(T, o2, k), Laws.rd_at(T, o1, k), Laws.rdN(T, d, o, k), Equal.cong(Array<T>, T, q => Laws.rd_at(T, q, k), o2, o1, e2), Equal.trans(T, Laws.rd_at(T, o1, k), Laws.rdN(T, d, o1, k), Laws.rdN(T, d, o, k), cv2(k), Equal.cong(Array<T>, T, q => Laws.rdN(T, d, q, k), o1, o, e1))))

def rd_all2_j(~T: Data, +d: Nat, -o: Array<T>, w: &o1: Array<T> -> {o1 == o : Array<T>} & Laws.WFArray(T, d, o1) & (@k: U32 -> {Laws.rd_at(T, o, k) == Laws.rdN(T, d, o, k) : T})) -> RdAll2(~T, d, o):
  (o1, +e1, w1, cv1) = w
  rd_all2_k(~T, d, o, o1, e1, cv1, PST.rd_all(T, d, o1, w1))

def rd_all2(~T: Data, +d: Nat, o: Array<T>, wf: Laws.WFArray(T, d, o)) -> RdAll2(~T, d, o):
  rd_all2_j(~T, d, o, PST.rd_all(T, d, o, wf))

# ---- Strs.decode as a forall over the rows ------------------------------------------------------------

def DecodeW(-s: ST.Strs, +n: U32, +d: Nat) -> Type:
  &o: Array<String> -> {ST.Strs.decode(n, d, s) == o : Array<String>} & (@i: U32 -> {U32.is_lt(i, n) == True{} : Bool} -> {Laws.rd_at(String, o, i) == Laws.scell(s, i) : String})

def decode_w_dict_k(+n: U32, +d: Nat, -codes: Array<U32>, +k: U32, +dd: Nat, -strs: Array<String>, +b: Nat, -slots: Array<ST.SSlot>, +tag: U32, -o: Array<String>, pm: Array<U32>, spec: @i: U32 -> {U32.is_lt(i, n) == True{} : Bool} -> {Laws.rdN(String, d, o, i) == Laws.rd_at(String, strs, Laws.rd_at(U32, codes, i)) : String},
  w: &o2: Array<String> -> {o2 == o : Array<String>} & Laws.WFArray(String, d, o2) & (@i: U32 -> {Laws.rd_at(String, o, i) == Laws.rdN(String, d, o, i) : String}))
  -> &o3: Array<String> -> {ST.Strs.fst(~String, (o, pm)) == o3 : Array<String>} & (@i: U32 -> {U32.is_lt(i, n) == True{} : Bool} -> {Laws.rd_at(String, o3, i) == Laws.scell(ST.SDict{codes, ST.Dict{k, dd, strs, b, slots, tag}}, i) : String}):
  (o2, +e2, w2, cv) = w
  (o2, Equal.sym(Array<String>, o2, o, e2), +i => hi => Equal.trans(String, Laws.rd_at(String, o2, i), Laws.rd_at(String, o, i), Laws.rd_at(String, strs, Laws.rd_at(U32, codes, i)), Equal.cong(Array<String>, String, q => Laws.rd_at(String, q, i), o2, o, e2), Equal.trans(String, Laws.rd_at(String, o, i), Laws.rdN(String, d, o, i), Laws.rd_at(String, strs, Laws.rd_at(U32, codes, i)), cv(i), spec(i, hi))))

def decode_w_dict(+n: U32, +d: Nat, -codes: Array<U32>, +k: U32, +dd: Nat, -strs: Array<String>, +b: Nat, -slots: Array<ST.SSlot>, +tag: U32, w: PST.TGW(~String, d, n, strs, codes, "")) -> DecodeW(ST.SDict{codes, ST.Dict{k, dd, strs, b, slots, tag}}, n, d):
  (o, pm, eq, epm, wo, spec) = w
  %Equal.sym(Array<String> & Array<U32>, K.Kernel.gather(~String, n, d, strs, codes, ""), (o, pm), eq) : &o3: Array<String> -> {ST.Strs.fst(~String, _) == o3 : Array<String>} & (@i: U32 -> {U32.is_lt(i, n) == True{} : Bool} -> {Laws.rd_at(String, o3, i) == Laws.scell(ST.SDict{codes, ST.Dict{k, dd, strs, b, slots, tag}}, i) : String})
  decode_w_dict_k(n, d, codes, k, dd, strs, b, slots, tag, o, pm, spec, PST.rd_all(String, d, o, wo))

def decode_w_d(+n: U32, +d: Nat, codes: Array<U32>, dict: ST.Dict, fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}) -> DecodeW(ST.SDict{codes, dict}, n, d):
  match dict:
    case ST.Dict{+k, +dd, strs, +b, slots, +tag}:
      decode_w_dict(n, d, codes, k, dd, strs, b, slots, tag, PST.tgather_w(~String, d, n, strs, codes, "", fits))

# Strs.decode(n, d, s) for n <= 2^d: an array whose every row below n reads as scell(s, i)
def decode_w(+n: U32, +d: Nat, s: ST.Strs, fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}) -> DecodeW(s, n, d):
  match s:
    case ST.SRaw{a}:
      (a, {==}, +i => hi => {==})
    case ST.SDict{codes, dict}:
      decode_w_d(n, d, codes, dict, fits)

# ---- Strs.append, the Raw branch: both sides decoded, the String append -----------------------------------

# the Raw branch's conclusion over the decoded arrays A, B
def SAppRaw(-xa: ST.Strs, -xb: ST.Strs, +na: U32, +nb: U32, +d: Nat, -A: Array<String>, -B: Array<String>) -> Type:
  &o: ST.Strs -> {ST.SRaw{K.Kernel.append(~String, na, nb, d, A, B, "")} == o : ST.Strs} & (@k: U32 -> {U32.is_lt(k, na) == True{} : Bool} -> {Laws.scell(o, k) == Laws.scell(xa, k) : String}) & (@k: U32 -> {U32.is_lt(k, nb) == True{} : Bool} -> {Laws.scell(o, U32.add(na, k)) == Laws.scell(xb, k) : String})

def sapp_raw3(-xa: ST.Strs, -xb: ST.Strs, +na: U32, +nb: U32, +d: Nat, -A: Array<String>, -B: Array<String>, -o: Array<String>,
  ca: @i: U32 -> {U32.is_lt(i, na) == True{} : Bool} -> {Laws.rd_at(String, A, i) == Laws.scell(xa, i) : String},
  cb: @i: U32 -> {U32.is_lt(i, nb) == True{} : Bool} -> {Laws.rd_at(String, B, i) == Laws.scell(xb, i) : String},
  left: @k: U32 -> {U32.is_lt(k, na) == True{} : Bool} -> {Laws.rdN(String, d, o, k) == Laws.rd_at(String, A, k) : String},
  right: @k: U32 -> {U32.is_lt(k, nb) == True{} : Bool} -> {Laws.rdN(String, d, o, U32.add(na, k)) == Laws.rd_at(String, B, k) : String},
  w: RdAll2(~String, d, o))
  -> &o3: ST.Strs -> {ST.SRaw{o} == o3 : ST.Strs} & (@k: U32 -> {U32.is_lt(k, na) == True{} : Bool} -> {Laws.scell(o3, k) == Laws.scell(xa, k) : String}) & (@k: U32 -> {U32.is_lt(k, nb) == True{} : Bool} -> {Laws.scell(o3, U32.add(na, k)) == Laws.scell(xb, k) : String}):
  (o2, +e2, w2, cv1, cv2) = w
  (ST.SRaw{o2}, (%Equal.sym(Array<String>, o2, o, e2) : {ST.SRaw{o} == ST.SRaw{_} : ST.Strs}; {==}), +k => +hk => Equal.trans(String, Laws.rd_at(String, o2, k), Laws.rdN(String, d, o, k), Laws.scell(xa, k), cv1(k), Equal.trans(String, Laws.rdN(String, d, o, k), Laws.rd_at(String, A, k), Laws.scell(xa, k), left(k, hk), ca(k, hk))), +k => +hk => Equal.trans(String, Laws.rd_at(String, o2, U32.add(na, k)), Laws.rdN(String, d, o, U32.add(na, k)), Laws.scell(xb, k), cv2(U32.add(na, k)), Equal.trans(String, Laws.rdN(String, d, o, U32.add(na, k)), Laws.rd_at(String, B, k), Laws.scell(xb, k), right(k, hk), cb(k, hk))))

def sapp_raw2(-xa: ST.Strs, -xb: ST.Strs, +na: U32, +nb: U32, +d: Nat, -A: Array<String>, -B: Array<String>,
  ca: @i: U32 -> {U32.is_lt(i, na) == True{} : Bool} -> {Laws.rd_at(String, A, i) == Laws.scell(xa, i) : String},
  cb: @i: U32 -> {U32.is_lt(i, nb) == True{} : Bool} -> {Laws.rd_at(String, B, i) == Laws.scell(xb, i) : String},
  w: TAppendW(~String, A, B, na, nb, d, ""))
  -> SAppRaw(xa, xb, na, nb, d, A, B):
  (o, eq, wo, left, right) = w
  %Equal.sym(Array<String>, K.Kernel.append(~String, na, nb, d, A, B, ""), o, eq) : &o3: ST.Strs -> {ST.SRaw{_} == o3 : ST.Strs} & (@k: U32 -> {U32.is_lt(k, na) == True{} : Bool} -> {Laws.scell(o3, k) == Laws.scell(xa, k) : String}) & (@k: U32 -> {U32.is_lt(k, nb) == True{} : Bool} -> {Laws.scell(o3, U32.add(na, k)) == Laws.scell(xb, k) : String})
  sapp_raw3(xa, xb, na, nb, d, A, B, o, ca, cb, left, right, rd_all2(~String, d, o, wo))

def sapp_raw1(-xa: ST.Strs, -xb: ST.Strs, +na: U32, +nb: U32, +da: Nat, +db: Nat, +d: Nat, +fits: {Nat.is_le(Nat.add(U32.to_nat(na), U32.to_nat(nb)), U32.to_nat(U32.shln(1, d))) == True{} : Bool}, wa: DecodeW(xa, na, da), wb: DecodeW(xb, nb, db))
  -> &o: ST.Strs -> {ST.SRaw{K.Kernel.append(~String, na, nb, d, ST.Strs.decode(na, da, xa), ST.Strs.decode(nb, db, xb), "")} == o : ST.Strs} & (@k: U32 -> {U32.is_lt(k, na) == True{} : Bool} -> {Laws.scell(o, k) == Laws.scell(xa, k) : String}) & (@k: U32 -> {U32.is_lt(k, nb) == True{} : Bool} -> {Laws.scell(o, U32.add(na, k)) == Laws.scell(xb, k) : String}):
  (A, eA, ca) = wa
  (B, eB, cb) = wb
  %Equal.sym(Array<String>, ST.Strs.decode(na, da, xa), A, eA) : SAppRaw(xa, xb, na, nb, d, _, ST.Strs.decode(nb, db, xb))
  %Equal.sym(Array<String>, ST.Strs.decode(nb, db, xb), B, eB) : SAppRaw(xa, xb, na, nb, d, A, _)
  sapp_raw2(xa, xb, na, nb, d, A, B, ca, cb, append_w(~String, na, nb, d, A, B, "", fits))

def sapp_raw(xa: ST.Strs, xb: ST.Strs, +na: U32, +nb: U32, +da: Nat, +db: Nat, +d: Nat, fa: {U32.is_le(na, U32.shln(1, da)) == True{} : Bool}, fb: {U32.is_le(nb, U32.shln(1, db)) == True{} : Bool}, +fits: {Nat.is_le(Nat.add(U32.to_nat(na), U32.to_nat(nb)), U32.to_nat(U32.shln(1, d))) == True{} : Bool})
  -> &o: ST.Strs -> {ST.SRaw{K.Kernel.append(~String, na, nb, d, ST.Strs.decode(na, da, xa), ST.Strs.decode(nb, db, xb), "")} == o : ST.Strs} & (@k: U32 -> {U32.is_lt(k, na) == True{} : Bool} -> {Laws.scell(o, k) == Laws.scell(xa, k) : String}) & (@k: U32 -> {U32.is_lt(k, nb) == True{} : Bool} -> {Laws.scell(o, U32.add(na, k)) == Laws.scell(xb, k) : String}):
  sapp_raw1(xa, xb, na, nb, da, db, d, fits, decode_w(na, da, xa, fa), decode_w(nb, db, xb, fb))

# ---- Strs.append, two Dictionaries: b's entries merged into a's (dict_merge_spec), b's codes re-coded
#      through the map (gather), a's codes first (append); a's cells by Keep, b's by EncRows -------------
#
# The row facts are foralls over CODES (Keep over a's old codes, EncRows over the map's slots), and a
# row's code is the model term rd_at(ca, k), which as a TERM consumes the array. So the code arrays
# and the map are cloned: one copy goes into the production term, the other is READ (get_w) inside
# the per-row lambda, which hands a Data code with its equation to the forall.

# the cells of a: the output's row k is a's code, which keeps its entry in the extended dictionary
def LeftS(-o: ST.Strs, -ca: Array<U32>, -dca: ST.Dict, +na: U32) -> Type:
  @k: U32 -> {U32.is_lt(k, na) == True{} : Bool} -> {Laws.scell(o, k) == Laws.scell(ST.SDict{ca, dca}, k) : String}

# the cells of b: the output's row na + k is the re-coded code of b's row k
def RightS(-o: ST.Strs, -cb: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, +na: U32, +nb: U32) -> Type:
  @k: U32 -> {U32.is_lt(k, nb) == True{} : Bool} -> {Laws.scell(o, U32.add(na, k)) == Laws.scell(ST.SDict{cb, ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}}, k) : String}

# Keep per row of a's codes (on the copy ca2 of the code array)
def KeepA(-ca2: Array<U32>, -dca: ST.Dict, -dst2: ST.Dict, +na: U32) -> Type:
  @k: U32 -> {U32.is_lt(k, na) == True{} : Bool} -> {Laws.dentry(dst2, Laws.rd_at(U32, ca2, k)) == Laws.dentry(dca, Laws.rd_at(U32, ca2, k)) : String}

# the goal after the merge: the production's storage over the map m and the extended dictionary dst2
def SG1(-ca: Array<U32>, -cb: Array<U32>, -dca: ST.Dict, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, +na: U32, +nb: U32, +db: Nat, +d: Nat, -m: Array<U32>, -dst2: ST.Dict) -> Type:
  &o: ST.Strs -> {ST.SDict{K.Kernel.append(~U32, na, nb, d, ca, ST.Strs.fst(~U32, K.Kernel.gather(~U32, nb, db, m, cb, 0)), 0), dst2} == o : ST.Strs} & LeftS(o, ca, dca, na) & RightS(o, cb, kb, ddb, strsb, bb, slotsb, tagb, na, nb)

# ... with the gather's result pair in place
def SG2(-ca: Array<U32>, -cb: Array<U32>, -dca: ST.Dict, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, +na: U32, +nb: U32, +d: Nat, -r: Array<U32> & Array<U32>, -dst2: ST.Dict) -> Type:
  &o: ST.Strs -> {ST.SDict{K.Kernel.append(~U32, na, nb, d, ca, ST.Strs.fst(~U32, r), 0), dst2} == o : ST.Strs} & LeftS(o, ca, dca, na) & RightS(o, cb, kb, ddb, strsb, bb, slotsb, tagb, na, nb)

# ... with the re-coded array o1 in place
def SG3(-ca: Array<U32>, -cb: Array<U32>, -dca: ST.Dict, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, +na: U32, +nb: U32, +d: Nat, -o1: Array<U32>, -dst2: ST.Dict) -> Type:
  &o: ST.Strs -> {ST.SDict{K.Kernel.append(~U32, na, nb, d, ca, o1, 0), dst2} == o : ST.Strs} & LeftS(o, ca, dca, na) & RightS(o, cb, kb, ddb, strsb, bb, slotsb, tagb, na, nb)

# ... with the appended array o in place
def SG4(-ca: Array<U32>, -cb: Array<U32>, -dca: ST.Dict, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, +na: U32, +nb: U32, -o: Array<U32>, -dst2: ST.Dict) -> Type:
  &o3: ST.Strs -> {ST.SDict{o, dst2} == o3 : ST.Strs} & LeftS(o3, ca, dca, na) & RightS(o3, cb, kb, ddb, strsb, bb, slotsb, tagb, na, nb)

# a's rows: the output code is a's code (append's left clause), whose entry is kept (keepA)
def sapp_left(-ca1: Array<U32>, -ca2: Array<U32>, -dca: ST.Dict, +k2: U32, +dd2: Nat, -strs2: Array<String>, +b2: Nat, -slots2: Array<ST.SSlot>, +tag2: U32, +na: U32, +d: Nat, -o: Array<U32>, -o2: Array<U32>, +e21: {ca2 == ca1 : Array<U32>},
  cvA: @k: U32 -> {Laws.rd_at(U32, o2, k) == Laws.rdN(U32, d, o, k) : U32},
  left: @k: U32 -> {U32.is_lt(k, na) == True{} : Bool} -> {Laws.rdN(U32, d, o, k) == Laws.rd_at(U32, ca1, k) : U32},
  keepA: KeepA(ca2, dca, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}, na))
  -> LeftS(ST.SDict{o2, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}}, ca1, dca, na):
  +k => +hk =>
    %Equal.sym(U32, Laws.rd_at(U32, o2, k), Laws.rd_at(U32, ca1, k), Equal.trans(U32, Laws.rd_at(U32, o2, k), Laws.rdN(U32, d, o, k), Laws.rd_at(U32, ca1, k), cvA(k), left(k, hk))) : {Laws.rd_at(String, strs2, _) == Laws.dentry(dca, Laws.rd_at(U32, ca1, k)) : String}
    %e21 : {Laws.rd_at(String, strs2, Laws.rd_at(U32, _, k)) == Laws.dentry(dca, Laws.rd_at(U32, _, k)) : String}
    keepA(k, hk)

# the code names b's entry in the extended dictionary (EncRows' clause), which the extended entry
# array holds (WFDictE's entry clause, the word bound from the list bound)
def sapp_right_fin(+kb: U32, +ddb: Nat, -strsb: Array<String>, +k2: U32, -strs2: Array<String>, +es2: List<&2, String>, +ek2: {U32.to_nat(k2) == List.length(&2, String, es2) : Nat}, +c: U32, +code: U32,
  ent: @c2: U32 -> {U32.is_lt(c2, k2) == True{} : Bool} -> {Laws.rd_at(String, strs2, c2) == Laws.nthd(es2, c2) : String},
  h: {Cmp.is_lt(Nat.cmp(U32.to_nat(code), List.length(&2, String, es2))) == True{} : Bool} & {Laws.nthd(es2, code) == Laws.rd_at(String, strsb, c) : String})
  -> {Laws.rd_at(String, strs2, code) == Laws.rd_at(String, strsb, c) : String}:
  (+hb, hdec) = h
  Equal.trans(String, Laws.rd_at(String, strs2, code), Laws.nthd(es2, code), Laws.rd_at(String, strsb, c), ent(code, PST.lt_u_of_nat(code, k2, (%Equal.sym(Nat, U32.to_nat(k2), List.length(&2, String, es2), ek2) : {Cmp.is_lt(Nat.cmp(U32.to_nat(code), _)) == True{} : Bool}; hb))), hdec)

# one row of b with its code c (Data, = b's row k) and the map's slot code (Data, = m[c]): the output
# code at na + k is code (the chain through append, gather and the map copies); code names b's entry
# in the extended dictionary (EncRows), which the extended entry array holds (WFDictE's entry clause)
def sapp_right_row(+kb: U32, +ddb: Nat, -strsb: Array<String>, -cb: Array<U32>, -cb1: Array<U32>, +k2: U32, -strs2: Array<String>, +es2: List<&2, String>, +na: U32, +nb: U32, +d: Nat, +db: Nat, -o: Array<U32>, -o2: Array<U32>, -o1: Array<U32>, -o1b: Array<U32>, -m: Array<U32>, -m2: Array<U32>,
  +eo1: {o1b == o1 : Array<U32>}, +em2: {m2 == m : Array<U32>}, +ecb1: {cb1 == cb : Array<U32>}, +ek2: {U32.to_nat(k2) == List.length(&2, String, es2) : Nat}, +k: U32, +hk: {U32.is_lt(k, nb) == True{} : Bool},
  +c: U32, +ec: {c == Laws.rd_at(U32, cb, k) : U32}, +code: U32, +ecode: {code == Laws.rd_at(U32, m, c) : U32},
  cvB: @j: U32 -> {Laws.rd_at(U32, o2, j) == Laws.rdN(U32, d, o, j) : U32},
  right: @j: U32 -> {U32.is_lt(j, nb) == True{} : Bool} -> {Laws.rdN(U32, d, o, U32.add(na, j)) == Laws.rd_at(U32, o1b, j) : U32},
  cv1: @j: U32 -> {Laws.rd_at(U32, o1, j) == Laws.rdN(U32, db, o1, j) : U32},
  spec1: @j: U32 -> {U32.is_lt(j, nb) == True{} : Bool} -> {Laws.rdN(U32, db, o1, j) == Laws.rd_at(U32, m2, Laws.rd_at(U32, cb1, j)) : U32},
  cvm: @j: U32 -> {Laws.rd_at(U32, m, j) == Laws.rdN(U32, ddb, m, j) : U32},
  rows: Laws.EncRows(kb, ddb, strsb, m, es2), hc: {U32.is_lt(Laws.rd_at(U32, cb, k), kb) == True{} : Bool},
  ent: @c2: U32 -> {U32.is_lt(c2, k2) == True{} : Bool} -> {Laws.rd_at(String, strs2, c2) == Laws.nthd(es2, c2) : String})
  -> {Laws.rd_at(String, strs2, Laws.rd_at(U32, o2, U32.add(na, k))) == Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, k)) : String}:
  %ec : {Laws.rd_at(String, strs2, Laws.rd_at(U32, o2, U32.add(na, k))) == Laws.rd_at(String, strsb, _) : String}
  %Equal.sym(U32, Laws.rd_at(U32, o2, U32.add(na, k)), code, Equal.trans(U32, Laws.rd_at(U32, o2, U32.add(na, k)), Laws.rdN(U32, d, o, U32.add(na, k)), code, cvB(U32.add(na, k)),
    Equal.trans(U32, Laws.rdN(U32, d, o, U32.add(na, k)), Laws.rd_at(U32, o1b, k), code, right(k, hk),
      Equal.trans(U32, Laws.rd_at(U32, o1b, k), Laws.rd_at(U32, o1, k), code, Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, k), o1b, o1, eo1),
        Equal.trans(U32, Laws.rd_at(U32, o1, k), Laws.rdN(U32, db, o1, k), code, cv1(k),
          Equal.trans(U32, Laws.rdN(U32, db, o1, k), Laws.rd_at(U32, m2, Laws.rd_at(U32, cb1, k)), code, spec1(k, hk),
            Equal.trans(U32, Laws.rd_at(U32, m2, Laws.rd_at(U32, cb1, k)), Laws.rd_at(U32, m, c), code, Equal.trans(U32, Laws.rd_at(U32, m2, Laws.rd_at(U32, cb1, k)), Laws.rd_at(U32, m, Laws.rd_at(U32, cb1, k)), Laws.rd_at(U32, m, c), Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, Laws.rd_at(U32, cb1, k)), m2, m, em2), Equal.cong(U32, U32, q => Laws.rd_at(U32, m, q), Laws.rd_at(U32, cb1, k), c, Equal.trans(U32, Laws.rd_at(U32, cb1, k), Laws.rd_at(U32, cb, k), c, Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, k), cb1, cb, ecb1), Equal.sym(U32, c, Laws.rd_at(U32, cb, k), ec)))), Equal.sym(U32, code, Laws.rd_at(U32, m, c), ecode)))))))) : {Laws.rd_at(String, strs2, _) == Laws.rd_at(String, strsb, c) : String}
  sapp_right_fin(kb, ddb, strsb, k2, strs2, es2, ek2, c, code, ent, rows(c, (%Equal.sym(U32, c, Laws.rd_at(U32, cb, k), ec) : {U32.is_lt(_, kb) == True{} : Bool}; hc), code, Equal.trans(U32, code, Laws.rd_at(U32, m, c), Laws.rdN(U32, ddb, m, c), ecode, cvm(c))))

# the map's slot at c read on the copy m3
def sapp_right_m(+kb: U32, +ddb: Nat, -strsb: Array<String>, -cb: Array<U32>, -cb1: Array<U32>, +k2: U32, -strs2: Array<String>, +es2: List<&2, String>, +na: U32, +nb: U32, +d: Nat, +db: Nat, -o: Array<U32>, -o2: Array<U32>, -o1: Array<U32>, -o1b: Array<U32>, -m: Array<U32>, -m2: Array<U32>, -m3: Array<U32>,
  +eo1: {o1b == o1 : Array<U32>}, +em2: {m2 == m : Array<U32>}, +em3: {m3 == m : Array<U32>}, +ecb1: {cb1 == cb : Array<U32>}, +ek2: {U32.to_nat(k2) == List.length(&2, String, es2) : Nat}, +k: U32, +hk: {U32.is_lt(k, nb) == True{} : Bool},
  +c: U32, +ec: {c == Laws.rd_at(U32, cb, k) : U32},
  cvB: @j: U32 -> {Laws.rd_at(U32, o2, j) == Laws.rdN(U32, d, o, j) : U32},
  right: @j: U32 -> {U32.is_lt(j, nb) == True{} : Bool} -> {Laws.rdN(U32, d, o, U32.add(na, j)) == Laws.rd_at(U32, o1b, j) : U32},
  cv1: @j: U32 -> {Laws.rd_at(U32, o1, j) == Laws.rdN(U32, db, o1, j) : U32},
  spec1: @j: U32 -> {U32.is_lt(j, nb) == True{} : Bool} -> {Laws.rdN(U32, db, o1, j) == Laws.rd_at(U32, m2, Laws.rd_at(U32, cb1, j)) : U32},
  cvm: @j: U32 -> {Laws.rd_at(U32, m, j) == Laws.rdN(U32, ddb, m, j) : U32},
  rows: Laws.EncRows(kb, ddb, strsb, m, es2), hc: {U32.is_lt(Laws.rd_at(U32, cb, k), kb) == True{} : Bool},
  ent: @c2: U32 -> {U32.is_lt(c2, k2) == True{} : Bool} -> {Laws.rd_at(String, strs2, c2) == Laws.nthd(es2, c2) : String},
  w: &m4: Array<U32> -> &code: U32 -> {m4 == m3 : Array<U32>} & {Array.get(U32, m3, c) == (m3, code) : Array<U32> & U32} & {code == Laws.rd_at(U32, m3, c) : U32})
  -> {Laws.rd_at(String, strs2, Laws.rd_at(U32, o2, U32.add(na, k))) == Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, k)) : String}:
  (m4, +code, em4, e1, ecode) = w
  sapp_right_row(kb, ddb, strsb, cb, cb1, k2, strs2, es2, na, nb, d, db, o, o2, o1, o1b, m, m2, eo1, em2, ecb1, ek2, k, hk, c, ec, code, Equal.trans(U32, code, Laws.rd_at(U32, m3, c), Laws.rd_at(U32, m, c), ecode, Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, c), m3, m, em3)), cvB, right, cv1, spec1, cvm, rows, hc, ent)

# b's row k read on the copy cb2
def sapp_right_c(+kb: U32, +ddb: Nat, -strsb: Array<String>, -cb: Array<U32>, -cb1: Array<U32>, -cb2: Array<U32>, +k2: U32, -strs2: Array<String>, +es2: List<&2, String>, +na: U32, +nb: U32, +d: Nat, +db: Nat, -o: Array<U32>, -o2: Array<U32>, -o1: Array<U32>, -o1b: Array<U32>, -m: Array<U32>, -m2: Array<U32>, m3: Array<U32>,
  +eo1: {o1b == o1 : Array<U32>}, +em2: {m2 == m : Array<U32>}, +em3: {m3 == m : Array<U32>}, +ecb1: {cb1 == cb : Array<U32>}, +ecb2: {cb2 == cb : Array<U32>}, +ek2: {U32.to_nat(k2) == List.length(&2, String, es2) : Nat}, +k: U32, +hk: {U32.is_lt(k, nb) == True{} : Bool},
  cvB: @j: U32 -> {Laws.rd_at(U32, o2, j) == Laws.rdN(U32, d, o, j) : U32},
  right: @j: U32 -> {U32.is_lt(j, nb) == True{} : Bool} -> {Laws.rdN(U32, d, o, U32.add(na, j)) == Laws.rd_at(U32, o1b, j) : U32},
  cv1: @j: U32 -> {Laws.rd_at(U32, o1, j) == Laws.rdN(U32, db, o1, j) : U32},
  spec1: @j: U32 -> {U32.is_lt(j, nb) == True{} : Bool} -> {Laws.rdN(U32, db, o1, j) == Laws.rd_at(U32, m2, Laws.rd_at(U32, cb1, j)) : U32},
  cvm: @j: U32 -> {Laws.rd_at(U32, m, j) == Laws.rdN(U32, ddb, m, j) : U32},
  rows: Laws.EncRows(kb, ddb, strsb, m, es2), hc: {U32.is_lt(Laws.rd_at(U32, cb, k), kb) == True{} : Bool},
  ent: @c2: U32 -> {U32.is_lt(c2, k2) == True{} : Bool} -> {Laws.rd_at(String, strs2, c2) == Laws.nthd(es2, c2) : String},
  w: &cb3: Array<U32> -> &c: U32 -> {cb3 == cb2 : Array<U32>} & {Array.get(U32, cb2, k) == (cb2, c) : Array<U32> & U32} & {c == Laws.rd_at(U32, cb2, k) : U32})
  -> {Laws.rd_at(String, strs2, Laws.rd_at(U32, o2, U32.add(na, k))) == Laws.rd_at(String, strsb, Laws.rd_at(U32, cb, k)) : String}:
  (cb3, +c, ecb3, e1, ec) = w
  sapp_right_m(kb, ddb, strsb, cb, cb1, k2, strs2, es2, na, nb, d, db, o, o2, o1, o1b, m, m2, m3, eo1, em2, em3, ecb1, ek2, k, hk, c, Equal.trans(U32, c, Laws.rd_at(U32, cb2, k), Laws.rd_at(U32, cb, k), ec, Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, k), cb2, cb, ecb2)), cvB, right, cv1, spec1, cvm, rows, hc, ent, PC.get_w(U32, m3, c))

def sapp_right(-cb: Array<U32>, -cb1: Array<U32>, cb2: Array<U32>, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, +k2: U32, +dd2: Nat, -strs2: Array<String>, +b2: Nat, -slots2: Array<ST.SSlot>, +tag2: U32, +es2: List<&2, String>, +na: U32, +nb: U32, +d: Nat, +db: Nat, -o: Array<U32>, -o2: Array<U32>, -o1: Array<U32>, -o1b: Array<U32>, -m: Array<U32>, -m2: Array<U32>, m3: Array<U32>,
  +eo1: {o1b == o1 : Array<U32>}, +em2: {m2 == m : Array<U32>}, +em3: {m3 == m : Array<U32>}, +ecb1: {cb1 == cb : Array<U32>}, +ecb2: {cb2 == cb : Array<U32>}, +ek2: {U32.to_nat(k2) == List.length(&2, String, es2) : Nat},
  cvB: @j: U32 -> {Laws.rd_at(U32, o2, j) == Laws.rdN(U32, d, o, j) : U32},
  right: @j: U32 -> {U32.is_lt(j, nb) == True{} : Bool} -> {Laws.rdN(U32, d, o, U32.add(na, j)) == Laws.rd_at(U32, o1b, j) : U32},
  cv1: @j: U32 -> {Laws.rd_at(U32, o1, j) == Laws.rdN(U32, db, o1, j) : U32},
  spec1: @j: U32 -> {U32.is_lt(j, nb) == True{} : Bool} -> {Laws.rdN(U32, db, o1, j) == Laws.rd_at(U32, m2, Laws.rd_at(U32, cb1, j)) : U32},
  cvm: @j: U32 -> {Laws.rd_at(U32, m, j) == Laws.rdN(U32, ddb, m, j) : U32},
  rows: Laws.EncRows(kb, ddb, strsb, m, es2), cbb: Laws.CodesBelow(nb, cb, kb),
  ent: @c2: U32 -> {U32.is_lt(c2, k2) == True{} : Bool} -> {Laws.rd_at(String, strs2, c2) == Laws.nthd(es2, c2) : String})
  -> RightS(ST.SDict{o2, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}}, cb, kb, ddb, strsb, bb, slotsb, tagb, na, nb):
  +k => +hk => sapp_right_c(kb, ddb, strsb, cb, cb1, cb2, k2, strs2, es2, na, nb, d, db, o, o2, o1, o1b, m, m2, m3, eo1, em2, em3, ecb1, ecb2, ek2, k, hk, cvB, right, cv1, spec1, cvm, rows, cbb(k, hk), ent, PC.get_w(U32, cb2, k))

# the extended dictionary taken apart (its entry clause), the witness assembled
def sapp_dd6(-ca1: Array<U32>, -ca2: Array<U32>, -cb: Array<U32>, -cb1: Array<U32>, cb2: Array<U32>, -dca: ST.Dict, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, +na: U32, +nb: U32, +d: Nat, +db: Nat, dst2: ST.Dict, +es2: List<&2, String>, -o: Array<U32>, -o1: Array<U32>, -o1b: Array<U32>, -m: Array<U32>, -m2: Array<U32>, m3: Array<U32>,
  +eo1: {o1b == o1 : Array<U32>}, +em2: {m2 == m : Array<U32>}, +em3: {m3 == m : Array<U32>}, +e21: {ca2 == ca1 : Array<U32>}, +ecb1: {cb1 == cb : Array<U32>}, +ecb2: {cb2 == cb : Array<U32>},
  wf2: Laws.WFDictE(dst2, es2), keepA: KeepA(ca2, dca, dst2, na), rows: Laws.EncRows(kb, ddb, strsb, m, es2), cbb: Laws.CodesBelow(nb, cb, kb),
  left: @k: U32 -> {U32.is_lt(k, na) == True{} : Bool} -> {Laws.rdN(U32, d, o, k) == Laws.rd_at(U32, ca1, k) : U32},
  right: @j: U32 -> {U32.is_lt(j, nb) == True{} : Bool} -> {Laws.rdN(U32, d, o, U32.add(na, j)) == Laws.rd_at(U32, o1b, j) : U32},
  cv1: @j: U32 -> {Laws.rd_at(U32, o1, j) == Laws.rdN(U32, db, o1, j) : U32},
  spec1: @j: U32 -> {U32.is_lt(j, nb) == True{} : Bool} -> {Laws.rdN(U32, db, o1, j) == Laws.rd_at(U32, m2, Laws.rd_at(U32, cb1, j)) : U32},
  cvm: @j: U32 -> {Laws.rd_at(U32, m, j) == Laws.rdN(U32, ddb, m, j) : U32},
  w: RdAll2(~U32, d, o))
  -> SG4(ca1, cb1, dca, kb, ddb, strsb, bb, slotsb, tagb, na, nb, o, dst2):
  match dst2:
    case ST.Dict{+k2, +dd2, strs2, +b2, slots2, +tag2}:
      (+ek2, hle2, hpos2, h02, wfs2, ent, wfix2) = wf2
      (o2, +eo2, wo2, cvA, cvB) = w
      %Equal.sym(Array<U32>, cb1, cb, ecb1) : &o3: ST.Strs -> {ST.SDict{o, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}} == o3 : ST.Strs} & LeftS(o3, ca1, dca, na) & RightS(o3, _, kb, ddb, strsb, bb, slotsb, tagb, na, nb)
      (ST.SDict{o2, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}}, (%Equal.sym(Array<U32>, o2, o, eo2) : {ST.SDict{o, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}} == ST.SDict{_, ST.Dict{k2, dd2, strs2, b2, slots2, tag2}} : ST.Strs}; {==}), sapp_left(ca1, ca2, dca, k2, dd2, strs2, b2, slots2, tag2, na, d, o, o2, e21, cvA, left, keepA), sapp_right(cb, cb1, cb2, kb, ddb, strsb, bb, slotsb, tagb, k2, dd2, strs2, b2, slots2, tag2, es2, na, nb, d, db, o, o2, o1, o1b, m, m2, m3, eo1, em2, em3, ecb1, ecb2, ek2, cvB, right, cv1, spec1, cvm, rows, cbb, ent))

# the append computed
def sapp_dd5(-ca1: Array<U32>, -ca2: Array<U32>, -cb: Array<U32>, -cb1: Array<U32>, cb2: Array<U32>, -dca: ST.Dict, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, +na: U32, +nb: U32, +d: Nat, +db: Nat, dst2: ST.Dict, +es2: List<&2, String>, -o1: Array<U32>, -o1b: Array<U32>, -m: Array<U32>, -m2: Array<U32>, m3: Array<U32>,
  +eo1: {o1b == o1 : Array<U32>}, +em2: {m2 == m : Array<U32>}, +em3: {m3 == m : Array<U32>}, +e21: {ca2 == ca1 : Array<U32>}, +ecb1: {cb1 == cb : Array<U32>}, +ecb2: {cb2 == cb : Array<U32>},
  wf2: Laws.WFDictE(dst2, es2), keepA: KeepA(ca2, dca, dst2, na), rows: Laws.EncRows(kb, ddb, strsb, m, es2), cbb: Laws.CodesBelow(nb, cb, kb),
  cv1: @j: U32 -> {Laws.rd_at(U32, o1, j) == Laws.rdN(U32, db, o1, j) : U32},
  spec1: @j: U32 -> {U32.is_lt(j, nb) == True{} : Bool} -> {Laws.rdN(U32, db, o1, j) == Laws.rd_at(U32, m2, Laws.rd_at(U32, cb1, j)) : U32},
  cvm: @j: U32 -> {Laws.rd_at(U32, m, j) == Laws.rdN(U32, ddb, m, j) : U32},
  w: TAppendW(~U32, ca1, o1b, na, nb, d, 0))
  -> SG3(ca1, cb1, dca, kb, ddb, strsb, bb, slotsb, tagb, na, nb, d, o1b, dst2):
  (o, eqA, wo, left, right) = w
  %Equal.sym(Array<U32>, K.Kernel.append(~U32, na, nb, d, ca1, o1b, 0), o, eqA) : SG4(ca1, cb1, dca, kb, ddb, strsb, bb, slotsb, tagb, na, nb, _, dst2)
  sapp_dd6(ca1, ca2, cb, cb1, cb2, dca, kb, ddb, strsb, bb, slotsb, tagb, na, nb, d, db, dst2, es2, o, o1, o1b, m, m2, m3, eo1, em2, em3, e21, ecb1, ecb2, wf2, keepA, rows, cbb, left, right, cv1, spec1, cvm, rd_all2(~U32, d, o, wo))

# the re-coded codes read back (rd_all), then appended
def sapp_dd4(ca1: Array<U32>, -ca2: Array<U32>, -cb: Array<U32>, -cb1: Array<U32>, cb2: Array<U32>, -dca: ST.Dict, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, +na: U32, +nb: U32, +d: Nat, +db: Nat, dst2: ST.Dict, +es2: List<&2, String>, -o1: Array<U32>, -m: Array<U32>, -m2: Array<U32>, m3: Array<U32>,
  +em2: {m2 == m : Array<U32>}, +em3: {m3 == m : Array<U32>}, +e21: {ca2 == ca1 : Array<U32>}, +ecb1: {cb1 == cb : Array<U32>}, +ecb2: {cb2 == cb : Array<U32>}, +fits: {Nat.is_le(Nat.add(U32.to_nat(na), U32.to_nat(nb)), U32.to_nat(U32.shln(1, d))) == True{} : Bool},
  wf2: Laws.WFDictE(dst2, es2), keepA: KeepA(ca2, dca, dst2, na), rows: Laws.EncRows(kb, ddb, strsb, m, es2), cbb: Laws.CodesBelow(nb, cb, kb),
  spec1: @j: U32 -> {U32.is_lt(j, nb) == True{} : Bool} -> {Laws.rdN(U32, db, o1, j) == Laws.rd_at(U32, m2, Laws.rd_at(U32, cb1, j)) : U32},
  cvm: @j: U32 -> {Laws.rd_at(U32, m, j) == Laws.rdN(U32, ddb, m, j) : U32},
  w: &o1b: Array<U32> -> {o1b == o1 : Array<U32>} & Laws.WFArray(U32, db, o1b) & (@j: U32 -> {Laws.rd_at(U32, o1, j) == Laws.rdN(U32, db, o1, j) : U32}))
  -> SG3(ca1, cb1, dca, kb, ddb, strsb, bb, slotsb, tagb, na, nb, d, o1, dst2):
  (o1b, +eo1, wo1b, cv1) = w
  %eo1 : SG3(ca1, cb1, dca, kb, ddb, strsb, bb, slotsb, tagb, na, nb, d, _, dst2)
  sapp_dd5(ca1, ca2, cb, cb1, cb2, dca, kb, ddb, strsb, bb, slotsb, tagb, na, nb, d, db, dst2, es2, o1, o1b, m, m2, m3, eo1, em2, em3, e21, ecb1, ecb2, wf2, keepA, rows, cbb, cv1, spec1, cvm, append_w(~U32, na, nb, d, ca1, o1b, 0, fits))

# the gather computed: its result pair replaces the call
def sapp_dd3(ca1: Array<U32>, -ca2: Array<U32>, -cb: Array<U32>, -cb1: Array<U32>, cb2: Array<U32>, -dca: ST.Dict, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, +na: U32, +nb: U32, +d: Nat, +db: Nat, dst2: ST.Dict, +es2: List<&2, String>, -m: Array<U32>, -m2: Array<U32>, m3: Array<U32>,
  +em2: {m2 == m : Array<U32>}, +em3: {m3 == m : Array<U32>}, +e21: {ca2 == ca1 : Array<U32>}, +ecb1: {cb1 == cb : Array<U32>}, +ecb2: {cb2 == cb : Array<U32>}, +fits: {Nat.is_le(Nat.add(U32.to_nat(na), U32.to_nat(nb)), U32.to_nat(U32.shln(1, d))) == True{} : Bool},
  wf2: Laws.WFDictE(dst2, es2), keepA: KeepA(ca2, dca, dst2, na), rows: Laws.EncRows(kb, ddb, strsb, m, es2), cbb: Laws.CodesBelow(nb, cb, kb),
  cvm: @j: U32 -> {Laws.rd_at(U32, m, j) == Laws.rdN(U32, ddb, m, j) : U32},
  w: PST.TGW(~U32, db, nb, m2, cb1, 0))
  -> SG1(ca1, cb1, dca, kb, ddb, strsb, bb, slotsb, tagb, na, nb, db, d, m2, dst2):
  (o1, pm, eq1, epm, wo1, spec1) = w
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.gather(~U32, nb, db, m2, cb1, 0), (o1, pm), eq1) : SG2(ca1, cb1, dca, kb, ddb, strsb, bb, slotsb, tagb, na, nb, d, _, dst2)
  sapp_dd4(ca1, ca2, cb, cb1, cb2, dca, kb, ddb, strsb, bb, slotsb, tagb, na, nb, d, db, dst2, es2, o1, m, m2, m3, em2, em3, e21, ecb1, ecb2, fits, wf2, keepA, rows, cbb, spec1, cvm, PST.rd_all(U32, db, o1, wo1))

# the map's copy cloned again: one copy feeds the gather, the other is read per row
def sapp_dd2b(ca1: Array<U32>, -ca2: Array<U32>, -cb: Array<U32>, cb1: Array<U32>, cb2: Array<U32>, -dca: ST.Dict, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, +na: U32, +nb: U32, +d: Nat, +db: Nat, dst2: ST.Dict, +es2: List<&2, String>, -m: Array<U32>, -m2: Array<U32>,
  +em2: {m2 == m : Array<U32>}, +e21: {ca2 == ca1 : Array<U32>}, +ecb1: {cb1 == cb : Array<U32>}, +ecb2: {cb2 == cb : Array<U32>}, +fb: {U32.is_le(nb, U32.shln(1, db)) == True{} : Bool}, +fits: {Nat.is_le(Nat.add(U32.to_nat(na), U32.to_nat(nb)), U32.to_nat(U32.shln(1, d))) == True{} : Bool},
  wf2: Laws.WFDictE(dst2, es2), keepA: KeepA(ca2, dca, dst2, na), rows: Laws.EncRows(kb, ddb, strsb, m, es2), cbb: Laws.CodesBelow(nb, cb, kb),
  cvm: @j: U32 -> {Laws.rd_at(U32, m, j) == Laws.rdN(U32, ddb, m, j) : U32},
  w: &m2a: Array<U32> -> &m3: Array<U32> -> {m2a == m2 : Array<U32>} & {m3 == m2 : Array<U32>})
  -> SG1(ca1, cb1, dca, kb, ddb, strsb, bb, slotsb, tagb, na, nb, db, d, m2, dst2):
  (m2a, m3, +ea, +e3) = w
  %ea : SG1(ca1, cb1, dca, kb, ddb, strsb, bb, slotsb, tagb, na, nb, db, d, _, dst2)
  sapp_dd3(ca1, ca2, cb, cb1, cb2, dca, kb, ddb, strsb, bb, slotsb, tagb, na, nb, d, db, dst2, es2, m, m2a, m3, Equal.trans(Array<U32>, m2a, m2, m, ea, em2), Equal.trans(Array<U32>, m3, m2, m, e3, em2), e21, ecb1, ecb2, fits, wf2, keepA, rows, cbb, cvm, PST.tgather_w(~U32, db, nb, m2a, cb1, 0, fb))

# the map read back (rd_all): its copy m2 is cloned next
def sapp_dd2(ca1: Array<U32>, -ca2: Array<U32>, -cb: Array<U32>, cb1: Array<U32>, cb2: Array<U32>, -dca: ST.Dict, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, +na: U32, +nb: U32, +d: Nat, +db: Nat, dst2: ST.Dict, +es2: List<&2, String>, -m: Array<U32>,
  +e21: {ca2 == ca1 : Array<U32>}, +ecb1: {cb1 == cb : Array<U32>}, +ecb2: {cb2 == cb : Array<U32>}, +fb: {U32.is_le(nb, U32.shln(1, db)) == True{} : Bool}, +fits: {Nat.is_le(Nat.add(U32.to_nat(na), U32.to_nat(nb)), U32.to_nat(U32.shln(1, d))) == True{} : Bool},
  wf2: Laws.WFDictE(dst2, es2), keepA: KeepA(ca2, dca, dst2, na), rows: Laws.EncRows(kb, ddb, strsb, m, es2), cbb: Laws.CodesBelow(nb, cb, kb),
  w: &m2: Array<U32> -> {m2 == m : Array<U32>} & Laws.WFArray(U32, ddb, m2) & (@j: U32 -> {Laws.rd_at(U32, m, j) == Laws.rdN(U32, ddb, m, j) : U32}))
  -> SG1(ca1, cb1, dca, kb, ddb, strsb, bb, slotsb, tagb, na, nb, db, d, m, dst2):
  (m2, +em2, wm2, cvm) = w
  %em2 : SG1(ca1, cb1, dca, kb, ddb, strsb, bb, slotsb, tagb, na, nb, db, d, _, dst2)
  sapp_dd2b(ca1, ca2, cb, cb1, cb2, dca, kb, ddb, strsb, bb, slotsb, tagb, na, nb, d, db, dst2, es2, m, m2, em2, e21, ecb1, ecb2, fb, fits, wf2, keepA, rows, cbb, cvm, PC.clone_eq(U32, m2))

# Keep composed with the in-range hypothesis, per row, on the copy ca2 (read while it is live)
def keep_rows(ca2: Array<U32>, -ca: Array<U32>, -dca: ST.Dict, -dst2: ST.Dict, +na: U32, +e2: {ca2 == ca : Array<U32>},
  keep: @c: U32 -> {U32.is_lt(c, Laws.dk(dca)) == True{} : Bool} -> {Laws.dentry(dst2, c) == Laws.dentry(dca, c) : String}, cba: Laws.CodesBelow(na, ca, Laws.dk(dca)))
  -> KeepA(ca2, dca, dst2, na):
  +k => +hk => keep(Laws.rd_at(U32, ca2, k), (%Equal.sym(Array<U32>, ca2, ca, e2) : {U32.is_lt(Laws.rd_at(U32, _, k), Laws.dk(dca)) == True{} : Bool}; cba(k, hk)))

# b's codes cloned: the first copy goes to the gather, the second is read per row
def sapp_dd1c(ca1: Array<U32>, -ca2: Array<U32>, -cb: Array<U32>, -dca: ST.Dict, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, +na: U32, +nb: U32, +d: Nat, +db: Nat, dst2: ST.Dict, +es2: List<&2, String>, m: Array<U32>,
  +e21: {ca2 == ca1 : Array<U32>}, +fb: {U32.is_le(nb, U32.shln(1, db)) == True{} : Bool}, +fits: {Nat.is_le(Nat.add(U32.to_nat(na), U32.to_nat(nb)), U32.to_nat(U32.shln(1, d))) == True{} : Bool},
  wm: Laws.WFArray(U32, ddb, m), wf2: Laws.WFDictE(dst2, es2), keepA: KeepA(ca2, dca, dst2, na), rows: Laws.EncRows(kb, ddb, strsb, m, es2), cbb: Laws.CodesBelow(nb, cb, kb),
  w: &cb1: Array<U32> -> &cb2: Array<U32> -> {cb1 == cb : Array<U32>} & {cb2 == cb : Array<U32>})
  -> SG1(ca1, cb, dca, kb, ddb, strsb, bb, slotsb, tagb, na, nb, db, d, m, dst2):
  (cb1, cb2, +ecb1, +ecb2) = w
  %ecb1 : SG1(ca1, _, dca, kb, ddb, strsb, bb, slotsb, tagb, na, nb, db, d, m, dst2)
  sapp_dd2(ca1, ca2, cb, cb1, cb2, dca, kb, ddb, strsb, bb, slotsb, tagb, na, nb, d, db, dst2, es2, m, e21, ecb1, ecb2, fb, fits, wf2, keepA, rows, cbb, PST.rd_all(U32, ddb, m, wm))

# a's codes cloned: the first copy goes to the append, the second is read for Keep
def sapp_dd1b(-ca: Array<U32>, cb: Array<U32>, -dca: ST.Dict, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, +na: U32, +nb: U32, +d: Nat, +db: Nat, dst2: ST.Dict, +es2: List<&2, String>, m: Array<U32>, +fb: {U32.is_le(nb, U32.shln(1, db)) == True{} : Bool}, +fits: {Nat.is_le(Nat.add(U32.to_nat(na), U32.to_nat(nb)), U32.to_nat(U32.shln(1, d))) == True{} : Bool},
  wm: Laws.WFArray(U32, ddb, m), wf2: Laws.WFDictE(dst2, es2), keep: @c: U32 -> {U32.is_lt(c, Laws.dk(dca)) == True{} : Bool} -> {Laws.dentry(dst2, c) == Laws.dentry(dca, c) : String}, rows: Laws.EncRows(kb, ddb, strsb, m, es2),
  cba: Laws.CodesBelow(na, ca, Laws.dk(dca)), cbb: Laws.CodesBelow(nb, cb, kb),
  w: &ca1: Array<U32> -> &ca2: Array<U32> -> {ca1 == ca : Array<U32>} & {ca2 == ca : Array<U32>})
  -> SG1(ca, cb, dca, kb, ddb, strsb, bb, slotsb, tagb, na, nb, db, d, m, dst2):
  (ca1, ca2, +e1, +e2) = w
  %e1 : SG1(_, cb, dca, kb, ddb, strsb, bb, slotsb, tagb, na, nb, db, d, m, dst2)
  sapp_dd1c(ca1, ca2, cb, dca, kb, ddb, strsb, bb, slotsb, tagb, na, nb, d, db, dst2, es2, m, Equal.trans(Array<U32>, ca2, ca, ca1, e2, Equal.sym(Array<U32>, ca1, ca, e1)), fb, fits, wm, wf2, keep_rows(ca2, ca, dca, dst2, na, e2, keep, cba), rows, cbb, PC.clone_eq(U32, cb))

# the merge computed: its result triple replaces the call
def sapp_dd1(ca: Array<U32>, cb: Array<U32>, -dca: ST.Dict, +kb: U32, +ddb: Nat, -strsb: Array<String>, +bb: Nat, -slotsb: Array<ST.SSlot>, +tagb: U32, +na: U32, +nb: U32, +d: Nat, +db: Nat, +esa: List<&2, String>, +fb: {U32.is_le(nb, U32.shln(1, db)) == True{} : Bool}, +fits: {Nat.is_le(Nat.add(U32.to_nat(na), U32.to_nat(nb)), U32.to_nat(U32.shln(1, d))) == True{} : Bool},
  cba: Laws.CodesBelow(na, ca, Laws.dk(dca)), cbb: Laws.CodesBelow(nb, cb, kb),
  w: Laws.MergeW(ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}, dca, esa))
  -> &o: ST.Strs -> {ST.Strs.app.m(na, nb, db, d, ca, cb, ST.Dict.merge(ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}, dca)) == o : ST.Strs} & LeftS(o, ca, dca, na) & RightS(o, cb, kb, ddb, strsb, bb, slotsb, tagb, na, nb):
  (src2, dst2, m, +es2, eqm, esrc, ext, wm, wf2, keep, rows) = w
  %Equal.sym(ST.Dict & ST.Dict & Array<U32>, ST.Dict.merge(ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}, dca), (src2, dst2, m), eqm) : &o: ST.Strs -> {ST.Strs.app.m(na, nb, db, d, ca, cb, _) == o : ST.Strs} & LeftS(o, ca, dca, na) & RightS(o, cb, kb, ddb, strsb, bb, slotsb, tagb, na, nb)
  sapp_dd1b(ca, cb, dca, kb, ddb, strsb, bb, slotsb, tagb, na, nb, d, db, dst2, es2, m, fb, fits, wm, wf2, keep, rows, cba, cbb, PC.clone_eq(U32, ca))

# a's dictionary's entry list taken apart, the merge theorem applied
def sapp_dd0b(ca: Array<U32>, dca: ST.Dict, cb: Array<U32>, +kb: U32, +ddb: Nat, strsb: Array<String>, +bb: Nat, slotsb: Array<ST.SSlot>, +tagb: U32, +na: U32, +nb: U32, +da: Nat, +db: Nat, +d: Nat, +fb: {U32.is_le(nb, U32.shln(1, db)) == True{} : Bool}, +fits: {Nat.is_le(Nat.add(U32.to_nat(na), U32.to_nat(nb)), U32.to_nat(U32.shln(1, d))) == True{} : Bool},
  wfd: Laws.WFDict(dca), fitsb: {U32.is_le(kb, U32.shln(1, ddb)) == True{} : Bool}, cba: Laws.CodesBelow(na, ca, Laws.dk(dca)), cbb: Laws.CodesBelow(nb, cb, kb), probes: Laws.MergeProbe(U32.to_nat(kb), 0, strsb, dca))
  -> Laws.AppendStrsW(ST.SDict{ca, dca}, ST.SDict{cb, ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}}, na, nb, da, db, d):
  (+esa, wfa) = wfd
  sapp_dd1(ca, cb, dca, kb, ddb, strsb, bb, slotsb, tagb, na, nb, d, db, esa, fb, fits, cba, cbb, Laws.dict_merge_spec(ST.Dict{kb, ddb, strsb, bb, slotsb, tagb}, dca, esa, fitsb, wfa, probes))

# b's dictionary taken apart, the hypotheses taken apart
def sapp_dd0(ca: Array<U32>, dca: ST.Dict, cb: Array<U32>, dcb: ST.Dict, +na: U32, +nb: U32, +da: Nat, +db: Nat, +d: Nat, +fb: {U32.is_le(nb, U32.shln(1, db)) == True{} : Bool}, +fits: {Nat.is_le(Nat.add(U32.to_nat(na), U32.to_nat(nb)), U32.to_nat(U32.shln(1, d))) == True{} : Bool}, hyp: Laws.AppendHyp(ST.SDict{ca, dca}, ST.SDict{cb, dcb}, na, nb))
  -> Laws.AppendStrsW(ST.SDict{ca, dca}, ST.SDict{cb, dcb}, na, nb, da, db, d):
  match dcb:
    case ST.Dict{+kb, +ddb, strsb, +bb, slotsb, +tagb}:
      (wfd, fitsb, cba, cbb, probes) = hyp
      sapp_dd0b(ca, dca, cb, kb, ddb, strsb, bb, slotsb, tagb, na, nb, da, db, d, fb, fits, wfd, fitsb, cba, cbb, probes)

def Laws.strs_append_cells(xa, xb, na, nb, da, db, d, fa, fb, fits, hyp):
  match xa xb:
    case ST.SDict{ca, dca} ST.SDict{cb, dcb}:
      sapp_dd0(ca, dca, cb, dcb, na, nb, da, db, d, fb, fits, hyp)
    case ST.SRaw{a} ST.SRaw{b}:
      sapp_raw(ST.SRaw{a}, ST.SRaw{b}, na, nb, da, db, d, fa, fb, fits)
    case ST.SRaw{a} ST.SDict{cb, dcb}:
      sapp_raw(ST.SRaw{a}, ST.SDict{cb, dcb}, na, nb, da, db, d, fa, fb, fits)
    case ST.SDict{ca, dca} ST.SRaw{b}:
      sapp_raw(ST.SDict{ca, dca}, ST.SRaw{b}, na, nb, da, db, d, fa, fb, fits)
