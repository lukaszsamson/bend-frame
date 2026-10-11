# PROOF_chunks.bend -- proofs of LAWS.bend section 21 (v0.2 T5.1, DESIGN.md 16.1 D1): the chunk tree CW of
# src/chunks.bend (the word tree: Bool/U32/I32 payloads, validity masks, dictionary codes). The F32 and
# Raw-string trees CF / CS are the same text over another element type (the generator keeps them so);
# as everywhere in LAWS the claims are stated at the U32 instance.
#
# Shape of the proofs:
#  - the logical model is Nat-indexed (Laws.ncell: a node answers its left child below lrows, else its
#    right child at m - lrows, a NAT subtraction), so no word subtraction is ever reasoned about in the
#    trees; the words meet the model through Laws.addn(0, m) and the U32 <-> Nat bridge below
#    (to_nat_add: U32.add is the Nat sum while the sum stays below some word; sub_nat: U32.sub is the Nat
#    difference when it does not wrap; both by the existing Word lemmas: add_inc_r, addn_to_nat, inc_nat_u
#    and a new carry-cancelling lemma cancel_add);
#  - every production walk is proven with WITNESSES, as PROOF_append does: a lemma takes the live tree /
#    stack / buffers, rebuilds what the production function builds and answers &x: {f(..) == x} & facts(x),
#    so a later step can match the witness (a live child goes to ONE lemma; its facts come back bundled);
#  - the builder (binary-counter stack) is described by LayS: the stack's trees laid back to back over the
#    source rows (start offsets as Nat Sigmas, no subtraction), each tree's rows those of the source from
#    its start (TreeAt);
#  - the leaf lemmas are the existing kernel theorems: PC.range_go (Kernel.range, through the Ch.rng
#    simulation), PA.copy_into_w (flatten), PA.append_w (rechunk), PC.map_cell (the chunked map).
import Base
import ./src/dtype.bend as D
import ./src/err.bend as E
import ./src/kernels.bend as K
import ./src/chunks.bend as CH
import ./LAWS.bend as Laws
import ./PROOF_lib.bend as L
import ./PROOF_kernels.bend as PK
import ./PROOF_bits.bend as B
import ./PROOF_contents.bend as PC
import ./PROOF_strs.bend as PST
import ./PROOF_append.bend as PA

# ==== Nat arithmetic ====================================================================================

def nat_add_zero_r(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 0n), p, nat_add_zero_r(p))

def nat_add_assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), nat_add_assoc(p, b, c))

def nat_add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, nat_add_zero_r(b))
    case 1n++p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), B.add_succ(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, b), Nat.add(b, p), nat_add_comm(p, b))

# (a + b) - a == b
def nat_add_sub(a: Nat, +b: Nat) -> {Nat.sub(Nat.add(a, b), a) == b : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      nat_add_sub(p, b)

# l <= m: l + (m - l) == m
def nat_sub_add(l: Nat, m: Nat, h: {Nat.is_le(l, m) == True{} : Bool}) -> {Nat.add(l, Nat.sub(m, l)) == m : Nat}:
  match l m:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, L.false_true(h))
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, Nat.sub(q, p)), q, nat_sub_add(p, q, h))

# (m - a) - b == m - (a + b)
def nat_sub_sub(m: Nat, a: Nat, +b: Nat) -> {Nat.sub(Nat.sub(m, a), b) == Nat.sub(m, Nat.add(a, b)) : Nat}:
  match m a:
    case 0n 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 0n 1n+p:
      match b:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+q 0n:
      {==}
    case 1n+q 1n+p:
      nat_sub_sub(q, p, b)

# m < l + r and not m < l: m - l < r
def nat_lt_sub(m: Nat, l: Nat, +r: Nat, h: {Nat.is_lt(m, Nat.add(l, r)) == True{} : Bool}, nl: {Nat.is_lt(m, l) == False{} : Bool}) -> {Nat.is_lt(Nat.sub(m, l), r) == True{} : Bool}:
  match m l:
    case 0n 0n:
      h
    case 1n+q 0n:
      h
    case 0n 1n+p:
      Empty.absurd({Nat.is_lt(Nat.sub(0n, 1n+p), r) == True{} : Bool}, L.true_false(nl))
    case 1n+q 1n+p:
      nat_lt_sub(q, p, r, h, nl)

# not m < l: l <= m
def nat_le_of_not_lt(m: Nat, l: Nat, h: {Nat.is_lt(m, l) == False{} : Bool}) -> {Nat.is_le(l, m) == True{} : Bool}:
  match m l:
    case 0n 0n:
      {==}
    case 1n+q 0n:
      {==}
    case 0n 1n+p:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, L.true_false(h))
    case 1n+q 1n+p:
      nat_le_of_not_lt(q, p, h)

# m < l: m < l + r
def nat_lt_add_r(m: Nat, l: Nat, +r: Nat, h: {Nat.is_lt(m, l) == True{} : Bool}) -> {Nat.is_lt(m, Nat.add(l, r)) == True{} : Bool}:
  match m l:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, Nat.add(0n, r)) == True{} : Bool}, L.false_true(h))
    case 1n+q 0n:
      Empty.absurd({Nat.is_lt(1n+q, Nat.add(0n, r)) == True{} : Bool}, L.false_true(h))
    case 0n 1n+p:
      {==}
    case 1n+q 1n+p:
      nat_lt_add_r(q, p, r, h)

# a <= a + b
def nat_le_add(a: Nat, +b: Nat) -> {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  PA.nat_le_add_r(a, b)

# b <= a + b
def nat_le_add_l(+a: Nat, +b: Nat) -> {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}:
  %nat_add_comm(b, a) : {Nat.is_le(b, _) == True{} : Bool}
  PA.nat_le_add_r(b, a)

# a + b <= c: a <= c and b <= c
def nat_le_of_add_l(+a: Nat, +b: Nat, +c: Nat, h: {Nat.is_le(Nat.add(a, b), c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  PST.nat_le_trans(a, Nat.add(a, b), c, PA.nat_le_add_r(a, b), h)

def nat_le_of_add_r(+a: Nat, +b: Nat, +c: Nat, h: {Nat.is_le(Nat.add(a, b), c) == True{} : Bool}) -> {Nat.is_le(b, c) == True{} : Bool}:
  PST.nat_le_trans(b, Nat.add(a, b), c, nat_le_add_l(a, b), h)

# a < b gives a <= b
def nat_le_of_lt(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, L.false_true(h))
    case 1n+p 1n+q:
      nat_le_of_lt(p, q, h)

def nat_le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+q:
      {==}

# a < b: 1 + a <= b
def nat_succ_le_of_lt(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, L.false_true(h))
    case 0n 1n+q:
      nat_le_zero(q)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(2n+p, 0n) == True{} : Bool}, L.false_true(h))
    case 1n+p 1n+q:
      nat_succ_le_of_lt(p, q, h)

# a + b <= a + c from b <= c
def nat_add_le_mono(a: Nat, +b: Nat, +c: Nat, h: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, b), Nat.add(a, c)) == True{} : Bool}:
  match a:
    case 0n:
      h
    case 1n+p:
      nat_add_le_mono(p, b, c, h)

# a + b < a + c from b < c
def nat_add_lt_mono(a: Nat, +b: Nat, +c: Nat, h: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(Nat.add(a, b), Nat.add(a, c)) == True{} : Bool}:
  match a:
    case 0n:
      h
    case 1n+p:
      nat_add_lt_mono(p, b, c, h)

def nat_le_refl(a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  PST.nat_le_refl(a)

# a < b <= c: a < c
def nat_lt_le(+a: Nat, +b: Nat, +c: Nat, h1: {Nat.is_lt(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  PST.nat_lt_le_trans(a, b, c, h1, h2)

def nat_le_trans(+a: Nat, +b: Nat, +c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  PST.nat_le_trans(a, b, c, h1, h2)

# ==== the U32 <-> Nat bridge ============================================================================

# x + (0 + f increments) is f increments from x
def add_addn(+x: U32, f: Nat) -> {U32.add(x, Laws.addn(0, f)) == Laws.addn(x, f) : U32}:
  match f:
    case 0n:
      PC.u_add0(x)
    case 1n++p:
      %Equal.sym(U32, U32.add(x, U32.inc(Laws.addn(0, p))), U32.inc(U32.add(x, Laws.addn(0, p))), PA.add_inc_r(x, Laws.addn(0, p))) : {_ == U32.inc(Laws.addn(x, p)) : U32}
      Equal.cong(U32, U32, w => U32.inc(w), U32.add(x, Laws.addn(0, p)), Laws.addn(x, p), add_addn(x, p))

# x + y is to_nat(y) increments from x
def add_eq_addn(+x: U32, +y: U32) -> {U32.add(x, y) == Laws.addn(x, U32.to_nat(y)) : U32}:
  %B.addn_to_nat(y) : {U32.add(x, _) == Laws.addn(x, U32.to_nat(y)) : U32}
  add_addn(x, U32.to_nat(y))

def addn_addn(+x: U32, +a: Nat, b: Nat) -> {Laws.addn(Laws.addn(x, a), b) == Laws.addn(x, Nat.add(a, b)) : U32}:
  match b:
    case 0n:
      %Equal.sym(Nat, Nat.add(a, 0n), a, nat_add_zero_r(a)) : {Laws.addn(x, a) == Laws.addn(x, _) : U32}
      {==}
    case 1n++q:
      %Equal.sym(Nat, Nat.add(a, 1n+q), 1n+Nat.add(a, q), B.add_succ(a, q)) : {U32.inc(Laws.addn(Laws.addn(x, a), q)) == Laws.addn(x, _) : U32}
      Equal.cong(U32, U32, w => U32.inc(w), Laws.addn(Laws.addn(x, a), q), Laws.addn(x, Nat.add(a, q)), addn_addn(x, a, q))

# the step of to_nat_addn: inc does not wrap below a bound word
def tna_step(bb: Bool, +j: U32, +bound: U32, s: B.IncSpecU(bb, j), lt: {U32.is_lt(j, bound) == True{} : Bool}) -> {U32.to_nat(U32.inc(j)) == 1n+U32.to_nat(j) : Nat}:
  match bb:
    case True{}:
      s
    case False{}:
      Empty.absurd({U32.to_nat(U32.inc(j)) == 1n+U32.to_nat(j) : Nat}, s(bound)(B.gt_of_lt_u(j, bound, lt)))

def tna_fin(+j: U32, +bound: U32, w: &bb: Bool -> B.IncSpecU(bb, j), lt: {U32.is_lt(j, bound) == True{} : Bool}) -> {U32.to_nat(U32.inc(j)) == 1n+U32.to_nat(j) : Nat}:
  (bb, s) = w
  tna_step(bb, j, bound, s, lt)

# to_nat(x) + f <= to_nat(bound): f increments from x add f (no wrap on the way)
def to_nat_addn(+x: U32, f: Nat, +bound: U32, +h: {Nat.is_le(Nat.add(U32.to_nat(x), f), U32.to_nat(bound)) == True{} : Bool}) -> {U32.to_nat(Laws.addn(x, f)) == Nat.add(U32.to_nat(x), f) : Nat}:
  match f:
    case 0n:
      Equal.sym(Nat, Nat.add(U32.to_nat(x), 0n), U32.to_nat(x), nat_add_zero_r(U32.to_nat(x)))
    case 1n++p:
      %Equal.sym(Nat, Nat.add(U32.to_nat(x), 1n+p), 1n+Nat.add(U32.to_nat(x), p), B.add_succ(U32.to_nat(x), p)) : {U32.to_nat(U32.inc(Laws.addn(x, p))) == _ : Nat}
      +ih = to_nat_addn(x, p, bound, PST.nat_le_trans(Nat.add(U32.to_nat(x), p), Nat.add(U32.to_nat(x), 1n+p), U32.to_nat(bound), (%Equal.sym(Nat, Nat.add(U32.to_nat(x), 1n+p), 1n+Nat.add(U32.to_nat(x), p), B.add_succ(U32.to_nat(x), p)) : {Nat.is_le(Nat.add(U32.to_nat(x), p), _) == True{} : Bool}; PST.nat_le_succ(Nat.add(U32.to_nat(x), p))), h))
      %ih : {U32.to_nat(U32.inc(Laws.addn(x, p))) == 1n+_ : Nat}
      tna_fin(Laws.addn(x, p), bound, B.inc_nat_u(Laws.addn(x, p)), B.lt_of_nat_u(Laws.addn(x, p), bound, (%Equal.sym(Nat, U32.to_nat(Laws.addn(x, p)), Nat.add(U32.to_nat(x), p), ih) : {Cmp.is_lt(Nat.cmp(_, U32.to_nat(bound))) == True{} : Bool}; PST.lt_of_succ_le(Nat.add(U32.to_nat(x), p), U32.to_nat(bound), (%B.add_succ(U32.to_nat(x), p) : {Nat.is_le(_, U32.to_nat(bound)) == True{} : Bool}; h)))))

# U32.add is the Nat sum while the sum stays below a word
def to_nat_add(+x: U32, +y: U32, +bound: U32, h: {Nat.is_le(Nat.add(U32.to_nat(x), U32.to_nat(y)), U32.to_nat(bound)) == True{} : Bool}) -> {U32.to_nat(U32.add(x, y)) == Nat.add(U32.to_nat(x), U32.to_nat(y)) : Nat}:
  %Equal.sym(U32, U32.add(x, y), Laws.addn(x, U32.to_nat(y)), add_eq_addn(x, y)) : {U32.to_nat(_) == Nat.add(U32.to_nat(x), U32.to_nat(y)) : Nat}
  to_nat_addn(x, U32.to_nat(y), bound, h)

# the word of a Nat below a word: to_nat(addn(0, f)) == f
def to_nat_addn0(+f: Nat, +bound: U32, h: {Nat.is_le(f, U32.to_nat(bound)) == True{} : Bool}) -> {U32.to_nat(Laws.addn(0, f)) == f : Nat}:
  to_nat_addn(0, f, bound, h)

# to_nat is injective
def u32_eq_of_nat(+x: U32, +y: U32, e: {U32.to_nat(x) == U32.to_nat(y) : Nat}) -> {x == y : U32}:
  %B.addn_to_nat(x) : {_ == y : U32}
  %B.addn_to_nat(y) : {Laws.addn(0, U32.to_nat(x)) == _ : U32}
  Equal.cong(Nat, U32, q => Laws.addn(0, q), U32.to_nat(x), U32.to_nat(y), e)

# addn(0, a) + addn(0, b) == addn(0, a + b)
def addn0_add(+a: Nat, +b: Nat) -> {U32.add(Laws.addn(0, a), Laws.addn(0, b)) == Laws.addn(0, Nat.add(a, b)) : U32}:
  %Equal.sym(U32, U32.add(Laws.addn(0, a), Laws.addn(0, b)), Laws.addn(Laws.addn(0, a), b), add_addn(Laws.addn(0, a), b)) : {_ == Laws.addn(0, Nat.add(a, b)) : U32}
  addn_addn(0, a, b)

# a word is addn(0, its value)
def addn0_to_nat(+x: U32) -> {x == Laws.addn(0, U32.to_nat(x)) : U32}:
  Equal.sym(U32, Laws.addn(0, U32.to_nat(x)), x, B.addn_to_nat(x))

# ---- comparisons --------------------------------------------------------------------------------------

def nle_of_u(+a: U32, +b: U32, h: {U32.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(U32.to_nat(a), U32.to_nat(b)) == True{} : Bool}:
  B.le_nat_u(a, b, h)

def ule_of_n(+a: U32, +b: U32, h: {Nat.is_le(U32.to_nat(a), U32.to_nat(b)) == True{} : Bool}) -> {U32.is_le(a, b) == True{} : Bool}:
  PST.le_u_of_nat(a, b, h)

def nlt_of_u(+a: U32, +b: U32, h: {U32.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(U32.to_nat(a), U32.to_nat(b)) == True{} : Bool}:
  PST.lt_nat_of_u(a, b, h)

def ult_of_n(+a: U32, +b: U32, h: {Nat.is_lt(U32.to_nat(a), U32.to_nat(b)) == True{} : Bool}) -> {U32.is_lt(a, b) == True{} : Bool}:
  B.lt_of_nat_u(a, b, h)

# U32.is_lt is Nat.is_lt of the values (as a Bool equation)
def ult_nat(+a: U32, +b: U32) -> {U32.is_lt(a, b) == Nat.is_lt(U32.to_nat(a), U32.to_nat(b)) : Bool}:
  Equal.cong(Cmp, Bool, c => Cmp.is_lt(c), U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), B.cmp_nat_u(a, b))

def ule_nat(+a: U32, +b: U32) -> {U32.is_le(a, b) == Nat.is_le(U32.to_nat(a), U32.to_nat(b)) : Bool}:
  Equal.cong(Cmp, Bool, c => Cmp.is_le(c), U32.cmp(a, b), Nat.cmp(U32.to_nat(a), U32.to_nat(b)), B.cmp_nat_u(a, b))

# ---- subtraction that does not wrap ---------------------------------------------------------------------

# (w + h) - h == w, with the carries generalised: adc(adc(w, h, F, c), h, T, not c) == w
def cancel_add(n: Nat, w: Word(n), h: Word(n), c: Bool) -> {Word.adc(n, Word.adc(n, w, h, False{}, c), h, True{}, Bool.not(c)) == w : Word(n)}:
  match n:
    case 0n:
      match w h:
        case WNil{} WNil{}:
          {==}
    case 1n++p:
      match w h c:
        case WCon{False{}, +t} WCon{False{}, +u} False{}:
          %cancel_add(p, t, u, False{}) : {WCon{False{}, Word.adc(p, Word.adc(p, t, u, False{}, False{}), u, True{}, True{})} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{False{}, +t} WCon{False{}, +u} True{}:
          %cancel_add(p, t, u, False{}) : {WCon{False{}, Word.adc(p, Word.adc(p, t, u, False{}, False{}), u, True{}, True{})} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{False{}, +t} WCon{True{}, +u} False{}:
          %cancel_add(p, t, u, False{}) : {WCon{False{}, Word.adc(p, Word.adc(p, t, u, False{}, False{}), u, True{}, True{})} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{False{}, +t} WCon{True{}, +u} True{}:
          %cancel_add(p, t, u, True{}) : {WCon{False{}, Word.adc(p, Word.adc(p, t, u, False{}, True{}), u, True{}, False{})} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +t} WCon{False{}, +u} False{}:
          %cancel_add(p, t, u, False{}) : {WCon{True{}, Word.adc(p, Word.adc(p, t, u, False{}, False{}), u, True{}, True{})} == WCon{True{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +t} WCon{False{}, +u} True{}:
          %cancel_add(p, t, u, True{}) : {WCon{True{}, Word.adc(p, Word.adc(p, t, u, False{}, True{}), u, True{}, False{})} == WCon{True{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +t} WCon{True{}, +u} False{}:
          %cancel_add(p, t, u, True{}) : {WCon{True{}, Word.adc(p, Word.adc(p, t, u, False{}, True{}), u, True{}, False{})} == WCon{True{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +t} WCon{True{}, +u} True{}:
          %cancel_add(p, t, u, True{}) : {WCon{True{}, Word.adc(p, Word.adc(p, t, u, False{}, True{}), u, True{}, False{})} == WCon{True{}, _} : Word(1n+p)}
          {==}

# (y + l) - l == y
def u_sub_add(y: U32, l: U32) -> {U32.sub(U32.add(y, l), l) == y : U32}:
  match y l:
    case U32{a} U32{+b}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.adc(32n, Word.adc(32n, a, b, False{}, False{}), b, True{}, True{}), a, cancel_add(32n, a, b, False{}))

# l <= h: h - l is the Nat difference, as a word: U32.sub(h, l) == addn(0, to_nat(h) - to_nat(l))
def sub_addn(+h: U32, +l: U32, hle: {U32.is_le(l, h) == True{} : Bool}) -> {U32.sub(h, l) == Laws.addn(0, Nat.sub(U32.to_nat(h), U32.to_nat(l))) : U32}:
  +hn = nle_of_u(l, h, hle)
  +m = Nat.sub(U32.to_nat(h), U32.to_nat(l))
  +em = nat_sub_add(U32.to_nat(l), U32.to_nat(h), hn)
  +ey = to_nat_addn0(m, h, (%em : {Nat.is_le(m, _) == True{} : Bool}; nat_le_add_l(U32.to_nat(l), m)))
  # l + y == h as words (their values agree below h)
  +eh = u32_eq_of_nat(U32.add(Laws.addn(0, m), l), h, (%U32.add_comm(l, Laws.addn(0, m)) : {U32.to_nat(_) == U32.to_nat(h) : Nat}; %Equal.sym(Nat, U32.to_nat(U32.add(l, Laws.addn(0, m))), Nat.add(U32.to_nat(l), U32.to_nat(Laws.addn(0, m))), to_nat_add(l, Laws.addn(0, m), h, (%Equal.sym(Nat, U32.to_nat(Laws.addn(0, m)), m, ey) : {Nat.is_le(Nat.add(U32.to_nat(l), _), U32.to_nat(h)) == True{} : Bool}; %Equal.sym(Nat, Nat.add(U32.to_nat(l), m), U32.to_nat(h), em) : {Nat.is_le(_, U32.to_nat(h)) == True{} : Bool}; nat_le_refl(U32.to_nat(h))))) : {_ == U32.to_nat(h) : Nat}; %Equal.sym(Nat, U32.to_nat(Laws.addn(0, m)), m, ey) : {Nat.add(U32.to_nat(l), _) == U32.to_nat(h) : Nat}; em))
  %eh : {U32.sub(_, l) == Laws.addn(0, m) : U32}
  u_sub_add(Laws.addn(0, m), l)

# l <= h: to_nat(h - l) == to_nat(h) - to_nat(l)
def sub_nat(+h: U32, +l: U32, +hle: {U32.is_le(l, h) == True{} : Bool}) -> {U32.to_nat(U32.sub(h, l)) == Nat.sub(U32.to_nat(h), U32.to_nat(l)) : Nat}:
  %Equal.sym(U32, U32.sub(h, l), Laws.addn(0, Nat.sub(U32.to_nat(h), U32.to_nat(l))), sub_addn(h, l, hle)) : {U32.to_nat(_) == Nat.sub(U32.to_nat(h), U32.to_nat(l)) : Nat}
  to_nat_addn0(Nat.sub(U32.to_nat(h), U32.to_nat(l)), h, PST.nat_le_trans(Nat.sub(U32.to_nat(h), U32.to_nat(l)), Nat.add(U32.to_nat(l), Nat.sub(U32.to_nat(h), U32.to_nat(l))), U32.to_nat(h), nat_le_add_l(U32.to_nat(l), Nat.sub(U32.to_nat(h), U32.to_nat(l))), (%Equal.sym(Nat, Nat.add(U32.to_nat(l), Nat.sub(U32.to_nat(h), U32.to_nat(l))), U32.to_nat(h), nat_sub_add(U32.to_nat(l), U32.to_nat(h), nle_of_u(l, h, hle))) : {Nat.is_le(_, U32.to_nat(h)) == True{} : Bool}; nat_le_refl(U32.to_nat(h)))))

# ==== Ch.rng IS Kernel.range with the source handed back (simulation, as PROOF_fused's mpb_sim) ==========

def RngSim(~T: Data, fl: Nat, +k: U32, +off: U32, -out: Array<T>, -a: Array<T>) -> Type:
  {CH.Ch.rng.go(~T, fl, k, off, out, Array.get(T, a, U32.add(off, k))) == (K.Kernel.range.go(~T, fl, k, off, out, Array.get(T, a, U32.add(off, k))), a) : Array<T> & Array<T>}

def rng_zero(~T: Data, +k: U32, +off: U32, -out: Array<T>, -a: Array<T>,
  w: &b: Array<T> -> &x: T -> {b == a : Array<T>} & {Array.get(T, a, U32.add(off, k)) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, U32.add(off, k)) : T})
  -> RngSim(~T, 0n, k, off, out, a):
  (a2, +x, ea, e1, ex) = w
  %Equal.sym(Array<T> & T, Array.get(T, a, U32.add(off, k)), (a, x), e1) : {CH.Ch.rng.go(~T, 0n, k, off, out, _) == (K.Kernel.range.go(~T, 0n, k, off, out, _), a) : Array<T> & Array<T>}
  {==}

def rng_step(~T: Data, q: Nat, +k: U32, +off: U32, out: Array<T>, -a: Array<T>,
  w: &b: Array<T> -> &x: T -> {b == a : Array<T>} & {Array.get(T, a, U32.add(off, k)) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, U32.add(off, k)) : T},
  ih: @a2: Array<T> -> @c: Array<T> -> RngSim(~T, q, U32.inc(k), off, c, a2))
  -> RngSim(~T, 1n+q, k, off, out, a):
  (a2, +x, +ea, e1, ex) = w
  %Equal.sym(Array<T> & T, Array.get(T, a, U32.add(off, k)), (a, x), e1) : {CH.Ch.rng.go(~T, 1n+q, k, off, out, _) == (K.Kernel.range.go(~T, 1n+q, k, off, out, _), a) : Array<T> & Array<T>}
  %ea : {CH.Ch.rng.go(~T, 1n+q, k, off, out, (_, x)) == (K.Kernel.range.go(~T, 1n+q, k, off, out, (_, x)), _) : Array<T> & Array<T>}
  ih(a2, Array.set(T, out, k, x))

def rng_sim(~T: Data, fl: Nat, +k: U32, +off: U32, out: Array<T>, a: Array<T>) -> RngSim(~T, fl, k, off, out, a):
  match fl:
    case 0n:
      rng_zero(~T, k, off, out, a, PC.get_w(T, a, U32.add(off, k)))
    case 1n++q:
      rng_step(~T, q, k, off, out, a, PC.get_w(T, a, U32.add(off, k)), a2 => c => rng_sim(~T, q, U32.inc(k), off, c, a2))

def Laws.ch_rng_range(n, d, off, a, z):
  rng_sim(~U32, U32.to_nat(n), 0, off, Array.new(U32, d, z), a)

# ==== trees in the model: a node over two consecutive trees =============================================

# addn(0, st + m) is where row m of a tree starting at st sits: the word index off + K of a leaf copy
def idx_eq(+off: U32, +k: Nat) -> {U32.add(off, Laws.addn(0, k)) == Laws.addn(0, Nat.add(U32.to_nat(off), k)) : U32}:
  Equal.trans(U32, U32.add(off, Laws.addn(0, k)), Laws.addn(off, k), Laws.addn(0, Nat.add(U32.to_nat(off), k)), add_addn(off, k), Equal.trans(U32, Laws.addn(off, k), Laws.addn(Laws.addn(0, U32.to_nat(off)), k), Laws.addn(0, Nat.add(U32.to_nat(off), k)), Equal.cong(U32, U32, q => Laws.addn(q, k), off, Laws.addn(0, U32.to_nat(off)), addn0_to_nat(off)), addn_addn(0, U32.to_nat(off), k)))

def node_at_b(b: Bool, +st: Nat, +rows: U32, +lrows: U32, -l: CH.CW, -r: CH.CW, -src: Array<U32>, +m: Nat,
  eb: {Nat.is_lt(m, U32.to_nat(lrows)) == b : Bool}, hm: {Nat.is_lt(m, U32.to_nat(rows)) == True{} : Bool},
  el: {lrows == Laws.crows(l) : U32}, esum: {Nat.add(U32.to_nat(lrows), Laws.nrows(r)) == U32.to_nat(rows) : Nat},
  al: Laws.TreeAt(l, st, src), ar: Laws.TreeAt(r, Nat.add(st, U32.to_nat(lrows)), src))
  -> {Laws.ncell(CH.WN{rows, lrows, l, r}, m) == Laws.rd_at(U32, src, Laws.addn(0, Nat.add(st, m))) : U32}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(m, U32.to_nat(lrows)), True{}, eb) : {Bool.pick(U32, _, Laws.ncell(l, m), Laws.ncell(r, Nat.sub(m, U32.to_nat(lrows)))) == Laws.rd_at(U32, src, Laws.addn(0, Nat.add(st, m))) : U32}
      al(m, (%el : {Nat.is_lt(m, U32.to_nat(_)) == True{} : Bool}; eb))
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(m, U32.to_nat(lrows)), False{}, eb) : {Bool.pick(U32, _, Laws.ncell(l, m), Laws.ncell(r, Nat.sub(m, U32.to_nat(lrows)))) == Laws.rd_at(U32, src, Laws.addn(0, Nat.add(st, m))) : U32}
      +ix = Equal.trans(Nat, Nat.add(Nat.add(st, U32.to_nat(lrows)), Nat.sub(m, U32.to_nat(lrows))), Nat.add(st, Nat.add(U32.to_nat(lrows), Nat.sub(m, U32.to_nat(lrows)))), Nat.add(st, m), nat_add_assoc(st, U32.to_nat(lrows), Nat.sub(m, U32.to_nat(lrows))), Equal.cong(Nat, Nat, q => Nat.add(st, q), Nat.add(U32.to_nat(lrows), Nat.sub(m, U32.to_nat(lrows))), m, nat_sub_add(U32.to_nat(lrows), m, nat_le_of_not_lt(m, U32.to_nat(lrows), eb))))
      %ix : {Laws.ncell(r, Nat.sub(m, U32.to_nat(lrows))) == Laws.rd_at(U32, src, Laws.addn(0, _)) : U32}
      ar(Nat.sub(m, U32.to_nat(lrows)), nat_lt_sub(m, U32.to_nat(lrows), Laws.nrows(r), (%Equal.sym(Nat, Nat.add(U32.to_nat(lrows), Laws.nrows(r)), U32.to_nat(rows), esum) : {Nat.is_lt(m, _) == True{} : Bool}; hm), eb))

# the node over l (at st) and r (right after it) has the rows of the source from st
def node_at(+st: Nat, +rows: U32, +lrows: U32, -l: CH.CW, -r: CH.CW, -src: Array<U32>,
  el: {lrows == Laws.crows(l) : U32}, esum: {Nat.add(U32.to_nat(lrows), Laws.nrows(r)) == U32.to_nat(rows) : Nat},
  al: Laws.TreeAt(l, st, src), ar: Laws.TreeAt(r, Nat.add(st, U32.to_nat(lrows)), src))
  -> Laws.TreeAt(CH.WN{rows, lrows, l, r}, st, src):
  +m => hm => node_at_b(Nat.is_lt(m, U32.to_nat(lrows)), st, rows, lrows, l, r, src, m, {==}, hm, el, esum, al, ar)

# ==== the builder ======================================================================================

# the stack's trees laid back to back over the source: the top one ends at e (exclusive); each tree
# starts at st with st + rows = the end of the one above it; the bottom one starts at 0
def LayS(s: CH.CWS, +e: Nat, -src: Array<U32>) -> Type:
  match s:
    case CH.CWNil{}:
      {e == 0n : Nat}
    case CH.CWCons{+rows, c, next}:
      &st: Nat -> {Nat.add(st, U32.to_nat(rows)) == e : Nat} & {rows == Laws.crows(c) : U32} & Laws.WFChunks(c) & Laws.TreeAt(c, st, src) & LayS(next, st, src)

# the two top trees of the stack as one node: its end, its well-formedness, its rows
def lay_join(+r2: U32, -c2: CH.CW, +rows: U32, -c: CH.CW, +st2: Nat, +st: Nat, +e: Nat, -src: Array<U32>, +n: U32,
  +e2: {Nat.add(st2, U32.to_nat(r2)) == st : Nat}, ec2: {r2 == Laws.crows(c2) : U32}, wc2: Laws.WFChunks(c2), at2: Laws.TreeAt(c2, st2, src),
  +est: {Nat.add(st, U32.to_nat(rows)) == e : Nat}, +ec: {rows == Laws.crows(c) : U32}, wc: Laws.WFChunks(c), at: Laws.TreeAt(c, st, src),
  hn: {Nat.is_le(e, U32.to_nat(n)) == True{} : Bool})
  -> {Nat.add(st2, U32.to_nat(U32.add(r2, rows))) == e : Nat} & Laws.WFChunks(CH.WN{U32.add(r2, rows), r2, c2, c}) & Laws.TreeAt(CH.WN{U32.add(r2, rows), r2, c2, c}, st2, src):
  +x = Nat.add(U32.to_nat(r2), U32.to_nat(rows))
  +eqx = Equal.trans(Nat, Nat.add(st2, x), Nat.add(Nat.add(st2, U32.to_nat(r2)), U32.to_nat(rows)), e, Equal.sym(Nat, Nat.add(Nat.add(st2, U32.to_nat(r2)), U32.to_nat(rows)), Nat.add(st2, x), nat_add_assoc(st2, U32.to_nat(r2), U32.to_nat(rows))), (%e2 : {Nat.add(_, U32.to_nat(rows)) == e : Nat}; est))
  +tsum = to_nat_add(r2, rows, n, PST.nat_le_trans(x, Nat.add(st2, x), U32.to_nat(n), nat_le_add_l(st2, x), (%Equal.sym(Nat, Nat.add(st2, x), e, eqx) : {Nat.is_le(_, U32.to_nat(n)) == True{} : Bool}; hn)))
  +esum = (%ec : {Nat.add(U32.to_nat(r2), U32.to_nat(_)) == U32.to_nat(U32.add(r2, rows)) : Nat}; Equal.sym(Nat, U32.to_nat(U32.add(r2, rows)), x, tsum))
  ((%Equal.sym(Nat, x, U32.to_nat(U32.add(r2, rows)), Equal.sym(Nat, U32.to_nat(U32.add(r2, rows)), x, tsum)) : {Nat.add(st2, _) == e : Nat}; eqx), (ec2, esum, wc2, wc), node_at(st2, U32.add(r2, rows), r2, c2, c, src, ec2, esum, at2, (%Equal.sym(Nat, st, Nat.add(st2, U32.to_nat(r2)), e2) : Laws.TreeAt(c, _, src); at)))
