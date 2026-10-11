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

def nat_add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
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
def nat_lt_sub(m: Nat, l: Nat, -r: Nat, h: {Nat.is_lt(m, Nat.add(l, r)) == True{} : Bool}, nl: {Nat.is_lt(m, l) == False{} : Bool}) -> {Nat.is_lt(Nat.sub(m, l), r) == True{} : Bool}:
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
def nat_lt_add_r(m: Nat, l: Nat, -r: Nat, h: {Nat.is_lt(m, l) == True{} : Bool}) -> {Nat.is_lt(m, Nat.add(l, r)) == True{} : Bool}:
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
def nat_add_le_mono(a: Nat, -b: Nat, -c: Nat, h: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, b), Nat.add(a, c)) == True{} : Bool}:
  match a:
    case 0n:
      h
    case 1n+p:
      nat_add_le_mono(p, b, c, h)

# a + b < a + c from b < c
def nat_add_lt_mono(a: Nat, -b: Nat, -c: Nat, h: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(Nat.add(a, b), Nat.add(a, c)) == True{} : Bool}:
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
  +eb: {Nat.is_lt(m, U32.to_nat(lrows)) == b : Bool}, hm: {Nat.is_lt(m, U32.to_nat(rows)) == True{} : Bool},
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

def lj_esum(+r2: U32, +rows: U32, -c: CH.CW, ec: {rows == Laws.crows(c) : U32}, tsum: {U32.to_nat(U32.add(r2, rows)) == Nat.add(U32.to_nat(r2), U32.to_nat(rows)) : Nat}) -> {Nat.add(U32.to_nat(r2), Laws.nrows(c)) == U32.to_nat(U32.add(r2, rows)) : Nat}:
  %ec : {Nat.add(U32.to_nat(r2), U32.to_nat(_)) == U32.to_nat(U32.add(r2, rows)) : Nat}
  Equal.sym(Nat, U32.to_nat(U32.add(r2, rows)), Nat.add(U32.to_nat(r2), U32.to_nat(rows)), tsum)

# the two top trees of the stack as one node: its end, its well-formedness, its rows
def lay_join(+r2: U32, -c2: CH.CW, +rows: U32, -c: CH.CW, +st2: Nat, +st: Nat, +e: Nat, -src: Array<U32>, +n: U32,
  +e2: {Nat.add(st2, U32.to_nat(r2)) == st : Nat}, +ec2: {r2 == Laws.crows(c2) : U32}, wc2: Laws.WFChunks(c2), at2: Laws.TreeAt(c2, st2, src),
  +est: {Nat.add(st, U32.to_nat(rows)) == e : Nat}, +ec: {rows == Laws.crows(c) : U32}, wc: Laws.WFChunks(c), at: Laws.TreeAt(c, st, src),
  hn: {Nat.is_le(e, U32.to_nat(n)) == True{} : Bool})
  -> {Nat.add(st2, U32.to_nat(U32.add(r2, rows))) == e : Nat} & Laws.WFChunks(CH.WN{U32.add(r2, rows), r2, c2, c}) & Laws.TreeAt(CH.WN{U32.add(r2, rows), r2, c2, c}, st2, src):
  +x = Nat.add(U32.to_nat(r2), U32.to_nat(rows))
  +eqx = Equal.trans(Nat, Nat.add(st2, x), Nat.add(Nat.add(st2, U32.to_nat(r2)), U32.to_nat(rows)), e, Equal.sym(Nat, Nat.add(Nat.add(st2, U32.to_nat(r2)), U32.to_nat(rows)), Nat.add(st2, x), nat_add_assoc(st2, U32.to_nat(r2), U32.to_nat(rows))), (%Equal.sym(Nat, Nat.add(st2, U32.to_nat(r2)), st, e2) : {Nat.add(_, U32.to_nat(rows)) == e : Nat}; est))
  +tsum = to_nat_add(r2, rows, n, PST.nat_le_trans(x, Nat.add(st2, x), U32.to_nat(n), nat_le_add_l(st2, x), (%Equal.sym(Nat, Nat.add(st2, x), e, eqx) : {Nat.is_le(_, U32.to_nat(n)) == True{} : Bool}; hn)))
  +esum = lj_esum(r2, rows, c, ec, tsum)
  ((%Equal.sym(Nat, U32.to_nat(U32.add(r2, rows)), x, tsum) : {Nat.add(st2, _) == e : Nat}; eqx), (ec2, esum, wc2, wc), node_at(st2, U32.add(r2, rows), r2, c2, c, src, ec2, esum, at2, (%Equal.sym(Nat, Nat.add(st2, U32.to_nat(r2)), st, e2) : Laws.TreeAt(c, _, src); at)))

# the stack after a push / merge, laid up to e
def MergeW(m: Nat, +rows: U32, -c: CH.CW, -s: CH.CWS, +e: Nat, -src: Array<U32>) -> Type:
  &s2: CH.CWS -> {CH.CWS.merge(m, rows, c, s) == s2 : CH.CWS} & LayS(s2, e, src)

def merge_j(p: Nat, +r2: U32, -c2: CH.CW, +rows: U32, -c: CH.CW, -nx: CH.CWS, +st2: Nat, +e: Nat, -src: Array<U32>,
  j: {Nat.add(st2, U32.to_nat(U32.add(r2, rows))) == e : Nat} & Laws.WFChunks(CH.WN{U32.add(r2, rows), r2, c2, c}) & Laws.TreeAt(CH.WN{U32.add(r2, rows), r2, c2, c}, st2, src),
  ih: {Nat.add(st2, U32.to_nat(U32.add(r2, rows))) == e : Nat} -> Laws.WFChunks(CH.WN{U32.add(r2, rows), r2, c2, c}) -> Laws.TreeAt(CH.WN{U32.add(r2, rows), r2, c2, c}, st2, src) -> MergeW(p, U32.add(r2, rows), CH.WN{U32.add(r2, rows), r2, c2, c}, nx, e, src))
  -> MergeW(p, U32.add(r2, rows), CH.WN{U32.add(r2, rows), r2, c2, c}, nx, e, src):
  (est2, wn, an) = j
  ih(est2, wn, an)

# CWS.merge keeps the stack laid back to back (the merged node's counts are exact below n rows)
def merge_w(m: Nat, +rows: U32, c: CH.CW, s: CH.CWS, +st: Nat, +e: Nat, -src: Array<U32>, +n: U32,
  +est: {Nat.add(st, U32.to_nat(rows)) == e : Nat}, +ec: {rows == Laws.crows(c) : U32}, wc: Laws.WFChunks(c), at: Laws.TreeAt(c, st, src),
  lay: LayS(s, st, src), +hn: {Nat.is_le(e, U32.to_nat(n)) == True{} : Bool})
  -> MergeW(m, rows, c, s, e, src):
  match m s:
    case 0n CH.CWNil{}:
      (CH.CWCons{rows, c, CH.CWNil{}}, {==}, (st, est, ec, wc, at, lay))
    case 0n CH.CWCons{+r2, c2, nx}:
      (CH.CWCons{rows, c, CH.CWCons{r2, c2, nx}}, {==}, (st, est, ec, wc, at, lay))
    case 1n+p CH.CWNil{}:
      (CH.CWCons{rows, c, CH.CWNil{}}, {==}, (st, est, ec, wc, at, lay))
    case 1n++p CH.CWCons{+r2, c2, nx}:
      (+st2, +e2, +ec2, wc2, at2, lay2) = lay
      merge_j(p, r2, c2, rows, c, nx, st2, e, src, lay_join(r2, c2, rows, c, st2, st, e, src, n, e2, ec2, wc2, at2, est, ec, wc, at, hn), est2 => wn => an => merge_w(p, U32.add(r2, rows), CH.WN{U32.add(r2, rows), r2, c2, c}, nx, st2, e, src, n, est2, {==}, wn, an, lay2, hn))

# the folded tree: well formed, e rows, the source's rows from 0
def CollW(-t0: CH.CW, +e: Nat, -src: Array<U32>) -> Type:
  &t: CH.CW -> {t0 == t : CH.CW} & Laws.WFChunks(t) & {Laws.nrows(t) == e : Nat} & Laws.TreeAt(t, 0n, src)

def coll_j(+r2: U32, -c2: CH.CW, +rows: U32, -c: CH.CW, -nx: CH.CWS, +st2: Nat, +e: Nat, -src: Array<U32>,
  j: {Nat.add(st2, U32.to_nat(U32.add(r2, rows))) == e : Nat} & Laws.WFChunks(CH.WN{U32.add(r2, rows), r2, c2, c}) & Laws.TreeAt(CH.WN{U32.add(r2, rows), r2, c2, c}, st2, src),
  ih: {Nat.add(st2, U32.to_nat(U32.add(r2, rows))) == e : Nat} -> Laws.WFChunks(CH.WN{U32.add(r2, rows), r2, c2, c}) -> Laws.TreeAt(CH.WN{U32.add(r2, rows), r2, c2, c}, st2, src) -> CollW(CH.CWS.collapse.go(nx, U32.add(r2, rows), CH.WN{U32.add(r2, rows), r2, c2, c}), e, src))
  -> CollW(CH.CWS.collapse.go(nx, U32.add(r2, rows), CH.WN{U32.add(r2, rows), r2, c2, c}), e, src):
  (est2, wn, an) = j
  ih(est2, wn, an)

def coll_nil_n(+rows: U32, -c: CH.CW, +st: Nat, +e: Nat, +est: {Nat.add(st, U32.to_nat(rows)) == e : Nat}, +ec: {rows == Laws.crows(c) : U32}, +lay: {st == 0n : Nat}) -> {Laws.nrows(c) == e : Nat}:
  Equal.trans(Nat, Laws.nrows(c), Nat.add(st, U32.to_nat(rows)), e, Equal.trans(Nat, Laws.nrows(c), Nat.add(0n, U32.to_nat(rows)), Nat.add(st, U32.to_nat(rows)), Equal.cong(U32, Nat, q => U32.to_nat(q), Laws.crows(c), rows, Equal.sym(U32, rows, Laws.crows(c), ec)), Equal.cong(Nat, Nat, q => Nat.add(q, U32.to_nat(rows)), 0n, st, Equal.sym(Nat, st, 0n, lay))), est)

def coll_nil_c(-c: CH.CW, +st: Nat, -src: Array<U32>, +m: Nat, +lay: {st == 0n : Nat}, h: {Laws.ncell(c, m) == Laws.rd_at(U32, src, Laws.addn(0, Nat.add(st, m))) : U32}) -> {Laws.ncell(c, m) == Laws.rd_at(U32, src, Laws.addn(0, Nat.add(0n, m))) : U32}:
  Equal.trans(U32, Laws.ncell(c, m), Laws.rd_at(U32, src, Laws.addn(0, Nat.add(st, m))), Laws.rd_at(U32, src, Laws.addn(0, Nat.add(0n, m))), h, Equal.cong(Nat, U32, q => Laws.rd_at(U32, src, Laws.addn(0, Nat.add(q, m))), st, 0n, lay))

def coll_nil(+rows: U32, c: CH.CW, +st: Nat, +e: Nat, -src: Array<U32>, +est: {Nat.add(st, U32.to_nat(rows)) == e : Nat}, +ec: {rows == Laws.crows(c) : U32}, wc: Laws.WFChunks(c), at: Laws.TreeAt(c, st, src), +lay: {st == 0n : Nat})
  -> CollW(c, e, src):
  (c, {==}, wc, coll_nil_n(rows, c, st, e, est, ec, lay), +m => hm => coll_nil_c(c, st, src, m, lay, at(m, hm)))

def collapse_go_w(s: CH.CWS, +rows: U32, c: CH.CW, +st: Nat, +e: Nat, -src: Array<U32>, +n: U32,
  +est: {Nat.add(st, U32.to_nat(rows)) == e : Nat}, +ec: {rows == Laws.crows(c) : U32}, wc: Laws.WFChunks(c), at: Laws.TreeAt(c, st, src),
  lay: LayS(s, st, src), +hn: {Nat.is_le(e, U32.to_nat(n)) == True{} : Bool})
  -> CollW(CH.CWS.collapse.go(s, rows, c), e, src):
  match s:
    case CH.CWNil{}:
      coll_nil(rows, c, st, e, src, est, ec, wc, at, lay)
    case CH.CWCons{+r2, c2, nx}:
      (+st2, +e2, +ec2, wc2, at2, lay2) = lay
      coll_j(r2, c2, rows, c, nx, st2, e, src, lay_join(r2, c2, rows, c, st2, st, e, src, n, e2, ec2, wc2, at2, est, ec, wc, at, hn), est2 => wn => an => collapse_go_w(nx, U32.add(r2, rows), CH.WN{U32.add(r2, rows), r2, c2, c}, st2, e, src, n, est2, {==}, wn, an, lay2, hn))

def collapse_w(s: CH.CWS, +e: Nat, -src: Array<U32>, +n: U32, lay: LayS(s, e, src), +hn: {Nat.is_le(e, U32.to_nat(n)) == True{} : Bool}) -> CollW(CH.CWS.collapse(s), e, src):
  match s:
    case CH.CWNil{}:
      (CH.WL{0, 0n, Array.new(U32, 0n, 0)}, {==}, ({==}, Laws.wf_new(U32, 0n, 0)), Equal.sym(Nat, e, 0n, lay), m => hm => Empty.absurd({Laws.ncell(CH.WL{0, 0n, Array.new(U32, 0n, 0)}, m) == Laws.rd_at(U32, src, Laws.addn(0, Nat.add(0n, m))) : U32}, PST.nat_lt0(m, hm)))
    case CH.CWCons{+rows, c, nx}:
      (+st, +est, +ec, wc, at, lay2) = lay
      collapse_go_w(nx, rows, c, st, e, src, n, est, ec, wc, at, lay2, hn)

# ---- one leaf of a build: Ch.rng's copy of rows off .. off + m, its cells the source's from off -------

def LeafW(+m: U32, +g: Nat, +off: U32, -src: Array<U32>) -> Type:
  &b: Array<U32> -> {CH.Ch.rng(~U32, m, g, off, src, 0) == (b, src) : Array<U32> & Array<U32>} & Laws.WFChunks(CH.WL{m, g, b}) & Laws.TreeAt(CH.WL{m, g, b}, U32.to_nat(off), src)

def leaf_cell(+g: Nat, +off: U32, +k: Nat, -src: Array<U32>, -a2: Array<U32>, -o: Array<U32>, -b: Array<U32>,
  +esb: {Array.size(U32, b) == (b, U32.shln(1, g)) : Array<U32> & U32}, +eb: {b == o : Array<U32>}, +ea2: {a2 == src : Array<U32>},
  ro: {Laws.rdN(U32, g, o, Laws.addn(0, k)) == Laws.rd_at(U32, a2, U32.add(off, Laws.addn(0, k))) : U32})
  -> {Laws.rd_at(U32, b, Laws.addn(0, k)) == Laws.rd_at(U32, src, Laws.addn(0, Nat.add(U32.to_nat(off), k))) : U32}:
  %Equal.sym(Array<U32> & U32, Array.size(U32, b), (b, U32.shln(1, g)), esb) : {Laws.rd_size(U32, Laws.addn(0, k), _) == Laws.rd_at(U32, src, Laws.addn(0, Nat.add(U32.to_nat(off), k))) : U32}
  %Equal.sym(Array<U32>, b, o, eb) : {Laws.rdN(U32, g, _, Laws.addn(0, k)) == Laws.rd_at(U32, src, Laws.addn(0, Nat.add(U32.to_nat(off), k))) : U32}
  %idx_eq(off, k) : {Laws.rdN(U32, g, o, Laws.addn(0, k)) == Laws.rd_at(U32, src, _) : U32}
  %ea2 : {Laws.rdN(U32, g, o, Laws.addn(0, k)) == Laws.rd_at(U32, _, U32.add(off, Laws.addn(0, k))) : U32}
  ro

# k < to_nat(m): addn(0, k) < addn(0, to_nat(m)) as words
def hk_lt(+m: U32, +k: Nat, +hk: {Nat.is_lt(k, U32.to_nat(m)) == True{} : Bool}) -> {U32.is_lt(Laws.addn(0, k), Laws.addn(0, U32.to_nat(m))) == True{} : Bool}:
  %Equal.sym(U32, Laws.addn(0, U32.to_nat(m)), m, B.addn_to_nat(m)) : {U32.is_lt(Laws.addn(0, k), _) == True{} : Bool}
  ult_of_n(Laws.addn(0, k), m, (%Equal.sym(Nat, U32.to_nat(Laws.addn(0, k)), k, to_nat_addn0(k, m, nat_le_of_lt(k, U32.to_nat(m), hk))) : {Nat.is_lt(_, U32.to_nat(m)) == True{} : Bool}; hk))

def size_back(+g: Nat, -o: Array<U32>, -b: Array<U32>, +eb: {b == o : Array<U32>}, es: {Array.size(U32, o) == (b, U32.shln(1, g)) : Array<U32> & U32}) -> {Array.size(U32, b) == (b, U32.shln(1, g)) : Array<U32> & U32}:
  %Equal.sym(Array<U32>, b, o, eb) : {Array.size(U32, _) == (b, U32.shln(1, g)) : Array<U32> & U32}
  es

def rng_eq(+m: U32, +g: Nat, +off: U32, -src: Array<U32>, -a1: Array<U32>, -a2: Array<U32>, -o: Array<U32>, -b: Array<U32>, +ea1: {a1 == src : Array<U32>}, +ea2: {a2 == src : Array<U32>},
  rr: {CH.Ch.rng(~U32, m, g, off, a1, 0) == (K.Kernel.range(~U32, m, g, off, a1, 0), a1) : Array<U32> & Array<U32>},
  +eo: {K.Kernel.range.go(~U32, U32.to_nat(m), 0, off, Array.new(U32, g, 0), Array.get(U32, a2, U32.add(off, 0))) == o : Array<U32>}, +eb: {b == o : Array<U32>})
  -> {CH.Ch.rng(~U32, m, g, off, src, 0) == (b, src) : Array<U32> & Array<U32>}:
  %ea1 : {CH.Ch.rng(~U32, m, g, off, _, 0) == (b, _) : Array<U32> & Array<U32>}
  %Equal.sym(Array<U32> & Array<U32>, CH.Ch.rng(~U32, m, g, off, a1, 0), (K.Kernel.range(~U32, m, g, off, a1, 0), a1), rr) : {_ == (b, a1) : Array<U32> & Array<U32>}
  %Equal.trans(Array<U32>, a2, src, a1, ea2, Equal.sym(Array<U32>, a1, src, ea1)) : {(K.Kernel.range(~U32, m, g, off, _, 0), a1) == (b, a1) : Array<U32> & Array<U32>}
  %Equal.sym(Array<U32>, K.Kernel.range.go(~U32, U32.to_nat(m), 0, off, Array.new(U32, g, 0), Array.get(U32, a2, U32.add(off, 0))), o, eo) : {(_, a1) == (b, a1) : Array<U32> & Array<U32>}
  %eb : {(_, a1) == (b, a1) : Array<U32> & Array<U32>}
  {==}

def mk_leaf_c(+m: U32, +g: Nat, +off: U32, -src: Array<U32>, -a1: Array<U32>, -a2: Array<U32>, -o: Array<U32>, +ea1: {a1 == src : Array<U32>}, +ea2: {a2 == src : Array<U32>},
  rr: {CH.Ch.rng(~U32, m, g, off, a1, 0) == (K.Kernel.range(~U32, m, g, off, a1, 0), a1) : Array<U32> & Array<U32>},
  +eo: {K.Kernel.range.go(~U32, U32.to_nat(m), 0, off, Array.new(U32, g, 0), Array.get(U32, a2, U32.add(off, 0))) == o : Array<U32>},
  ro: @kk: U32 -> {U32.is_lt(kk, Laws.addn(0, U32.to_nat(m))) == True{} : Bool} -> {Laws.rdN(U32, g, o, kk) == Laws.rd_at(U32, a2, U32.add(off, kk)) : U32},
  +fits: {U32.is_le(m, U32.shln(1, g)) == True{} : Bool},
  w: &b: Array<U32> -> {b == o : Array<U32>} & Laws.WFArray(U32, g, b) & {Array.size(U32, o) == (b, U32.shln(1, g)) : Array<U32> & U32})
  -> LeafW(m, g, off, src):
  (b, +eb, wb, es) = w
  +esb = size_back(g, o, b, eb, es)
  (b, rng_eq(m, g, off, src, a1, a2, o, b, ea1, ea2, rr, eo, eb), (fits, wb), +k => +hk => leaf_cell(g, off, k, src, a2, o, b, esb, eb, ea2, ro(Laws.addn(0, k), hk_lt(m, k, hk))))

def mk_leaf_b(+m: U32, +g: Nat, +off: U32, -src: Array<U32>, -a1: Array<U32>, -a2: Array<U32>, +ea1: {a1 == src : Array<U32>}, +ea2: {a2 == src : Array<U32>},
  rr: {CH.Ch.rng(~U32, m, g, off, a1, 0) == (K.Kernel.range(~U32, m, g, off, a1, 0), a1) : Array<U32> & Array<U32>}, +fits: {U32.is_le(m, U32.shln(1, g)) == True{} : Bool},
  w: &o: Array<U32> -> {K.Kernel.range.go(~U32, U32.to_nat(m), 0, off, Array.new(U32, g, 0), Array.get(U32, a2, U32.add(off, 0))) == o : Array<U32>} & PC.RRes(~U32, g, off, a2, o, Laws.addn(0, U32.to_nat(m))))
  -> LeafW(m, g, off, src):
  (o, +eo, wo, ro) = w
  mk_leaf_c(m, g, off, src, a1, a2, o, ea1, ea2, rr, eo, ro, fits, PC.wf_size(U32, g, o, wo))

def mk_leaf_a(+m: U32, +g: Nat, +off: U32, -src: Array<U32>, -a: Array<U32>, +ea: {a == src : Array<U32>}, +fits: {U32.is_le(m, U32.shln(1, g)) == True{} : Bool},
  w: &a1: Array<U32> -> &a2: Array<U32> -> {a1 == a : Array<U32>} & {a2 == a : Array<U32>})
  -> LeafW(m, g, off, src):
  (a1, a2, +e1, +e2) = w
  mk_leaf_b(m, g, off, src, a1, a2, Equal.trans(Array<U32>, a1, a, src, e1, ea), Equal.trans(Array<U32>, a2, a, src, e2, ea), Laws.ch_rng_range(m, g, off, a1, 0), fits, PC.range_go(~U32, U32.to_nat(m), 0, g, off, a2, Array.new(U32, g, 0), Laws.wf_new(U32, g, 0), B.room_from(g, m, fits))(PC.rhyp0(~U32, g, off, a2, Array.new(U32, g, 0))))

def mk_leaf(+m: U32, +g: Nat, +off: U32, -src: Array<U32>, a: Array<U32>, +ea: {a == src : Array<U32>}, +fits: {U32.is_le(m, U32.shln(1, g)) == True{} : Bool}) -> LeafW(m, g, off, src):
  mk_leaf_a(m, g, off, src, a, ea, fits, PC.clone_eq(U32, a))

# ---- the leaf loop ------------------------------------------------------------------------------------

def nat_sub_le(a: Nat, b: Nat) -> {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      nat_le_refl(1n+p)
    case 1n++p 1n++q:
      PST.nat_le_trans(Nat.sub(p, q), p, 1n+p, nat_sub_le(p, q), PST.nat_le_succ(p))

def u_le_of_not_lt(+a: U32, +b: U32, h: {U32.is_lt(a, b) == False{} : Bool}) -> {U32.is_le(b, a) == True{} : Bool}:
  ule_of_n(b, a, nat_le_of_not_lt(U32.to_nat(a), U32.to_nat(b), (%ult_nat(a, b) : {_ == False{} : Bool}; h)))

def le_refl_u(+a: U32) -> {U32.is_le(a, a) == True{} : Bool}:
  ule_of_n(a, a, nat_le_refl(U32.to_nat(a)))

# off + (n - off) == n (as values)
def est_sub(+n: U32, +off: U32, +hoff: {Nat.is_le(U32.to_nat(off), U32.to_nat(n)) == True{} : Bool}) -> {Nat.add(U32.to_nat(off), U32.to_nat(U32.sub(n, off))) == U32.to_nat(n) : Nat}:
  %Equal.sym(Nat, U32.to_nat(U32.sub(n, off)), Nat.sub(U32.to_nat(n), U32.to_nat(off)), sub_nat(n, off, ule_of_n(off, n, hoff))) : {Nat.add(U32.to_nat(off), _) == U32.to_nat(n) : Nat}
  nat_sub_add(U32.to_nat(off), U32.to_nat(n), hoff)

# a full leaf of 2^g rows left more than 2^g rows: off + 2^g stays below n
def adv_lt(+off: U32, +n: U32, +g: Nat, +hoff: {Nat.is_le(U32.to_nat(off), U32.to_nat(n)) == True{} : Bool}, +lt: {U32.is_lt(U32.shln(1, g), U32.sub(n, off)) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(U32.to_nat(off), U32.to_nat(U32.shln(1, g))), U32.to_nat(n)) == True{} : Bool}:
  %nat_sub_add(U32.to_nat(off), U32.to_nat(n), hoff) : {Nat.is_lt(Nat.add(U32.to_nat(off), U32.to_nat(U32.shln(1, g))), _) == True{} : Bool}
  nat_add_lt_mono(U32.to_nat(off), U32.to_nat(U32.shln(1, g)), Nat.sub(U32.to_nat(n), U32.to_nat(off)), (%sub_nat(n, off, ule_of_n(off, n, hoff)) : {Nat.is_lt(U32.to_nat(U32.shln(1, g)), _) == True{} : Bool}; nlt_of_u(U32.shln(1, g), U32.sub(n, off), lt)))

def adv_sum(+off: U32, +n: U32, +g: Nat, +hoff: {Nat.is_le(U32.to_nat(off), U32.to_nat(n)) == True{} : Bool}, +lt: {U32.is_lt(U32.shln(1, g), U32.sub(n, off)) == True{} : Bool})
  -> {U32.to_nat(U32.add(off, U32.shln(1, g))) == Nat.add(U32.to_nat(off), U32.to_nat(U32.shln(1, g))) : Nat}:
  to_nat_add(off, U32.shln(1, g), n, nat_le_of_lt(Nat.add(U32.to_nat(off), U32.to_nat(U32.shln(1, g))), U32.to_nat(n), adv_lt(off, n, g, hoff, lt)))

def adv_est(+off: U32, +n: U32, +g: Nat, +hoff: {Nat.is_le(U32.to_nat(off), U32.to_nat(n)) == True{} : Bool}, +lt: {U32.is_lt(U32.shln(1, g), U32.sub(n, off)) == True{} : Bool})
  -> {Nat.add(U32.to_nat(off), U32.to_nat(U32.shln(1, g))) == U32.to_nat(U32.add(off, U32.shln(1, g))) : Nat}:
  Equal.sym(Nat, U32.to_nat(U32.add(off, U32.shln(1, g))), Nat.add(U32.to_nat(off), U32.to_nat(U32.shln(1, g))), adv_sum(off, n, g, hoff, lt))

def adv_le(+off: U32, +n: U32, +g: Nat, +hoff: {Nat.is_le(U32.to_nat(off), U32.to_nat(n)) == True{} : Bool}, +lt: {U32.is_lt(U32.shln(1, g), U32.sub(n, off)) == True{} : Bool})
  -> {Nat.is_le(U32.to_nat(U32.add(off, U32.shln(1, g))), U32.to_nat(n)) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat(U32.add(off, U32.shln(1, g))), Nat.add(U32.to_nat(off), U32.to_nat(U32.shln(1, g))), adv_sum(off, n, g, hoff, lt)) : {Nat.is_le(_, U32.to_nat(n)) == True{} : Bool}
  nat_le_of_lt(Nat.add(U32.to_nat(off), U32.to_nat(U32.shln(1, g))), U32.to_nat(n), adv_lt(off, n, g, hoff, lt))

# n - o2 <= n <= 2^ds
def rest_fits(+n: U32, +o2: U32, +ds: Nat, +hoff2: {Nat.is_le(U32.to_nat(o2), U32.to_nat(n)) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, ds)) == True{} : Bool}) -> {U32.is_le(U32.sub(n, o2), U32.shln(1, ds)) == True{} : Bool}:
  ule_of_n(U32.sub(n, o2), U32.shln(1, ds), PST.nat_le_trans(U32.to_nat(U32.sub(n, o2)), U32.to_nat(n), U32.to_nat(U32.shln(1, ds)), (%Equal.sym(Nat, U32.to_nat(U32.sub(n, o2)), Nat.sub(U32.to_nat(n), U32.to_nat(o2)), sub_nat(n, o2, ule_of_n(o2, n, hoff2))) : {Nat.is_le(_, U32.to_nat(n)) == True{} : Bool}; nat_sub_le(U32.to_nat(n), U32.to_nat(o2))), nle_of_u(n, U32.shln(1, ds), fits)))

def OfGo(f: Nat, +more: Bool, +i: U32, +off: U32, +n: U32, +g: Nat, +ds: Nat, -s: CH.CWS, -src: Array<U32>) -> Type:
  &s2: CH.CWS -> {CH.CW.of.go(f, more, i, off, n, g, ds, s, CH.Ch.rng(~U32, Bool.pick(U32, more, U32.shln(1, g), U32.sub(n, off)), g, off, src, 0)) == s2 : CH.CWS} & LayS(s2, U32.to_nat(n), src)

# the last leaf (rows off .. n, at most 2^g of them)
def of_last_a(f: Nat, +i: U32, +off: U32, +n: U32, +g: Nat, +ds: Nat, s: CH.CWS, -src: Array<U32>, +hoff: {Nat.is_le(U32.to_nat(off), U32.to_nat(n)) == True{} : Bool}, lay: LayS(s, U32.to_nat(off), src), lw: LeafW(U32.sub(n, off), g, off, src))
  -> OfGo(f, False{}, i, off, n, g, ds, s, src):
  match f:
    case 0n:
      (b, eqr, wl, al) = lw
      %Equal.sym(Array<U32> & Array<U32>, CH.Ch.rng(~U32, U32.sub(n, off), g, off, src, 0), (b, src), eqr) : &s2: CH.CWS -> {CH.CW.of.go(0n, False{}, i, off, n, g, ds, s, _) == s2 : CH.CWS} & LayS(s2, U32.to_nat(n), src)
      merge_w(CH.Ch.tz(U32.inc(i)), U32.sub(n, off), CH.WL{U32.sub(n, off), g, b}, s, U32.to_nat(off), U32.to_nat(n), src, n, est_sub(n, off, hoff), {==}, wl, al, lay, nat_le_refl(U32.to_nat(n)))
    case 1n+p:
      (b, eqr, wl, al) = lw
      %Equal.sym(Array<U32> & Array<U32>, CH.Ch.rng(~U32, U32.sub(n, off), g, off, src, 0), (b, src), eqr) : &s2: CH.CWS -> {CH.CW.of.go(1n+p, False{}, i, off, n, g, ds, s, _) == s2 : CH.CWS} & LayS(s2, U32.to_nat(n), src)
      merge_w(CH.Ch.tz(U32.inc(i)), U32.sub(n, off), CH.WL{U32.sub(n, off), g, b}, s, U32.to_nat(off), U32.to_nat(n), src, n, est_sub(n, off, hoff), {==}, wl, al, lay, nat_le_refl(U32.to_nat(n)))

def of_last(f: Nat, +i: U32, +off: U32, +n: U32, +g: Nat, +ds: Nat, s: CH.CWS, -src: Array<U32>, a: Array<U32>, +ea: {a == src : Array<U32>}, +hoff: {Nat.is_le(U32.to_nat(off), U32.to_nat(n)) == True{} : Bool}, lay: LayS(s, U32.to_nat(off), src), nle: {U32.is_lt(U32.shln(1, g), U32.sub(n, off)) == False{} : Bool})
  -> OfGo(f, False{}, i, off, n, g, ds, s, src):
  of_last_a(f, i, off, n, g, ds, s, src, hoff, lay, mk_leaf(U32.sub(n, off), g, off, src, a, ea, u_le_of_not_lt(U32.shln(1, g), U32.sub(n, off), nle)))

# out of fuel: the full leaf, then the rest as one leaf of the source's depth
def of_rest_d(+i: U32, +o2: U32, +n: U32, +ds: Nat, s3: CH.CWS, -src: Array<U32>, +hoff2: {Nat.is_le(U32.to_nat(o2), U32.to_nat(n)) == True{} : Bool}, lay3: LayS(s3, U32.to_nat(o2), src), lw: LeafW(U32.sub(n, o2), ds, o2, src))
  -> &s2: CH.CWS -> {CH.CW.of.rest(i, o2, n, ds, s3, CH.Ch.rng(~U32, U32.sub(n, o2), ds, o2, src, 0)) == s2 : CH.CWS} & LayS(s2, U32.to_nat(n), src):
  (b2, eqr, wl, al) = lw
  %Equal.sym(Array<U32> & Array<U32>, CH.Ch.rng(~U32, U32.sub(n, o2), ds, o2, src, 0), (b2, src), eqr) : &s2: CH.CWS -> {CH.CW.of.rest(i, o2, n, ds, s3, _) == s2 : CH.CWS} & LayS(s2, U32.to_nat(n), src)
  merge_w(CH.Ch.tz(U32.inc(i)), U32.sub(n, o2), CH.WL{U32.sub(n, o2), ds, b2}, s3, U32.to_nat(o2), U32.to_nat(n), src, n, est_sub(n, o2, hoff2), {==}, wl, al, lay3, nat_le_refl(U32.to_nat(n)))

def of_rest_c(+i: U32, +off: U32, +n: U32, +g: Nat, +ds: Nat, -s: CH.CWS, -b: Array<U32>, -src: Array<U32>, a2: Array<U32>, +ea2: {a2 == src : Array<U32>},
  +hoff2: {Nat.is_le(U32.to_nat(U32.add(off, U32.shln(1, g))), U32.to_nat(n)) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, ds)) == True{} : Bool},
  mw: MergeW(CH.Ch.tz(U32.inc(i)), U32.shln(1, g), CH.WL{U32.shln(1, g), g, b}, s, U32.to_nat(U32.add(off, U32.shln(1, g))), src))
  -> &s2: CH.CWS -> {CH.CW.of.rest(U32.inc(i), U32.add(off, U32.shln(1, g)), n, ds, CH.CWS.push(i, U32.shln(1, g), CH.WL{U32.shln(1, g), g, b}, s), CH.Ch.rng(~U32, U32.sub(n, U32.add(off, U32.shln(1, g))), ds, U32.add(off, U32.shln(1, g)), src, 0)) == s2 : CH.CWS} & LayS(s2, U32.to_nat(n), src):
  (s3, eqs, lay3) = mw
  %Equal.sym(CH.CWS, CH.CWS.push(i, U32.shln(1, g), CH.WL{U32.shln(1, g), g, b}, s), s3, eqs) : &s2: CH.CWS -> {CH.CW.of.rest(U32.inc(i), U32.add(off, U32.shln(1, g)), n, ds, _, CH.Ch.rng(~U32, U32.sub(n, U32.add(off, U32.shln(1, g))), ds, U32.add(off, U32.shln(1, g)), src, 0)) == s2 : CH.CWS} & LayS(s2, U32.to_nat(n), src)
  of_rest_d(U32.inc(i), U32.add(off, U32.shln(1, g)), n, ds, s3, src, hoff2, lay3, mk_leaf(U32.sub(n, U32.add(off, U32.shln(1, g))), ds, U32.add(off, U32.shln(1, g)), src, a2, ea2, rest_fits(n, U32.add(off, U32.shln(1, g)), ds, hoff2, fits)))

def of_rest_b(+i: U32, +off: U32, +n: U32, +g: Nat, +ds: Nat, s: CH.CWS, -src: Array<U32>, a2: Array<U32>, +ea2: {a2 == src : Array<U32>}, +hoff: {Nat.is_le(U32.to_nat(off), U32.to_nat(n)) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, ds)) == True{} : Bool}, lay: LayS(s, U32.to_nat(off), src), +lt: {U32.is_lt(U32.shln(1, g), U32.sub(n, off)) == True{} : Bool}, lw: LeafW(U32.shln(1, g), g, off, src))
  -> OfGo(0n, True{}, i, off, n, g, ds, s, src):
  (b, eqr, wl, al) = lw
  %Equal.sym(Array<U32> & Array<U32>, CH.Ch.rng(~U32, U32.shln(1, g), g, off, src, 0), (b, src), eqr) : &s2: CH.CWS -> {CH.CW.of.go(0n, True{}, i, off, n, g, ds, s, _) == s2 : CH.CWS} & LayS(s2, U32.to_nat(n), src)
  of_rest_c(i, off, n, g, ds, s, b, src, a2, ea2, adv_le(off, n, g, hoff, lt), fits, merge_w(CH.Ch.tz(U32.inc(i)), U32.shln(1, g), CH.WL{U32.shln(1, g), g, b}, s, U32.to_nat(off), U32.to_nat(U32.add(off, U32.shln(1, g))), src, n, adv_est(off, n, g, hoff, lt), {==}, wl, al, lay, adv_le(off, n, g, hoff, lt)))

def of_rest_a(+i: U32, +off: U32, +n: U32, +g: Nat, +ds: Nat, s: CH.CWS, -src: Array<U32>, -a: Array<U32>, +ea: {a == src : Array<U32>}, +hoff: {Nat.is_le(U32.to_nat(off), U32.to_nat(n)) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, ds)) == True{} : Bool}, lay: LayS(s, U32.to_nat(off), src), +lt: {U32.is_lt(U32.shln(1, g), U32.sub(n, off)) == True{} : Bool},
  w: &a1: Array<U32> -> &a2: Array<U32> -> {a1 == a : Array<U32>} & {a2 == a : Array<U32>})
  -> OfGo(0n, True{}, i, off, n, g, ds, s, src):
  (a1, a2, +e1, +e2) = w
  of_rest_b(i, off, n, g, ds, s, src, a2, Equal.trans(Array<U32>, a2, a, src, e2, ea), hoff, fits, lay, lt, mk_leaf(U32.shln(1, g), g, off, src, a1, Equal.trans(Array<U32>, a1, a, src, e1, ea), le_refl_u(U32.shln(1, g))))

# a full leaf and the loop goes on (the induction hypothesis takes the stack and a live source copy)
def of_step_c(p: Nat, +i: U32, +off: U32, +n: U32, +g: Nat, +ds: Nat, -s: CH.CWS, -b: Array<U32>, -src: Array<U32>, a2: Array<U32>, +ea2: {a2 == src : Array<U32>},
  mw: MergeW(CH.Ch.tz(U32.inc(i)), U32.shln(1, g), CH.WL{U32.shln(1, g), g, b}, s, U32.to_nat(U32.add(off, U32.shln(1, g))), src),
  ih: @a3: Array<U32> -> {a3 == src : Array<U32>} -> @s3: CH.CWS -> LayS(s3, U32.to_nat(U32.add(off, U32.shln(1, g))), src) -> OfGo(p, U32.is_lt(U32.shln(1, g), U32.sub(n, U32.add(off, U32.shln(1, g)))), U32.inc(i), U32.add(off, U32.shln(1, g)), n, g, ds, s3, src))
  -> OfGo(p, U32.is_lt(U32.shln(1, g), U32.sub(n, U32.add(off, U32.shln(1, g)))), U32.inc(i), U32.add(off, U32.shln(1, g)), n, g, ds, CH.CWS.push(i, U32.shln(1, g), CH.WL{U32.shln(1, g), g, b}, s), src):
  (s3, eqs, lay3) = mw
  %Equal.sym(CH.CWS, CH.CWS.push(i, U32.shln(1, g), CH.WL{U32.shln(1, g), g, b}, s), s3, eqs) : OfGo(p, U32.is_lt(U32.shln(1, g), U32.sub(n, U32.add(off, U32.shln(1, g)))), U32.inc(i), U32.add(off, U32.shln(1, g)), n, g, ds, _, src)
  ih(a2, ea2, s3, lay3)

def of_step_b(p: Nat, +i: U32, +off: U32, +n: U32, +g: Nat, +ds: Nat, s: CH.CWS, -src: Array<U32>, a2: Array<U32>, +ea2: {a2 == src : Array<U32>}, +hoff: {Nat.is_le(U32.to_nat(off), U32.to_nat(n)) == True{} : Bool}, lay: LayS(s, U32.to_nat(off), src), +lt: {U32.is_lt(U32.shln(1, g), U32.sub(n, off)) == True{} : Bool}, lw: LeafW(U32.shln(1, g), g, off, src),
  ih: @a3: Array<U32> -> {a3 == src : Array<U32>} -> @s3: CH.CWS -> LayS(s3, U32.to_nat(U32.add(off, U32.shln(1, g))), src) -> OfGo(p, U32.is_lt(U32.shln(1, g), U32.sub(n, U32.add(off, U32.shln(1, g)))), U32.inc(i), U32.add(off, U32.shln(1, g)), n, g, ds, s3, src))
  -> OfGo(1n+p, True{}, i, off, n, g, ds, s, src):
  (b, eqr, wl, al) = lw
  %Equal.sym(Array<U32> & Array<U32>, CH.Ch.rng(~U32, U32.shln(1, g), g, off, src, 0), (b, src), eqr) : &s2: CH.CWS -> {CH.CW.of.go(1n+p, True{}, i, off, n, g, ds, s, _) == s2 : CH.CWS} & LayS(s2, U32.to_nat(n), src)
  of_step_c(p, i, off, n, g, ds, s, b, src, a2, ea2, merge_w(CH.Ch.tz(U32.inc(i)), U32.shln(1, g), CH.WL{U32.shln(1, g), g, b}, s, U32.to_nat(off), U32.to_nat(U32.add(off, U32.shln(1, g))), src, n, adv_est(off, n, g, hoff, lt), {==}, wl, al, lay, adv_le(off, n, g, hoff, lt)), ih)

def of_step_a(p: Nat, +i: U32, +off: U32, +n: U32, +g: Nat, +ds: Nat, s: CH.CWS, -src: Array<U32>, -a: Array<U32>, +ea: {a == src : Array<U32>}, +hoff: {Nat.is_le(U32.to_nat(off), U32.to_nat(n)) == True{} : Bool}, lay: LayS(s, U32.to_nat(off), src), +lt: {U32.is_lt(U32.shln(1, g), U32.sub(n, off)) == True{} : Bool},
  ih: @a3: Array<U32> -> {a3 == src : Array<U32>} -> @s3: CH.CWS -> LayS(s3, U32.to_nat(U32.add(off, U32.shln(1, g))), src) -> OfGo(p, U32.is_lt(U32.shln(1, g), U32.sub(n, U32.add(off, U32.shln(1, g)))), U32.inc(i), U32.add(off, U32.shln(1, g)), n, g, ds, s3, src),
  w: &a1: Array<U32> -> &a2: Array<U32> -> {a1 == a : Array<U32>} & {a2 == a : Array<U32>})
  -> OfGo(1n+p, True{}, i, off, n, g, ds, s, src):
  (a1, a2, +e1, +e2) = w
  of_step_b(p, i, off, n, g, ds, s, src, a2, Equal.trans(Array<U32>, a2, a, src, e2, ea), hoff, lay, lt, mk_leaf(U32.shln(1, g), g, off, src, a1, Equal.trans(Array<U32>, a1, a, src, e1, ea), le_refl_u(U32.shln(1, g))), ih)

# CW.of.go keeps the stack laid over the source up to n rows
def of_go_w(f: Nat, more: Bool, +i: U32, +off: U32, +n: U32, +g: Nat, +ds: Nat, s: CH.CWS, -src: Array<U32>, a: Array<U32>, +ea: {a == src : Array<U32>},
  +emore: {more == U32.is_lt(U32.shln(1, g), U32.sub(n, off)) : Bool}, +hoff: {Nat.is_le(U32.to_nat(off), U32.to_nat(n)) == True{} : Bool}, +fits: {U32.is_le(n, U32.shln(1, ds)) == True{} : Bool}, lay: LayS(s, U32.to_nat(off), src))
  -> OfGo(f, more, i, off, n, g, ds, s, src):
  match f more:
    case 0n False{}:
      of_last(0n, i, off, n, g, ds, s, src, a, ea, hoff, lay, Equal.sym(Bool, False{}, U32.is_lt(U32.shln(1, g), U32.sub(n, off)), emore))
    case 1n+p False{}:
      of_last(1n+p, i, off, n, g, ds, s, src, a, ea, hoff, lay, Equal.sym(Bool, False{}, U32.is_lt(U32.shln(1, g), U32.sub(n, off)), emore))
    case 0n True{}:
      of_rest_a(i, off, n, g, ds, s, src, a, ea, hoff, fits, lay, Equal.sym(Bool, True{}, U32.is_lt(U32.shln(1, g), U32.sub(n, off)), emore), PC.clone_eq(U32, a))
    case 1n++p True{}:
      of_step_a(p, i, off, n, g, ds, s, src, a, ea, hoff, lay, Equal.sym(Bool, True{}, U32.is_lt(U32.shln(1, g), U32.sub(n, off)), emore), a3 => ea3 => s3 => lay3 => of_go_w(p, U32.is_lt(U32.shln(1, g), U32.sub(n, U32.add(off, U32.shln(1, g)))), U32.inc(i), U32.add(off, U32.shln(1, g)), n, g, ds, s3, src, a3, ea3, {==}, adv_le(off, n, g, hoff, Equal.sym(Bool, True{}, U32.is_lt(U32.shln(1, g), U32.sub(n, off)), emore)), fits, lay3), PC.clone_eq(U32, a))

# ---- CW.of ----------------------------------------------------------------------------------------------

def of_k_fin2(+n: U32, -t0: CH.CW, -src: Array<U32>, t: CH.CW, et: {t0 == t : CH.CW}, wt: Laws.WFChunks(t), en: {Laws.nrows(t) == U32.to_nat(n) : Nat}, at: Laws.TreeAt(t, 0n, src))
  -> &t: CH.CW -> {t0 == t : CH.CW} & Laws.WFChunks(t) & {Laws.crows(t) == n : U32} & Laws.TreeAt(t, 0n, src):
  match t:
    case CH.WL{+m, d, a}:
      (CH.WL{m, d, a}, et, wt, u32_eq_of_nat(m, n, en), at)
    case CH.WN{+rows, lrows, l, r}:
      (CH.WN{rows, lrows, l, r}, et, wt, u32_eq_of_nat(rows, n, en), at)

def of_k_fin(+n: U32, -t0: CH.CW, -src: Array<U32>, w: CollW(t0, U32.to_nat(n), src))
  -> &t: CH.CW -> {t0 == t : CH.CW} & Laws.WFChunks(t) & {Laws.crows(t) == n : U32} & Laws.TreeAt(t, 0n, src):
  (t, et, wt, en, at) = w
  of_k_fin2(n, t0, src, t, et, wt, en, at)

def of_k_go(+n: U32, +ds: Nat, +g: Nat, -src: Array<U32>, -s0: CH.CWS, w: &s2: CH.CWS -> {s0 == s2 : CH.CWS} & LayS(s2, U32.to_nat(n), src))
  -> &t: CH.CW -> {CH.CWS.collapse(s0) == t : CH.CW} & Laws.WFChunks(t) & {Laws.crows(t) == n : U32} & Laws.TreeAt(t, 0n, src):
  (s2, es, lay) = w
  %Equal.sym(CH.CWS, s0, s2, es) : &t: CH.CW -> {CH.CWS.collapse(_) == t : CH.CW} & Laws.WFChunks(t) & {Laws.crows(t) == n : U32} & Laws.TreeAt(t, 0n, src)
  of_k_fin(n, CH.CWS.collapse(s2), src, collapse_w(s2, U32.to_nat(n), src, n, lay, nat_le_refl(U32.to_nat(n))))

def of_k_w(sm: Bool, +n: U32, +ds: Nat, +g: Nat, src: Array<U32>, +fits: {U32.is_le(n, U32.shln(1, ds)) == True{} : Bool}, wf: Laws.WFArray(U32, ds, src))
  -> &t: CH.CW -> {CH.CW.of.k(sm, n, ds, g, src) == t : CH.CW} & Laws.WFChunks(t) & {Laws.crows(t) == n : U32} & Laws.TreeAt(t, 0n, src):
  match sm:
    case True{}:
      (CH.WL{n, ds, src}, {==}, (fits, wf), {==}, m => hm => {==})
    case False{}:
      of_k_go(n, ds, g, src, CH.CW.of.go(U32.to_nat(U32.shrn(n, g)), U32.is_lt(U32.shln(1, g), U32.sub(n, 0)), 0, 0, n, g, ds, CH.CWNil{}, CH.Ch.rng(~U32, Bool.pick(U32, U32.is_lt(U32.shln(1, g), U32.sub(n, 0)), U32.shln(1, g), U32.sub(n, 0)), g, 0, src, 0)), of_go_w(U32.to_nat(U32.shrn(n, g)), U32.is_lt(U32.shln(1, g), U32.sub(n, 0)), 0, 0, n, g, ds, CH.CWNil{}, src, src, {==}, {==}, nat_le_zero(U32.to_nat(n)), fits, {==}))

def Laws.cw_of(n, ds, g, src, fits, wf):
  of_k_w(U32.is_le(n, U32.shln(1, g)), n, ds, g, src, fits, wf)


# ==== flatten ==========================================================================================
#
# One forall per subtree (a forall is affine: the node needs each child's fact once per slot): every
# slot j below st + rows(t) of the output holds out's slot below st and row j - st of t from st on.

def FlatUp(-t: CH.CW, +st: Nat, +dd: Nat, -out: Array<U32>, -o: Array<U32>) -> Type:
  @j: U32 -> {Nat.is_lt(U32.to_nat(j), Nat.add(st, Laws.nrows(t))) == True{} : Bool} -> {Laws.rdN(U32, dd, o, j) == Bool.pick(U32, Nat.is_lt(U32.to_nat(j), st), Laws.rdN(U32, dd, out, j), Laws.ncell(t, Nat.sub(U32.to_nat(j), st))) : U32}

def FlatGo(-t: CH.CW, +off: U32, +st: Nat, +dd: Nat, -out: Array<U32>) -> Type:
  &o: Array<U32> -> {CH.CW.flat(t, off, out) == o : Array<U32>} & Laws.WFArray(U32, dd, o) & FlatUp(t, st, dd, out, o)

def nat_sub_zero(m: Nat) -> {Nat.sub(m, 0n) == m : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      {==}

def nat_lt_zero_f(m: Nat) -> {Nat.is_lt(m, 0n) == False{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      {==}

# not m < a + b: not m < a
def nat_not_lt_add(m: Nat, a: Nat, -b: Nat, h: {Nat.is_lt(m, Nat.add(a, b)) == False{} : Bool}) -> {Nat.is_lt(m, a) == False{} : Bool}:
  match m a:
    case 0n 0n:
      {==}
    case 1n+q 0n:
      {==}
    case 0n 1n+p:
      Empty.absurd({Nat.is_lt(0n, 1n+p) == False{} : Bool}, L.true_false(h))
    case 1n+q 1n+p:
      nat_not_lt_add(q, p, b, h)

# not m < a + b and not m < a: not m - a < b
def nat_not_lt_sub(m: Nat, a: Nat, -b: Nat, h: {Nat.is_lt(m, Nat.add(a, b)) == False{} : Bool}, h2: {Nat.is_lt(m, a) == False{} : Bool}) -> {Nat.is_lt(Nat.sub(m, a), b) == False{} : Bool}:
  match m a:
    case 0n 0n:
      h
    case 1n+q 0n:
      h
    case 0n 1n+p:
      Empty.absurd({Nat.is_lt(Nat.sub(0n, 1n+p), b) == False{} : Bool}, L.true_false(h2))
    case 1n+q 1n+p:
      nat_not_lt_sub(q, p, b, h, h2)

# k < to_nat(m): addn(0, k) < m as words
def hk_ltw(+m: U32, +k: Nat, +hk: {Nat.is_lt(k, U32.to_nat(m)) == True{} : Bool}) -> {U32.is_lt(Laws.addn(0, k), m) == True{} : Bool}:
  ult_of_n(Laws.addn(0, k), m, (%Equal.sym(Nat, U32.to_nat(Laws.addn(0, k)), k, to_nat_addn0(k, m, nat_le_of_lt(k, U32.to_nat(m), hk))) : {Nat.is_lt(_, U32.to_nat(m)) == True{} : Bool}; hk))

# addn(0, st) has the value st below a bound
def eoff_n(+off: U32, +st: Nat, +bound: U32, +eoff: {off == Laws.addn(0, st) : U32}, +h: {Nat.is_le(st, U32.to_nat(bound)) == True{} : Bool}) -> {U32.to_nat(off) == st : Nat}:
  %Equal.sym(U32, off, Laws.addn(0, st), eoff) : {U32.to_nat(_) == st : Nat}
  to_nat_addn0(st, bound, h)

# off + (j - st) is j when st <= j and off is st
def ejk(+off: U32, +st: Nat, +j: U32, +eoffn: {U32.to_nat(off) == st : Nat}, +le: {Nat.is_le(st, U32.to_nat(j)) == True{} : Bool})
  -> {U32.add(off, Laws.addn(0, Nat.sub(U32.to_nat(j), st))) == j : U32}:
  Equal.trans(U32, U32.add(off, Laws.addn(0, Nat.sub(U32.to_nat(j), st))), Laws.addn(0, Nat.add(U32.to_nat(off), Nat.sub(U32.to_nat(j), st))), j, idx_eq(off, Nat.sub(U32.to_nat(j), st)), (%Equal.sym(Nat, U32.to_nat(off), st, eoffn) : {Laws.addn(0, Nat.add(_, Nat.sub(U32.to_nat(j), st))) == j : U32}; %Equal.sym(Nat, Nat.add(st, Nat.sub(U32.to_nat(j), st)), U32.to_nat(j), nat_sub_add(st, U32.to_nat(j), le)) : {Laws.addn(0, _) == j : U32}; B.addn_to_nat(j)))

def flat_leaf_b(bb: Bool, +n: U32, +off: U32, +st: Nat, +dd: Nat, -a: Array<U32>, -out: Array<U32>, -o: Array<U32>, +j: U32,
  +ebb: {Nat.is_lt(U32.to_nat(j), st) == bb : Bool}, +hj: {Nat.is_lt(U32.to_nat(j), Nat.add(st, U32.to_nat(n))) == True{} : Bool}, +eoffn: {U32.to_nat(off) == st : Nat},
  rows: @k: U32 -> {U32.is_lt(k, n) == True{} : Bool} -> {Laws.rdN(U32, dd, o, U32.add(off, k)) == Laws.rd_at(U32, a, k) : U32},
  low: PA.CPLow(~U32, off, dd, out, o))
  -> {Laws.rdN(U32, dd, o, j) == Bool.pick(U32, Nat.is_lt(U32.to_nat(j), st), Laws.rdN(U32, dd, out, j), Laws.rd_at(U32, a, Laws.addn(0, Nat.sub(U32.to_nat(j), st)))) : U32}:
  match bb:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(U32.to_nat(j), st), True{}, ebb) : {Laws.rdN(U32, dd, o, j) == Bool.pick(U32, _, Laws.rdN(U32, dd, out, j), Laws.rd_at(U32, a, Laws.addn(0, Nat.sub(U32.to_nat(j), st)))) : U32}
      low(j, ult_of_n(j, off, (%Equal.sym(Nat, U32.to_nat(off), st, eoffn) : {Nat.is_lt(U32.to_nat(j), _) == True{} : Bool}; ebb)))
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(U32.to_nat(j), st), False{}, ebb) : {Laws.rdN(U32, dd, o, j) == Bool.pick(U32, _, Laws.rdN(U32, dd, out, j), Laws.rd_at(U32, a, Laws.addn(0, Nat.sub(U32.to_nat(j), st)))) : U32}
      %ejk(off, st, j, eoffn, nat_le_of_not_lt(U32.to_nat(j), st, ebb)) : {Laws.rdN(U32, dd, o, _) == Laws.rd_at(U32, a, Laws.addn(0, Nat.sub(U32.to_nat(j), st))) : U32}
      rows(Laws.addn(0, Nat.sub(U32.to_nat(j), st)), hk_ltw(n, Nat.sub(U32.to_nat(j), st), nat_lt_sub(U32.to_nat(j), st, U32.to_nat(n), hj, ebb)))

def flat_leaf_k(+n: U32, +d: Nat, +off: U32, +st: Nat, +dd: Nat, -a: Array<U32>, -out: Array<U32>, +eoffn: {U32.to_nat(off) == st : Nat}, w: PA.CPW(~U32, n, off, dd, a, out))
  -> FlatGo(CH.WL{n, d, a}, off, st, dd, out):
  (o, eo, wo, rows, low) = w
  (o, eo, wo, +j => +hj => flat_leaf_b(Nat.is_lt(U32.to_nat(j), st), n, off, st, dd, a, out, o, j, {==}, hj, eoffn, rows, low))

def flat_node_b2(bb: Bool, +st: Nat, +dd: Nat, +rows: U32, +lrows: U32, -l: CH.CW, -r: CH.CW, -out: Array<U32>, -o1: Array<U32>, +j: U32,
  +ebb: {Nat.is_lt(U32.to_nat(j), st) == bb : Bool}, +hjl: {Nat.is_lt(U32.to_nat(j), Nat.add(st, U32.to_nat(lrows))) == True{} : Bool})
  -> {Bool.pick(U32, Nat.is_lt(U32.to_nat(j), st), Laws.rdN(U32, dd, out, j), Laws.ncell(l, Nat.sub(U32.to_nat(j), st))) == Bool.pick(U32, Nat.is_lt(U32.to_nat(j), st), Laws.rdN(U32, dd, out, j), Laws.ncell(CH.WN{rows, lrows, l, r}, Nat.sub(U32.to_nat(j), st))) : U32}:
  match bb:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(U32.to_nat(j), st), True{}, ebb) : {Bool.pick(U32, _, Laws.rdN(U32, dd, out, j), Laws.ncell(l, Nat.sub(U32.to_nat(j), st))) == Bool.pick(U32, _, Laws.rdN(U32, dd, out, j), Laws.ncell(CH.WN{rows, lrows, l, r}, Nat.sub(U32.to_nat(j), st))) : U32}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(U32.to_nat(j), st), False{}, ebb) : {Bool.pick(U32, _, Laws.rdN(U32, dd, out, j), Laws.ncell(l, Nat.sub(U32.to_nat(j), st))) == Bool.pick(U32, _, Laws.rdN(U32, dd, out, j), Laws.ncell(CH.WN{rows, lrows, l, r}, Nat.sub(U32.to_nat(j), st))) : U32}
      %Equal.sym(Bool, Nat.is_lt(Nat.sub(U32.to_nat(j), st), U32.to_nat(lrows)), True{}, nat_lt_sub(U32.to_nat(j), st, U32.to_nat(lrows), hjl, ebb)) : {Laws.ncell(l, Nat.sub(U32.to_nat(j), st)) == Bool.pick(U32, _, Laws.ncell(l, Nat.sub(U32.to_nat(j), st)), Laws.ncell(r, Nat.sub(Nat.sub(U32.to_nat(j), st), U32.to_nat(lrows)))) : U32}
      {==}

def hj_r(+st: Nat, +lrows: U32, -r: CH.CW, +rows: U32, +j: U32, +esum: {Nat.add(U32.to_nat(lrows), Laws.nrows(r)) == U32.to_nat(rows) : Nat}, +hj: {Nat.is_lt(U32.to_nat(j), Nat.add(st, U32.to_nat(rows))) == True{} : Bool})
  -> {Nat.is_lt(U32.to_nat(j), Nat.add(Nat.add(st, U32.to_nat(lrows)), Laws.nrows(r))) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.add(st, U32.to_nat(lrows)), Laws.nrows(r)), Nat.add(st, Nat.add(U32.to_nat(lrows), Laws.nrows(r))), nat_add_assoc(st, U32.to_nat(lrows), Laws.nrows(r))) : {Nat.is_lt(U32.to_nat(j), _) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(U32.to_nat(lrows), Laws.nrows(r)), U32.to_nat(rows), esum) : {Nat.is_lt(U32.to_nat(j), Nat.add(st, _)) == True{} : Bool}
  hj

def flat_node_b(bb: Bool, +st: Nat, +dd: Nat, +rows: U32, +lrows: U32, -l: CH.CW, -r: CH.CW, -out: Array<U32>, -o1: Array<U32>, -o2: Array<U32>, +j: U32,
  +ebb: {Nat.is_lt(U32.to_nat(j), Nat.add(st, U32.to_nat(lrows))) == bb : Bool}, +hj: {Nat.is_lt(U32.to_nat(j), Nat.add(st, U32.to_nat(rows))) == True{} : Bool},
  +el: {lrows == Laws.crows(l) : U32}, +esum: {Nat.add(U32.to_nat(lrows), Laws.nrows(r)) == U32.to_nat(rows) : Nat},
  fl: FlatUp(l, st, dd, out, o1), fr: FlatUp(r, Nat.add(st, U32.to_nat(lrows)), dd, o1, o2))
  -> {Laws.rdN(U32, dd, o2, j) == Bool.pick(U32, Nat.is_lt(U32.to_nat(j), st), Laws.rdN(U32, dd, out, j), Laws.ncell(CH.WN{rows, lrows, l, r}, Nat.sub(U32.to_nat(j), st))) : U32}:
  match bb:
    case True{}:
      Equal.trans(U32, Laws.rdN(U32, dd, o2, j), Laws.rdN(U32, dd, o1, j), Bool.pick(U32, Nat.is_lt(U32.to_nat(j), st), Laws.rdN(U32, dd, out, j), Laws.ncell(CH.WN{rows, lrows, l, r}, Nat.sub(U32.to_nat(j), st))),
        (%ebb : {Laws.rdN(U32, dd, o2, j) == Bool.pick(U32, _, Laws.rdN(U32, dd, o1, j), Laws.ncell(r, Nat.sub(U32.to_nat(j), Nat.add(st, U32.to_nat(lrows))))) : U32}; fr(j, hj_r(st, lrows, r, rows, j, esum, hj))),
        Equal.trans(U32, Laws.rdN(U32, dd, o1, j), Bool.pick(U32, Nat.is_lt(U32.to_nat(j), st), Laws.rdN(U32, dd, out, j), Laws.ncell(l, Nat.sub(U32.to_nat(j), st))), Bool.pick(U32, Nat.is_lt(U32.to_nat(j), st), Laws.rdN(U32, dd, out, j), Laws.ncell(CH.WN{rows, lrows, l, r}, Nat.sub(U32.to_nat(j), st))),
          fl(j, (%el : {Nat.is_lt(U32.to_nat(j), Nat.add(st, U32.to_nat(_))) == True{} : Bool}; ebb)), flat_node_b2(Nat.is_lt(U32.to_nat(j), st), st, dd, rows, lrows, l, r, out, o1, j, {==}, ebb)))
    case False{}:
      +nst = nat_not_lt_add(U32.to_nat(j), st, U32.to_nat(lrows), ebb)
      %Equal.sym(Bool, Nat.is_lt(U32.to_nat(j), st), False{}, nst) : {Laws.rdN(U32, dd, o2, j) == Bool.pick(U32, _, Laws.rdN(U32, dd, out, j), Laws.ncell(CH.WN{rows, lrows, l, r}, Nat.sub(U32.to_nat(j), st))) : U32}
      %Equal.sym(Bool, Nat.is_lt(Nat.sub(U32.to_nat(j), st), U32.to_nat(lrows)), False{}, nat_not_lt_sub(U32.to_nat(j), st, U32.to_nat(lrows), ebb, nst)) : {Laws.rdN(U32, dd, o2, j) == Bool.pick(U32, _, Laws.ncell(l, Nat.sub(U32.to_nat(j), st)), Laws.ncell(r, Nat.sub(Nat.sub(U32.to_nat(j), st), U32.to_nat(lrows)))) : U32}
      %Equal.sym(Nat, Nat.sub(Nat.sub(U32.to_nat(j), st), U32.to_nat(lrows)), Nat.sub(U32.to_nat(j), Nat.add(st, U32.to_nat(lrows))), nat_sub_sub(U32.to_nat(j), st, U32.to_nat(lrows))) : {Laws.rdN(U32, dd, o2, j) == Laws.ncell(r, _) : U32}
      %ebb : {Laws.rdN(U32, dd, o2, j) == Bool.pick(U32, _, Laws.rdN(U32, dd, o1, j), Laws.ncell(r, Nat.sub(U32.to_nat(j), Nat.add(st, U32.to_nat(lrows))))) : U32}
      fr(j, hj_r(st, lrows, r, rows, j, esum, hj))

def flat_node_c(+off: U32, +st: Nat, +dd: Nat, +rows: U32, +lrows: U32, -l: CH.CW, -r: CH.CW, -out: Array<U32>, -o1: Array<U32>,
  +el: {lrows == Laws.crows(l) : U32}, +esum: {Nat.add(U32.to_nat(lrows), Laws.nrows(r)) == U32.to_nat(rows) : Nat},
  +e1: {CH.CW.flat(l, off, out) == o1 : Array<U32>}, fl: FlatUp(l, st, dd, out, o1),
  w: FlatGo(r, U32.add(off, lrows), Nat.add(st, U32.to_nat(lrows)), dd, o1))
  -> FlatGo(CH.WN{rows, lrows, l, r}, off, st, dd, out):
  (o2, e2, wo2, fr) = w
  %Equal.sym(Array<U32>, CH.CW.flat(l, off, out), o1, e1) : &o: Array<U32> -> {CH.CW.flat(r, U32.add(off, lrows), _) == o : Array<U32>} & Laws.WFArray(U32, dd, o) & FlatUp(CH.WN{rows, lrows, l, r}, st, dd, out, o)
  (o2, e2, wo2, +j => +hj => flat_node_b(Nat.is_lt(U32.to_nat(j), Nat.add(st, U32.to_nat(lrows))), st, dd, rows, lrows, l, r, out, o1, o2, j, {==}, hj, el, esum, fl, fr))

def flat_node_a(+off: U32, +st: Nat, +dd: Nat, +rows: U32, +lrows: U32, -l: CH.CW, -r: CH.CW, -out: Array<U32>,
  +el: {lrows == Laws.crows(l) : U32}, +esum: {Nat.add(U32.to_nat(lrows), Laws.nrows(r)) == U32.to_nat(rows) : Nat},
  w: FlatGo(l, off, st, dd, out),
  ih: @o1: Array<U32> -> Laws.WFArray(U32, dd, o1) -> FlatGo(r, U32.add(off, lrows), Nat.add(st, U32.to_nat(lrows)), dd, o1))
  -> FlatGo(CH.WN{rows, lrows, l, r}, off, st, dd, out):
  (o1, +e1, wo1, fl) = w
  flat_node_c(off, st, dd, rows, lrows, l, r, out, o1, el, esum, e1, fl, ih(o1, wo1))

# st + lrows + rows(r) == st + rows
def fit_r(+st: Nat, +lrows: U32, -r: CH.CW, +rows: U32, +dd: Nat, +esum: {Nat.add(U32.to_nat(lrows), Laws.nrows(r)) == U32.to_nat(rows) : Nat}, +hb: {Nat.is_le(Nat.add(st, U32.to_nat(rows)), U32.to_nat(U32.shln(1, dd))) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.add(st, U32.to_nat(lrows)), Laws.nrows(r)), U32.to_nat(U32.shln(1, dd))) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.add(st, U32.to_nat(lrows)), Laws.nrows(r)), Nat.add(st, Nat.add(U32.to_nat(lrows), Laws.nrows(r))), nat_add_assoc(st, U32.to_nat(lrows), Laws.nrows(r))) : {Nat.is_le(_, U32.to_nat(U32.shln(1, dd))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(U32.to_nat(lrows), Laws.nrows(r)), U32.to_nat(rows), esum) : {Nat.is_le(Nat.add(st, _), U32.to_nat(U32.shln(1, dd))) == True{} : Bool}
  hb

def nz(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def succ_ne_zero(-x: Nat, e: {1n+x == 0n : Nat}) -> Empty:
  %e : nz(_)
  Unit{}

def npred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# a + b == c: a <= c (b only in the types)
def nat_le_of_sum(a: Nat, -b: Nat, c: Nat, e: {Nat.add(a, b) == c : Nat}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a c:
    case 0n _:
      nat_le_zero(c)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, succ_ne_zero(Nat.add(p, b), e))
    case 1n+p 1n+q:
      nat_le_of_sum(p, b, q, Equal.cong(Nat, Nat, x => npred(x), 1n+Nat.add(p, b), 1n+q, e))

def fit_l(+st: Nat, +lrows: U32, -l: CH.CW, -r: CH.CW, +rows: U32, +dd: Nat, +el: {lrows == Laws.crows(l) : U32}, +esum: {Nat.add(U32.to_nat(lrows), Laws.nrows(r)) == U32.to_nat(rows) : Nat}, +hb: {Nat.is_le(Nat.add(st, U32.to_nat(rows)), U32.to_nat(U32.shln(1, dd))) == True{} : Bool})
  -> {Nat.is_le(Nat.add(st, Laws.nrows(l)), U32.to_nat(U32.shln(1, dd))) == True{} : Bool}:
  %el : {Nat.is_le(Nat.add(st, U32.to_nat(_)), U32.to_nat(U32.shln(1, dd))) == True{} : Bool}
  nat_le_trans(Nat.add(st, U32.to_nat(lrows)), Nat.add(st, U32.to_nat(rows)), U32.to_nat(U32.shln(1, dd)), nat_add_le_mono(st, U32.to_nat(lrows), U32.to_nat(rows), nat_le_of_sum(U32.to_nat(lrows), Laws.nrows(r), U32.to_nat(rows), esum)), hb)

# the right child's offset: off + lrows == addn(0, st + lrows)
def eoff_r(+off: U32, +st: Nat, +lrows: U32, +eoff: {off == Laws.addn(0, st) : U32}) -> {U32.add(off, lrows) == Laws.addn(0, Nat.add(st, U32.to_nat(lrows))) : U32}:
  Equal.trans(U32, U32.add(off, lrows), Laws.addn(off, U32.to_nat(lrows)), Laws.addn(0, Nat.add(st, U32.to_nat(lrows))), add_eq_addn(off, lrows), Equal.trans(U32, Laws.addn(off, U32.to_nat(lrows)), Laws.addn(Laws.addn(0, st), U32.to_nat(lrows)), Laws.addn(0, Nat.add(st, U32.to_nat(lrows))), Equal.cong(U32, U32, q => Laws.addn(q, U32.to_nat(lrows)), off, Laws.addn(0, st), eoff), addn_addn(0, st, U32.to_nat(lrows))))

def flat_w(t: CH.CW, +off: U32, +st: Nat, +dd: Nat, out: Array<U32>, wfo: Laws.WFArray(U32, dd, out), wft: Laws.WFChunks(t), +eoff: {off == Laws.addn(0, st) : U32}, +hb: {Nat.is_le(Nat.add(st, Laws.nrows(t)), U32.to_nat(U32.shln(1, dd))) == True{} : Bool})
  -> FlatGo(t, off, st, dd, out):
  match t:
    case CH.WL{+n, +d, a}:
      (fits, wa) = wft
      +eoffn = eoff_n(off, st, U32.shln(1, dd), eoff, nat_le_trans(st, Nat.add(st, U32.to_nat(n)), U32.to_nat(U32.shln(1, dd)), nat_le_add(st, U32.to_nat(n)), hb))
      flat_leaf_k(n, d, off, st, dd, a, out, eoffn, PA.copy_into_w(~U32, n, off, dd, a, out, wfo, (%Equal.sym(Nat, U32.to_nat(off), st, eoffn) : {Nat.is_le(Nat.add(_, U32.to_nat(n)), U32.to_nat(U32.shln(1, dd))) == True{} : Bool}; hb)))
    case CH.WN{+rows, +lrows, l, r}:
      (+el, +esum, wl, wr) = wft
      flat_node_a(off, st, dd, rows, lrows, l, r, out, el, esum, flat_w(l, off, st, dd, out, wfo, wl, eoff, fit_l(st, lrows, l, r, rows, dd, el, esum, hb)), o1 => wo1 => flat_w(r, U32.add(off, lrows), Nat.add(st, U32.to_nat(lrows)), dd, o1, wo1, wr, eoff_r(off, st, lrows, eoff), fit_r(st, lrows, r, rows, dd, esum, hb)))

# at st = 0: row m of t at slot m
def flat_cell(-t: CH.CW, +dd: Nat, -o: Array<U32>, +m: Nat, +hm: {Nat.is_lt(m, Laws.nrows(t)) == True{} : Bool}, +hmd: {Nat.is_le(m, U32.to_nat(U32.shln(1, dd))) == True{} : Bool}, fu: FlatUp(t, 0n, dd, Array.new(U32, dd, 0), o))
  -> {Laws.rdN(U32, dd, o, Laws.addn(0, m)) == Laws.ncell(t, m) : U32}:
  +em = to_nat_addn0(m, U32.shln(1, dd), hmd)
  +ev = fu(Laws.addn(0, m), (%Equal.sym(Nat, U32.to_nat(Laws.addn(0, m)), m, em) : {Nat.is_lt(_, Laws.nrows(t)) == True{} : Bool}; hm))
  %nat_sub_zero(m) : {Laws.rdN(U32, dd, o, Laws.addn(0, m)) == Laws.ncell(t, _) : U32}
  %nat_lt_zero_f(m) : {Laws.rdN(U32, dd, o, Laws.addn(0, m)) == Bool.pick(U32, _, Laws.rdN(U32, dd, Array.new(U32, dd, 0), Laws.addn(0, m)), Laws.ncell(t, Nat.sub(m, 0n))) : U32}
  %em : {Laws.rdN(U32, dd, o, Laws.addn(0, m)) == Bool.pick(U32, Nat.is_lt(_, 0n), Laws.rdN(U32, dd, Array.new(U32, dd, 0), Laws.addn(0, m)), Laws.ncell(t, Nat.sub(_, 0n))) : U32}
  ev

def flat_fin(+dd: Nat, -t: CH.CW, mle: @m: Nat -> {Nat.is_lt(m, Laws.nrows(t)) == True{} : Bool} -> {Nat.is_le(m, U32.to_nat(U32.shln(1, dd))) == True{} : Bool}, w: FlatGo(t, 0, 0n, dd, Array.new(U32, dd, 0))) -> Laws.FlatW(dd, t):
  (o, eo, wo, fu) = w
  (o, eo, wo, +m => +hm => flat_cell(t, dd, o, m, hm, mle(m, hm), fu))

def RowsFit(-t: CH.CW, +dd: Nat) -> Type:
  &t2: CH.CW -> {t2 == t : CH.CW} & {Nat.is_le(Laws.nrows(t2), U32.to_nat(U32.shln(1, dd))) == True{} : Bool} & (@m: Nat -> {Nat.is_lt(m, Laws.nrows(t2)) == True{} : Bool} -> {Nat.is_le(m, U32.to_nat(U32.shln(1, dd))) == True{} : Bool})

def rows_fit(t: CH.CW, +dd: Nat, +fits: {U32.is_le(Laws.crows(t), U32.shln(1, dd)) == True{} : Bool}) -> RowsFit(t, dd):
  match t:
    case CH.WL{+n, d, a}:
      (CH.WL{n, d, a}, {==}, nle_of_u(n, U32.shln(1, dd), fits), +m => +hm => nat_le_trans(m, U32.to_nat(n), U32.to_nat(U32.shln(1, dd)), nat_le_of_lt(m, U32.to_nat(n), hm), nle_of_u(n, U32.shln(1, dd), fits)))
    case CH.WN{+rows, lrows, l, r}:
      (CH.WN{rows, lrows, l, r}, {==}, nle_of_u(rows, U32.shln(1, dd), fits), +m => +hm => nat_le_trans(m, U32.to_nat(rows), U32.to_nat(U32.shln(1, dd)), nat_le_of_lt(m, U32.to_nat(rows), hm), nle_of_u(rows, U32.shln(1, dd), fits)))

def cw_flatten_k(+dd: Nat, -t: CH.CW, wf: Laws.WFChunks(t), w: RowsFit(t, dd)) -> Laws.FlatW(dd, t):
  (t2, +et, +hb, mle) = w
  %et : Laws.FlatW(dd, _)
  flat_fin(dd, t2, mle, flat_w(t2, 0, 0n, dd, Array.new(U32, dd, 0), Laws.wf_new(U32, dd, 0), (%Equal.sym(CH.CW, t2, t, et) : Laws.WFChunks(_); wf), {==}, hb))

def Laws.cw_flatten(dd, t, wf, fits):
  cw_flatten_k(dd, t, wf, rows_fit(t, dd, fits))

# ==== the round trip ===================================================================================

def rt_hm(+n: U32, -t: CH.CW, +j: U32, +hj: {U32.is_lt(j, n) == True{} : Bool}, +ect: {Laws.crows(t) == n : U32}) -> {Nat.is_lt(U32.to_nat(j), Laws.nrows(t)) == True{} : Bool}:
  %Equal.sym(U32, Laws.crows(t), n, ect) : {Nat.is_lt(U32.to_nat(j), U32.to_nat(_)) == True{} : Bool}
  nlt_of_u(j, n, hj)

def rt_fin(+n: U32, +dd: Nat, -src: Array<U32>, -t: CH.CW, -o: Array<U32>, +j: U32, +hj: {U32.is_lt(j, n) == True{} : Bool}, +ect: {Laws.crows(t) == n : U32}, at: Laws.TreeAt(t, 0n, src),
  fa: @m: Nat -> {Nat.is_lt(m, Laws.nrows(t)) == True{} : Bool} -> {Laws.rdN(U32, dd, o, Laws.addn(0, m)) == Laws.ncell(t, m) : U32})
  -> {Laws.rdN(U32, dd, o, j) == Laws.rd_at(U32, src, j) : U32}:
  %B.addn_to_nat(j) : {Laws.rdN(U32, dd, o, _) == Laws.rd_at(U32, src, _) : U32}
  Equal.trans(U32, Laws.rdN(U32, dd, o, Laws.addn(0, U32.to_nat(j))), Laws.ncell(t, U32.to_nat(j)), Laws.rd_at(U32, src, Laws.addn(0, U32.to_nat(j))), fa(U32.to_nat(j), rt_hm(n, t, j, hj, ect)), at(U32.to_nat(j), rt_hm(n, t, j, hj, ect)))

def rt_c(+n: U32, +dd: Nat, -src: Array<U32>, -t: CH.CW, +j: U32, +hj: {U32.is_lt(j, n) == True{} : Bool}, +ect: {Laws.crows(t) == n : U32}, at: Laws.TreeAt(t, 0n, src), w: Laws.FlatW(dd, t))
  -> {Laws.rdN(U32, dd, CH.CW.flatten(dd, t), j) == Laws.rd_at(U32, src, j) : U32}:
  (o, eo, wo, fa) = w
  %Equal.sym(Array<U32>, CH.CW.flatten(dd, t), o, eo) : {Laws.rdN(U32, dd, _, j) == Laws.rd_at(U32, src, j) : U32}
  rt_fin(n, dd, src, t, o, j, hj, ect, at, fa)

def rt_b(+n: U32, +ds: Nat, +g: Nat, +dd: Nat, -src: Array<U32>, +j: U32, +hj: {U32.is_lt(j, n) == True{} : Bool}, +fitd: {U32.is_le(n, U32.shln(1, dd)) == True{} : Bool}, w: Laws.OfW(n, ds, g, src))
  -> {Laws.rdN(U32, dd, CH.CW.flatten(dd, CH.CW.of(n, ds, g, src)), j) == Laws.rd_at(U32, src, j) : U32}:
  (t, et, wt, +ect, at) = w
  %Equal.sym(CH.CW, CH.CW.of(n, ds, g, src), t, et) : {Laws.rdN(U32, dd, CH.CW.flatten(dd, _), j) == Laws.rd_at(U32, src, j) : U32}
  rt_c(n, dd, src, t, j, hj, ect, at, Laws.cw_flatten(dd, t, wt, (%Equal.sym(U32, Laws.crows(t), n, ect) : {U32.is_le(_, U32.shln(1, dd)) == True{} : Bool}; fitd)))

def Laws.cw_roundtrip(n, ds, g, dd, src, fits, wf, fitd, j, hj):
  rt_b(n, ds, g, dd, src, j, hj, fitd, Laws.cw_of(n, ds, g, src, fits, wf))

# ==== concat: the node smart constructor =================================================================

# a + b <= cap from the wrap-free check (a <= cap, b <= cap - a)
def fits2_bnd(+cap: U32, +ra: U32, +rb: U32, +eok: {CH.Ch.fits2(cap, ra, rb) == True{} : Bool}) -> {Nat.is_le(Nat.add(U32.to_nat(ra), U32.to_nat(rb)), U32.to_nat(cap)) == True{} : Bool}:
  +ha = nle_of_u(ra, cap, L.and_left(U32.is_le(ra, cap), U32.is_le(rb, U32.sub(cap, ra)), eok))
  +hb = nle_of_u(rb, U32.sub(cap, ra), L.and_right(U32.is_le(ra, cap), U32.is_le(rb, U32.sub(cap, ra)), eok))
  %nat_sub_add(U32.to_nat(ra), U32.to_nat(cap), ha) : {Nat.is_le(Nat.add(U32.to_nat(ra), U32.to_nat(rb)), _) == True{} : Bool}
  nat_add_le_mono(U32.to_nat(ra), U32.to_nat(rb), Nat.sub(U32.to_nat(cap), U32.to_nat(ra)), (%sub_nat(cap, ra, ule_of_n(ra, cap, ha)) : {Nat.is_le(U32.to_nat(rb), _) == True{} : Bool}; hb))

def cat_core(ok: Bool, +cap: U32, +ra: U32, +rb: U32, -a: CH.CW, -b: CH.CW, +eok: {CH.Ch.fits2(cap, ra, rb) == ok : Bool}, +ea: {Laws.crows(a) == ra : U32}, +eb: {Laws.crows(b) == rb : U32}, wa: Laws.WFChunks(a), wb: Laws.WFChunks(b))
  -> Laws.ConcatOK(cap, a, b, CH.CW.concat.k(ok, cap, ra, rb, a, b)):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      +bnd = fits2_bnd(cap, ra, rb, eok)
      +sum = to_nat_add(ra, rb, cap, bnd)
      ((%Equal.sym(U32, Laws.crows(a), ra, ea) : {CH.WN{U32.add(ra, rb), ra, a, b} == CH.WN{U32.add(_, Laws.crows(b)), _, a, b} : CH.CW}; %Equal.sym(U32, Laws.crows(b), rb, eb) : {CH.WN{U32.add(ra, rb), ra, a, b} == CH.WN{U32.add(ra, _), ra, a, b} : CH.CW}; {==}),
       (Equal.sym(U32, Laws.crows(a), ra, ea), (%Equal.sym(U32, Laws.crows(b), rb, eb) : {Nat.add(U32.to_nat(ra), U32.to_nat(_)) == U32.to_nat(U32.add(ra, rb)) : Nat}; Equal.sym(Nat, U32.to_nat(U32.add(ra, rb)), Nat.add(U32.to_nat(ra), U32.to_nat(rb)), sum)), wa, wb),
       ule_of_n(U32.add(ra, rb), cap, (%Equal.sym(Nat, U32.to_nat(U32.add(ra, rb)), Nat.add(U32.to_nat(ra), U32.to_nat(rb)), sum) : {Nat.is_le(_, U32.to_nat(cap)) == True{} : Bool}; bnd)))

def Laws.cw_concat(cap, a, b, wa, wb):
  match a b:
    case CH.WL{+n1, d1, x1} CH.WL{+n2, d2, x2}:
      cat_core(CH.Ch.fits2(cap, n1, n2), cap, n1, n2, CH.WL{n1, d1, x1}, CH.WL{n2, d2, x2}, {==}, {==}, {==}, wa, wb)
    case CH.WL{+n1, d1, x1} CH.WN{+r2, l2, y2, z2}:
      cat_core(CH.Ch.fits2(cap, n1, r2), cap, n1, r2, CH.WL{n1, d1, x1}, CH.WN{r2, l2, y2, z2}, {==}, {==}, {==}, wa, wb)
    case CH.WN{+r1, l1, y1, z1} CH.WL{+n2, d2, x2}:
      cat_core(CH.Ch.fits2(cap, r1, n2), cap, r1, n2, CH.WN{r1, l1, y1, z1}, CH.WL{n2, d2, x2}, {==}, {==}, {==}, wa, wb)
    case CH.WN{+r1, l1, y1, z1} CH.WN{+r2, l2, y2, z2}:
      cat_core(CH.Ch.fits2(cap, r1, r2), cap, r1, r2, CH.WN{r1, l1, y1, z1}, CH.WN{r2, l2, y2, z2}, {==}, {==}, {==}, wa, wb)

# ==== croom_of_cap: the compaction cursor stays below the leaf's capacity ===============================

# every word a read of a 0/1 buffer answers is 0 or 1
def rd_le1(d: Nat, a: Array<U32>, z: Bool, w: Laws.WFWords(True{}, d, a), +n: U32, +i: U32) -> {U32.is_le(Laws.rd(U32, a, n, i, z), 1) == True{} : Bool}:
  match d a z:
    case 0n ALeaf{x} _:
      w
    case 1n+p ANode{xs, ys} True{}:
      (wl, wr) = w
      rd_le1(p, xs, U32.is_lt(i, U32.shr(U32.shr(n))), wl, U32.shr(n), i)
    case 1n+p ANode{xs, ys} False{}:
      (wl, wr) = w
      rd_le1(p, ys, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))), wr, U32.shr(n), U32.sub(i, U32.shr(n)))
    case 0n ANode{xs, ys} _:
      Empty.absurd({U32.is_le(Laws.rd(U32, ANode{xs, ys}, n, i, z), 1) == True{} : Bool}, w)
    case 1n+p ALeaf{x} _:
      Empty.absurd({U32.is_le(Laws.rd(U32, ALeaf{x}, n, i, z), 1) == True{} : Bool}, w)

def bit_k(+d: Nat, -a: Array<U32>, w: Laws.WFWords(True{}, d, a), +i: U32, s: &b: Array<U32> -> &n: U32 -> {b == a : Array<U32>} & {Array.size(U32, a) == (b, n) : Array<U32> & U32} & {Laws.slots(U32, b) == n : U32})
  -> {U32.is_le(Laws.rd_at(U32, a, i), 1) == True{} : Bool}:
  (b, n0, +eb, es, sl) = s
  +n = n0
  %Equal.sym(Array<U32> & U32, Array.size(U32, a), (b, n), es) : {U32.is_le(Laws.rd_size(U32, i, _), 1) == True{} : Bool}
  rd_le1(d, b, U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n)), (%Equal.sym(Array<U32>, b, a, eb) : Laws.WFWords(True{}, d, _); w), n, U32.and(i, U32.sub(n, 1)))

# the word at i of a 0/1 buffer is 0 or 1 (consumes the buffer: the caller clones it)
def bit_at(+d: Nat, a: Array<U32>, w: Laws.WFWords(True{}, d, a), +i: U32) -> {U32.is_le(Laws.rd_at(U32, a, i), 1) == True{} : Bool}:
  bit_k(d, a, w, i, PK.size_same(U32, a))

def bits_dup(+x: U32, +h: {U32.is_le(x, 1) == True{} : Bool}) -> {U32.is_le(x, 1) == True{} : Bool} & {U32.is_le(x, 1) == True{} : Bool}:
  (h, h)

def CloneW(+d: Nat, -a: Array<U32>) -> Type:
  &a1: Array<U32> -> &a2: Array<U32> -> {a1 == a : Array<U32>} & {a2 == a : Array<U32>} & Laws.WFWords(True{}, d, a1) & Laws.WFWords(True{}, d, a2)

def clone_words_leaf(+x: U32, r: {U32.is_le(x, 1) == True{} : Bool} & {U32.is_le(x, 1) == True{} : Bool}) -> CloneW(0n, ALeaf{x}):
  (h1, h2) = r
  (ALeaf{x}, ALeaf{x}, {==}, {==}, h1, h2)

def clone_words_node(+p: Nat, -xs: Array<U32>, -ys: Array<U32>, wx: CloneW(p, xs), wy: CloneW(p, ys)) -> CloneW(1n+p, ANode{xs, ys}):
  (x1, x2, ex1, ex2, wx1, wx2) = wx
  (y1, y2, ey1, ey2, wy1, wy2) = wy
  (ANode{x1, y1}, ANode{x2, y2}, (%ey1 : {ANode{x1, y1} == ANode{xs, _} : Array<U32>}; %ex1 : {ANode{x1, y1} == ANode{_, y1} : Array<U32>}; {==}), (%ey2 : {ANode{x2, y2} == ANode{xs, _} : Array<U32>}; %ex2 : {ANode{x2, y2} == ANode{_, y2} : Array<U32>}; {==}), (wx1, wy1), (wx2, wy2))

def clone_words(d: Nat, a: Array<U32>, w: Laws.WFWords(True{}, d, a)) -> CloneW(d, a):
  match d a:
    case 0n ALeaf{+x}:
      clone_words_leaf(x, bits_dup(x, w))
    case 1n++p ANode{xs, ys}:
      (wl, wr) = w
      clone_words_node(p, xs, ys, clone_words(p, xs, wl), clone_words(p, ys, wr))
    case 0n ANode{xs, ys}:
      Empty.absurd(CloneW(0n, ANode{xs, ys}), w)
    case 1n+p ALeaf{x}:
      Empty.absurd(CloneW(1n+p, ALeaf{x}), w)

# a + b <= c + e from a <= c and b <= e
def nat_add_le2(a: Nat, +b: Nat, +c: Nat, +e: Nat, h1: {Nat.is_le(a, c) == True{} : Bool}, h2: {Nat.is_le(b, e) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, b), Nat.add(c, e)) == True{} : Bool}:
  match a c:
    case 0n _:
      nat_le_trans(b, e, Nat.add(c, e), h2, nat_le_add_l(c, e))
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(Nat.add(1n+p, b), Nat.add(0n, e)) == True{} : Bool}, L.false_true(h1))
    case 1n+p 1n+q:
      nat_add_le2(p, b, q, e, h1, h2)

def nat_add_one(+x: Nat) -> {Nat.add(x, 1n) == 1n+x : Nat}:
  %nat_add_zero_r(x) : {Nat.add(x, 1n) == 1n+_ : Nat}
  B.add_succ(x, 0n)

def croom_le(+i: U32, +k: U32, +b: U32, +hb: {U32.is_le(b, 1) == True{} : Bool}, +hki: {Nat.is_le(U32.to_nat(k), U32.to_nat(i)) == True{} : Bool})
  -> {Nat.is_le(Nat.add(U32.to_nat(k), U32.to_nat(b)), 1n+U32.to_nat(i)) == True{} : Bool}:
  %nat_add_one(U32.to_nat(i)) : {Nat.is_le(Nat.add(U32.to_nat(k), U32.to_nat(b)), _) == True{} : Bool}
  nat_add_le2(U32.to_nat(k), U32.to_nat(b), U32.to_nat(i), 1n, hki, nle_of_u(b, 1, hb))

# the cursor after the step: k + b <= i + 1 below 2^d
def croom_k(+i: U32, +k: U32, +b: U32, +d: Nat, +hb: {U32.is_le(b, 1) == True{} : Bool}, +hki: {Nat.is_le(U32.to_nat(k), U32.to_nat(i)) == True{} : Bool}, +hi1: {Nat.is_le(1n+U32.to_nat(i), U32.to_nat(U32.shln(1, d))) == True{} : Bool}, +ei: {U32.to_nat(U32.inc(i)) == 1n+U32.to_nat(i) : Nat})
  -> {Nat.is_le(U32.to_nat(U32.add(k, b)), U32.to_nat(U32.inc(i))) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat(U32.inc(i)), 1n+U32.to_nat(i), ei) : {Nat.is_le(U32.to_nat(U32.add(k, b)), _) == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(U32.add(k, b)), Nat.add(U32.to_nat(k), U32.to_nat(b)), to_nat_add(k, b, U32.shln(1, d), nat_le_trans(Nat.add(U32.to_nat(k), U32.to_nat(b)), 1n+U32.to_nat(i), U32.to_nat(U32.shln(1, d)), croom_le(i, k, b, hb, hki), hi1))) : {Nat.is_le(_, 1n+U32.to_nat(i)) == True{} : Bool}
  croom_le(i, k, b, hb, hki)

def bit_eq(+d: Nat, -mask: Array<U32>, m1: Array<U32>, +e1: {m1 == mask : Array<U32>}, w1: Laws.WFWords(True{}, d, m1), +i: U32) -> {U32.is_le(Laws.rd_at(U32, mask, i), 1) == True{} : Bool}:
  %e1 : {U32.is_le(Laws.rd_at(U32, _, i), 1) == True{} : Bool}
  bit_at(d, m1, w1, i)

def hb_of(+b: U32, -mask: Array<U32>, +i: U32, +eb: {b == Laws.rd_at(U32, mask, i) : U32}, +hb: {U32.is_le(Laws.rd_at(U32, mask, i), 1) == True{} : Bool}) -> {U32.is_le(b, 1) == True{} : Bool}:
  %Equal.sym(U32, b, Laws.rd_at(U32, mask, i), eb) : {U32.is_le(_, 1) == True{} : Bool}
  hb

def CroomIH(p: Nat, +i: U32, +k: U32, +d: Nat, -mask: Array<U32>) -> Type:
  @b2: U32 -> @m5: Array<U32> -> {m5 == mask : Array<U32>} -> Laws.WFWords(True{}, d, m5) -> {Nat.is_le(U32.to_nat(U32.add(k, b2)), U32.to_nat(U32.inc(i))) == True{} : Bool} -> {Nat.is_le(Nat.add(U32.to_nat(U32.inc(i)), p), U32.to_nat(U32.shln(1, d))) == True{} : Bool} -> Laws.CRoom(p, U32.inc(i), U32.add(k, b2), d, mask)

def croom_step3(+p: Nat, +i: U32, +k: U32, +d: Nat, -mask: Array<U32>, m4: Array<U32>, +em4: {m4 == mask : Array<U32>}, w4: Laws.WFWords(True{}, d, m4),
  +hki: {Nat.is_le(U32.to_nat(k), U32.to_nat(i)) == True{} : Bool}, +hif: {Nat.is_le(Nat.add(U32.to_nat(i), 1n+p), U32.to_nat(U32.shln(1, d))) == True{} : Bool},
  +hb: {U32.is_le(Laws.rd_at(U32, mask, i), 1) == True{} : Bool}, +b: U32, +eb: {b == Laws.rd_at(U32, mask, i) : U32}, ih: CroomIH(p, i, k, d, mask))
  -> Laws.CRoom(1n+p, i, k, d, mask):
  +lti = B.lt_of_le_add(U32.to_nat(i), p, U32.to_nat(U32.shln(1, d)), hif)
  +ei = tna_fin(i, U32.shln(1, d), B.inc_nat_u(i), ult_of_n(i, U32.shln(1, d), lti))
  +hbb = hb_of(b, mask, i, eb, hb)
  (b, eb, hbb, ult_of_n(k, U32.shln(1, d), PST.nat_le_lt_trans(U32.to_nat(k), U32.to_nat(i), U32.to_nat(U32.shln(1, d)), hki, lti)), ih(b, m4, em4, w4, croom_k(i, k, b, d, hbb, hki, nat_succ_le_of_lt(U32.to_nat(i), U32.to_nat(U32.shln(1, d)), lti), ei), (%Equal.sym(Nat, U32.to_nat(U32.inc(i)), 1n+U32.to_nat(i), ei) : {Nat.is_le(Nat.add(_, p), U32.to_nat(U32.shln(1, d))) == True{} : Bool}; %B.add_succ(U32.to_nat(i), p) : {Nat.is_le(_, U32.to_nat(U32.shln(1, d))) == True{} : Bool}; hif)))

def croom_step2(p: Nat, +i: U32, +k: U32, +d: Nat, -mask: Array<U32>, -m2: Array<U32>, +em2: {m2 == mask : Array<U32>},
  +hki: {Nat.is_le(U32.to_nat(k), U32.to_nat(i)) == True{} : Bool}, +hif: {Nat.is_le(Nat.add(U32.to_nat(i), 1n+p), U32.to_nat(U32.shln(1, d))) == True{} : Bool},
  +hb: {U32.is_le(Laws.rd_at(U32, mask, i), 1) == True{} : Bool}, c: CloneW(d, m2), ih: CroomIH(p, i, k, d, mask))
  -> Laws.CRoom(1n+p, i, k, d, mask):
  (m3, m4, +e3, +e4, w3, w4) = c
  croom_step3(p, i, k, d, mask, m4, Equal.trans(Array<U32>, m4, m2, mask, e4, em2), w4, hki, hif, hb, Laws.rd_at(U32, m3, i), Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, i), m3, mask, Equal.trans(Array<U32>, m3, m2, mask, e3, em2)), ih)

def croom_step(p: Nat, +i: U32, +k: U32, +d: Nat, -mask: Array<U32>, -m: Array<U32>, +em: {m == mask : Array<U32>},
  +hki: {Nat.is_le(U32.to_nat(k), U32.to_nat(i)) == True{} : Bool}, +hif: {Nat.is_le(Nat.add(U32.to_nat(i), 1n+p), U32.to_nat(U32.shln(1, d))) == True{} : Bool},
  c: CloneW(d, m), ih: CroomIH(p, i, k, d, mask))
  -> Laws.CRoom(1n+p, i, k, d, mask):
  (m1, m2, +e1, +e2, w1, w2) = c
  croom_step2(p, i, k, d, mask, m2, Equal.trans(Array<U32>, m2, m, mask, e2, em), hki, hif, bit_eq(d, mask, m1, Equal.trans(Array<U32>, m1, m, mask, e1, em), w1, i), clone_words(d, m2, w2), ih)

def croom_go(f: Nat, +i: U32, +k: U32, +d: Nat, -mask: Array<U32>, m: Array<U32>, +em: {m == mask : Array<U32>}, w: Laws.WFWords(True{}, d, m),
  +hki: {Nat.is_le(U32.to_nat(k), U32.to_nat(i)) == True{} : Bool}, +hif: {Nat.is_le(Nat.add(U32.to_nat(i), f), U32.to_nat(U32.shln(1, d))) == True{} : Bool})
  -> Laws.CRoom(f, i, k, d, mask):
  match f:
    case 0n:
      Unit{}
    case 1n++p:
      croom_step(p, i, k, d, mask, m, em, hki, hif, clone_words(d, m, w), b2 => m5 => em5 => w5 => hk2 => hif2 => croom_go(p, U32.inc(i), U32.add(k, b2), d, mask, m5, em5, w5, hk2, hif2))

def Laws.croom_of_cap(n, d, mask, fits, bits):
  croom_go(U32.to_nat(n), 0, 0, d, mask, mask, {==}, bits, {==}, nle_of_u(n, U32.shln(1, d), fits))

# ==== the chunked map (ported from bench/spikes/w0_engine/laws_spike.bend) ==============================

def cmap_shape_node(+rows: U32, +lrows: U32, -l: CH.CW, -r: CH.CW, e1: {lrows == Laws.crows(l) : U32}, e2: {Nat.add(U32.to_nat(lrows), Laws.nrows(r)) == U32.to_nat(rows) : Nat},
  x: {Laws.crows(CH.CW.map(~(x => U32.xor(x, 1)), l)) == Laws.crows(l) : U32} & Laws.ShapeWF(CH.CW.map(~(x => U32.xor(x, 1)), l)),
  y: {Laws.crows(CH.CW.map(~(x => U32.xor(x, 1)), r)) == Laws.crows(r) : U32} & Laws.ShapeWF(CH.CW.map(~(x => U32.xor(x, 1)), r)))
  -> {rows == rows : U32} & ({lrows == Laws.crows(CH.CW.map(~(x => U32.xor(x, 1)), l)) : U32} & {Nat.add(U32.to_nat(lrows), Laws.nrows(CH.CW.map(~(x => U32.xor(x, 1)), r))) == U32.to_nat(rows) : Nat} & Laws.ShapeWF(CH.CW.map(~(x => U32.xor(x, 1)), l)) & Laws.ShapeWF(CH.CW.map(~(x => U32.xor(x, 1)), r))):
  (el, sl) = x
  (er, sr) = y
  ({==}, (Equal.trans(U32, lrows, Laws.crows(l), Laws.crows(CH.CW.map(~(x => U32.xor(x, 1)), l)), e1, Equal.sym(U32, Laws.crows(CH.CW.map(~(x => U32.xor(x, 1)), l)), Laws.crows(l), el)), (%Equal.sym(U32, Laws.crows(CH.CW.map(~(x => U32.xor(x, 1)), r)), Laws.crows(r), er) : {Nat.add(U32.to_nat(lrows), U32.to_nat(_)) == U32.to_nat(rows) : Nat}; e2), sl, sr))

def Laws.cmap_shape(t, wf):
  match t:
    case CH.WL{+n, +d, a}:
      (fits, wfa) = wf
      ({==}, fits)
    case CH.WN{+rows, +lrows, l, r}:
      (e1, e2, wl, wr) = wf
      cmap_shape_node(rows, lrows, l, r, e1, e2, Laws.cmap_shape(l, wl), Laws.cmap_shape(r, wr))

def Laws.cmap_leafwise(t, wf):
  match t:
    case CH.WL{+n, +d, a}:
      (fits, wfa) = wf
      ({==}, {==}, k => hk => PC.map_cell(~U32, ~U32, ~(x => U32.xor(x, 1)), d, n, a, 0, k, fits, hk))
    case CH.WN{+rows, +lrows, l, r}:
      (e1, e2, wl, wr) = wf
      ({==}, {==}, Laws.cmap_leafwise(l, wl), Laws.cmap_leafwise(r, wr))

# rows(t): the tree back and its row count
def RowsW(-t: CH.CW) -> Type:
  &t2: CH.CW -> &r: U32 -> {CH.CW.rows(t) == (t2, r) : CH.CW & U32} & {t2 == t : CH.CW} & {Laws.crows(t) == r : U32}

def rows_w(t: CH.CW) -> RowsW(t):
  match t:
    case CH.WL{+n, d, a}:
      (CH.WL{n, d, a}, n, {==}, {==}, {==})
    case CH.WN{+rows, lrows, l, r}:
      (CH.WN{rows, lrows, l, r}, rows, {==}, {==}, {==})


# ==== rechunk ===========================================================================================

# the node's rows from the children's (each child's fact used once)
def rc_cells_b(bb: Bool, +rows: U32, +lrows: U32, -l: CH.CW, -r: CH.CW, -x: CH.CW, -y: CH.CW, +m: Nat,
  +ebb: {Nat.is_lt(m, U32.to_nat(lrows)) == bb : Bool}, +hm: {Nat.is_lt(m, U32.to_nat(rows)) == True{} : Bool}, +el: {lrows == Laws.crows(l) : U32}, +esum: {Nat.add(U32.to_nat(lrows), Laws.nrows(r)) == U32.to_nat(rows) : Nat},
  fx: @m2: Nat -> {Nat.is_lt(m2, Laws.nrows(l)) == True{} : Bool} -> {Laws.ncell(x, m2) == Laws.ncell(l, m2) : U32},
  fy: @m2: Nat -> {Nat.is_lt(m2, Laws.nrows(r)) == True{} : Bool} -> {Laws.ncell(y, m2) == Laws.ncell(r, m2) : U32})
  -> {Laws.ncell(CH.WN{rows, lrows, x, y}, m) == Laws.ncell(CH.WN{rows, lrows, l, r}, m) : U32}:
  match bb:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(m, U32.to_nat(lrows)), True{}, ebb) : {Bool.pick(U32, _, Laws.ncell(x, m), Laws.ncell(y, Nat.sub(m, U32.to_nat(lrows)))) == Bool.pick(U32, _, Laws.ncell(l, m), Laws.ncell(r, Nat.sub(m, U32.to_nat(lrows)))) : U32}
      fx(m, (%el : {Nat.is_lt(m, U32.to_nat(_)) == True{} : Bool}; ebb))
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(m, U32.to_nat(lrows)), False{}, ebb) : {Bool.pick(U32, _, Laws.ncell(x, m), Laws.ncell(y, Nat.sub(m, U32.to_nat(lrows)))) == Bool.pick(U32, _, Laws.ncell(l, m), Laws.ncell(r, Nat.sub(m, U32.to_nat(lrows)))) : U32}
      fy(Nat.sub(m, U32.to_nat(lrows)), nat_lt_sub(m, U32.to_nat(lrows), Laws.nrows(r), (%Equal.sym(Nat, Nat.add(U32.to_nat(lrows), Laws.nrows(r)), U32.to_nat(rows), esum) : {Nat.is_lt(m, _) == True{} : Bool}; hm), ebb))

# a + b == d and a + c == d: b == c (b, c only in the types)
def nat_add_cancel_l(a: Nat, -b: Nat, -c: Nat, -d: Nat, e1: {Nat.add(a, b) == d : Nat}, e2: {Nat.add(a, c) == d : Nat}) -> {b == c : Nat}:
  match a:
    case 0n:
      Equal.trans(Nat, b, d, c, e1, Equal.sym(Nat, c, d, e2))
    case 1n+p:
      nat_add_cancel_l(p, b, c, npred(d), Equal.cong(Nat, Nat, x => npred(x), 1n+Nat.add(p, b), d, e1), Equal.cong(Nat, Nat, x => npred(x), 1n+Nat.add(p, c), d, e2))

def RcGo(-t: CH.CW, fits: Bool, +g: Nat) -> Type:
  &t2: CH.CW -> {CH.CW.rechunk.go(t, fits, g) == t2 : CH.CW} & Laws.WFChunks(t2) & {Laws.crows(t2) == Laws.crows(t) : U32} & (@m: Nat -> {Nat.is_lt(m, Laws.nrows(t)) == True{} : Bool} -> {Laws.ncell(t2, m) == Laws.ncell(t, m) : U32})

# the merged leaf's row m: flatten's row m (read through the buffer the leaf holds)
def rc_cell(+g: Nat, -o: Array<U32>, -b: Array<U32>, +m: Nat, -t: CH.CW, +esb: {Array.size(U32, b) == (b, U32.shln(1, g)) : Array<U32> & U32}, +eb: {b == o : Array<U32>},
  f: {Laws.rdN(U32, g, o, Laws.addn(0, m)) == Laws.ncell(t, m) : U32})
  -> {Laws.rd_at(U32, b, Laws.addn(0, m)) == Laws.ncell(t, m) : U32}:
  %Equal.sym(Array<U32> & U32, Array.size(U32, b), (b, U32.shln(1, g)), esb) : {Laws.rd_size(U32, Laws.addn(0, m), _) == Laws.ncell(t, m) : U32}
  %Equal.sym(Array<U32>, b, o, eb) : {Laws.rdN(U32, g, _, Laws.addn(0, m)) == Laws.ncell(t, m) : U32}
  f

def rc_flat_b(+g: Nat, +rows: U32, -t: CH.CW, -o: Array<U32>, +hf: {Nat.is_le(U32.to_nat(rows), U32.to_nat(U32.shln(1, g))) == True{} : Bool}, +eo: {CH.CW.flatten(g, t) == o : Array<U32>},
  fa: @m: Nat -> {Nat.is_lt(m, Laws.nrows(t)) == True{} : Bool} -> {Laws.rdN(U32, g, o, Laws.addn(0, m)) == Laws.ncell(t, m) : U32},
  w: &b: Array<U32> -> {b == o : Array<U32>} & Laws.WFArray(U32, g, b) & {Array.size(U32, o) == (b, U32.shln(1, g)) : Array<U32> & U32})
  -> &t2: CH.CW -> {CH.WL{rows, g, CH.CW.flatten(g, t)} == t2 : CH.CW} & Laws.WFChunks(t2) & {Laws.crows(t2) == rows : U32} & (@m: Nat -> {Nat.is_lt(m, Laws.nrows(t)) == True{} : Bool} -> {Laws.ncell(t2, m) == Laws.ncell(t, m) : U32}):
  (b, +eb, wb, es) = w
  +esb = size_back(g, o, b, eb, es)
  (CH.WL{rows, g, b}, Equal.cong(Array<U32>, CH.CW, q => CH.WL{rows, g, q}, CH.CW.flatten(g, t), b, Equal.trans(Array<U32>, CH.CW.flatten(g, t), o, b, eo, Equal.sym(Array<U32>, b, o, eb))), (ule_of_n(rows, U32.shln(1, g), hf), wb), {==}, +m => +hm => rc_cell(g, o, b, m, t, esb, eb, fa(m, hm)))

def rc_flat_a(+g: Nat, +rows: U32, -t: CH.CW, +hf: {Nat.is_le(U32.to_nat(rows), U32.to_nat(U32.shln(1, g))) == True{} : Bool}, w: Laws.FlatW(g, t))
  -> &t2: CH.CW -> {CH.WL{rows, g, CH.CW.flatten(g, t)} == t2 : CH.CW} & Laws.WFChunks(t2) & {Laws.crows(t2) == rows : U32} & (@m: Nat -> {Nat.is_lt(m, Laws.nrows(t)) == True{} : Bool} -> {Laws.ncell(t2, m) == Laws.ncell(t, m) : U32}):
  (o, +eo, wo, fa) = w
  rc_flat_b(g, rows, t, o, hf, eo, fa, PC.wf_size(U32, g, o, wo))

# a fitting node becomes one flattened leaf
def rc_flat(+g: Nat, +rows: U32, +lrows: U32, l: CH.CW, r: CH.CW, wf: Laws.WFChunks(CH.WN{rows, lrows, l, r}), +hf: {Nat.is_le(U32.to_nat(rows), U32.to_nat(U32.shln(1, g))) == True{} : Bool})
  -> RcGo(CH.WN{rows, lrows, l, r}, True{}, g):
  rc_flat_a(g, rows, CH.WN{rows, lrows, l, r}, hf, flat_fin(g, CH.WN{rows, lrows, l, r}, +m => +hm => nat_le_trans(m, U32.to_nat(rows), U32.to_nat(U32.shln(1, g)), nat_le_of_lt(m, U32.to_nat(rows), hm), hf), flat_w(CH.WN{rows, lrows, l, r}, 0, 0n, g, Array.new(U32, g, 0), Laws.wf_new(U32, g, 0), wf, {==}, hf)))

# a node that does not fit: both children rechunked, the counts kept
def rc_split(+g: Nat, +rows: U32, +lrows: U32, -l: CH.CW, -r: CH.CW, +el: {lrows == Laws.crows(l) : U32}, +esum: {Nat.add(U32.to_nat(lrows), Laws.nrows(r)) == U32.to_nat(rows) : Nat},
  wx: RcGo(l, U32.is_le(lrows, U32.shln(1, g)), g), wy: RcGo(r, U32.is_le(U32.sub(rows, lrows), U32.shln(1, g)), g))
  -> RcGo(CH.WN{rows, lrows, l, r}, False{}, g):
  (x, ex, wxx, +cx, fx) = wx
  (y, ey, wyy, +cy, fy) = wy
  %Equal.sym(CH.CW, CH.CW.rechunk.go(l, U32.is_le(lrows, U32.shln(1, g)), g), x, ex) : &t2: CH.CW -> {CH.WN{rows, lrows, _, CH.CW.rechunk.go(r, U32.is_le(U32.sub(rows, lrows), U32.shln(1, g)), g)} == t2 : CH.CW} & Laws.WFChunks(t2) & {Laws.crows(t2) == rows : U32} & (@m: Nat -> {Nat.is_lt(m, U32.to_nat(rows)) == True{} : Bool} -> {Laws.ncell(t2, m) == Laws.ncell(CH.WN{rows, lrows, l, r}, m) : U32})
  %Equal.sym(CH.CW, CH.CW.rechunk.go(r, U32.is_le(U32.sub(rows, lrows), U32.shln(1, g)), g), y, ey) : &t2: CH.CW -> {CH.WN{rows, lrows, x, _} == t2 : CH.CW} & Laws.WFChunks(t2) & {Laws.crows(t2) == rows : U32} & (@m: Nat -> {Nat.is_lt(m, U32.to_nat(rows)) == True{} : Bool} -> {Laws.ncell(t2, m) == Laws.ncell(CH.WN{rows, lrows, l, r}, m) : U32})
  (CH.WN{rows, lrows, x, y}, {==}, (Equal.trans(U32, lrows, Laws.crows(l), Laws.crows(x), el, Equal.sym(U32, Laws.crows(x), Laws.crows(l), cx)), (%Equal.sym(U32, Laws.crows(y), Laws.crows(r), cy) : {Nat.add(U32.to_nat(lrows), U32.to_nat(_)) == U32.to_nat(rows) : Nat}; esum), wxx, wyy), {==}, +m => +hm => rc_cells_b(Nat.is_lt(m, U32.to_nat(lrows)), rows, lrows, l, r, x, y, m, {==}, hm, el, esum, fx, fy))

# the right child's rows are rows - lrows
def ent_r(+rows: U32, +lrows: U32, -r: CH.CW, +esum: {Nat.add(U32.to_nat(lrows), Laws.nrows(r)) == U32.to_nat(rows) : Nat}) -> {Laws.nrows(r) == U32.to_nat(U32.sub(rows, lrows)) : Nat}:
  nat_add_cancel_l(U32.to_nat(lrows), Laws.nrows(r), U32.to_nat(U32.sub(rows, lrows)), U32.to_nat(rows), esum, est_sub(rows, lrows, nat_le_of_sum(U32.to_nat(lrows), Laws.nrows(r), U32.to_nat(rows), esum)))

def hf_of(+rows: U32, +rt: U32, +g: Nat, +ent: {U32.to_nat(rows) == U32.to_nat(rt) : Nat}, +efit: {True{} == U32.is_le(rt, U32.shln(1, g)) : Bool}) -> {Nat.is_le(U32.to_nat(rows), U32.to_nat(U32.shln(1, g))) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat(rows), U32.to_nat(rt), ent) : {Nat.is_le(_, U32.to_nat(U32.shln(1, g))) == True{} : Bool}
  nle_of_u(rt, U32.shln(1, g), Equal.sym(Bool, True{}, U32.is_le(rt, U32.shln(1, g)), efit))

def rcgo(t: CH.CW, fits: Bool, +g: Nat, +rt: U32, +ent: {Laws.nrows(t) == U32.to_nat(rt) : Nat}, +efit: {fits == U32.is_le(rt, U32.shln(1, g)) : Bool}, wf: Laws.WFChunks(t))
  -> RcGo(t, fits, g):
  match t fits:
    case CH.WL{+n, +d, a} True{}:
      (CH.WL{n, d, a}, {==}, wf, {==}, m => hm => {==})
    case CH.WL{+n, +d, a} False{}:
      (CH.WL{n, d, a}, {==}, wf, {==}, m => hm => {==})
    case CH.WN{+rows, +lrows, l, r} True{}:
      rc_flat(g, rows, lrows, l, r, wf, hf_of(rows, rt, g, ent, efit))
    case CH.WN{+rows, +lrows, l, r} False{}:
      (+el, +esum, wl, wr) = wf
      rc_split(g, rows, lrows, l, r, el, esum, rcgo(l, U32.is_le(lrows, U32.shln(1, g)), g, lrows, Equal.cong(U32, Nat, q => U32.to_nat(q), Laws.crows(l), lrows, Equal.sym(U32, lrows, Laws.crows(l), el)), {==}, wl), rcgo(r, U32.is_le(U32.sub(rows, lrows), U32.shln(1, g)), g, U32.sub(rows, lrows), ent_r(rows, lrows, r, esum), {==}, wr))

def rc_top(+g: Nat, -t: CH.CW, wf: Laws.WFChunks(t), w: RowsW(t)) -> Laws.RechunkW(g, t):
  (t2, +r, er, +et2, ecr) = w
  %Equal.sym(CH.CW & U32, CH.CW.rows(t), (t2, r), er) : &t3: CH.CW -> {CH.CW.rechunk.k(g, _) == t3 : CH.CW} & Laws.WFChunks(t3) & {Laws.crows(t3) == Laws.crows(t) : U32} & (@m: Nat -> {Nat.is_lt(m, Laws.nrows(t)) == True{} : Bool} -> {Laws.ncell(t3, m) == Laws.ncell(t, m) : U32})
  %et2 : &t3: CH.CW -> {CH.CW.rechunk.k(g, (t2, r)) == t3 : CH.CW} & Laws.WFChunks(t3) & {Laws.crows(t3) == Laws.crows(_) : U32} & (@m: Nat -> {Nat.is_lt(m, Laws.nrows(_)) == True{} : Bool} -> {Laws.ncell(t3, m) == Laws.ncell(_, m) : U32})
  rcgo(t2, U32.is_le(r, U32.shln(1, g)), g, r, (%Equal.sym(CH.CW, t2, t, et2) : {Laws.nrows(_) == U32.to_nat(r) : Nat}; Equal.cong(U32, Nat, q => U32.to_nat(q), Laws.crows(t), r, ecr)), {==}, (%Equal.sym(CH.CW, t2, t, et2) : Laws.WFChunks(_); wf))

def Laws.cw_rechunk(g, t, wf):
  rc_top(g, t, wf, rows_w(t))

# ==== head: min arithmetic ==============================================================================

def nat_min_pick_k(c: Bool, +p: Nat, +q: Nat, +e: {Nat.is_lt(p, q) == c : Bool}, ih: {Nat.min(p, q) == Bool.pick(Nat, Nat.is_lt(p, q), p, q) : Nat})
  -> {1n+Nat.min(p, q) == Bool.pick(Nat, Nat.is_lt(p, q), 1n+p, 1n+q) : Nat}:
  match c:
    case True{}:
      %Equal.sym(Nat, Nat.min(p, q), Bool.pick(Nat, Nat.is_lt(p, q), p, q), ih) : {1n+_ == Bool.pick(Nat, Nat.is_lt(p, q), 1n+p, 1n+q) : Nat}
      %Equal.sym(Bool, Nat.is_lt(p, q), True{}, e) : {1n+Bool.pick(Nat, _, p, q) == Bool.pick(Nat, _, 1n+p, 1n+q) : Nat}
      {==}
    case False{}:
      %Equal.sym(Nat, Nat.min(p, q), Bool.pick(Nat, Nat.is_lt(p, q), p, q), ih) : {1n+_ == Bool.pick(Nat, Nat.is_lt(p, q), 1n+p, 1n+q) : Nat}
      %Equal.sym(Bool, Nat.is_lt(p, q), False{}, e) : {1n+Bool.pick(Nat, _, p, q) == Bool.pick(Nat, _, 1n+p, 1n+q) : Nat}
      {==}

def nat_min_pick(a: Nat, b: Nat) -> {Nat.min(a, b) == Bool.pick(Nat, Nat.is_lt(a, b), a, b) : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n++p 1n++q:
      nat_min_pick_k(Nat.is_lt(p, q), p, q, {==}, nat_min_pick(p, q))

# a <= b: min(a, b) == a
def nat_min_le(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.min(a, b) == a : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.min(1n+p, 0n) == 1n+p : Nat}, L.false_true(h))
    case 1n++p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.min(p, q), p, nat_min_le(p, q, h))

def nat_min_zero(a: Nat) -> {Nat.min(a, 0n) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# b <= a: min(a, b) == b
def nat_min_ge(a: Nat, b: Nat, h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.min(a, b) == b : Nat}:
  match a b:
    case _ 0n:
      nat_min_zero(a)
    case 0n 1n+q:
      Empty.absurd({Nat.min(0n, 1n+q) == 1n+q : Nat}, L.false_true(h))
    case 1n+p 1n++q:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.min(p, q), q, nat_min_ge(p, q, h))

def nat_min_le_r(a: Nat, b: Nat) -> {Nat.is_le(Nat.min(a, b), b) == True{} : Bool}:
  match a b:
    case 0n _:
      nat_le_zero(b)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      nat_min_le_r(p, q)

# not a <= b: b < a
def nat_lt_of_not_le(a: Nat, b: Nat, h: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, L.true_false(h))
    case 0n 1n+q:
      Empty.absurd({Nat.is_lt(1n+q, 0n) == True{} : Bool}, L.true_false(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      nat_lt_of_not_le(p, q, h)

# l <= h: l + min(h - l, r) == min(h, l + r)
def nat_add_min(l: Nat, h: Nat, -r: Nat, le: {Nat.is_le(l, h) == True{} : Bool}) -> {Nat.add(l, Nat.min(Nat.sub(h, l), r)) == Nat.min(h, Nat.add(l, r)) : Nat}:
  match l h:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.add(1n+p, Nat.min(Nat.sub(0n, 1n+p), r)) == Nat.min(0n, Nat.add(1n+p, r)) : Nat}, L.false_true(le))
    case 1n++p 1n++q:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, Nat.min(Nat.sub(q, p), r)), Nat.min(q, Nat.add(p, r)), nat_add_min(p, q, r, le))

def min_nat_k(c: Bool, +a: U32, +b: U32, +e: {U32.is_lt(a, b) == c : Bool}) -> {U32.to_nat(Bool.pick(U32, U32.is_lt(a, b), a, b)) == Nat.min(U32.to_nat(a), U32.to_nat(b)) : Nat}:
  match c:
    case True{}:
      %Equal.sym(Nat, Nat.min(U32.to_nat(a), U32.to_nat(b)), Bool.pick(Nat, Nat.is_lt(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(a), U32.to_nat(b)), nat_min_pick(U32.to_nat(a), U32.to_nat(b))) : {U32.to_nat(Bool.pick(U32, U32.is_lt(a, b), a, b)) == _ : Nat}
      %ult_nat(a, b) : {U32.to_nat(Bool.pick(U32, U32.is_lt(a, b), a, b)) == Bool.pick(Nat, _, U32.to_nat(a), U32.to_nat(b)) : Nat}
      %Equal.sym(Bool, U32.is_lt(a, b), True{}, e) : {U32.to_nat(Bool.pick(U32, _, a, b)) == Bool.pick(Nat, _, U32.to_nat(a), U32.to_nat(b)) : Nat}
      {==}
    case False{}:
      %Equal.sym(Nat, Nat.min(U32.to_nat(a), U32.to_nat(b)), Bool.pick(Nat, Nat.is_lt(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(a), U32.to_nat(b)), nat_min_pick(U32.to_nat(a), U32.to_nat(b))) : {U32.to_nat(Bool.pick(U32, U32.is_lt(a, b), a, b)) == _ : Nat}
      %ult_nat(a, b) : {U32.to_nat(Bool.pick(U32, U32.is_lt(a, b), a, b)) == Bool.pick(Nat, _, U32.to_nat(a), U32.to_nat(b)) : Nat}
      %Equal.sym(Bool, U32.is_lt(a, b), False{}, e) : {U32.to_nat(Bool.pick(U32, _, a, b)) == Bool.pick(Nat, _, U32.to_nat(a), U32.to_nat(b)) : Nat}
      {==}

# to_nat(min(a, b)) == min(to_nat a, to_nat b)
def min_nat(a: U32, b: U32) -> {U32.to_nat(U32.min(a, b)) == Nat.min(U32.to_nat(a), U32.to_nat(b)) : Nat}:
  match a b:
    case U32{+x} U32{+y}:
      min_nat_k(U32.is_lt(U32{x}, U32{y}), U32{x}, U32{y}, {==})

# h <= l: min(h, l) == h
def umin_le(+h: U32, +l: U32, +e: {U32.is_le(h, l) == True{} : Bool}) -> {U32.min(h, l) == h : U32}:
  u32_eq_of_nat(U32.min(h, l), h, (%Equal.sym(Nat, U32.to_nat(U32.min(h, l)), Nat.min(U32.to_nat(h), U32.to_nat(l)), min_nat(h, l)) : {_ == U32.to_nat(h) : Nat}; nat_min_le(U32.to_nat(h), U32.to_nat(l), nle_of_u(h, l, e))))

# not h <= l: min(h, l) == l
def umin_gt(+h: U32, +l: U32, +e: {U32.is_le(h, l) == False{} : Bool}) -> {U32.min(h, l) == l : U32}:
  u32_eq_of_nat(U32.min(h, l), l, (%Equal.sym(Nat, U32.to_nat(U32.min(h, l)), Nat.min(U32.to_nat(h), U32.to_nat(l)), min_nat(h, l)) : {_ == U32.to_nat(l) : Nat}; nat_min_ge(U32.to_nat(h), U32.to_nat(l), nat_le_of_lt(U32.to_nat(l), U32.to_nat(h), nat_lt_of_not_le(U32.to_nat(h), U32.to_nat(l), (%ule_nat(h, l) : {_ == False{} : Bool}; e))))))

# ==== head ==============================================================================================

def HeadNode(c: Bool, +h: U32, +rows: U32, +lrows: U32, -l: CH.CW, -r: CH.CW, -x2: CH.CW, -y2: CH.CW, +ry: U32) -> Type:
  &t2: CH.CW -> {CH.CW.head.j(c, lrows, x2, (y2, ry)) == t2 : CH.CW} & Laws.WFChunks(t2) & {Laws.nrows(t2) == Nat.min(U32.to_nat(h), U32.to_nat(rows)) : Nat} & (@m: Nat -> {Nat.is_lt(m, Laws.nrows(t2)) == True{} : Bool} -> {Laws.ncell(t2, m) == Laws.ncell(CH.WN{rows, lrows, l, r}, m) : U32})

def ssub_gt(+h: U32, +l: U32, +ec: {U32.is_le(h, l) == False{} : Bool}) -> {CH.Ch.ssub(h, l) == U32.sub(h, l) : U32}:
  %Equal.sym(Bool, U32.is_le(h, l), False{}, ec) : {Bool.pick(U32, _, 0, U32.sub(h, l)) == U32.sub(h, l) : U32}
  {==}

def lt_hl(+h: U32, +lrows: U32, +ec: {U32.is_le(h, lrows) == False{} : Bool}) -> {Nat.is_lt(U32.to_nat(lrows), U32.to_nat(h)) == True{} : Bool}:
  nat_lt_of_not_le(U32.to_nat(h), U32.to_nat(lrows), (%ule_nat(h, lrows) : {_ == False{} : Bool}; ec))

def tssub(+h: U32, +lrows: U32, +ec: {U32.is_le(h, lrows) == False{} : Bool}) -> {U32.to_nat(CH.Ch.ssub(h, lrows)) == Nat.sub(U32.to_nat(h), U32.to_nat(lrows)) : Nat}:
  %Equal.sym(U32, CH.Ch.ssub(h, lrows), U32.sub(h, lrows), ssub_gt(h, lrows, ec)) : {U32.to_nat(_) == Nat.sub(U32.to_nat(h), U32.to_nat(lrows)) : Nat}
  sub_nat(h, lrows, ule_of_n(lrows, h, nat_le_of_lt(U32.to_nat(lrows), U32.to_nat(h), lt_hl(h, lrows, ec))))

# the right part's rows: min(h - lrows, rows(r))
def hd_ery(+h: U32, +lrows: U32, -r: CH.CW, -y: CH.CW, +ry: U32, +ec: {U32.is_le(h, lrows) == False{} : Bool}, +ecy: {Laws.crows(y) == ry : U32}, +cy: {Laws.nrows(y) == Nat.min(U32.to_nat(CH.Ch.ssub(h, lrows)), Laws.nrows(r)) : Nat})
  -> {U32.to_nat(ry) == Nat.min(Nat.sub(U32.to_nat(h), U32.to_nat(lrows)), Laws.nrows(r)) : Nat}:
  %ecy : {U32.to_nat(_) == Nat.min(Nat.sub(U32.to_nat(h), U32.to_nat(lrows)), Laws.nrows(r)) : Nat}
  %Equal.sym(Nat, Laws.nrows(y), Nat.min(U32.to_nat(CH.Ch.ssub(h, lrows)), Laws.nrows(r)), cy) : {_ == Nat.min(Nat.sub(U32.to_nat(h), U32.to_nat(lrows)), Laws.nrows(r)) : Nat}
  %tssub(h, lrows, ec) : {Nat.min(U32.to_nat(CH.Ch.ssub(h, lrows)), Laws.nrows(r)) == Nat.min(_, Laws.nrows(r)) : Nat}
  {==}

def hd_bnd(+h: U32, +rows: U32, +lrows: U32, -r: CH.CW, +ry: U32, +ec: {U32.is_le(h, lrows) == False{} : Bool}, +esum: {Nat.add(U32.to_nat(lrows), Laws.nrows(r)) == U32.to_nat(rows) : Nat},
  +ery: {U32.to_nat(ry) == Nat.min(Nat.sub(U32.to_nat(h), U32.to_nat(lrows)), Laws.nrows(r)) : Nat})
  -> {Nat.is_le(Nat.add(U32.to_nat(lrows), U32.to_nat(ry)), U32.to_nat(rows)) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat(ry), Nat.min(Nat.sub(U32.to_nat(h), U32.to_nat(lrows)), Laws.nrows(r)), ery) : {Nat.is_le(Nat.add(U32.to_nat(lrows), _), U32.to_nat(rows)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(U32.to_nat(lrows), Nat.min(Nat.sub(U32.to_nat(h), U32.to_nat(lrows)), Laws.nrows(r))), Nat.min(U32.to_nat(h), Nat.add(U32.to_nat(lrows), Laws.nrows(r))), nat_add_min(U32.to_nat(lrows), U32.to_nat(h), Laws.nrows(r), nat_le_of_lt(U32.to_nat(lrows), U32.to_nat(h), lt_hl(h, lrows, ec)))) : {Nat.is_le(_, U32.to_nat(rows)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(U32.to_nat(lrows), Laws.nrows(r)), U32.to_nat(rows), esum) : {Nat.is_le(Nat.min(U32.to_nat(h), _), U32.to_nat(rows)) == True{} : Bool}
  nat_min_le_r(U32.to_nat(h), U32.to_nat(rows))

def hd_count(+h: U32, +rows: U32, +lrows: U32, -r: CH.CW, +ry: U32, +ec: {U32.is_le(h, lrows) == False{} : Bool}, +esum: {Nat.add(U32.to_nat(lrows), Laws.nrows(r)) == U32.to_nat(rows) : Nat},
  +ery: {U32.to_nat(ry) == Nat.min(Nat.sub(U32.to_nat(h), U32.to_nat(lrows)), Laws.nrows(r)) : Nat}, +tsum: {U32.to_nat(U32.add(lrows, ry)) == Nat.add(U32.to_nat(lrows), U32.to_nat(ry)) : Nat})
  -> {U32.to_nat(U32.add(lrows, ry)) == Nat.min(U32.to_nat(h), U32.to_nat(rows)) : Nat}:
  %Equal.sym(Nat, U32.to_nat(U32.add(lrows, ry)), Nat.add(U32.to_nat(lrows), U32.to_nat(ry)), tsum) : {_ == Nat.min(U32.to_nat(h), U32.to_nat(rows)) : Nat}
  %Equal.sym(Nat, U32.to_nat(ry), Nat.min(Nat.sub(U32.to_nat(h), U32.to_nat(lrows)), Laws.nrows(r)), ery) : {Nat.add(U32.to_nat(lrows), _) == Nat.min(U32.to_nat(h), U32.to_nat(rows)) : Nat}
  %esum : {Nat.add(U32.to_nat(lrows), Nat.min(Nat.sub(U32.to_nat(h), U32.to_nat(lrows)), Laws.nrows(r))) == Nat.min(U32.to_nat(h), _) : Nat}
  nat_add_min(U32.to_nat(lrows), U32.to_nat(h), Laws.nrows(r), nat_le_of_lt(U32.to_nat(lrows), U32.to_nat(h), lt_hl(h, lrows, ec)))

def hd_cells_f(bb: Bool, +lrows: U32, +rows: U32, +ry: U32, -l: CH.CW, -r: CH.CW, -x: CH.CW, -x2: CH.CW, -y: CH.CW, -y2: CH.CW, +m: Nat,
  +ebb: {Nat.is_lt(m, U32.to_nat(lrows)) == bb : Bool}, +hm: {Nat.is_lt(m, U32.to_nat(U32.add(lrows, ry))) == True{} : Bool},
  +enx: {Laws.nrows(x) == U32.to_nat(lrows) : Nat}, +tsum: {U32.to_nat(U32.add(lrows, ry)) == Nat.add(U32.to_nat(lrows), U32.to_nat(ry)) : Nat}, +ex2: {x2 == x : CH.CW}, +ey2: {y2 == y : CH.CW}, +ecy: {Laws.crows(y) == ry : U32},
  fx: @m2: Nat -> {Nat.is_lt(m2, Laws.nrows(x)) == True{} : Bool} -> {Laws.ncell(x, m2) == Laws.ncell(l, m2) : U32},
  fy: @m2: Nat -> {Nat.is_lt(m2, Laws.nrows(y)) == True{} : Bool} -> {Laws.ncell(y, m2) == Laws.ncell(r, m2) : U32})
  -> {Laws.ncell(CH.WN{U32.add(lrows, ry), lrows, x2, y2}, m) == Laws.ncell(CH.WN{rows, lrows, l, r}, m) : U32}:
  match bb:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(m, U32.to_nat(lrows)), True{}, ebb) : {Bool.pick(U32, _, Laws.ncell(x2, m), Laws.ncell(y2, Nat.sub(m, U32.to_nat(lrows)))) == Bool.pick(U32, _, Laws.ncell(l, m), Laws.ncell(r, Nat.sub(m, U32.to_nat(lrows)))) : U32}
      %Equal.sym(CH.CW, x2, x, ex2) : {Laws.ncell(_, m) == Laws.ncell(l, m) : U32}
      fx(m, (%Equal.sym(Nat, Laws.nrows(x), U32.to_nat(lrows), enx) : {Nat.is_lt(m, _) == True{} : Bool}; ebb))
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(m, U32.to_nat(lrows)), False{}, ebb) : {Bool.pick(U32, _, Laws.ncell(x2, m), Laws.ncell(y2, Nat.sub(m, U32.to_nat(lrows)))) == Bool.pick(U32, _, Laws.ncell(l, m), Laws.ncell(r, Nat.sub(m, U32.to_nat(lrows)))) : U32}
      %Equal.sym(CH.CW, y2, y, ey2) : {Laws.ncell(_, Nat.sub(m, U32.to_nat(lrows))) == Laws.ncell(r, Nat.sub(m, U32.to_nat(lrows))) : U32}
      fy(Nat.sub(m, U32.to_nat(lrows)), (%Equal.sym(U32, Laws.crows(y), ry, ecy) : {Nat.is_lt(Nat.sub(m, U32.to_nat(lrows)), U32.to_nat(_)) == True{} : Bool}; nat_lt_sub(m, U32.to_nat(lrows), U32.to_nat(ry), (%tsum : {Nat.is_lt(m, _) == True{} : Bool}; hm), ebb)))

# head's left part: min(h, rows(l)) rows
def hd_nx(+h: U32, +lrows: U32, -l: CH.CW, -x: CH.CW, +el: {lrows == Laws.crows(l) : U32}, +cx: {Laws.nrows(x) == Nat.min(U32.to_nat(h), Laws.nrows(l)) : Nat}) -> {Laws.nrows(x) == Nat.min(U32.to_nat(h), U32.to_nat(lrows)) : Nat}:
  %Equal.sym(U32, lrows, Laws.crows(l), el) : {Laws.nrows(x) == Nat.min(U32.to_nat(h), U32.to_nat(_)) : Nat}
  cx

def hmx_of(-x: CH.CW, -x2: CH.CW, +m: Nat, +ex2: {x2 == x : CH.CW}, +hm: {Nat.is_lt(m, Laws.nrows(x2)) == True{} : Bool}) -> {Nat.is_lt(m, Laws.nrows(x)) == True{} : Bool}:
  %ex2 : {Nat.is_lt(m, Laws.nrows(_)) == True{} : Bool}
  hm

def hd_t_cells(+h: U32, +rows: U32, +lrows: U32, -l: CH.CW, -r: CH.CW, -x: CH.CW, -x2: CH.CW, +m: Nat, +ex2: {x2 == x : CH.CW}, +ec: {U32.is_le(h, lrows) == True{} : Bool},
  +enx: {Laws.nrows(x) == U32.to_nat(h) : Nat}, +hm: {Nat.is_lt(m, Laws.nrows(x2)) == True{} : Bool},
  fx: @m2: Nat -> {Nat.is_lt(m2, Laws.nrows(x)) == True{} : Bool} -> {Laws.ncell(x, m2) == Laws.ncell(l, m2) : U32})
  -> {Laws.ncell(x2, m) == Laws.ncell(CH.WN{rows, lrows, l, r}, m) : U32}:
  +hmx = hmx_of(x, x2, m, ex2, hm)
  %Equal.sym(CH.CW, x2, x, ex2) : {Laws.ncell(_, m) == Laws.ncell(CH.WN{rows, lrows, l, r}, m) : U32}
  %Equal.sym(Bool, Nat.is_lt(m, U32.to_nat(lrows)), True{}, nat_lt_le(m, U32.to_nat(h), U32.to_nat(lrows), (%enx : {Nat.is_lt(m, _) == True{} : Bool}; hmx), nle_of_u(h, lrows, ec))) : {Laws.ncell(x, m) == Bool.pick(U32, _, Laws.ncell(l, m), Laws.ncell(r, Nat.sub(m, U32.to_nat(lrows)))) : U32}
  fx(m, hmx)

def hd_true(+h: U32, +rows: U32, +lrows: U32, -l: CH.CW, -r: CH.CW, -x: CH.CW, x2: CH.CW, -y2: CH.CW, +ry: U32,
  +ec: {U32.is_le(h, lrows) == True{} : Bool}, +ex2: {x2 == x : CH.CW}, +esum: {Nat.add(U32.to_nat(lrows), Laws.nrows(r)) == U32.to_nat(rows) : Nat},
  wx: Laws.WFChunks(x), +nx: {Laws.nrows(x) == Nat.min(U32.to_nat(h), U32.to_nat(lrows)) : Nat}, fx: @m2: Nat -> {Nat.is_lt(m2, Laws.nrows(x)) == True{} : Bool} -> {Laws.ncell(x, m2) == Laws.ncell(l, m2) : U32})
  -> HeadNode(True{}, h, rows, lrows, l, r, x2, y2, ry):
  +enx = Equal.trans(Nat, Laws.nrows(x), Nat.min(U32.to_nat(h), U32.to_nat(lrows)), U32.to_nat(h), nx, nat_min_le(U32.to_nat(h), U32.to_nat(lrows), nle_of_u(h, lrows, ec)))
  +hle = nat_le_trans(U32.to_nat(h), U32.to_nat(lrows), U32.to_nat(rows), nle_of_u(h, lrows, ec), nat_le_of_sum(U32.to_nat(lrows), Laws.nrows(r), U32.to_nat(rows), esum))
  (x2, {==}, (%Equal.sym(CH.CW, x2, x, ex2) : Laws.WFChunks(_); wx), (%Equal.sym(CH.CW, x2, x, ex2) : {Laws.nrows(_) == Nat.min(U32.to_nat(h), U32.to_nat(rows)) : Nat}; Equal.trans(Nat, Laws.nrows(x), U32.to_nat(h), Nat.min(U32.to_nat(h), U32.to_nat(rows)), enx, Equal.sym(Nat, Nat.min(U32.to_nat(h), U32.to_nat(rows)), U32.to_nat(h), nat_min_le(U32.to_nat(h), U32.to_nat(rows), hle)))),
   +m => +hm => hd_t_cells(h, rows, lrows, l, r, x, x2, m, ex2, ec, enx, hm, fx))

def hd_false(+h: U32, +rows: U32, +lrows: U32, -l: CH.CW, -r: CH.CW, -x: CH.CW, x2: CH.CW, +rx: U32, -y: CH.CW, y2: CH.CW, +ry: U32,
  +ec: {U32.is_le(h, lrows) == False{} : Bool}, +ex2: {x2 == x : CH.CW}, +ecx: {Laws.crows(x) == rx : U32}, +ey2: {y2 == y : CH.CW}, +ecy: {Laws.crows(y) == ry : U32},
  +esum: {Nat.add(U32.to_nat(lrows), Laws.nrows(r)) == U32.to_nat(rows) : Nat},
  wx: Laws.WFChunks(x), +nx: {Laws.nrows(x) == Nat.min(U32.to_nat(h), U32.to_nat(lrows)) : Nat}, fx: @m2: Nat -> {Nat.is_lt(m2, Laws.nrows(x)) == True{} : Bool} -> {Laws.ncell(x, m2) == Laws.ncell(l, m2) : U32},
  wy: Laws.WFChunks(y), +cy: {Laws.nrows(y) == Nat.min(U32.to_nat(CH.Ch.ssub(h, lrows)), Laws.nrows(r)) : Nat}, fy: @m2: Nat -> {Nat.is_lt(m2, Laws.nrows(y)) == True{} : Bool} -> {Laws.ncell(y, m2) == Laws.ncell(r, m2) : U32})
  -> HeadNode(False{}, h, rows, lrows, l, r, x2, y2, ry):
  +enx = Equal.trans(Nat, Laws.nrows(x), Nat.min(U32.to_nat(h), U32.to_nat(lrows)), U32.to_nat(lrows), nx, nat_min_ge(U32.to_nat(h), U32.to_nat(lrows), nat_le_of_lt(U32.to_nat(lrows), U32.to_nat(h), lt_hl(h, lrows, ec))))
  +elr = u32_eq_of_nat(lrows, rx, (%ecx : {U32.to_nat(lrows) == U32.to_nat(_) : Nat}; Equal.sym(Nat, Laws.nrows(x), U32.to_nat(lrows), enx)))
  +ery = hd_ery(h, lrows, r, y, ry, ec, ecy, cy)
  +tsum = to_nat_add(lrows, ry, rows, hd_bnd(h, rows, lrows, r, ry, ec, esum, ery))
  (CH.WN{U32.add(lrows, ry), lrows, x2, y2}, {==},
   ((%Equal.sym(CH.CW, x2, x, ex2) : {lrows == Laws.crows(_) : U32}; %Equal.sym(U32, Laws.crows(x), rx, ecx) : {lrows == _ : U32}; elr), (%Equal.sym(CH.CW, y2, y, ey2) : {Nat.add(U32.to_nat(lrows), Laws.nrows(_)) == U32.to_nat(U32.add(lrows, ry)) : Nat}; %Equal.sym(U32, Laws.crows(y), ry, ecy) : {Nat.add(U32.to_nat(lrows), U32.to_nat(_)) == U32.to_nat(U32.add(lrows, ry)) : Nat}; Equal.sym(Nat, U32.to_nat(U32.add(lrows, ry)), Nat.add(U32.to_nat(lrows), U32.to_nat(ry)), tsum)), (%Equal.sym(CH.CW, x2, x, ex2) : Laws.WFChunks(_); wx), (%Equal.sym(CH.CW, y2, y, ey2) : Laws.WFChunks(_); wy)),
   hd_count(h, rows, lrows, r, ry, ec, esum, ery, tsum),
   +m => +hm => hd_cells_f(Nat.is_lt(m, U32.to_nat(lrows)), lrows, rows, ry, l, r, x, x2, y, y2, m, {==}, hm, enx, tsum, ex2, ey2, ecy, fx, fy))

def hd_node3(c: Bool, +h: U32, +rows: U32, +lrows: U32, -l: CH.CW, -r: CH.CW, -x: CH.CW, x2: CH.CW, +rx: U32, -y: CH.CW, y2: CH.CW, +ry: U32,
  +ec: {U32.is_le(h, lrows) == c : Bool}, +ex2: {x2 == x : CH.CW}, +ecx: {Laws.crows(x) == rx : U32}, +ey2: {y2 == y : CH.CW}, +ecy: {Laws.crows(y) == ry : U32},
  +esum: {Nat.add(U32.to_nat(lrows), Laws.nrows(r)) == U32.to_nat(rows) : Nat},
  wx: Laws.WFChunks(x), +nx: {Laws.nrows(x) == Nat.min(U32.to_nat(h), U32.to_nat(lrows)) : Nat}, fx: @m2: Nat -> {Nat.is_lt(m2, Laws.nrows(x)) == True{} : Bool} -> {Laws.ncell(x, m2) == Laws.ncell(l, m2) : U32},
  wy: Laws.WFChunks(y), +cy: {Laws.nrows(y) == Nat.min(U32.to_nat(CH.Ch.ssub(h, lrows)), Laws.nrows(r)) : Nat}, fy: @m2: Nat -> {Nat.is_lt(m2, Laws.nrows(y)) == True{} : Bool} -> {Laws.ncell(y, m2) == Laws.ncell(r, m2) : U32})
  -> HeadNode(c, h, rows, lrows, l, r, x2, y2, ry):
  match c:
    case True{}:
      hd_true(h, rows, lrows, l, r, x, x2, y2, ry, ec, ex2, esum, wx, nx, fx)
    case False{}:
      hd_false(h, rows, lrows, l, r, x, x2, rx, y, y2, ry, ec, ex2, ecx, ey2, ecy, esum, wx, nx, fx, wy, cy, fy)

def HeadTop(+h: U32, +rows: U32, +lrows: U32, -l: CH.CW, -r: CH.CW, -xt: CH.CW, -yt: CH.CW & U32) -> Type:
  &t2: CH.CW -> {CH.CW.head.j(U32.is_le(h, lrows), lrows, xt, yt) == t2 : CH.CW} & Laws.WFChunks(t2) & {Laws.nrows(t2) == Nat.min(U32.to_nat(h), U32.to_nat(rows)) : Nat} & (@m: Nat -> {Nat.is_lt(m, Laws.nrows(t2)) == True{} : Bool} -> {Laws.ncell(t2, m) == Laws.ncell(CH.WN{rows, lrows, l, r}, m) : U32})

def hd_node2(+h: U32, +rows: U32, +lrows: U32, -l: CH.CW, -r: CH.CW, -x: CH.CW, -y: CH.CW,
  +esum: {Nat.add(U32.to_nat(lrows), Laws.nrows(r)) == U32.to_nat(rows) : Nat},
  wx: Laws.WFChunks(x), +nx: {Laws.nrows(x) == Nat.min(U32.to_nat(h), U32.to_nat(lrows)) : Nat}, fx: @m2: Nat -> {Nat.is_lt(m2, Laws.nrows(x)) == True{} : Bool} -> {Laws.ncell(x, m2) == Laws.ncell(l, m2) : U32},
  wy: Laws.WFChunks(y), +cy: {Laws.nrows(y) == Nat.min(U32.to_nat(CH.Ch.ssub(h, lrows)), Laws.nrows(r)) : Nat}, fy: @m2: Nat -> {Nat.is_lt(m2, Laws.nrows(y)) == True{} : Bool} -> {Laws.ncell(y, m2) == Laws.ncell(r, m2) : U32},
  rwx: RowsW(x), rwy: RowsW(y))
  -> HeadTop(h, rows, lrows, l, r, x, CH.CW.rows(y)):
  (x2, +rx, erx, +ex2, ecx) = rwx
  (y2, +ry, erw, +ey2, ecy) = rwy
  %Equal.sym(CH.CW & U32, CH.CW.rows(y), (y2, ry), erw) : HeadTop(h, rows, lrows, l, r, x, _)
  %ex2 : HeadTop(h, rows, lrows, l, r, _, (y2, ry))
  hd_node3(U32.is_le(h, lrows), h, rows, lrows, l, r, x, x2, rx, y, y2, ry, {==}, ex2, ecx, ey2, ecy, esum, wx, nx, fx, wy, cy, fy)

def hd_node(+h: U32, +rows: U32, +lrows: U32, -l: CH.CW, -r: CH.CW, +el: {lrows == Laws.crows(l) : U32}, +esum: {Nat.add(U32.to_nat(lrows), Laws.nrows(r)) == U32.to_nat(rows) : Nat},
  wl: Laws.HeadW(l, h), wr: Laws.HeadW(r, CH.Ch.ssub(h, lrows)))
  -> Laws.HeadW(CH.WN{rows, lrows, l, r}, h):
  (x, ex, wx, +cx, fx) = wl
  (y, ey, wy, +cy, fy) = wr
  %Equal.sym(CH.CW, CH.CW.head(l, h), x, ex) : HeadTop(h, rows, lrows, l, r, _, CH.CW.rows(CH.CW.head(r, CH.Ch.ssub(h, lrows))))
  %Equal.sym(CH.CW, CH.CW.head(r, CH.Ch.ssub(h, lrows)), y, ey) : HeadTop(h, rows, lrows, l, r, x, CH.CW.rows(_))
  hd_node2(h, rows, lrows, l, r, x, y, esum, wx, hd_nx(h, lrows, l, x, el, cx), fx, wy, cy, fy, rows_w(x), rows_w(y))

def Laws.cw_head(t, h, wf):
  match t:
    case CH.WL{+n, +d, a}:
      (fits, wfa) = wf
      (CH.WL{U32.min(h, n), d, a}, {==}, (Laws.u32_min_le(h, n, U32.shln(1, d), fits), wfa), min_nat(h, n), m => hm => {==})
    case CH.WN{+rows, +lrows, l, r}:
      (+el, +esum, wl, wr) = wf
      hd_node(h, rows, lrows, l, r, el, esum, Laws.cw_head(l, h, wl), Laws.cw_head(r, CH.Ch.ssub(h, lrows), wr))

# ==== the lockstep shape walk ===========================================================================

def eq_of_cmp(c: Cmp, +x: Word(32n), +y: Word(32n), e: {Word.cmp(32n, x, y) == c : Cmp}, h: {Cmp.is_eq(c) == True{} : Bool}) -> {U32{x} == U32{y} : U32}:
  match c:
    case EQ{}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y, L.word_cmp_eq(32n, x, y, e))
    case LT{}:
      Empty.absurd({U32{x} == U32{y} : U32}, L.false_true(h))
    case GT{}:
      Empty.absurd({U32{x} == U32{y} : U32}, L.false_true(h))

# U32.is_eq answers True only on equal words
def u32_eq_of_is_eq(a: U32, b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      eq_of_cmp(Word.cmp(32n, x, y), x, y, {==}, h)

def hc_of(c: Bool, -x: Bool, y: Bool, +ec: {c == x : Bool}, h: {Bool.and(c, y) == True{} : Bool}) -> {x == True{} : Bool}:
  %ec : {_ == True{} : Bool}
  L.and_left(c, y, h)

def fits_node_k(+rows: U32, +lrows: U32, +rows2: U32, +lrows2: U32, -l: CH.CW, -r: CH.CW, -sl: CH.Skel, -sr: CH.Skel, +c: Bool, +a: Bool, +b: Bool,
  +ec: {c == Bool.and(U32.is_eq(rows, rows2), U32.is_eq(lrows, lrows2)) : Bool},
  il: {a == True{} : Bool} -> {Laws.skel(l) == sl : CH.Skel}, ir: {b == True{} : Bool} -> {Laws.skel(r) == sr : CH.Skel},
  +h: {Bool.and(c, Bool.and(a, b)) == True{} : Bool})
  -> {CH.KNode{rows, lrows, Laws.skel(l), Laws.skel(r)} == CH.KNode{rows2, lrows2, sl, sr} : CH.Skel}:
  +hc = hc_of(c, Bool.and(U32.is_eq(rows, rows2), U32.is_eq(lrows, lrows2)), Bool.and(a, b), ec, h)
  +er = u32_eq_of_is_eq(rows, rows2, L.and_left(U32.is_eq(rows, rows2), U32.is_eq(lrows, lrows2), hc))
  +el = u32_eq_of_is_eq(lrows, lrows2, L.and_right(U32.is_eq(rows, rows2), U32.is_eq(lrows, lrows2), hc))
  +hab = L.and_right(c, Bool.and(a, b), h)
  %er : {CH.KNode{rows, lrows, Laws.skel(l), Laws.skel(r)} == CH.KNode{_, lrows2, sl, sr} : CH.Skel}
  %el : {CH.KNode{rows, lrows, Laws.skel(l), Laws.skel(r)} == CH.KNode{rows, _, sl, sr} : CH.Skel}
  %il(L.and_left(a, b, hab)) : {CH.KNode{rows, lrows, Laws.skel(l), Laws.skel(r)} == CH.KNode{rows, lrows, _, sr} : CH.Skel}
  %ir(L.and_right(a, b, hab)) : {CH.KNode{rows, lrows, Laws.skel(l), Laws.skel(r)} == CH.KNode{rows, lrows, Laws.skel(l), _} : CH.Skel}
  {==}

def fits_node(+rows: U32, +lrows: U32, +rows2: U32, +lrows2: U32, -l: CH.CW, -r: CH.CW, -sl: CH.Skel, -sr: CH.Skel, wl: Laws.FitsW(l, sl), wr: Laws.FitsW(r, sr))
  -> Laws.FitsW(CH.WN{rows, lrows, l, r}, CH.KNode{rows2, lrows2, sl, sr}):
  (l2, +a, ea, el2, il) = wl
  (r2, +b, eb, er2, ir) = wr
  %Equal.sym(CH.CW & Bool, CH.CW.fits(l, sl), (l2, a), ea) : &t2: CH.CW -> &ok: Bool -> {CH.CW.fits.j(Bool.and(U32.is_eq(rows, rows2), U32.is_eq(lrows, lrows2)), rows, lrows, _, CH.CW.fits(r, sr)) == (t2, ok) : CH.CW & Bool} & {t2 == CH.WN{rows, lrows, l, r} : CH.CW} & ({ok == True{} : Bool} -> {CH.KNode{rows, lrows, Laws.skel(l), Laws.skel(r)} == CH.KNode{rows2, lrows2, sl, sr} : CH.Skel})
  %Equal.sym(CH.CW & Bool, CH.CW.fits(r, sr), (r2, b), eb) : &t2: CH.CW -> &ok: Bool -> {CH.CW.fits.j(Bool.and(U32.is_eq(rows, rows2), U32.is_eq(lrows, lrows2)), rows, lrows, (l2, a), _) == (t2, ok) : CH.CW & Bool} & {t2 == CH.WN{rows, lrows, l, r} : CH.CW} & ({ok == True{} : Bool} -> {CH.KNode{rows, lrows, Laws.skel(l), Laws.skel(r)} == CH.KNode{rows2, lrows2, sl, sr} : CH.Skel})
  (CH.WN{rows, lrows, l2, r2}, Bool.and(Bool.and(U32.is_eq(rows, rows2), U32.is_eq(lrows, lrows2)), Bool.and(a, b)), {==}, (%el2 : {CH.WN{rows, lrows, l2, r2} == CH.WN{rows, lrows, _, r} : CH.CW}; %er2 : {CH.WN{rows, lrows, l2, r2} == CH.WN{rows, lrows, l2, _} : CH.CW}; {==}), h => fits_node_k(rows, lrows, rows2, lrows2, l, r, sl, sr, Bool.and(U32.is_eq(rows, rows2), U32.is_eq(lrows, lrows2)), a, b, {==}, il, ir, h))

def Laws.cw_fits(t, s):
  match t s:
    case CH.WL{+n, d, a} CH.KLeaf{+m}:
      (CH.WL{n, d, a}, U32.is_eq(n, m), {==}, {==}, h => Equal.cong(U32, CH.Skel, q => CH.KLeaf{q}, n, m, u32_eq_of_is_eq(n, m, h)))
    case CH.WL{n, d, a} CH.KNode{rows2, lrows2, sl, sr}:
      (CH.WL{n, d, a}, False{}, {==}, {==}, h => Empty.absurd({Laws.skel(CH.WL{n, d, a}) == CH.KNode{rows2, lrows2, sl, sr} : CH.Skel}, L.false_true(h)))
    case CH.WN{rows, lrows, l, r} CH.KLeaf{m}:
      (CH.WN{rows, lrows, l, r}, False{}, {==}, {==}, h => Empty.absurd({Laws.skel(CH.WN{rows, lrows, l, r}) == CH.KLeaf{m} : CH.Skel}, L.false_true(h)))
    case CH.WN{+rows, +lrows, l, r} CH.KNode{+rows2, +lrows2, sl, sr}:
      fits_node(rows, lrows, rows2, lrows2, l, r, sl, sr, Laws.cw_fits(l, sl), Laws.cw_fits(r, sr))
