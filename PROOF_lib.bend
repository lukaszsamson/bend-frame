# PROOF_lib.bend -- the proof toolkit shared by every PROOF_*.bend (DESIGN.md
# section 8): injectivity and refutation lemmas, Bool.and facts, and the
# number lemmas (Word / U32 comparison, String.eq) the other files build on.
#
# Toolkit (probes p08/p20): a goal that both sides compute to is `{==}`;
# `%e : P` rewrites the goal with `e : {a == b : T}` (P is the goal with `_`
# marking b, and becomes P with a there), so a hypothesis `h : {f(p) == Done{s}}`
# is flipped with Equal.sym before it replaces f(p); `Done` is injective through
# Equal.cong + Result.default; `Fail == Done` and `False == True` are refuted
# through a motive (Fail/False -> Unit, Done/True -> Empty) and Empty.absurd; a
# value the code computes (a dtype lookup, a sub-plan's schema) is passed to a
# lemma as a PARAMETER and matched there; a hypothesis that must be rewritten
# moves into the goal as a function type (`H -> G`), is rewritten there, and is
# taken back with `h => ...`.
import Base
import ./src/dtype.bend as D
import ./src/err.bend as E
import ./src/kernels.bend as K
import ./src/column.bend as C
import ./src/schema.bend as S
import ./src/expr.bend as X
import ./src/analysis.bend as A
import ./src/sort.bend as O
import ./src/plan.bend as P
import ./LAWS.bend as Laws

# ---- toolkit --------------------------------------------------------------------

# Done is injective: the payload, read back through a default
def done_inj(-A: Data, -xs: A, -ys: A, e: {Done{xs} == Done{ys} : E.Res(A)}) -> {xs == ys : A}:
  Equal.cong(E.Res(A), A, r => Result.default(&2, &2, E.Err, A, r, xs), Done{xs}, Done{ys}, e)

# the motive that refutes Fail == Done
def res_disc(-A: Data, r: E.Res(A)) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{x}:
      Empty

def fail_done(-A: Data, -e: E.Err, -x: A, h: {Fail{e} == Done{x} : E.Res(A)}) -> Empty:
  %h : res_disc(A, _)
  Unit{}

# the motive that refutes False == True
def bool_disc(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def false_true(h: {False{} == True{} : Bool}) -> Empty:
  %h : bool_disc(_)
  Unit{}

# the motive that refutes True == False
def bool_disc_t(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def true_false(h: {True{} == False{} : Bool}) -> Empty:
  %h : bool_disc_t(_)
  Unit{}

# Bool.not(b) == True gives b == False
def not_true(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, false_true(h))
    case False{}:
      {==}

# both True gives Bool.and True
def and_true(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

# Bool.and(a, b) == True gives both
def and_left(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def and_right(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, false_true(h))

# =====================================================================================
# 6. I32
# =====================================================================================

def Laws.i32_add_comm(a, b):
  match a b:
    case D.I32{x} D.I32{y}:
      Equal.cong(U32, D.I32, w => D.I32{w}, U32.add(x, y), U32.add(y, x), U32.add_comm(x, y))

def Laws.i32_bits_roundtrip(a):
  match a:
    case D.I32{x}:
      {==}

# =====================================================================================
# 7. Names and numbers: Word / U32 comparison, U32.min, String.eq (LAWS.bend section 7)
# =====================================================================================
#
# U32 is Word(32n), a 32-bit little-endian word of Bools (head = least
# significant bit); Word.cmp compares the tail first. Every lemma is an
# induction over the word length n with the comparison of the tails passed as
# a parameter (the p08 idiom), so nothing here is an axiom.

# the three-valued refutations
def cmp_disc_eq(c: Cmp) -> Type:
  match c:
    case EQ{}:
      Empty
    case o:
      Unit

def lt_eq(h: {LT{} == EQ{} : Cmp}) -> Empty:
  %h : cmp_disc_eq(_)
  Unit{}

def gt_eq(h: {GT{} == EQ{} : Cmp}) -> Empty:
  %h : cmp_disc_eq(_)
  Unit{}

def cmp_disc_lt(c: Cmp) -> Type:
  match c:
    case LT{}:
      Empty
    case o:
      Unit

def eq_lt(h: {EQ{} == LT{} : Cmp}) -> Empty:
  %h : cmp_disc_lt(_)
  Unit{}

def gt_lt(h: {GT{} == LT{} : Cmp}) -> Empty:
  %h : cmp_disc_lt(_)
  Unit{}

# the opposite verdict
def cmp_flip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

def bool_cmp_refl(b: Bool) -> {Bool.cmp(b, b) == EQ{} : Cmp}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def bool_cmp_eq(a: Bool, b: Bool, h: {Bool.cmp(a, b) == EQ{} : Cmp}) -> {a == b : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case True{} True{}:
      {==}
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, lt_eq(h))
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, gt_eq(h))

def bool_cmp_flip(a: Bool, b: Bool) -> {Bool.cmp(b, a) == cmp_flip(Bool.cmp(a, b)) : Cmp}:
  match a b:
    case False{} False{}:
      {==}
    case True{} True{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}

# Bool.cmp(a, b) = LT and Bool.cmp(b, c) = LT is impossible
def bool_lt_lt(a: Bool, b: Bool, c: Bool, h1: {Bool.cmp(a, b) == LT{} : Cmp}, h2: {Bool.cmp(b, c) == LT{} : Cmp}) -> Empty:
  match a b c:
    case False{} True{} False{}:
      gt_lt(h2)
    case False{} True{} True{}:
      eq_lt(h2)
    case False{} False{} _:
      eq_lt(h1)
    case True{} _ _:
      match b:
        case False{}:
          gt_lt(h1)
        case True{}:
          eq_lt(h1)

# ---- Word.cmp: reflexive, EQ means equal, antisymmetric (flip), LT transitive ----

def word_cmp_refl(n: Nat, x: Word(n)) -> {Word.cmp(n, x, x) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match x:
        case WCon{b, t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, word_cmp_refl(p, t)) : {Word.cmp.fin(b, b, _) == EQ{} : Cmp}
          bool_cmp_refl(b)

def word_eq_step(-p: Nat, a: Bool, b: Bool, -t: Word(p), -u: Word(p), c: Cmp, e: {Word.cmp(p, t, u) == c : Cmp}, h: {Word.cmp.fin(a, b, c) == EQ{} : Cmp},
  ih: {Word.cmp(p, t, u) == EQ{} : Cmp} -> {t == u : Word(p)}) -> {WCon{a, t} == WCon{b, u} : Word(1n+p)}:
  match c:
    case LT{}:
      Empty.absurd({WCon{a, t} == WCon{b, u} : Word(1n+p)}, lt_eq(h))
    case GT{}:
      Empty.absurd({WCon{a, t} == WCon{b, u} : Word(1n+p)}, gt_eq(h))
    case EQ{}:
      %ih(e) : {WCon{a, t} == WCon{b, _} : Word(1n+p)}
      %bool_cmp_eq(a, b, h) : {WCon{a, t} == WCon{_, t} : Word(1n+p)}
      {==}

def word_cmp_eq(n: Nat, x: Word(n), y: Word(n), h: {Word.cmp(n, x, y) == EQ{} : Cmp}) -> {x == y : Word(n)}:
  match n:
    case 0n:
      match x y:
        case WNil{} WNil{}:
          {==}
    case 1n++p:
      match x y:
        case WCon{+a, +t} WCon{+b, +u}:
          word_eq_step(p, a, b, t, u, Word.cmp(p, t, u), {==}, h, e => word_cmp_eq(p, t, u, e))

def word_flip_step(a: Bool, b: Bool, c: Cmp) -> {Word.cmp.fin(b, a, cmp_flip(c)) == cmp_flip(Word.cmp.fin(a, b, c)) : Cmp}:
  match c:
    case LT{}:
      {==}
    case GT{}:
      {==}
    case EQ{}:
      bool_cmp_flip(a, b)

# comparing the other way round gives the opposite verdict
def word_cmp_flip(n: Nat, x: Word(n), y: Word(n)) -> {Word.cmp(n, y, x) == cmp_flip(Word.cmp(n, x, y)) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      match x y:
        case WCon{+a, +t} WCon{+b, +u}:
          %Equal.sym(Cmp, Word.cmp(p, u, t), cmp_flip(Word.cmp(p, t, u)), word_cmp_flip(p, t, u)) : {Word.cmp.fin(b, a, _) == cmp_flip(Word.cmp.fin(a, b, Word.cmp(p, t, u))) : Cmp}
          word_flip_step(a, b, Word.cmp(p, t, u))

def word_lt_step(-p: Nat, a: Bool, b: Bool, c: Bool, -t: Word(p), -u: Word(p), -v: Word(p),
  c1: Cmp, c2: Cmp,
  e1: {Word.cmp(p, t, u) == c1 : Cmp}, e2: {Word.cmp(p, u, v) == c2 : Cmp},
  h1: {Word.cmp.fin(a, b, c1) == LT{} : Cmp}, h2: {Word.cmp.fin(b, c, c2) == LT{} : Cmp},
  ih: {Word.cmp(p, t, u) == LT{} : Cmp} -> {Word.cmp(p, u, v) == LT{} : Cmp} -> {Word.cmp(p, t, v) == LT{} : Cmp},
  eqtu: {Word.cmp(p, t, u) == EQ{} : Cmp} -> {t == u : Word(p)},
  equv: {Word.cmp(p, u, v) == EQ{} : Cmp} -> {u == v : Word(p)})
  -> {Word.cmp.fin(a, c, Word.cmp(p, t, v)) == LT{} : Cmp}:
  match c1 c2:
    case GT{} _:
      Empty.absurd({Word.cmp.fin(a, c, Word.cmp(p, t, v)) == LT{} : Cmp}, gt_lt(h1))
    case _ GT{}:
      Empty.absurd({Word.cmp.fin(a, c, Word.cmp(p, t, v)) == LT{} : Cmp}, gt_lt(h2))
    case LT{} LT{}:
      %Equal.sym(Cmp, Word.cmp(p, t, v), LT{}, ih(e1, e2)) : {Word.cmp.fin(a, c, _) == LT{} : Cmp}
      {==}
    case LT{} EQ{}:
      %equv(e2) : {Word.cmp.fin(a, c, Word.cmp(p, t, _)) == LT{} : Cmp}
      %Equal.sym(Cmp, Word.cmp(p, t, u), LT{}, e1) : {Word.cmp.fin(a, c, _) == LT{} : Cmp}
      {==}
    case EQ{} LT{}:
      %Equal.sym(Word(p), t, u, eqtu(e1)) : {Word.cmp.fin(a, c, Word.cmp(p, _, v)) == LT{} : Cmp}
      %Equal.sym(Cmp, Word.cmp(p, u, v), LT{}, e2) : {Word.cmp.fin(a, c, _) == LT{} : Cmp}
      {==}
    case EQ{} EQ{}:
      Empty.absurd({Word.cmp.fin(a, c, Word.cmp(p, t, v)) == LT{} : Cmp}, bool_lt_lt(a, b, c, h1, h2))

def word_lt_trans(n: Nat, x: Word(n), y: Word(n), z: Word(n), h1: {Word.cmp(n, x, y) == LT{} : Cmp}, h2: {Word.cmp(n, y, z) == LT{} : Cmp}) -> {Word.cmp(n, x, z) == LT{} : Cmp}:
  match n:
    case 0n:
      Empty.absurd({Word.cmp(0n, x, z) == LT{} : Cmp}, eq_lt(h1))
    case 1n++p:
      match x y z:
        case WCon{+a, +t} WCon{+b, +u} WCon{+c, +v}:
          word_lt_step(p, a, b, c, t, u, v, Word.cmp(p, t, u), Word.cmp(p, u, v), {==}, {==}, h1, h2, f1 => f2 => word_lt_trans(p, t, u, v, f1, f2), e => word_cmp_eq(p, t, u, e), e => word_cmp_eq(p, u, v, e))

# cmp(x, y) == GT gives cmp(y, x) == LT
def word_gt_lt(+n: Nat, +x: Word(n), +y: Word(n), h: {Word.cmp(n, x, y) == GT{} : Cmp}) -> {Word.cmp(n, y, x) == LT{} : Cmp}:
  %Equal.sym(Cmp, Word.cmp(n, y, x), cmp_flip(Word.cmp(n, x, y)), word_cmp_flip(n, x, y)) : {_ == LT{} : Cmp}
  %Equal.sym(Cmp, Word.cmp(n, x, y), GT{}, h) : {cmp_flip(_) == LT{} : Cmp}
  {==}

# cmp(y, x) == LT gives cmp(x, y) == GT
def word_lt_gt(+n: Nat, +x: Word(n), +y: Word(n), h: {Word.cmp(n, y, x) == LT{} : Cmp}) -> {Word.cmp(n, x, y) == GT{} : Cmp}:
  %Equal.sym(Cmp, Word.cmp(n, x, y), cmp_flip(Word.cmp(n, y, x)), word_cmp_flip(n, y, x)) : {_ == GT{} : Cmp}
  %Equal.sym(Cmp, Word.cmp(n, y, x), LT{}, h) : {cmp_flip(_) == GT{} : Cmp}
  {==}

# GT transitivity, through flip and LT transitivity
def word_gt_trans(+n: Nat, +x: Word(n), +y: Word(n), +z: Word(n), h1: {Word.cmp(n, x, y) == GT{} : Cmp}, h2: {Word.cmp(n, y, z) == GT{} : Cmp}) -> {Word.cmp(n, x, z) == GT{} : Cmp}:
  word_lt_gt(n, x, z, word_lt_trans(n, z, y, x, word_gt_lt(n, y, z, h2), word_gt_lt(n, x, y, h1)))

# ---- U32.min: commutative and associative ----

# pick by c and by its flip agree once x == y is known for EQ
def min_comm_k(+x: Word(32n), +y: Word(32n), c: Cmp, e: {Word.cmp(32n, x, y) == c : Cmp}) -> {Bool.pick(U32, Cmp.is_lt(c), U32{x}, U32{y}) == Bool.pick(U32, Cmp.is_lt(cmp_flip(c)), U32{y}, U32{x}) : U32}:
  match c:
    case LT{}:
      {==}
    case GT{}:
      {==}
    case EQ{}:
      %Equal.sym(Word(32n), x, y, word_cmp_eq(32n, x, y, e)) : {U32{y} == U32{_} : U32}
      {==}

def Laws.u32_min_comm(a, b):
  match a b:
    case U32{+x} U32{+y}:
      %Equal.sym(Cmp, Word.cmp(32n, y, x), cmp_flip(Word.cmp(32n, x, y)), word_cmp_flip(32n, x, y)) : {Bool.pick(U32, Cmp.is_lt(Word.cmp(32n, x, y)), U32{x}, U32{y}) == Bool.pick(U32, Cmp.is_lt(_), U32{y}, U32{x}) : U32}
      min_comm_k(x, y, Word.cmp(32n, x, y), {==})

# min(x, min(y, z)) == min(min(x, y), z) with c1 = cmp(x, y) and c2 = cmp(y, z) as parameters
def min_assoc_k(+x: Word(32n), +y: Word(32n), +z: Word(32n), c1: Cmp, c2: Cmp, +e1: {Word.cmp(32n, x, y) == c1 : Cmp}, +e2: {Word.cmp(32n, y, z) == c2 : Cmp})
  -> {U32.min(U32{x}, Bool.pick(U32, Cmp.is_lt(c2), U32{y}, U32{z})) == U32.min(Bool.pick(U32, Cmp.is_lt(c1), U32{x}, U32{y}), U32{z}) : U32}:
  match c1 c2:
    case LT{} LT{}:
      %Equal.sym(Cmp, Word.cmp(32n, x, y), LT{}, e1) : {Bool.pick(U32, Cmp.is_lt(_), U32{x}, U32{y}) == U32.min(U32{x}, U32{z}) : U32}
      %Equal.sym(Cmp, Word.cmp(32n, x, z), LT{}, word_lt_trans(32n, x, y, z, e1, e2)) : {U32{x} == Bool.pick(U32, Cmp.is_lt(_), U32{x}, U32{z}) : U32}
      {==}
    case EQ{} LT{}:
      %Equal.sym(Cmp, Word.cmp(32n, x, y), EQ{}, e1) : {Bool.pick(U32, Cmp.is_lt(_), U32{x}, U32{y}) == U32.min(U32{y}, U32{z}) : U32}
      %Equal.sym(Cmp, Word.cmp(32n, y, z), LT{}, e2) : {U32{y} == Bool.pick(U32, Cmp.is_lt(_), U32{y}, U32{z}) : U32}
      {==}
    case GT{} LT{}:
      %Equal.sym(Cmp, Word.cmp(32n, x, y), GT{}, e1) : {Bool.pick(U32, Cmp.is_lt(_), U32{x}, U32{y}) == U32.min(U32{y}, U32{z}) : U32}
      %Equal.sym(Cmp, Word.cmp(32n, y, z), LT{}, e2) : {U32{y} == Bool.pick(U32, Cmp.is_lt(_), U32{y}, U32{z}) : U32}
      {==}
    case LT{} EQ{}:
      {==}
    case LT{} GT{}:
      {==}
    case EQ{} EQ{}:
      %Equal.sym(Word(32n), x, y, word_cmp_eq(32n, x, y, e1)) : {Bool.pick(U32, Cmp.is_lt(Word.cmp(32n, _, z)), U32{_}, U32{z}) == U32.min(U32{y}, U32{z}) : U32}
      {==}
    case EQ{} GT{}:
      %Equal.sym(Word(32n), x, y, word_cmp_eq(32n, x, y, e1)) : {Bool.pick(U32, Cmp.is_lt(Word.cmp(32n, _, z)), U32{_}, U32{z}) == U32.min(U32{y}, U32{z}) : U32}
      {==}
    case GT{} EQ{}:
      %word_cmp_eq(32n, y, z, e2) : {Bool.pick(U32, Cmp.is_lt(Word.cmp(32n, x, _)), U32{x}, U32{_}) == U32.min(U32{y}, U32{_}) : U32}
      %Equal.sym(Cmp, Word.cmp(32n, x, y), GT{}, e1) : {Bool.pick(U32, Cmp.is_lt(_), U32{x}, U32{y}) == Bool.pick(U32, Cmp.is_lt(Word.cmp(32n, y, y)), U32{y}, U32{y}) : U32}
      %Equal.sym(Cmp, Word.cmp(32n, y, y), EQ{}, word_cmp_refl(32n, y)) : {U32{y} == Bool.pick(U32, Cmp.is_lt(_), U32{y}, U32{y}) : U32}
      {==}
    case GT{} GT{}:
      %Equal.sym(Cmp, Word.cmp(32n, x, z), GT{}, word_gt_trans(32n, x, y, z, e1, e2)) : {Bool.pick(U32, Cmp.is_lt(_), U32{x}, U32{z}) == U32.min(U32{y}, U32{z}) : U32}
      %Equal.sym(Cmp, Word.cmp(32n, y, z), GT{}, e2) : {U32{z} == Bool.pick(U32, Cmp.is_lt(_), U32{y}, U32{z}) : U32}
      {==}

def Laws.u32_min_assoc(a, b, c):
  match a b c:
    case U32{+x} U32{+y} U32{+z}:
      min_assoc_k(x, y, z, Word.cmp(32n, x, y), Word.cmp(32n, y, z), {==}, {==})

# ---- String.eq: reflexive and sound (the runtime name equality of Names.has, Schema.find, Env.take, Opt.ren.find) ----

def chr_cmp_refl(c: Char) -> {Char.cmp(c, c) == ((c, c), EQ{}) : (Char & Char) & Cmp}:
  match c:
    case Chr{U32{x}}:
      %Equal.sym(Cmp, Word.cmp(32n, x, x), EQ{}, word_cmp_refl(32n, x)) : {((Chr{U32{x}}, Chr{U32{x}}), _) == ((Chr{U32{x}}, Chr{U32{x}}), EQ{}) : (Char & Char) & Cmp}
      {==}

def str_cmp_refl(s: String) -> {String.cmp(s, s) == ((s, s), EQ{}) : (String & String) & Cmp}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Equal.sym((Char & Char) & Cmp, Char.cmp(h, h), ((h, h), EQ{}), chr_cmp_refl(h)) : {String.cmp.fin(t, t, _) == ((SCon{h, t}, SCon{h, t}), EQ{}) : (String & String) & Cmp}
      %Equal.sym((String & String) & Cmp, String.cmp(t, t), ((t, t), EQ{}), str_cmp_refl(t)) : {String.cmp.rec(h, h, _) == ((SCon{h, t}, SCon{h, t}), EQ{}) : (String & String) & Cmp}
      {==}

def Laws.str_eq_refl(s):
  %Equal.sym((String & String) & Cmp, String.cmp(s, s), ((s, s), EQ{}), str_cmp_refl(s)) : {Cmp.is_eq(Pair.snd(String & String, Cmp, _)) == True{} : Bool}
  {==}

# the tail step: rr is String.cmp(t1, t2)
def str_sound_rec(-h1: Char, -h2: Char, -t1: String, -t2: String, rr: (String & String) & Cmp, e: {String.cmp(t1, t2) == rr : (String & String) & Cmp},
  ih: {String.eq(t1, t2) == True{} : Bool} -> {t1 == t2 : String})
  -> {Cmp.is_eq(Pair.snd(String & String, Cmp, String.cmp.rec(h1, h2, rr))) == True{} : Bool} -> {t1 == t2 : String}:
  ((t1b, t2b), r) = rr
  h => ih((%Equal.sym((String & String) & Cmp, String.cmp(t1, t2), ((t1b, t2b), r), e) : {Cmp.is_eq(Pair.snd(String & String, Cmp, _)) == True{} : Bool}; h))

# the head step: c is Word.cmp(32n, x, y)
def str_sound_step(+x: Word(32n), +y: Word(32n), +t1: String, +t2: String, c: Cmp, e: {Word.cmp(32n, x, y) == c : Cmp},
  ih: {String.eq(t1, t2) == True{} : Bool} -> {t1 == t2 : String})
  -> {Cmp.is_eq(Pair.snd(String & String, Cmp, String.cmp.fin(t1, t2, ((Chr{U32{x}}, Chr{U32{y}}), c)))) == True{} : Bool} -> {SCon{Chr{U32{x}}, t1} == SCon{Chr{U32{y}}, t2} : String}:
  match c:
    case LT{}:
      h => Empty.absurd({SCon{Chr{U32{x}}, t1} == SCon{Chr{U32{y}}, t2} : String}, false_true(h))
    case GT{}:
      h => Empty.absurd({SCon{Chr{U32{x}}, t1} == SCon{Chr{U32{y}}, t2} : String}, false_true(h))
    case EQ{}:
      h =>
        %word_cmp_eq(32n, x, y, e) : {SCon{Chr{U32{x}}, t1} == SCon{Chr{U32{_}}, t2} : String}
        %str_sound_rec(Chr{U32{x}}, Chr{U32{y}}, t1, t2, String.cmp(t1, t2), {==}, ih)(h) : {SCon{Chr{U32{x}}, t1} == SCon{Chr{U32{x}}, _} : String}
        {==}

def Laws.str_eq_sound(a, b, h):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h2, t2}:
      Empty.absurd({SNil{} == SCon{h2, t2} : String}, false_true(h))
    case SCon{h1, t1} SNil{}:
      Empty.absurd({SCon{h1, t1} == SNil{} : String}, false_true(h))
    case SCon{Chr{U32{+x}}, +t1} SCon{Chr{U32{+y}}, +t2}:
      str_sound_step(x, y, t1, t2, Word.cmp(32n, x, y), {==}, e => Laws.str_eq_sound(t1, t2, e))(h)

# the name just added is found (Names.has, used by Names.dup and the schema checks)
def Laws.names_has_head(ns, n):
  %Equal.sym(Bool, String.eq(n, n), True{}, Laws.str_eq_refl(n)) : {Bool.or(_, C.Names.has(ns, n)) == True{} : Bool}
  {==}
