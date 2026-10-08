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
