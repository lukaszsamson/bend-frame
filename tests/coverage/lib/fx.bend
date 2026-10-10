# tests/coverage/lib/fx.bend -- fixture frames of the T6 coverage tests (scripts/coverage_matrix.py).
# Not a test itself: its main prints nothing. The same frames are built by bench/coverage/fx.py
# (Polars) so that each expectation can be checked against Polars 2.0.0.
#
#   t(): 7 rows, every dtype with nulls, NaN, inf, -0.0, MIN, MAX
#     a u32  7 0 4294967295 null 5 1 2          b u32  2 3 1 1 null 0 0
#     p i32  7 -7 7 -7 MIN null 0               q i32  2 2 -2 -2 -1 1 0
#     x f32  1.5 -2.0 null NaN inf 0.0 -0.0     y f32  2.0 0.5 1.0 1.0 inf 0.0 null
#     k bool T F null T F T null                s  str "a" "" "é" null "abc" "ab" "a"
#   z(): the same schema, zero rows
import Base
import ./../../../frame.bend as DF
import ./../../../src/dtype.bend as D
import ./../../../src/err.bend as E
import ./../../../src/column.bend as C
import ./../../../src/plan.bend as P
import ./../../regress/lib/rx.bend as R

def t() -> E.ResT(C.Frame):
  R.frame([
    R.mk("a", [R.u(7), R.u(0), R.u(4294967295), R.null(), R.u(5), R.u(1), R.u(2)], D.TU32{}),
    R.mk("b", [R.u(2), R.u(3), R.u(1), R.u(1), R.null(), R.u(0), R.u(0)], D.TU32{}),
    R.mk("p", [R.i(7), R.ineg(7), R.i(7), R.ineg(7), R.ineg(2147483648), R.null(), R.i(0)], D.TI32{}),
    R.mk("q", [R.i(2), R.i(2), R.ineg(2), R.ineg(2), R.ineg(1), R.i(1), R.i(0)], D.TI32{}),
    R.mk("x", [R.f(1.5), R.f(F32.neg(2.0)), R.null(), R.f(R.nan()), R.f(R.inf()), R.f(0.0), R.f(R.nzero())], D.TF32{}),
    R.mk("y", [R.f(2.0), R.f(0.5), R.f(1.0), R.f(1.0), R.f(R.inf()), R.f(0.0), R.null()], D.TF32{}),
    R.mk("k", [R.b(True{}), R.b(False{}), R.null(), R.b(True{}), R.b(False{}), R.b(True{}), R.null()], D.TBool{}),
    R.mk("s", [R.s("a"), R.s(""), R.s("é"), R.null(), R.s("abc"), R.s("ab"), R.s("a")], D.TStr{})])

def z() -> E.ResT(C.Frame):
  R.frame([
    R.mk("a", [], D.TU32{}),
    R.mk("b", [], D.TU32{}),
    R.mk("p", [], D.TI32{}),
    R.mk("q", [], D.TI32{}),
    R.mk("x", [], D.TF32{}),
    R.mk("y", [], D.TF32{}),
    R.mk("k", [], D.TBool{}),
    R.mk("s", [], D.TStr{})])

# one-frame environments (a collect consumes its env: build one per run)
def envt() -> P.Env:
  R.env1("t", t())

def envz() -> P.Env:
  R.env1("z", z())

def srct() -> P.Plan:
  R.src("t", t())

def srcz() -> P.Plan:
  R.src("z", z())

def main() -> IO(Unit):
  IO.pure(Unit, Unit{})
