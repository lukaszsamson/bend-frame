#! xfail B03-a
# B03-a (Astra C): grouped mean of [inf, 1] is NaN (Kahan computes inf - inf).
# DESIGN.md 15.5.3: Neumaier compensation while the partial sum is finite, plain IEEE add
# once it is not, rows in ascending order within a group. Expected means per group:
#   1 [inf, 1] -> inf   2 [1, inf] -> inf   3 [inf, -inf] -> NaN   4 [NaN, 1] -> NaN
#   5 [1e8, 1, -1e8] -> 1/3 (Neumaier sum 1; Kahan gives 0)   6 [null, null] -> null
# Polars 2.0.0 group_by mean agrees on every group (regress_expect.py).
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def t() -> E.ResT(C.Frame):
  R.frame([
    R.mk("g", [R.u(1), R.u(1), R.u(2), R.u(2), R.u(3), R.u(3), R.u(4), R.u(4), R.u(5), R.u(5), R.u(5), R.u(6), R.u(6)], D.TU32{}),
    R.mk("x", [R.f(R.inf()), R.f(1.0), R.f(1.0), R.f(R.inf()), R.f(R.inf()), R.f(R.ninf()), R.f(R.nan()), R.f(1.0), R.f(100000000.0), R.f(1.0), R.f(F32.neg(100000000.0)), R.null(), R.null()], D.TF32{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def keys() -> List<&2, X.Expr>:
  [DF.col("g")]

def aggs() -> List<&2, X.Expr>:
  [DF.alias(DF.mean(DF.col("x")), "m")]

def main() -> IO(Unit):
  do IO<Unit>:
    R.three("B03-a group-mean", R.e_group(t(), keys(), aggs()), DF.lazy_group_by(src(), keys(), aggs()), env(), env())
#|-- B03-a group-mean eager
#|frame
#|height	6
#|width	2
#|col	u32	"g"
#|col	f32	"m"
#|row	1	0x7f800000
#|row	2	0x7f800000
#|row	3	0x7fc00000
#|row	4	0x7fc00000
#|row	5	0x3eaaaaab
#|row	6	null
#|
#|-- B03-a group-mean raw
#|frame
#|height	6
#|width	2
#|col	u32	"g"
#|col	f32	"m"
#|row	1	0x7f800000
#|row	2	0x7f800000
#|row	3	0x7fc00000
#|row	4	0x7fc00000
#|row	5	0x3eaaaaab
#|row	6	null
#|
#|-- B03-a group-mean opt
#|frame
#|height	6
#|width	2
#|col	u32	"g"
#|col	f32	"m"
#|row	1	0x7f800000
#|row	2	0x7f800000
#|row	3	0x7fc00000
#|row	4	0x7fc00000
#|row	5	0x3eaaaaab
#|row	6	null
#|
