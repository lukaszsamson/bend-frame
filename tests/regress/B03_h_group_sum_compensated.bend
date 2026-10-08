#! xfail B03-h
# B03-h (Fable B5, Astra 1): grouped f32 sum is a plain sequential add. DESIGN.md 15.5.3:
# group sums use the Neumaier step of every f32 sum, rows in ascending order. Groups:
#   1 ten 0.1 -> 0x3f800000 (1.0; sequential f32 gives 0x3f800001)
#   2 [1e8, 1, -1e8] -> 1.0 (sequential gives 0)
#   3 [inf, 1] -> inf
# Polars 2.0.0 eager answers 0x3f800001 for group 1 (contract: we match the f64 reference,
# not Polars' bits; documented in 15.5.3), 1.0 for group 2, inf for group 3. The eager
# sum over the ten 0.1 is the same accumulation: 0x3f800000.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def tenth() -> D.Scalar:
  R.f(0.1)

def t() -> E.ResT(C.Frame):
  R.frame([
    R.mk("g", [R.u(1), R.u(1), R.u(1), R.u(1), R.u(1), R.u(1), R.u(1), R.u(1), R.u(1), R.u(1), R.u(2), R.u(2), R.u(2), R.u(3), R.u(3)], D.TU32{}),
    R.mk("x", [tenth(), tenth(), tenth(), tenth(), tenth(), tenth(), tenth(), tenth(), tenth(), tenth(), R.f(100000000.0), R.f(1.0), R.f(F32.neg(100000000.0)), R.f(R.inf()), R.f(1.0)], D.TF32{})])

def ten() -> E.ResT(C.Frame):
  R.frame([R.mk("x", [tenth(), tenth(), tenth(), tenth(), tenth(), tenth(), tenth(), tenth(), tenth(), tenth()], D.TF32{})])

def keys() -> List<&2, X.Expr>:
  [DF.col("g")]

def aggs() -> List<&2, X.Expr>:
  [DF.alias(DF.sum(DF.col("x")), "s")]

def main() -> IO(Unit):
  do IO<Unit>:
    R.three("B03-h group-sum", R.e_group(t(), keys(), aggs()), DF.lazy_group_by(R.src("t", t()), keys(), aggs()), R.env1("t", t()), R.env1("t", t()))
    R.three("B03-h eager-sum-ten-tenths", R.e_select(ten(), aggs()), DF.lazy_select(R.src("t", ten()), aggs()), R.env1("t", ten()), R.env1("t", ten()))
#|-- B03-h group-sum eager
#|frame
#|height	3
#|width	2
#|col	u32	"g"
#|col	f32	"s"
#|row	1	0x3f800000
#|row	2	0x3f800000
#|row	3	0x7f800000
#|
#|-- B03-h group-sum raw
#|frame
#|height	3
#|width	2
#|col	u32	"g"
#|col	f32	"s"
#|row	1	0x3f800000
#|row	2	0x3f800000
#|row	3	0x7f800000
#|
#|-- B03-h group-sum opt
#|frame
#|height	3
#|width	2
#|col	u32	"g"
#|col	f32	"s"
#|row	1	0x3f800000
#|row	2	0x3f800000
#|row	3	0x7f800000
#|
#|-- B03-h eager-sum-ten-tenths eager
#|frame
#|height	1
#|width	1
#|col	f32	"s"
#|row	0x3f800000
#|
#|-- B03-h eager-sum-ten-tenths raw
#|frame
#|height	1
#|width	1
#|col	f32	"s"
#|row	0x3f800000
#|
#|-- B03-h eager-sum-ten-tenths opt
#|frame
#|height	1
#|width	1
#|col	f32	"s"
#|row	0x3f800000
#|
