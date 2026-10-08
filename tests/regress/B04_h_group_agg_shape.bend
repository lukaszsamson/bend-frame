# B04-h (Astra G2): sum(x)/sum(y) is not an accepted group_by agg; the surface is
# narrower than "nine reducers" suggests (M1 doc, M3 example). DESIGN.md 15.2.4: an agg
# is Alias*(Agg{op, row-wise e}); anything else is InvalidOperation{"agg expects an
# aggregation: <Expr.show>"} (static: collect_schema reports it). The documented
# workaround (two named aggs, then with_columns) works. Pinned; passes today.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/schema.bend as S
import ./../../src/expr.bend as X
import ./../../src/join.bend as J
import ./../../src/groupby.bend as G
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def t() -> E.ResT(C.Frame):
  R.frame([R.mk("g", [R.u(1), R.u(1), R.u(2)], D.TU32{}), R.mk("x", [R.f(1.0), R.f(3.0), R.f(5.0)], D.TF32{}), R.mk("y", [R.f(2.0), R.f(2.0), R.f(4.0)], D.TF32{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def ratio() -> List<&2, X.Expr>:
  [DF.alias(DF.div(DF.sum(DF.col("x")), DF.sum(DF.col("y"))), "r")]

def two() -> List<&2, X.Expr>:
  [DF.alias(DF.sum(DF.col("x")), "sx"), DF.alias(DF.sum(DF.col("y")), "sy")]

def r() -> List<&2, X.Expr>:
  [DF.alias(DF.div(DF.col("sx"), DF.col("sy")), "r")]

def main() -> IO(Unit):
  do IO<Unit>:
    R.three("B04-h ratio-agg", R.e_group(t(), [DF.col("g")], ratio()), DF.lazy_group_by(src(), [DF.col("g")], ratio()), env(), env())
    IO.print(R.schema("B04-h ratio-agg", DF.lazy_group_by(src(), [DF.col("g")], ratio())))
    R.three("B04-h workaround", R.e_with(R.e_group(t(), [DF.col("g")], two()), r()), DF.lazy_with_columns(DF.lazy_group_by(src(), [DF.col("g")], two()), r()), env(), env())
#|-- B04-h ratio-agg eager
#|error	InvalidOperation: agg expects an aggregation: (col("x").sum() / col("y").sum()).alias("r")
#|
#|-- B04-h ratio-agg raw
#|error	InvalidOperation: agg expects an aggregation: (col("x").sum() / col("y").sum()).alias("r")
#|
#|-- B04-h ratio-agg opt
#|error	InvalidOperation: agg expects an aggregation: (col("x").sum() / col("y").sum()).alias("r")
#|
#|-- B04-h ratio-agg schema
#|error: InvalidOperation: agg expects an aggregation: (col("x").sum() / col("y").sum()).alias("r")
#|
#|-- B04-h workaround eager
#|frame
#|height	2
#|width	4
#|col	u32	"g"
#|col	f32	"sx"
#|col	f32	"sy"
#|col	f32	"r"
#|row	1	0x40800000	0x40800000	0x3f800000
#|row	2	0x40a00000	0x40800000	0x3fa00000
#|
#|-- B04-h workaround raw
#|frame
#|height	2
#|width	4
#|col	u32	"g"
#|col	f32	"sx"
#|col	f32	"sy"
#|col	f32	"r"
#|row	1	0x40800000	0x40800000	0x3f800000
#|row	2	0x40a00000	0x40800000	0x3fa00000
#|
#|-- B04-h workaround opt
#|frame
#|height	2
#|width	4
#|col	u32	"g"
#|col	f32	"sx"
#|col	f32	"sy"
#|col	f32	"r"
#|row	1	0x40800000	0x40800000	0x3f800000
#|row	2	0x40a00000	0x40800000	0x3fa00000
#|
