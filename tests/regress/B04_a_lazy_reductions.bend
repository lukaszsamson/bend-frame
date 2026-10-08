# B04-a (Fable B6, Astra G1): eager accepts global reductions in select / with_columns /
# filter, lazy refuses them ("aggregation in select (v1: use group_by)"). DESIGN.md
# 15.2.5 and 15.4 C6, C8-C13, C16, C17: reductions are allowed at any depth in both APIs,
# select height is 1 when no expression is KRow, 1-row outputs broadcast, filter and
# with_columns reduce over the full input first. collect_schema accepts them too.
# Polars 2.0.0: bench/contract/cardinality.py (u32 a; C11/C16 here use the f32 column x,
# since a - mean(a) mixes u32 and f32, a TypeMismatch under strict typing).
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
  R.frame([R.mk("a", [R.u(1), R.u(2), R.u(3)], D.TU32{}), R.mk("x", [R.f(1.0), R.f(2.0), R.f(3.0)], D.TF32{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def a() -> X.Expr:
  DF.col("a")

def x() -> X.Expr:
  DF.col("x")

def sel(+tag: String, +es: List<&2, X.Expr>) -> IO(Unit):
  do IO<Unit>:
    R.three(tag, R.e_select(t(), es), DF.lazy_select(src(), es), env(), env())
    IO.print(R.schema(tag, DF.lazy_select(src(), es)))

def flt(+tag: String, +e: X.Expr) -> IO(Unit):
  do IO<Unit>:
    R.three(tag, R.e_filter(t(), e), DF.lazy_filter(src(), e), env(), env())
    IO.print(R.schema(tag, DF.lazy_filter(src(), e)))

def main() -> IO(Unit):
  do IO<Unit>:
    sel("B04-a C6 sum", [DF.sum(a())])
    sel("B04-a C8 literal-and-sum", [DF.alias(DF.lit_u32(1), "one"), DF.sum(a())])
    sel("B04-a C10 column-and-sum", [a(), DF.alias(DF.sum(a()), "s")])
    sel("B04-a C11 centered", [DF.sub(x(), DF.mean(x()))])
    sel("B04-a C12 sum-plus-1", [DF.add(DF.sum(a()), DF.lit_u32(1))])
    R.three("B04-a C13 with-sum", R.e_with(t(), [DF.alias(DF.sum(a()), "s")]), DF.lazy_with_columns(src(), [DF.alias(DF.sum(a()), "s")]), env(), env())
    IO.print(R.schema("B04-a C13 with-sum", DF.lazy_with_columns(src(), [DF.alias(DF.sum(a()), "s")])))
    flt("B04-a C16 above-mean", DF.gt(x(), DF.mean(x())))
    flt("B04-a C17 sum-gt-5", DF.gt(DF.sum(a()), DF.lit_u32(5)))
    flt("B04-a C17 sum-gt-6", DF.gt(DF.sum(a()), DF.lit_u32(6)))
#|-- B04-a C6 sum eager
#|frame
#|height	1
#|width	1
#|col	u32	"a"
#|row	6
#|
#|-- B04-a C6 sum raw
#|frame
#|height	1
#|width	1
#|col	u32	"a"
#|row	6
#|
#|-- B04-a C6 sum opt
#|frame
#|height	1
#|width	1
#|col	u32	"a"
#|row	6
#|
#|-- B04-a C6 sum schema
#|a:u32
#|
#|-- B04-a C8 literal-and-sum eager
#|frame
#|height	1
#|width	2
#|col	u32	"one"
#|col	u32	"a"
#|row	1	6
#|
#|-- B04-a C8 literal-and-sum raw
#|frame
#|height	1
#|width	2
#|col	u32	"one"
#|col	u32	"a"
#|row	1	6
#|
#|-- B04-a C8 literal-and-sum opt
#|frame
#|height	1
#|width	2
#|col	u32	"one"
#|col	u32	"a"
#|row	1	6
#|
#|-- B04-a C8 literal-and-sum schema
#|one:u32, a:u32
#|
#|-- B04-a C10 column-and-sum eager
#|frame
#|height	3
#|width	2
#|col	u32	"a"
#|col	u32	"s"
#|row	1	6
#|row	2	6
#|row	3	6
#|
#|-- B04-a C10 column-and-sum raw
#|frame
#|height	3
#|width	2
#|col	u32	"a"
#|col	u32	"s"
#|row	1	6
#|row	2	6
#|row	3	6
#|
#|-- B04-a C10 column-and-sum opt
#|frame
#|height	3
#|width	2
#|col	u32	"a"
#|col	u32	"s"
#|row	1	6
#|row	2	6
#|row	3	6
#|
#|-- B04-a C10 column-and-sum schema
#|a:u32, s:u32
#|
#|-- B04-a C11 centered eager
#|frame
#|height	3
#|width	1
#|col	f32	"x"
#|row	0xbf800000
#|row	0x00000000
#|row	0x3f800000
#|
#|-- B04-a C11 centered raw
#|frame
#|height	3
#|width	1
#|col	f32	"x"
#|row	0xbf800000
#|row	0x00000000
#|row	0x3f800000
#|
#|-- B04-a C11 centered opt
#|frame
#|height	3
#|width	1
#|col	f32	"x"
#|row	0xbf800000
#|row	0x00000000
#|row	0x3f800000
#|
#|-- B04-a C11 centered schema
#|x:f32
#|
#|-- B04-a C12 sum-plus-1 eager
#|frame
#|height	1
#|width	1
#|col	u32	"a"
#|row	7
#|
#|-- B04-a C12 sum-plus-1 raw
#|frame
#|height	1
#|width	1
#|col	u32	"a"
#|row	7
#|
#|-- B04-a C12 sum-plus-1 opt
#|frame
#|height	1
#|width	1
#|col	u32	"a"
#|row	7
#|
#|-- B04-a C12 sum-plus-1 schema
#|a:u32
#|
#|-- B04-a C13 with-sum eager
#|frame
#|height	3
#|width	3
#|col	u32	"a"
#|col	f32	"x"
#|col	u32	"s"
#|row	1	0x3f800000	6
#|row	2	0x40000000	6
#|row	3	0x40400000	6
#|
#|-- B04-a C13 with-sum raw
#|frame
#|height	3
#|width	3
#|col	u32	"a"
#|col	f32	"x"
#|col	u32	"s"
#|row	1	0x3f800000	6
#|row	2	0x40000000	6
#|row	3	0x40400000	6
#|
#|-- B04-a C13 with-sum opt
#|frame
#|height	3
#|width	3
#|col	u32	"a"
#|col	f32	"x"
#|col	u32	"s"
#|row	1	0x3f800000	6
#|row	2	0x40000000	6
#|row	3	0x40400000	6
#|
#|-- B04-a C13 with-sum schema
#|a:u32, x:f32, s:u32
#|
#|-- B04-a C16 above-mean eager
#|frame
#|height	1
#|width	2
#|col	u32	"a"
#|col	f32	"x"
#|row	3	0x40400000
#|
#|-- B04-a C16 above-mean raw
#|frame
#|height	1
#|width	2
#|col	u32	"a"
#|col	f32	"x"
#|row	3	0x40400000
#|
#|-- B04-a C16 above-mean opt
#|frame
#|height	1
#|width	2
#|col	u32	"a"
#|col	f32	"x"
#|row	3	0x40400000
#|
#|-- B04-a C16 above-mean schema
#|a:u32, x:f32
#|
#|-- B04-a C17 sum-gt-5 eager
#|frame
#|height	3
#|width	2
#|col	u32	"a"
#|col	f32	"x"
#|row	1	0x3f800000
#|row	2	0x40000000
#|row	3	0x40400000
#|
#|-- B04-a C17 sum-gt-5 raw
#|frame
#|height	3
#|width	2
#|col	u32	"a"
#|col	f32	"x"
#|row	1	0x3f800000
#|row	2	0x40000000
#|row	3	0x40400000
#|
#|-- B04-a C17 sum-gt-5 opt
#|frame
#|height	3
#|width	2
#|col	u32	"a"
#|col	f32	"x"
#|row	1	0x3f800000
#|row	2	0x40000000
#|row	3	0x40400000
#|
#|-- B04-a C17 sum-gt-5 schema
#|a:u32, x:f32
#|
#|-- B04-a C17 sum-gt-6 eager
#|frame
#|height	0
#|width	2
#|col	u32	"a"
#|col	f32	"x"
#|
#|-- B04-a C17 sum-gt-6 raw
#|frame
#|height	0
#|width	2
#|col	u32	"a"
#|col	f32	"x"
#|
#|-- B04-a C17 sum-gt-6 opt
#|frame
#|height	0
#|width	2
#|col	u32	"a"
#|col	f32	"x"
#|
#|-- B04-a C17 sum-gt-6 schema
#|a:u32, x:f32
#|
