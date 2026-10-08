# M1 API test (was tests/regress/pending/; activated with the B03 numerics work).
# B03-e / B03-p / B03-m: try_cast is cast with failing cells set to null (DESIGN.md
# 15.5.5, 15.2.6); it never fails at runtime; typing as Cast.ok, error
# TypeMismatch{"try_cast", "castable to <to>", <t>}. Polars 2.0.0 cast(strict=False)
# gives the same cells except "+5" -> u32 (Polars 5; contract: null, U32.read refuses it).
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
    R.mk("x", [R.f(1.5), R.f(F32.neg(1.5)), R.f(1000000000000.0), R.f(R.nan()), R.f(R.inf()), R.f(F32.neg(0.5)), R.null()], D.TF32{}),
    R.mk("s", [R.s("1"), R.s(" 2 "), R.s("x"), R.s("+5"), R.null(), R.s("4294967295"), R.s("")], D.TStr{}),
    R.mk("big", [R.f(2147483648.0), R.f(F32.neg(2147483648.0)), R.f(R.nan()), R.f(1.9), R.f(F32.neg(1.9)), R.null(), R.f(0.0)], D.TF32{}),
    R.mk("u", [R.u(2147483648), R.u(5), R.null(), R.u(0), R.u(2147483647), R.u(4294967295), R.u(1)], D.TU32{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def es() -> List<&2, X.Expr>:
  [DF.alias(DF.try_cast(DF.col("x"), D.TU32{}), "x_u32"), DF.alias(DF.try_cast(DF.col("s"), D.TU32{}), "s_u32"), DF.alias(DF.try_cast(DF.col("big"), D.TI32{}), "big_i32"), DF.alias(DF.try_cast(DF.col("u"), D.TI32{}), "u_i32")]

def main() -> IO(Unit):
  do IO<Unit>:
    R.three("B03-e try-cast", R.e_select(t(), es()), DF.lazy_select(src(), es()), env(), env())
    IO.print(R.schema("B03-e try-cast", DF.lazy_select(src(), es())))
    IO.print(R.schema("B03-e try-cast-refused", DF.lazy_select(src(), [DF.try_cast(DF.col("u"), D.TBool{})])))
#|-- B03-e try-cast eager
#|frame
#|height	7
#|width	4
#|col	u32	"x_u32"
#|col	u32	"s_u32"
#|col	i32	"big_i32"
#|col	i32	"u_i32"
#|row	1	1	null	null
#|row	null	null	-2147483648	5
#|row	null	null	null	null
#|row	null	null	1	0
#|row	null	null	-1	2147483647
#|row	0	4294967295	null	null
#|row	null	null	0	1
#|
#|-- B03-e try-cast raw
#|frame
#|height	7
#|width	4
#|col	u32	"x_u32"
#|col	u32	"s_u32"
#|col	i32	"big_i32"
#|col	i32	"u_i32"
#|row	1	1	null	null
#|row	null	null	-2147483648	5
#|row	null	null	null	null
#|row	null	null	1	0
#|row	null	null	-1	2147483647
#|row	0	4294967295	null	null
#|row	null	null	0	1
#|
#|-- B03-e try-cast opt
#|frame
#|height	7
#|width	4
#|col	u32	"x_u32"
#|col	u32	"s_u32"
#|col	i32	"big_i32"
#|col	i32	"u_i32"
#|row	1	1	null	null
#|row	null	null	-2147483648	5
#|row	null	null	null	null
#|row	null	null	1	0
#|row	null	null	-1	2147483647
#|row	0	4294967295	null	null
#|row	null	null	0	1
#|
#|-- B03-e try-cast schema
#|x_u32:u32, s_u32:u32, big_i32:i32, u_i32:i32
#|
#|-- B03-e try-cast-refused schema
#|error: TypeMismatch in try_cast: expected castable to bool, got u32
#|
