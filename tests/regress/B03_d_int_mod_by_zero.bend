# B03-d (Fable B1): integer % by zero answers the dividend (and / by zero 0).
# DESIGN.md 15.5.1: mod by zero is null (u32 and i32); integer / is refused (B03-f) and
# floor_div by zero is null (M1 API: tests/regress/B03_d_floor_div.bend).
# Polars 2.0.0: 7 % 0 = null (regress_expect.py).
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
    R.mk("a", [R.u(7), R.u(7), R.null(), R.u(0)], D.TU32{}),
    R.mk("b", [R.u(2), R.u(0), R.u(0), R.u(0)], D.TU32{}),
    R.mk("ai", [R.i(7), R.ineg(7), R.i(5), R.i(0)], D.TI32{}),
    R.mk("bi", [R.i(0), R.i(0), R.i(2), R.i(0)], D.TI32{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def es() -> List<&2, X.Expr>:
  [DF.alias(DF.mod(DF.col("a"), DF.col("b")), "m"), DF.alias(DF.mod(DF.col("ai"), DF.col("bi")), "mi")]

def main() -> IO(Unit):
  do IO<Unit>:
    R.three("B03-d mod-by-zero", R.e_select(t(), es()), DF.lazy_select(src(), es()), env(), env())
#|-- B03-d mod-by-zero eager
#|frame
#|height	4
#|width	2
#|col	u32	"m"
#|col	i32	"mi"
#|row	1	null
#|row	null	null
#|row	null	1
#|row	null	null
#|
#|-- B03-d mod-by-zero raw
#|frame
#|height	4
#|width	2
#|col	u32	"m"
#|col	i32	"mi"
#|row	1	null
#|row	null	null
#|row	null	1
#|row	null	null
#|
#|-- B03-d mod-by-zero opt
#|frame
#|height	4
#|width	2
#|col	u32	"m"
#|col	i32	"mi"
#|row	1	null
#|row	null	null
#|row	null	1
#|row	null	null
#|
