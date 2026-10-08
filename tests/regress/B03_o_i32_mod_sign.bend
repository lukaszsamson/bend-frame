#! xfail B03-o
# B03-o: i32 % takes the dividend's sign (truncating). DESIGN.md 15.5.1: the result has
# the divisor's sign (floor modulo, consistent with floor_div):
#   7 % 2 = 1, -7 % 2 = 1, 7 % -2 = -1, -7 % -2 = -1, 6 % -3 = 0, -1 % 5 = 4,
#   MAX % MIN = -1
# Polars 2.0.0 (contract snippet and regress_expect.py) agrees.
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
    R.mk("a", [R.i(7), R.ineg(7), R.i(7), R.ineg(7), R.i(6), R.ineg(1), R.i(2147483647)], D.TI32{}),
    R.mk("b", [R.i(2), R.i(2), R.ineg(2), R.ineg(2), R.ineg(3), R.i(5), R.ineg(2147483648)], D.TI32{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def es() -> List<&2, X.Expr>:
  [DF.alias(DF.mod(DF.col("a"), DF.col("b")), "m")]

def main() -> IO(Unit):
  do IO<Unit>:
    R.three("B03-o mod-sign", R.e_with(t(), es()), DF.lazy_with_columns(src(), es()), env(), env())
#|-- B03-o mod-sign eager
#|frame
#|height	7
#|width	3
#|col	i32	"a"
#|col	i32	"b"
#|col	i32	"m"
#|row	7	2	1
#|row	-7	2	1
#|row	7	-2	-1
#|row	-7	-2	-1
#|row	6	-3	0
#|row	-1	5	4
#|row	2147483647	-2147483648	-1
#|
#|-- B03-o mod-sign raw
#|frame
#|height	7
#|width	3
#|col	i32	"a"
#|col	i32	"b"
#|col	i32	"m"
#|row	7	2	1
#|row	-7	2	1
#|row	7	-2	-1
#|row	-7	-2	-1
#|row	6	-3	0
#|row	-1	5	4
#|row	2147483647	-2147483648	-1
#|
#|-- B03-o mod-sign opt
#|frame
#|height	7
#|width	3
#|col	i32	"a"
#|col	i32	"b"
#|col	i32	"m"
#|row	7	2	1
#|row	-7	2	1
#|row	7	-2	-1
#|row	-7	-2	-1
#|row	6	-3	0
#|row	-1	5	4
#|row	2147483647	-2147483648	-1
#|
