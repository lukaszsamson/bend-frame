# B03-l: i32 MIN // -1 and MIN % -1 follow wrapping; the contract says null / 0.
# DESIGN.md 15.5.1: MIN % -1 = 0 (Polars 0); MIN % 1 = 0; MIN % MIN = 0 (Polars 2.0.0,
# regress_expect.py). The % half PASSES today (no xfail): I32 mod already answers 0 here.
# MIN // -1 = null needs floor_div (M1 API): tests/regress/B03_d_floor_div.bend.
# (MAX % MIN = -1 is a sign case: B03-o.)
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
    R.mk("a", [R.ineg(2147483648), R.ineg(2147483648), R.ineg(2147483648)], D.TI32{}),
    R.mk("b", [R.ineg(1), R.i(1), R.ineg(2147483648)], D.TI32{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def es() -> List<&2, X.Expr>:
  [DF.alias(DF.mod(DF.col("a"), DF.col("b")), "m")]

def main() -> IO(Unit):
  do IO<Unit>:
    R.three("B03-l min-mod", R.e_with(t(), es()), DF.lazy_with_columns(src(), es()), env(), env())
#|-- B03-l min-mod eager
#|frame
#|height	3
#|width	3
#|col	i32	"a"
#|col	i32	"b"
#|col	i32	"m"
#|row	-2147483648	-1	0
#|row	-2147483648	1	0
#|row	-2147483648	-2147483648	0
#|
#|-- B03-l min-mod raw
#|frame
#|height	3
#|width	3
#|col	i32	"a"
#|col	i32	"b"
#|col	i32	"m"
#|row	-2147483648	-1	0
#|row	-2147483648	1	0
#|row	-2147483648	-2147483648	0
#|
#|-- B03-l min-mod opt
#|frame
#|height	3
#|width	3
#|col	i32	"a"
#|col	i32	"b"
#|col	i32	"m"
#|row	-2147483648	-1	0
#|row	-2147483648	1	0
#|row	-2147483648	-2147483648	0
#|
