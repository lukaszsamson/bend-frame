# T6 coverage: literals and the checked i32 builders: lit_u32, lit_f32, lit_str, lit_bool, lit_i32,
# lit_i32_neg (including the failing out-of-range forms), the scalar builders s_i32 and the checked
# i32 / i32_neg, over the nullable fixture t, a zero-row frame and a zero-column frame (a literal is
# 1 row alone and broadcasts beside a column, DESIGN.md 15.4 C2, C3, C9, C22, C23). Eager (DX.e_*)
# and lazy (DF.lazy_*, raw / opt / full) agree (R.four).
# Expectations: DESIGN.md 15.2.1 (the lit_i32 rule D), 15.4, confirmed by bench/coverage/expr_lit.py
# (Polars 2.0.0) for the select / with_columns cases; the builders i32 / i32_neg print their text
# (reasoned: v < 2^31, v <= 2^31 for the negative, else "i32 out of range: <v>").
#@ cover lit_u32,lit_f32,lit_str,lit_bool,lit_i32,lit_i32_neg success null empty eager lazy zerocol
#@ cover lit_i32,lit_i32_neg invalid eager lazy
#@ na lit_u32,lit_f32,lit_str,lit_bool invalid -- a literal of these dtypes always builds and always evaluates; the only refused use is a type clash in an operator (covered in expr_arith.bend)
#@ cover i32,i32_neg,s_i32 success eager
#@ cover i32,i32_neg invalid eager
#@ na i32,i32_neg,s_i32 null -- a checked integer has no null form (an SNull scalar is s_null, covered in expr_cond.bend)
#@ na i32,i32_neg,s_i32 empty -- a scalar builder takes one value: there is no zero-row form
#@ na i32,i32_neg,s_i32 lazy -- a builder, not a plan node: the scalar it builds is used by the lazy is_in below
#@ cover s_i32 empty invalid lazy
#@ na s_i32 null -- see above: a scalar is never null here
#@ cover is_in,select,lazy_select,with_columns,lazy_with_columns,col,alias success null empty eager lazy
#@ cover is_in invalid
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./../diff/lib/dx.bend as DX
import ./../regress/lib/rx.bend as R
import ./lib/fx.bend as FX

def c(+n: String) -> DF.Expr():
  DF.col(n)

def al(e: DF.Expr(), +n: String) -> DF.Expr():
  DF.alias(e, n)

def sel(+tag: String, +es: List<&2, DF.Expr()>) -> IO(Unit):
  R.four(tag, DX.e_select(FX.t(), es), DF.lazy_select(FX.srct(), es), FX.envt(), FX.envt(), FX.envt())

def selz(+tag: String, +es: List<&2, DF.Expr()>) -> IO(Unit):
  R.four(tag, DX.e_select(FX.z(), es), DF.lazy_select(FX.srcz(), es), FX.envz(), FX.envz(), FX.envz())

def sel0(+tag: String, +es: List<&2, DF.Expr()>) -> IO(Unit):
  R.four(tag, DX.e_select(R.zcols(3), es), DF.lazy_select(R.src("z0", R.zcols(3)), es), R.env1("z0", R.zcols(3)), R.env1("z0", R.zcols(3)), R.env1("z0", R.zcols(3)))

def wthz(+tag: String, +es: List<&2, DF.Expr()>) -> IO(Unit):
  R.four(tag, DX.e_with_columns(FX.z(), es), DF.lazy_with_columns(FX.srcz(), es), FX.envz(), FX.envz(), FX.envz())

def wth(+tag: String, +es: List<&2, DF.Expr()>) -> IO(Unit):
  R.four(tag, DX.e_with_columns(FX.t(), es), DF.lazy_with_columns(FX.srct(), es), FX.envt(), FX.envt(), FX.envt())

def lits() -> List<&2, DF.Expr()>:
  [al(DF.lit_u32(1), "u"), al(DF.lit_f32(1.5), "f"), al(DF.lit_str("é"), "s"), al(DF.lit_bool(True{}), "b"), al(DF.lit_i32(7), "i"), al(DF.lit_i32_neg(7), "n"), al(DF.lit_i32(2147483647), "imax"), al(DF.lit_i32_neg(2147483648), "imin"), al(DF.lit_u32(4294967295), "umax"), al(DF.lit_str(""), "empty")]

# the text of a checked i32 (DF.i32 / DF.i32_neg): its value, or the error
def i32text(r: E.Res(D.I32)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ DF.err_show(e)
    case Done{i}:
      "ok " ++ D.I32.show(i)

# a scalar from a checked i32 (the null scalar when it was refused)
def si(r: E.Res(D.I32)) -> D.Scalar:
  match r:
    case Fail{e}:
      DF.s_null()
    case Done{i}:
      DF.s_i32(i)

def main() -> IO(Unit):
  do IO<Unit>:
    sel("literals beside a nullable column are broadcast", c("a") <> lits())
    sel("literals alone are one row", lits())
    selz("literals beside a zero-row column", c("a") <> lits())
    selz("literals alone over zero rows are one row", lits())
    sel0("literals over a zero-column frame are one row", lits())
    wth("with_columns literals are broadcast", [al(DF.lit_u32(1), "u"), al(DF.lit_str("s"), "s")])
    wthz("with_columns literals over zero rows", [al(DF.lit_u32(1), "u"), al(DF.lit_f32(0.5), "f"), al(DF.lit_bool(False{}), "b")])
    sel("a literal beside a null column compares to null", [al(DF.eq(c("a"), DF.lit_u32(7)), "eq7"), al(DF.add(c("a"), DF.lit_u32(1)), "a1"), al(DF.is_null(DF.lit_u32(1)), "litnull")])
    sel("lit_i32 holds v < 2^31", [al(DF.lit_i32(0), "z"), al(DF.lit_i32(2147483647), "imax"), al(DF.lit_i32_neg(0), "nz"), al(DF.lit_i32_neg(1), "n1"), al(DF.lit_i32_neg(2147483648), "imin")])
    sel("invalid lit_i32 above the i32 range fails when evaluated", [DF.lit_i32(2147483648)])
    sel("invalid lit_i32 at the u32 maximum", [al(DF.lit_i32(4294967295), "big")])
    sel("invalid lit_i32_neg above 2^31 fails when evaluated", [DF.lit_i32_neg(2147483649)])
    selz("invalid lit_i32 over zero rows is still evaluated", [DF.lit_i32(2147483648)])
    sel("invalid lit_u32 plus lit_f32", [DF.add(DF.lit_u32(1), DF.lit_f32(1.0))])
    sel("invalid lit_str times lit_bool", [DF.mul(DF.lit_str("a"), DF.lit_bool(True{}))])
    sel("is_in with checked i32 scalars", [al(DF.is_in(c("p"), [si(DF.i32(7)), si(DF.i32_neg(2147483648))]), "in")])
    selz("is_in with checked i32 scalars, zero rows", [al(DF.is_in(c("p"), [si(DF.i32(7))]), "in")])
    sel("invalid is_in with a refused i32 scalar (null)", [al(DF.is_in(c("p"), [si(DF.i32(2147483648))]), "in")])
    sel("invalid is_in i32 scalars in a u32 column", [al(DF.is_in(c("a"), [si(DF.i32(7))]), "in")])
    IO.print("-- i32 and i32_neg\n" ++ i32text(DF.i32(0)) ++ "\n" ++ i32text(DF.i32(7)) ++ "\n" ++ i32text(DF.i32(2147483647)) ++ "\n" ++ i32text(DF.i32(2147483648)) ++ "\n" ++ i32text(DF.i32(4294967295)) ++ "\n" ++ i32text(DF.i32_neg(0)) ++ "\n" ++ i32text(DF.i32_neg(7)) ++ "\n" ++ i32text(DF.i32_neg(2147483648)) ++ "\n" ++ i32text(DF.i32_neg(2147483649)) ++ "\n\n")
#|-- literals beside a nullable column are broadcast
#|frame
#|height	7
#|width	11
#|col	u32	"a"
#|col	u32	"u"
#|col	f32	"f"
#|col	str	"s"
#|col	bool	"b"
#|col	i32	"i"
#|col	i32	"n"
#|col	i32	"imax"
#|col	i32	"imin"
#|col	u32	"umax"
#|col	str	"empty"
#|row	7	1	0x3fc00000	"é"	true	7	-7	2147483647	-2147483648	4294967295	""
#|row	0	1	0x3fc00000	"é"	true	7	-7	2147483647	-2147483648	4294967295	""
#|row	4294967295	1	0x3fc00000	"é"	true	7	-7	2147483647	-2147483648	4294967295	""
#|row	null	1	0x3fc00000	"é"	true	7	-7	2147483647	-2147483648	4294967295	""
#|row	5	1	0x3fc00000	"é"	true	7	-7	2147483647	-2147483648	4294967295	""
#|row	1	1	0x3fc00000	"é"	true	7	-7	2147483647	-2147483648	4294967295	""
#|row	2	1	0x3fc00000	"é"	true	7	-7	2147483647	-2147483648	4294967295	""
#|raw same, opt same, full same
#|
#|-- literals alone are one row
#|frame
#|height	1
#|width	10
#|col	u32	"u"
#|col	f32	"f"
#|col	str	"s"
#|col	bool	"b"
#|col	i32	"i"
#|col	i32	"n"
#|col	i32	"imax"
#|col	i32	"imin"
#|col	u32	"umax"
#|col	str	"empty"
#|row	1	0x3fc00000	"é"	true	7	-7	2147483647	-2147483648	4294967295	""
#|raw same, opt same, full same
#|
#|-- literals beside a zero-row column
#|frame
#|height	0
#|width	11
#|col	u32	"a"
#|col	u32	"u"
#|col	f32	"f"
#|col	str	"s"
#|col	bool	"b"
#|col	i32	"i"
#|col	i32	"n"
#|col	i32	"imax"
#|col	i32	"imin"
#|col	u32	"umax"
#|col	str	"empty"
#|raw same, opt same, full same
#|
#|-- literals alone over zero rows are one row
#|frame
#|height	1
#|width	10
#|col	u32	"u"
#|col	f32	"f"
#|col	str	"s"
#|col	bool	"b"
#|col	i32	"i"
#|col	i32	"n"
#|col	i32	"imax"
#|col	i32	"imin"
#|col	u32	"umax"
#|col	str	"empty"
#|row	1	0x3fc00000	"é"	true	7	-7	2147483647	-2147483648	4294967295	""
#|raw same, opt same, full same
#|
#|-- literals over a zero-column frame are one row
#|frame
#|height	1
#|width	10
#|col	u32	"u"
#|col	f32	"f"
#|col	str	"s"
#|col	bool	"b"
#|col	i32	"i"
#|col	i32	"n"
#|col	i32	"imax"
#|col	i32	"imin"
#|col	u32	"umax"
#|col	str	"empty"
#|row	1	0x3fc00000	"é"	true	7	-7	2147483647	-2147483648	4294967295	""
#|raw same, opt same, full same
#|
#|-- with_columns literals are broadcast
#|frame
#|height	7
#|width	9
#|col	u32	"a"
#|col	u32	"b"
#|col	i32	"p"
#|col	i32	"q"
#|col	f32	"x"
#|col	f32	"y"
#|col	bool	"k"
#|col	str	"s"
#|col	u32	"u"
#|row	7	2	7	2	0x3fc00000	0x40000000	true	"s"	1
#|row	0	3	-7	2	0xc0000000	0x3f000000	false	"s"	1
#|row	4294967295	1	7	-2	null	0x3f800000	null	"s"	1
#|row	null	1	-7	-2	0x7fc00000	0x3f800000	true	"s"	1
#|row	5	null	-2147483648	-1	0x7f800000	0x7f800000	false	"s"	1
#|row	1	0	null	1	0x00000000	0x00000000	true	"s"	1
#|row	2	0	0	0	0x80000000	null	null	"s"	1
#|raw same, opt same, full same
#|
#|-- with_columns literals over zero rows
#|frame
#|height	0
#|width	10
#|col	u32	"a"
#|col	bool	"b"
#|col	i32	"p"
#|col	i32	"q"
#|col	f32	"x"
#|col	f32	"y"
#|col	bool	"k"
#|col	str	"s"
#|col	u32	"u"
#|col	f32	"f"
#|raw same, opt same, full same
#|
#|-- a literal beside a null column compares to null
#|frame
#|height	7
#|width	3
#|col	bool	"eq7"
#|col	u32	"a1"
#|col	bool	"litnull"
#|row	true	8	false
#|row	false	1	false
#|row	false	0	false
#|row	null	null	false
#|row	false	6	false
#|row	false	2	false
#|row	false	3	false
#|raw same, opt same, full same
#|
#|-- lit_i32 holds v < 2^31
#|frame
#|height	1
#|width	5
#|col	i32	"z"
#|col	i32	"imax"
#|col	i32	"nz"
#|col	i32	"n1"
#|col	i32	"imin"
#|row	0	2147483647	0	-1	-2147483648
#|raw same, opt same, full same
#|
#|-- invalid lit_i32 above the i32 range fails when evaluated
#|error	InvalidOperation: cast u32 to i32: row 0 holds 2147483648
#|raw same, opt same, full same
#|
#|-- invalid lit_i32 at the u32 maximum
#|error	InvalidOperation: cast u32 to i32: row 0 holds 4294967295
#|raw same, opt same, full same
#|
#|-- invalid lit_i32_neg above 2^31 fails when evaluated
#|error	InvalidOperation: cast u32 to i32: row 0 holds 2147483649
#|raw same, opt same, full same
#|
#|-- invalid lit_i32 over zero rows is still evaluated
#|error	InvalidOperation: cast u32 to i32: row 0 holds 2147483648
#|raw same, opt same, full same
#|
#|-- invalid lit_u32 plus lit_f32
#|error	TypeMismatch in add: expected u32, got f32
#|raw same, opt same, full same
#|
#|-- invalid lit_str times lit_bool
#|error	TypeMismatch in mul: expected numeric, got str
#|raw same, opt same, full same
#|
#|-- is_in with checked i32 scalars
#|frame
#|height	7
#|width	1
#|col	bool	"in"
#|row	true
#|row	false
#|row	true
#|row	false
#|row	true
#|row	null
#|row	false
#|raw same, opt same, full same
#|
#|-- is_in with checked i32 scalars, zero rows
#|frame
#|height	0
#|width	1
#|col	bool	"in"
#|raw same, opt same, full same
#|
#|-- invalid is_in with a refused i32 scalar (null)
#|error	TypeMismatch in is_in: expected i32, got null
#|raw same, opt same, full same
#|
#|-- invalid is_in i32 scalars in a u32 column
#|error	TypeMismatch in is_in: expected u32, got i32
#|raw same, opt same, full same
#|
#|-- i32 and i32_neg
#|ok 0
#|ok 7
#|ok 2147483647
#|error: InvalidOperation: i32 out of range: 2147483648
#|error: InvalidOperation: i32 out of range: 4294967295
#|ok 0
#|ok -7
#|ok -2147483648
#|error: InvalidOperation: i32 out of range: 2147483649
#|
#|
