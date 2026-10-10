# T6 coverage: string predicates and length (len_chars, contains_literal, starts_with, ends_with), cast,
# try_cast, cast_f32, cast_u32, lit_null and the dtype builders t_* (as cast targets), over the
# fixture t (tests/coverage/lib/fx.bend) and the text/number frame n below. Success and null rows,
# zero rows, strict-cast failures and static refusals (invalid), eager and lazy (raw / opt / full) agree.
# Expectations: DESIGN.md 15.5.5, 15.2.6, confirmed by bench/coverage/expr_str_cast.py (Polars 2.0.0);
# departures applied there: f32 -> str prints `nan`/`inf`/`-0`/`1.5`/`-2` (Polars `NaN`, `-0.0`, `1.5`,
# `-2.0`), str -> bool accepts true/false/True/False (Polars has no such cast), try_cast of "+5" to u32
# is null (Polars 5), a cast out of range is an error (Polars strict cast raises too).
#@ cover len_chars,contains_literal,starts_with,ends_with success null empty invalid eager lazy
#@ cover cast,try_cast,cast_f32,cast_u32 success null empty invalid eager lazy
#@ cover lit_null success null empty invalid eager lazy
#@ cover t_bool,t_u32,t_i32,t_f32,t_str success null eager lazy
#@ cover lit_str success null eager lazy
#@ cover select,lazy_select,col,alias success null empty invalid eager lazy
#@ na len_chars,contains_literal,starts_with,ends_with,cast,try_cast,cast_f32,cast_u32 zerocol -- every operand is a column, a zero-column frame has none (lit_null over a zero-column frame: tests/coverage/expr_lit.bend)
#@ na t_bool,t_u32,t_i32,t_f32,t_str invalid -- a dtype builder cannot be given bad input (a refused cast target is the cast's case)
#@ na t_bool,t_u32,t_i32,t_f32,t_str empty -- a dtype builder has no input to be empty (the cast over a zero-row frame is covered)
import Base
import ./../../frame.bend as DF
import ./../../src/column.bend as C
import ./../../src/err.bend as E
import ./../../src/plan.bend as P
import ./../diff/lib/dx.bend as DX
import ./../regress/lib/rx.bend as R
import ./lib/fx.bend as FX

# n: strings that parse as numbers, numbers that convert, and bad strings
#   u str "1" "42" null "4294967295" "007" "0" "3"     i str "-1" "42" null "2147483647" "-2147483648" "0" "5"
#   f str "1.5" "-2" "nan" "inf" ".5" "1e3" null       b str "true" "False" null "True" "false" "true" "false"
#   g f32 -1.9 2147483520.0 -2147483648.0 null 0.5 3.0 -0.0      h f32 1.9 0.5 null 4294967040.0 0.0 -0.5 7.0
#   v u32 0 1 2147483647 null 5 6 7                       w i32 0 1 2147483647 null 5 6 7
#   m str "1" " 2 " "x" "+5" null "4294967295" ""        pl str "1" "+5" "3" null "4" "0" "7"
#   nn f32 1.0 NaN 2.0 null 3.0 4.0 5.0
def n() -> E.ResT(C.Frame):
  R.frame([
    R.mk("u", [R.s("1"), R.s("42"), R.null(), R.s("4294967295"), R.s("007"), R.s("0"), R.s("3")], DF.t_str()),
    R.mk("i", [R.s("-1"), R.s("42"), R.null(), R.s("2147483647"), R.s("-2147483648"), R.s("0"), R.s("5")], DF.t_str()),
    R.mk("f", [R.s("1.5"), R.s("-2"), R.s("nan"), R.s("inf"), R.s(".5"), R.s("1e3"), R.null()], DF.t_str()),
    R.mk("b", [R.s("true"), R.s("False"), R.null(), R.s("True"), R.s("false"), R.s("true"), R.s("false")], DF.t_str()),
    R.mk("g", [R.f(F32.neg(1.9)), R.f(2147483520.0), R.f(F32.neg(2147483648.0)), R.null(), R.f(0.5), R.f(3.0), R.f(R.nzero())], DF.t_f32()),
    R.mk("h", [R.f(1.9), R.f(0.5), R.null(), R.f(4294967040.0), R.f(0.0), R.f(F32.neg(0.5)), R.f(7.0)], DF.t_f32()),
    R.mk("v", [R.u(0), R.u(1), R.u(2147483647), R.null(), R.u(5), R.u(6), R.u(7)], DF.t_u32()),
    R.mk("w", [R.i(0), R.i(1), R.i(2147483647), R.null(), R.i(5), R.i(6), R.i(7)], DF.t_i32()),
    R.mk("m", [R.s("1"), R.s(" 2 "), R.s("x"), R.s("+5"), R.null(), R.s("4294967295"), R.s("")], DF.t_str()),
    R.mk("pl", [R.s("1"), R.s("+5"), R.s("3"), R.null(), R.s("4"), R.s("0"), R.s("7")], DF.t_str()),
    R.mk("nn", [R.f(1.0), R.f(R.nan()), R.f(2.0), R.null(), R.f(3.0), R.f(4.0), R.f(5.0)], DF.t_f32())])

def nz() -> E.ResT(C.Frame):
  R.frame([R.mk("u", [], DF.t_str()), R.mk("h", [], DF.t_f32()), R.mk("v", [], DF.t_u32())])

def envn() -> P.Env:
  R.env1("n", n())

def srcn() -> P.Plan:
  R.src("n", n())

def c(+n: String) -> DF.Expr():
  DF.col(n)

def al(e: DF.Expr(), +n: String) -> DF.Expr():
  DF.alias(e, n)

def sel(+tag: String, +es: List<&2, DF.Expr()>) -> IO(Unit):
  R.four(tag, DX.e_select(FX.t(), es), DF.lazy_select(FX.srct(), es), FX.envt(), FX.envt(), FX.envt())

def seln(+tag: String, +es: List<&2, DF.Expr()>) -> IO(Unit):
  R.four(tag, DX.e_select(n(), es), DF.lazy_select(srcn(), es), envn(), envn(), envn())

def selz(+tag: String, +es: List<&2, DF.Expr()>) -> IO(Unit):
  R.four(tag, DX.e_select(FX.z(), es), DF.lazy_select(FX.srcz(), es), FX.envz(), FX.envz(), FX.envz())

def selnz(+tag: String, +es: List<&2, DF.Expr()>) -> IO(Unit):
  R.four(tag, DX.e_select(nz(), es), DF.lazy_select(R.src("nz", nz()), es), R.env1("nz", nz()), R.env1("nz", nz()), R.env1("nz", nz()))

def main() -> IO(Unit):
  do IO<Unit>:
    sel("len_chars and the string predicates, with nulls", [al(DF.len_chars(c("s")), "len"), al(DF.contains_literal(c("s"), "b"), "has_b"), al(DF.contains_literal(c("s"), "é"), "has_e"), al(DF.starts_with(c("s"), "a"), "sw_a"), al(DF.ends_with(c("s"), "c"), "ew_c"), al(DF.contains_literal(c("s"), ""), "has_empty"), al(DF.starts_with(c("s"), "ab"), "sw_ab"), al(DF.ends_with(c("s"), "bc"), "ew_bc")])
    selz("len_chars and the string predicates, zero rows", [al(DF.len_chars(c("s")), "len"), al(DF.contains_literal(c("s"), "b"), "has_b"), al(DF.starts_with(c("s"), "a"), "sw_a"), al(DF.ends_with(c("s"), "c"), "ew_c")])
    seln("cast str to u32 i32 f32 bool", [al(DF.cast(c("u"), DF.t_u32()), "u32"), al(DF.cast(c("i"), DF.t_i32()), "i32"), al(DF.cast(c("f"), DF.t_f32()), "f32"), al(DF.cast(c("b"), DF.t_bool()), "bool"), al(DF.cast_f32(c("f")), "f32b")])
    seln("cast f32 to u32 and i32 (truncate toward zero)", [al(DF.cast_u32(c("h")), "h_u32"), al(DF.cast(c("g"), DF.t_i32()), "g_i32"), al(DF.cast(c("v"), DF.t_i32()), "v_i32"), al(DF.cast(c("w"), DF.t_u32()), "w_u32")])
    seln("cast numbers to f32 and str, bool to numbers", [al(DF.cast_f32(c("v")), "v_f"), al(DF.cast_f32(c("w")), "w_f"), al(DF.cast(c("v"), DF.t_str()), "v_s"), al(DF.cast(c("w"), DF.t_str()), "w_s"), al(DF.cast(c("h"), DF.t_str()), "h_s"), al(DF.cast(c("v"), DF.t_u32()), "v_same")])
    sel("cast bool to u32 i32 f32 str, u32 to f32 above 2^24", [al(DF.cast_u32(c("k")), "k_u"), al(DF.cast(c("k"), DF.t_i32()), "k_i"), al(DF.cast_f32(c("k")), "k_f"), al(DF.cast(c("k"), DF.t_str()), "k_s"), al(DF.cast_f32(c("a")), "a_f"), al(DF.cast(c("x"), DF.t_str()), "x_s")])
    seln("try_cast turns failing cells into null", [al(DF.try_cast(c("m"), DF.t_u32()), "m_u"), al(DF.try_cast(c("m"), DF.t_f32()), "m_f"), al(DF.try_cast(c("f"), DF.t_i32()), "f_i"), al(DF.try_cast(c("h"), DF.t_u32()), "h_u"), al(DF.try_cast(c("v"), DF.t_i32()), "v_i")])
    sel("try_cast with out-of-range and non-finite cells", [al(DF.try_cast(c("a"), DF.t_i32()), "a_i"), al(DF.try_cast(c("x"), DF.t_u32()), "x_u"), al(DF.try_cast(c("p"), DF.t_u32()), "p_u"), al(DF.try_cast(c("x"), DF.t_i32()), "x_i"), al(DF.try_cast(c("s"), DF.t_f32()), "s_f")])
    sel("lit_null of every dtype beside a column", [c("a"), al(DF.lit_null(DF.t_u32()), "nu"), al(DF.lit_null(DF.t_i32()), "ni"), al(DF.lit_null(DF.t_f32()), "nf"), al(DF.lit_null(DF.t_bool()), "nb"), al(DF.lit_null(DF.t_str()), "ns")])
    sel("lit_null alone is one row", [al(DF.lit_null(DF.t_u32()), "nu"), al(DF.lit_str("lit"), "l")])
    selz("lit_null beside a zero-row column", [c("a"), al(DF.lit_null(DF.t_f32()), "nf")])
    selnz("cast and try_cast, zero rows", [al(DF.cast(c("u"), DF.t_u32()), "u32"), al(DF.try_cast(c("u"), DF.t_f32()), "uf"), al(DF.cast_f32(c("v")), "vf"), al(DF.cast_u32(c("h")), "hu"), al(DF.cast(c("v"), DF.t_str()), "vs")])
    sel("invalid len_chars u32", [DF.len_chars(c("a"))])
    sel("invalid contains_literal bool", [DF.contains_literal(c("k"), "t")])
    sel("invalid starts_with f32", [DF.starts_with(c("x"), "1")])
    sel("invalid ends_with i32", [DF.ends_with(c("p"), "1")])
    sel("invalid len_chars missing column", [DF.len_chars(c("nope"))])
    seln("invalid cast u32 above i32 range (strict, row 2)", [DF.cast(DF.add(c("v"), DF.lit_u32(2147483648)), DF.t_i32())])
    sel("invalid cast u32 MAX to i32 (strict, row 2)", [DF.cast(c("a"), DF.t_i32())])
    sel("invalid cast negative f32 to u32 (strict, row 1)", [DF.cast_u32(c("x"))])
    seln("invalid cast i32 negative to u32 (strict, row 0)", [DF.cast(DF.sub(c("w"), DF.lit_i32(1)), DF.t_u32())])
    seln("invalid cast_f32 of bad strings (strict, row 1)", [DF.cast_f32(c("m"))])
    seln("invalid cast str to u32 with a plus sign (strict, row 1)", [DF.cast(c("pl"), DF.t_u32())])
    seln("invalid cast f32 NaN to u32 (strict, row 1)", [DF.cast_u32(c("nn"))])
    sel("invalid cast to bool from u32 (static)", [DF.cast(c("a"), DF.t_bool())])
    sel("invalid cast f32 to bool (static)", [DF.cast(c("x"), DF.t_bool())])
    sel("invalid try_cast to bool from i32 (static)", [DF.try_cast(c("p"), DF.t_bool())])
    sel("invalid cast missing column", [DF.cast(c("nope"), DF.t_u32())])
#|-- len_chars and the string predicates, with nulls
#|frame
#|height	7
#|width	8
#|col	u32	"len"
#|col	bool	"has_b"
#|col	bool	"has_e"
#|col	bool	"sw_a"
#|col	bool	"ew_c"
#|col	bool	"has_empty"
#|col	bool	"sw_ab"
#|col	bool	"ew_bc"
#|row	1	false	false	true	false	true	false	false
#|row	0	false	false	false	false	true	false	false
#|row	1	false	true	false	false	true	false	false
#|row	null	null	null	null	null	null	null	null
#|row	3	true	false	true	true	true	true	true
#|row	2	true	false	true	false	true	true	false
#|row	1	false	false	true	false	true	false	false
#|raw same, opt same, full same
#|
#|-- len_chars and the string predicates, zero rows
#|frame
#|height	0
#|width	4
#|col	u32	"len"
#|col	bool	"has_b"
#|col	bool	"sw_a"
#|col	bool	"ew_c"
#|raw same, opt same, full same
#|
#|-- cast str to u32 i32 f32 bool
#|frame
#|height	7
#|width	5
#|col	u32	"u32"
#|col	i32	"i32"
#|col	f32	"f32"
#|col	bool	"bool"
#|col	f32	"f32b"
#|row	1	-1	0x3fc00000	true	0x3fc00000
#|row	42	42	0xc0000000	false	0xc0000000
#|row	null	null	0x7fc00000	null	0x7fc00000
#|row	4294967295	2147483647	0x7f800000	true	0x7f800000
#|row	7	-2147483648	0x3f000000	false	0x3f000000
#|row	0	0	0x447a0000	true	0x447a0000
#|row	3	5	null	false	null
#|raw same, opt same, full same
#|
#|-- cast f32 to u32 and i32 (truncate toward zero)
#|frame
#|height	7
#|width	4
#|col	u32	"h_u32"
#|col	i32	"g_i32"
#|col	i32	"v_i32"
#|col	u32	"w_u32"
#|row	1	-1	0	0
#|row	0	2147483520	1	1
#|row	null	-2147483648	2147483647	2147483647
#|row	4294967040	null	null	null
#|row	0	0	5	5
#|row	0	3	6	6
#|row	7	0	7	7
#|raw same, opt same, full same
#|
#|-- cast numbers to f32 and str, bool to numbers
#|frame
#|height	7
#|width	6
#|col	f32	"v_f"
#|col	f32	"w_f"
#|col	str	"v_s"
#|col	str	"w_s"
#|col	str	"h_s"
#|col	u32	"v_same"
#|row	0x00000000	0x00000000	"0"	"0"	"1.9"	0
#|row	0x3f800000	0x3f800000	"1"	"1"	"0.5"	1
#|row	0x4f000000	0x4f000000	"2147483647"	"2147483647"	null	2147483647
#|row	null	null	null	null	"4294967000"	null
#|row	0x40a00000	0x40a00000	"5"	"5"	"0"	5
#|row	0x40c00000	0x40c00000	"6"	"6"	"-0.5"	6
#|row	0x40e00000	0x40e00000	"7"	"7"	"7"	7
#|raw same, opt same, full same
#|
#|-- cast bool to u32 i32 f32 str, u32 to f32 above 2^24
#|frame
#|height	7
#|width	6
#|col	u32	"k_u"
#|col	i32	"k_i"
#|col	f32	"k_f"
#|col	str	"k_s"
#|col	f32	"a_f"
#|col	str	"x_s"
#|row	1	1	0x3f800000	"true"	0x40e00000	"1.5"
#|row	0	0	0x00000000	"false"	0x00000000	"-2"
#|row	null	null	null	null	0x4f800000	null
#|row	1	1	0x3f800000	"true"	null	"nan"
#|row	0	0	0x00000000	"false"	0x40a00000	"inf"
#|row	1	1	0x3f800000	"true"	0x3f800000	"0"
#|row	null	null	null	null	0x40000000	"-0"
#|raw same, opt same, full same
#|
#|-- try_cast turns failing cells into null
#|frame
#|height	7
#|width	5
#|col	u32	"m_u"
#|col	f32	"m_f"
#|col	i32	"f_i"
#|col	u32	"h_u"
#|col	i32	"v_i"
#|row	1	0x3f800000	null	1	0
#|row	null	null	-2	0	1
#|row	null	null	null	null	2147483647
#|row	null	0x40a00000	null	4294967040	null
#|row	null	null	null	0	5
#|row	4294967295	0x4f800000	null	0	6
#|row	null	null	null	7	7
#|raw same, opt same, full same
#|
#|-- try_cast with out-of-range and non-finite cells
#|frame
#|height	7
#|width	5
#|col	i32	"a_i"
#|col	u32	"x_u"
#|col	u32	"p_u"
#|col	i32	"x_i"
#|col	f32	"s_f"
#|row	7	1	7	1	null
#|row	0	null	null	-2	null
#|row	null	null	7	null	null
#|row	null	null	null	null	null
#|row	5	null	null	null	null
#|row	1	0	null	0	null
#|row	2	0	0	0	null
#|raw same, opt same, full same
#|
#|-- lit_null of every dtype beside a column
#|frame
#|height	7
#|width	6
#|col	u32	"a"
#|col	u32	"nu"
#|col	i32	"ni"
#|col	f32	"nf"
#|col	bool	"nb"
#|col	str	"ns"
#|row	7	null	null	null	null	null
#|row	0	null	null	null	null	null
#|row	4294967295	null	null	null	null	null
#|row	null	null	null	null	null	null
#|row	5	null	null	null	null	null
#|row	1	null	null	null	null	null
#|row	2	null	null	null	null	null
#|raw same, opt same, full same
#|
#|-- lit_null alone is one row
#|frame
#|height	1
#|width	2
#|col	u32	"nu"
#|col	str	"l"
#|row	null	"lit"
#|raw same, opt same, full same
#|
#|-- lit_null beside a zero-row column
#|frame
#|height	0
#|width	2
#|col	u32	"a"
#|col	f32	"nf"
#|raw same, opt same, full same
#|
#|-- cast and try_cast, zero rows
#|frame
#|height	0
#|width	5
#|col	u32	"u32"
#|col	f32	"uf"
#|col	f32	"vf"
#|col	u32	"hu"
#|col	str	"vs"
#|raw same, opt same, full same
#|
#|-- invalid len_chars u32
#|error	TypeMismatch in len_chars: expected str, got u32
#|raw same, opt same, full same
#|
#|-- invalid contains_literal bool
#|error	TypeMismatch in contains_literal: expected str, got bool
#|raw same, opt same, full same
#|
#|-- invalid starts_with f32
#|error	TypeMismatch in starts_with: expected str, got f32
#|raw same, opt same, full same
#|
#|-- invalid ends_with i32
#|error	TypeMismatch in ends_with: expected str, got i32
#|raw same, opt same, full same
#|
#|-- invalid len_chars missing column
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|-- invalid cast u32 above i32 range (strict, row 2)
#|error	InvalidOperation: cast u32 to i32: row 0 holds 2147483648
#|raw same, opt same, full same
#|
#|-- invalid cast u32 MAX to i32 (strict, row 2)
#|error	InvalidOperation: cast u32 to i32: row 2 holds 4294967295
#|raw same, opt same, full same
#|
#|-- invalid cast negative f32 to u32 (strict, row 1)
#|error	InvalidOperation: cast f32 to u32: row 1 holds -2
#|raw same, opt same, full same
#|
#|-- invalid cast i32 negative to u32 (strict, row 0)
#|error	InvalidOperation: cast i32 to u32: row 0 holds -1
#|raw same, opt same, full same
#|
#|-- invalid cast_f32 of bad strings (strict, row 1)
#|error	InvalidOperation: cast str to f32: row 1 holds " 2 "
#|raw same, opt same, full same
#|
#|-- invalid cast str to u32 with a plus sign (strict, row 1)
#|error	InvalidOperation: cast str to u32: row 1 holds "+5"
#|raw same, opt same, full same
#|
#|-- invalid cast f32 NaN to u32 (strict, row 1)
#|error	InvalidOperation: cast f32 to u32: row 1 holds nan
#|raw same, opt same, full same
#|
#|-- invalid cast to bool from u32 (static)
#|error	TypeMismatch in cast: expected castable to bool, got u32
#|raw same, opt same, full same
#|
#|-- invalid cast f32 to bool (static)
#|error	TypeMismatch in cast: expected castable to bool, got f32
#|raw same, opt same, full same
#|
#|-- invalid try_cast to bool from i32 (static)
#|error	TypeMismatch in try_cast: expected castable to bool, got i32
#|raw same, opt same, full same
#|
#|-- invalid cast missing column
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
