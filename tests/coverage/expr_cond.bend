# T6 coverage: when, is_in, clip, is_between, is_between_closed (and the closed_* builders) over the
# nullable fixture t (tests/coverage/lib/fx.bend). Success and null rows for every dtype each accepts,
# a zero-row frame, the refusals; eager (DX.e_select) and lazy (DF.lazy_select raw / opt / full) agree.
# Expectations: DESIGN.md 15.2.6, confirmed by bench/coverage/expr_cond.py (Polars 2.0.0); departures
# applied there: no coercion (a bound or listed scalar of another dtype is a TypeMismatch), is_in
# refuses an SNull scalar, is_between has no node (sugar for two comparisons: errors are theirs).
#@ cover when,is_in,clip,is_between,is_between_closed success null empty invalid eager lazy
#@ cover closed_both,closed_left,closed_right,closed_neither success null empty invalid eager lazy
#@ cover s_u32,s_f32,s_str,s_bool success null eager lazy
#@ cover s_null invalid eager lazy
#@ cover lit_u32,lit_f32,lit_str,lit_bool success null eager lazy
#@ cover select,lazy_select,col,alias success null empty invalid eager lazy
#@ na when,is_in,clip,is_between,is_between_closed zerocol -- every operand is a column, a zero-column frame has none
import Base
import ./../../frame.bend as DF
import ./../../src/expr.bend as X
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

def lu(v: U32) -> DF.Expr():
  DF.lit_u32(v)

def lf(v: F32) -> DF.Expr():
  DF.lit_f32(v)

def conds() -> List<&2, DF.Expr()>:
  [al(DF.when(c("k"), c("a"), c("b")), "w_u"), al(DF.when(c("k"), c("p"), c("q")), "w_i"), al(DF.when(c("k"), c("x"), c("y")), "w_f"), al(DF.when(c("k"), c("s"), DF.lit_str("z")), "w_s"), al(DF.when(c("k"), c("k"), DF.lit_bool(False{})), "w_k"), al(DF.when(DF.gt(c("a"), lu(1)), c("x"), lf(F32.neg(1.0))), "w_g")]

def isins() -> List<&2, DF.Expr()>:
  [al(DF.is_in(c("a"), [DF.s_u32(7), DF.s_u32(2), DF.s_u32(4294967295)]), "in_u"), al(DF.is_in(c("p"), [R.i(7), R.ineg(2147483648)]), "in_i"), al(DF.is_in(c("x"), [DF.s_f32(R.nan()), DF.s_f32(0.0)]), "in_f"), al(DF.is_in(c("s"), [DF.s_str("a"), DF.s_str("abc")]), "in_s"), al(DF.is_in(c("k"), [DF.s_bool(True{})]), "in_k"), al(DF.is_in(c("a"), []), "in_none")]

def clips() -> List<&2, DF.Expr()>:
  [al(DF.clip(c("a"), DF.s_u32(1), DF.s_u32(5)), "c_u"), al(DF.clip(c("p"), R.ineg(3), R.i(3)), "c_i"), al(DF.clip(c("x"), DF.s_f32(0.0), DF.s_f32(1.0)), "c_f"), al(DF.clip(c("a"), DF.s_u32(5), DF.s_u32(2)), "c_lohi")]

def betweens() -> List<&2, DF.Expr()>:
  [al(DF.is_between(c("a"), lu(1), lu(5)), "b_both"), al(DF.is_between_closed(c("a"), lu(1), lu(5), DF.closed_both()), "b_cboth"), al(DF.is_between_closed(c("a"), lu(1), lu(5), DF.closed_left()), "b_left"), al(DF.is_between_closed(c("a"), lu(1), lu(5), DF.closed_right()), "b_right"), al(DF.is_between_closed(c("a"), lu(1), lu(5), DF.closed_neither()), "b_neither"), al(DF.is_between(c("a"), lu(5), lu(1)), "b_lohi"), al(DF.is_between(c("x"), lf(0.0), c("y")), "b_f"), al(DF.is_between(c("s"), DF.lit_str("a"), DF.lit_str("abc")), "b_s"), al(DF.is_between(c("p"), DF.lit_i32_neg(7), DF.lit_i32(0)), "b_i")]

def cat(xs: List<&2, DF.Expr()>, ys: List<&2, DF.Expr()>) -> List<&2, DF.Expr()>:
  List.append(&2, X.Expr, xs, ys)

def main() -> IO(Unit):
  do IO<Unit>:
    sel("when then else, a null condition picks else", conds())
    sel("is_in u32 i32 f32 str bool, and an empty list", isins())
    sel("clip u32 i32 f32 with NaN and lo > hi", clips())
    sel("is_between closed both left right neither", betweens())
    selz("when is_in clip is_between, zero rows", cat(conds(), cat(isins(), cat(clips(), betweens()))))
    sel("invalid when condition u32", [DF.when(c("a"), c("a"), c("b"))])
    sel("invalid when branches u32 i32", [DF.when(c("k"), c("a"), c("p"))])
    sel("invalid when missing column", [DF.when(c("k"), c("a"), c("nope"))])
    sel("invalid is_in f32 scalar in u32 column", [DF.is_in(c("a"), [DF.s_f32(1.0)])])
    sel("invalid is_in null scalar", [DF.is_in(c("a"), [DF.s_u32(1), DF.s_null()])])
    sel("invalid is_in str scalar in bool column", [DF.is_in(c("k"), [DF.s_str("t")])])
    sel("invalid is_in missing column", [DF.is_in(c("nope"), [DF.s_u32(1)])])
    sel("invalid clip str", [DF.clip(c("s"), DF.s_str("a"), DF.s_str("b"))])
    sel("invalid clip bool", [DF.clip(c("k"), DF.s_bool(False{}), DF.s_bool(True{}))])
    sel("invalid clip f32 bounds on u32", [DF.clip(c("a"), DF.s_f32(0.0), DF.s_f32(1.0))])
    sel("invalid clip null upper bound", [DF.clip(c("a"), DF.s_u32(1), DF.s_null())])
    sel("invalid is_between f32 bounds on u32", [DF.is_between(c("a"), lf(0.0), lf(1.0))])
    sel("invalid is_between_closed left on i32 vs u32", [DF.is_between_closed(c("p"), lu(0), lu(1), DF.closed_left())])
    sel("invalid is_between_closed missing column", [DF.is_between_closed(c("nope"), lu(0), lu(1), DF.closed_right())])
    sel("invalid is_between_closed neither str vs u32", [DF.is_between_closed(c("s"), lu(0), lu(1), DF.closed_neither())])
#|-- when then else, a null condition picks else
#|frame
#|height	7
#|width	6
#|col	u32	"w_u"
#|col	i32	"w_i"
#|col	f32	"w_f"
#|col	str	"w_s"
#|col	bool	"w_k"
#|col	f32	"w_g"
#|row	7	7	0x3fc00000	"a"	true	0x3fc00000
#|row	3	2	0x3f000000	"z"	false	0xbf800000
#|row	1	-2	0x3f800000	"z"	false	null
#|row	null	-7	0x7fc00000	null	true	0xbf800000
#|row	null	-1	0x7f800000	"z"	false	0x7f800000
#|row	1	null	0x00000000	"ab"	true	0xbf800000
#|row	0	0	null	"z"	false	0x80000000
#|raw same, opt same, full same
#|
#|-- is_in u32 i32 f32 str bool, and an empty list
#|frame
#|height	7
#|width	6
#|col	bool	"in_u"
#|col	bool	"in_i"
#|col	bool	"in_f"
#|col	bool	"in_s"
#|col	bool	"in_k"
#|col	bool	"in_none"
#|row	true	true	false	true	true	false
#|row	false	false	false	false	false	false
#|row	true	true	null	false	null	false
#|row	null	false	true	null	true	null
#|row	false	true	false	true	false	false
#|row	false	null	true	false	true	false
#|row	true	false	true	true	null	false
#|raw same, opt same, full same
#|
#|-- clip u32 i32 f32 with NaN and lo > hi
#|frame
#|height	7
#|width	4
#|col	u32	"c_u"
#|col	i32	"c_i"
#|col	f32	"c_f"
#|col	u32	"c_lohi"
#|row	5	3	0x3f800000	2
#|row	1	-3	0x00000000	5
#|row	5	3	null	2
#|row	null	-3	0x7fc00000	null
#|row	5	-3	0x3f800000	2
#|row	1	null	0x00000000	5
#|row	2	0	0x80000000	5
#|raw same, opt same, full same
#|
#|-- is_between closed both left right neither
#|frame
#|height	7
#|width	9
#|col	bool	"b_both"
#|col	bool	"b_cboth"
#|col	bool	"b_left"
#|col	bool	"b_right"
#|col	bool	"b_neither"
#|col	bool	"b_lohi"
#|col	bool	"b_f"
#|col	bool	"b_s"
#|col	bool	"b_i"
#|row	false	false	false	false	false	false	true	true	false
#|row	false	false	false	false	false	false	false	false	true
#|row	false	false	false	false	false	false	null	false	false
#|row	null	null	null	null	null	null	false	null	true
#|row	true	true	false	true	false	false	true	true	false
#|row	true	true	true	false	false	false	true	true	null
#|row	true	true	true	true	true	false	null	true	true
#|raw same, opt same, full same
#|
#|-- when is_in clip is_between, zero rows
#|frame
#|height	0
#|width	25
#|col	u32	"w_u"
#|col	i32	"w_i"
#|col	f32	"w_f"
#|col	str	"w_s"
#|col	bool	"w_k"
#|col	f32	"w_g"
#|col	bool	"in_u"
#|col	bool	"in_i"
#|col	bool	"in_f"
#|col	bool	"in_s"
#|col	bool	"in_k"
#|col	bool	"in_none"
#|col	u32	"c_u"
#|col	i32	"c_i"
#|col	f32	"c_f"
#|col	u32	"c_lohi"
#|col	bool	"b_both"
#|col	bool	"b_cboth"
#|col	bool	"b_left"
#|col	bool	"b_right"
#|col	bool	"b_neither"
#|col	bool	"b_lohi"
#|col	bool	"b_f"
#|col	bool	"b_s"
#|col	bool	"b_i"
#|raw same, opt same, full same
#|
#|-- invalid when condition u32
#|error	TypeMismatch in when: expected bool, got u32
#|raw same, opt same, full same
#|
#|-- invalid when branches u32 i32
#|error	TypeMismatch in when: expected u32, got i32
#|raw same, opt same, full same
#|
#|-- invalid when missing column
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|-- invalid is_in f32 scalar in u32 column
#|error	TypeMismatch in is_in: expected u32, got f32
#|raw same, opt same, full same
#|
#|-- invalid is_in null scalar
#|error	TypeMismatch in is_in: expected u32, got null
#|raw same, opt same, full same
#|
#|-- invalid is_in str scalar in bool column
#|error	TypeMismatch in is_in: expected bool, got str
#|raw same, opt same, full same
#|
#|-- invalid is_in missing column
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|-- invalid clip str
#|error	TypeMismatch in clip: expected numeric, got str
#|raw same, opt same, full same
#|
#|-- invalid clip bool
#|error	TypeMismatch in clip: expected numeric, got bool
#|raw same, opt same, full same
#|
#|-- invalid clip f32 bounds on u32
#|error	TypeMismatch in clip: expected u32, got f32
#|raw same, opt same, full same
#|
#|-- invalid clip null upper bound
#|error	TypeMismatch in clip: expected u32, got null
#|raw same, opt same, full same
#|
#|-- invalid is_between f32 bounds on u32
#|error	TypeMismatch in ge: expected u32, got f32
#|raw same, opt same, full same
#|
#|-- invalid is_between_closed left on i32 vs u32
#|error	TypeMismatch in ge: expected i32, got u32
#|raw same, opt same, full same
#|
#|-- invalid is_between_closed missing column
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|-- invalid is_between_closed neither str vs u32
#|error	TypeMismatch in gt: expected str, got u32
#|raw same, opt same, full same
#|
