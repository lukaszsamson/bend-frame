# T6 coverage: comparisons, Kleene logic, null tests and fill_null (eq, ne, lt, le, gt, ge, and, or,
# not, is_null, is_not_null, fill_null) over the nullable fixture t (tests/coverage/lib/fx.bend).
# Cases: every dtype's six comparisons with null rows (f32: NaN, inf, -0.0: the 15.5.2 order), Kleene
# and / or / not (false & null = false, true | null = true), null tests, fill_null; a zero-row frame;
# the refusals. Eager (DX.e_select) and lazy (DF.lazy_select, raw / opt / full) agree (R.four).
# Expectations: DESIGN.md 15.5.2, 15.2.6, confirmed by bench/coverage/expr_cmp.py (Polars 2.0.0);
# departures applied there: no coercion across dtypes (Polars supertypes u32 vs i32).
#@ cover eq,ne,lt,le,gt,ge,and,or,not,is_null,is_not_null,fill_null success null empty invalid eager lazy
#@ cover lit_u32,lit_f32,lit_str,lit_bool,lit_i32,lit_i32_neg success null eager lazy
#@ cover col,alias success null empty invalid eager lazy
#@ cover select,lazy_select success null empty invalid eager lazy
#@ na eq,ne,lt,le,gt,ge,and,or,not,is_null,is_not_null,fill_null zerocol -- every operand is a column, a zero-column frame has none
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

# the six comparisons of two expressions, named <p>_eq .. <p>_ge
def six(+p: String, +l: DF.Expr(), +r: DF.Expr()) -> List<&2, DF.Expr()>:
  [al(DF.eq(l, r), p ++ "_eq"), al(DF.ne(l, r), p ++ "_ne"), al(DF.lt(l, r), p ++ "_lt"), al(DF.le(l, r), p ++ "_le"), al(DF.gt(l, r), p ++ "_gt"), al(DF.ge(l, r), p ++ "_ge")]

def cat(xs: List<&2, DF.Expr()>, ys: List<&2, DF.Expr()>) -> List<&2, DF.Expr()>:
  List.append(&2, X.Expr, xs, ys)

def all() -> List<&2, DF.Expr()>:
  cat(six("u", c("a"), c("b")), cat(six("i", c("p"), c("q")), cat(six("f", c("x"), c("y")), cat(six("s", c("s"), DF.lit_str("ab")), cat(six("k", c("k"), DF.lit_bool(True{})), [al(DF.and(c("k"), DF.gt(c("a"), DF.lit_u32(1))), "and"), al(DF.or(c("k"), DF.gt(c("a"), DF.lit_u32(1))), "or"), al(DF.not(c("k")), "not"), al(DF.is_null(c("x")), "isnull"), al(DF.is_not_null(c("s")), "notnull"), al(DF.fill_null(c("a"), DF.lit_u32(9)), "fill")])))))

def main() -> IO(Unit):
  do IO<Unit>:
    sel("cmp u32 with nulls", six("u", c("a"), c("b")))
    sel("cmp i32 MIN and negatives", six("i", c("p"), c("q")))
    sel("cmp f32 NaN inf -0.0 (the 15.5.2 order)", six("f", c("x"), c("y")))
    sel("cmp f32 against a literal", six("f0", c("x"), DF.lit_f32(0.0)))
    sel("cmp str against a literal", six("s", c("s"), DF.lit_str("ab")))
    sel("cmp bool against a literal", six("k", c("k"), DF.lit_bool(True{})))
    sel("cmp i32 against literals", cat(six("i1", c("p"), DF.lit_i32_neg(7)), six("i2", c("q"), DF.lit_i32(2))))
    sel("and or not Kleene, both operands nullable", [al(DF.and(c("k"), DF.gt(c("a"), DF.lit_u32(1))), "and_a"), al(DF.or(c("k"), DF.gt(c("a"), DF.lit_u32(1))), "or_a"), al(DF.and(c("k"), DF.gt(c("b"), DF.lit_u32(0))), "and_b"), al(DF.or(c("k"), DF.gt(c("b"), DF.lit_u32(0))), "or_b"), al(DF.not(c("k")), "not_k"), al(DF.not(DF.gt(c("a"), DF.lit_u32(1))), "not_a")])
    sel("is_null is_not_null on every dtype", [al(DF.is_null(c("a")), "n_a"), al(DF.is_null(c("p")), "n_p"), al(DF.is_null(c("x")), "n_x"), al(DF.is_null(c("k")), "n_k"), al(DF.is_null(c("s")), "n_s"), al(DF.is_not_null(c("a")), "v_a"), al(DF.is_not_null(c("p")), "v_p"), al(DF.is_not_null(c("x")), "v_x"), al(DF.is_not_null(c("k")), "v_k"), al(DF.is_not_null(c("s")), "v_s")])
    sel("fill_null with a literal and with a column", [al(DF.fill_null(c("a"), DF.lit_u32(9)), "fa"), al(DF.fill_null(c("p"), DF.lit_i32_neg(1)), "fp"), al(DF.fill_null(c("x"), DF.lit_f32(0.5)), "fx"), al(DF.fill_null(c("s"), DF.lit_str("?")), "fs"), al(DF.fill_null(c("k"), DF.lit_bool(False{})), "fk"), al(DF.fill_null(c("b"), c("a")), "fb")])
    selz("every comparison logic and null test, zero rows", all())
    sel("invalid eq u32 vs i32", [DF.eq(c("a"), c("p"))])
    sel("invalid ne bool vs u32", [DF.ne(c("k"), c("a"))])
    sel("invalid lt str vs f32", [DF.lt(c("s"), c("x"))])
    sel("invalid le f32 vs literal u32", [DF.le(c("x"), DF.lit_u32(1))])
    sel("invalid gt missing column", [DF.gt(c("nope"), c("a"))])
    sel("invalid ge i32 vs u32 literal", [DF.ge(c("p"), DF.lit_u32(1))])
    sel("invalid and u32", [DF.and(c("a"), c("k"))])
    sel("invalid and bool and u32", [DF.and(c("k"), c("a"))])
    sel("invalid or str", [DF.or(c("s"), c("k"))])
    sel("invalid not u32", [DF.not(c("a"))])
    sel("invalid is_null missing column", [DF.is_null(c("nope"))])
    sel("invalid is_not_null missing column", [DF.is_not_null(c("nope"))])
    sel("invalid fill_null u32 with f32", [DF.fill_null(c("a"), DF.lit_f32(1.0))])
    sel("invalid fill_null str with u32 column", [DF.fill_null(c("s"), c("a"))])
#|-- cmp u32 with nulls
#|frame
#|height	7
#|width	6
#|col	bool	"u_eq"
#|col	bool	"u_ne"
#|col	bool	"u_lt"
#|col	bool	"u_le"
#|col	bool	"u_gt"
#|col	bool	"u_ge"
#|row	false	true	false	false	true	true
#|row	false	true	true	true	false	false
#|row	false	true	false	false	true	true
#|row	null	null	null	null	null	null
#|row	null	null	null	null	null	null
#|row	false	true	false	false	true	true
#|row	false	true	false	false	true	true
#|raw same, opt same, full same
#|
#|-- cmp i32 MIN and negatives
#|frame
#|height	7
#|width	6
#|col	bool	"i_eq"
#|col	bool	"i_ne"
#|col	bool	"i_lt"
#|col	bool	"i_le"
#|col	bool	"i_gt"
#|col	bool	"i_ge"
#|row	false	true	false	false	true	true
#|row	false	true	true	true	false	false
#|row	false	true	false	false	true	true
#|row	false	true	true	true	false	false
#|row	false	true	true	true	false	false
#|row	null	null	null	null	null	null
#|row	true	false	false	true	false	true
#|raw same, opt same, full same
#|
#|-- cmp f32 NaN inf -0.0 (the 15.5.2 order)
#|frame
#|height	7
#|width	6
#|col	bool	"f_eq"
#|col	bool	"f_ne"
#|col	bool	"f_lt"
#|col	bool	"f_le"
#|col	bool	"f_gt"
#|col	bool	"f_ge"
#|row	false	true	true	true	false	false
#|row	false	true	true	true	false	false
#|row	null	null	null	null	null	null
#|row	false	true	false	false	true	true
#|row	true	false	false	true	false	true
#|row	true	false	false	true	false	true
#|row	null	null	null	null	null	null
#|raw same, opt same, full same
#|
#|-- cmp f32 against a literal
#|frame
#|height	7
#|width	6
#|col	bool	"f0_eq"
#|col	bool	"f0_ne"
#|col	bool	"f0_lt"
#|col	bool	"f0_le"
#|col	bool	"f0_gt"
#|col	bool	"f0_ge"
#|row	false	true	false	false	true	true
#|row	false	true	true	true	false	false
#|row	null	null	null	null	null	null
#|row	false	true	false	false	true	true
#|row	false	true	false	false	true	true
#|row	true	false	false	true	false	true
#|row	true	false	false	true	false	true
#|raw same, opt same, full same
#|
#|-- cmp str against a literal
#|frame
#|height	7
#|width	6
#|col	bool	"s_eq"
#|col	bool	"s_ne"
#|col	bool	"s_lt"
#|col	bool	"s_le"
#|col	bool	"s_gt"
#|col	bool	"s_ge"
#|row	false	true	true	true	false	false
#|row	false	true	true	true	false	false
#|row	false	true	false	false	true	true
#|row	null	null	null	null	null	null
#|row	false	true	false	false	true	true
#|row	true	false	false	true	false	true
#|row	false	true	true	true	false	false
#|raw same, opt same, full same
#|
#|-- cmp bool against a literal
#|frame
#|height	7
#|width	6
#|col	bool	"k_eq"
#|col	bool	"k_ne"
#|col	bool	"k_lt"
#|col	bool	"k_le"
#|col	bool	"k_gt"
#|col	bool	"k_ge"
#|row	true	false	false	true	false	true
#|row	false	true	true	true	false	false
#|row	null	null	null	null	null	null
#|row	true	false	false	true	false	true
#|row	false	true	true	true	false	false
#|row	true	false	false	true	false	true
#|row	null	null	null	null	null	null
#|raw same, opt same, full same
#|
#|-- cmp i32 against literals
#|frame
#|height	7
#|width	12
#|col	bool	"i1_eq"
#|col	bool	"i1_ne"
#|col	bool	"i1_lt"
#|col	bool	"i1_le"
#|col	bool	"i1_gt"
#|col	bool	"i1_ge"
#|col	bool	"i2_eq"
#|col	bool	"i2_ne"
#|col	bool	"i2_lt"
#|col	bool	"i2_le"
#|col	bool	"i2_gt"
#|col	bool	"i2_ge"
#|row	false	true	false	false	true	true	true	false	false	true	false	true
#|row	true	false	false	true	false	true	true	false	false	true	false	true
#|row	false	true	false	false	true	true	false	true	true	true	false	false
#|row	true	false	false	true	false	true	false	true	true	true	false	false
#|row	false	true	true	true	false	false	false	true	true	true	false	false
#|row	null	null	null	null	null	null	false	true	true	true	false	false
#|row	false	true	false	false	true	true	false	true	true	true	false	false
#|raw same, opt same, full same
#|
#|-- and or not Kleene, both operands nullable
#|frame
#|height	7
#|width	6
#|col	bool	"and_a"
#|col	bool	"or_a"
#|col	bool	"and_b"
#|col	bool	"or_b"
#|col	bool	"not_k"
#|col	bool	"not_a"
#|row	true	true	true	true	false	false
#|row	false	false	false	true	true	true
#|row	null	true	null	true	null	false
#|row	null	true	true	true	false	null
#|row	false	true	false	null	true	false
#|row	false	true	false	true	false	true
#|row	null	true	false	null	null	false
#|raw same, opt same, full same
#|
#|-- is_null is_not_null on every dtype
#|frame
#|height	7
#|width	10
#|col	bool	"n_a"
#|col	bool	"n_p"
#|col	bool	"n_x"
#|col	bool	"n_k"
#|col	bool	"n_s"
#|col	bool	"v_a"
#|col	bool	"v_p"
#|col	bool	"v_x"
#|col	bool	"v_k"
#|col	bool	"v_s"
#|row	false	false	false	false	false	true	true	true	true	true
#|row	false	false	false	false	false	true	true	true	true	true
#|row	false	false	true	true	false	true	true	false	false	true
#|row	true	false	false	false	true	false	true	true	true	false
#|row	false	false	false	false	false	true	true	true	true	true
#|row	false	true	false	false	false	true	false	true	true	true
#|row	false	false	false	true	false	true	true	true	false	true
#|raw same, opt same, full same
#|
#|-- fill_null with a literal and with a column
#|frame
#|height	7
#|width	6
#|col	u32	"fa"
#|col	i32	"fp"
#|col	f32	"fx"
#|col	str	"fs"
#|col	bool	"fk"
#|col	u32	"fb"
#|row	7	7	0x3fc00000	"a"	true	2
#|row	0	-7	0xc0000000	""	false	3
#|row	4294967295	7	0x3f000000	"é"	false	1
#|row	9	-7	0x7fc00000	"?"	true	1
#|row	5	-2147483648	0x7f800000	"abc"	false	5
#|row	1	-1	0x00000000	"ab"	true	0
#|row	2	0	0x80000000	"a"	false	0
#|raw same, opt same, full same
#|
#|-- every comparison logic and null test, zero rows
#|frame
#|height	0
#|width	36
#|col	bool	"u_eq"
#|col	bool	"u_ne"
#|col	bool	"u_lt"
#|col	bool	"u_le"
#|col	bool	"u_gt"
#|col	bool	"u_ge"
#|col	bool	"i_eq"
#|col	bool	"i_ne"
#|col	bool	"i_lt"
#|col	bool	"i_le"
#|col	bool	"i_gt"
#|col	bool	"i_ge"
#|col	bool	"f_eq"
#|col	bool	"f_ne"
#|col	bool	"f_lt"
#|col	bool	"f_le"
#|col	bool	"f_gt"
#|col	bool	"f_ge"
#|col	bool	"s_eq"
#|col	bool	"s_ne"
#|col	bool	"s_lt"
#|col	bool	"s_le"
#|col	bool	"s_gt"
#|col	bool	"s_ge"
#|col	bool	"k_eq"
#|col	bool	"k_ne"
#|col	bool	"k_lt"
#|col	bool	"k_le"
#|col	bool	"k_gt"
#|col	bool	"k_ge"
#|col	bool	"and"
#|col	bool	"or"
#|col	bool	"not"
#|col	bool	"isnull"
#|col	bool	"notnull"
#|col	u32	"fill"
#|raw same, opt same, full same
#|
#|-- invalid eq u32 vs i32
#|error	TypeMismatch in eq: expected u32, got i32
#|raw same, opt same, full same
#|
#|-- invalid ne bool vs u32
#|error	TypeMismatch in ne: expected bool, got u32
#|raw same, opt same, full same
#|
#|-- invalid lt str vs f32
#|error	TypeMismatch in lt: expected str, got f32
#|raw same, opt same, full same
#|
#|-- invalid le f32 vs literal u32
#|error	TypeMismatch in le: expected f32, got u32
#|raw same, opt same, full same
#|
#|-- invalid gt missing column
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|-- invalid ge i32 vs u32 literal
#|error	TypeMismatch in ge: expected i32, got u32
#|raw same, opt same, full same
#|
#|-- invalid and u32
#|error	TypeMismatch in and: expected bool, got u32
#|raw same, opt same, full same
#|
#|-- invalid and bool and u32
#|error	TypeMismatch in and: expected bool, got u32
#|raw same, opt same, full same
#|
#|-- invalid or str
#|error	TypeMismatch in or: expected bool, got str
#|raw same, opt same, full same
#|
#|-- invalid not u32
#|error	TypeMismatch in not: expected bool, got u32
#|raw same, opt same, full same
#|
#|-- invalid is_null missing column
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|-- invalid is_not_null missing column
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|-- invalid fill_null u32 with f32
#|error	TypeMismatch in fill_null: expected u32, got f32
#|raw same, opt same, full same
#|
#|-- invalid fill_null str with u32 column
#|error	TypeMismatch in fill_null: expected str, got u32
#|raw same, opt same, full same
#|
