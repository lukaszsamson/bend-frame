# V02-B1 (plans/REVIEW_V02_FABLE.txt B1, plans/REVIEW_V02_ASTRA.txt section 1): a nullable f32 column
# stores +0.0 under its null mask; v0.2's F32 neg mapped that slot to -0.0 without resetting it, and
# F4 (fill_null(e, default) = "validity := AllValid, payload untouched") then answered -0.0 on the null
# rows: fill_null(neg(x), 0.0) gave [-0.0, -0.0, 0.0, -2.0] where v0.1 and Polars give [0.0, -0.0,
# 0.0, -2.0], and 1 / that gave -inf instead of +inf. Every engine agreed on the wrong answer (they
# share Eval.runz), so the matrix compares each one with the UNFUSED evaluator (Eval.full, no Eval.fuse)
# and prints the P0 report (src/p0.bend) of every result: "p0 ok" = every null slot holds the dtype
# default. DESIGN.md 14 "v0.2 post-review: the null-slot invariant".
#
# Input x = [null, 0.0, -0.0, 2.0] (f32), i = [null, 0, 5, -3] (i32). Expected values (IEEE, F32 bits as
# DF.dump prints them): neg x = [null, -0.0, +0.0, -2.0] (valid -0.0 controls: row 1 stays -0.0);
# fill_null(neg x, 0.0) = [+0.0, -0.0, +0.0, -2.0]; 1 / that = [+inf, -inf, +inf, -0.5];
# fill_null(neg x, -0.0) (not the default: Kernel.choose) = [-0.0, -0.0, +0.0, -2.0];
# sqrt(neg x) = [null, -0.0, +0.0, NaN] (IEEE sqrt(-0.0) = -0.0); abs(neg x) = [null, 0, 0, 2];
# x * -1.0 = [null, -0.0, +0.0, -2.0]; x - 5.0 = [null, -5, -5, -3]; 0.0 - x = [null, +0.0, +0.0, -2.0];
# cast(neg x, str) = [null, "-0", "0", "-2"] (15.5.5: F32.show); f32(neg i) = [null, 0, -5, 3];
# when(x > 0.0, neg x, null) = [null, null, null, -2.0] (row 0: a null condition picks otherwise);
# when(x > 0.0, x, neg x) = [null, -0.0, +0.0, 2.0]; neg i = [null, 0, -5, 3], abs i = [null, 0, 5, 3].
# Every fill_null with the default turns the null row into +0.0 / 0, never -0.0.
#@ cover neg,abs,sqrt,fill_null null eager lazy
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./lib/rx.bend as R
import ./lib/nz.bend as N

def t() -> E.ResT(C.Frame):
  R.frame([R.mk("x", [R.null(), R.f(0.0), R.f(R.nzero()), R.f(2.0)], D.TF32{}), R.mk("i", [R.null(), R.i(0), R.i(5), R.ineg(3)], D.TI32{})])

def x() -> X.Expr:
  DF.col("x")

def nx() -> X.Expr:
  DF.neg(DF.col("x"))

def z() -> X.Expr:
  DF.lit_f32(0.0)

def go(+tag: String, +is_sel: Bool, +pre: List<&2, N.NE>, +nes: List<&2, N.NE>) -> IO(Unit):
  N.run(tag, is_sel, pre, nes, t(), t(), t(), t(), t(), t(), t(), t())

def main() -> IO(Unit):
  do IO<Unit>:
    # the review's case: x is read once (moved into the fused fill: F4 on an owned column)
    go("B1 neg-fill moved", True{}, [], [N.ne("a", DF.fill_null(nx(), z()))])
    # x read again after the fill (borrowed by the expression, kept for the second output)
    go("B1 neg-fill borrowed", True{}, [], [N.ne("a", DF.fill_null(nx(), z())), N.ne("x", x())])
    # Astra's reciprocal: the sign of the zero decides the sign of the infinity
    go("B1 reciprocal", True{}, [], [N.ne("r", DF.div(DF.lit_f32(1.0), DF.fill_null(nx(), z())))])
    # -0.0 is not the default: the unfused Kernel.choose path, the literal written at the null row
    go("B1 fill negzero", True{}, [], [N.ne("a", DF.fill_null(nx(), DF.lit_f32(R.nzero())))])
    # other null producers feeding the fill, with the valid -0.0 control (no fill)
    go("B1 producers", True{}, [], [N.ne("neg", nx()), N.ne("sq", DF.fill_null(DF.sqrt(nx()), z())), N.ne("ab", DF.fill_null(DF.abs(nx()), z())), N.ne("m1", DF.fill_null(DF.mul(x(), DF.lit_f32(F32.neg(1.0))), z())), N.ne("s5", DF.fill_null(DF.sub(x(), DF.lit_f32(5.0)), z())), N.ne("zs", DF.fill_null(DF.sub(z(), x()), z()))])
    go("B1 casts", True{}, [], [N.ne("s", DF.fill_null(DF.cast(nx(), DF.t_str()), DF.lit_str("n"))), N.ne("f", DF.fill_null(DF.cast(DF.neg(DF.col("i")), DF.t_f32()), z()))])
    go("B1 when", True{}, [], [N.ne("w1", DF.fill_null(DF.when(DF.gt(x(), z()), nx(), DF.lit_null(DF.t_f32())), z())), N.ne("w2", DF.fill_null(DF.when(DF.gt(x(), z()), x(), nx()), z()))])
    go("B1 i32", True{}, [], [N.ne("a", DF.fill_null(DF.neg(DF.col("i")), DF.lit_i32(0))), N.ne("b", DF.fill_null(DF.abs(DF.col("i")), DF.lit_i32(0)))])
    # staged intermediates: neg(x) stored in the frame by a with_columns, then read as a frame column
    # by F1 with a fill side (Z1), by F4 alone moved (select) and borrowed (with_columns keeps y)
    go("B1 staged fill-side", True{}, [N.ne("y", nx())], [N.ne("z", DF.mul(DF.fill_null(DF.col("y"), z()), DF.lit_f32(2.0))), N.ne("q", DF.div(DF.lit_f32(1.0), DF.fill_null(DF.col("y"), z()))), N.ne("y", DF.col("y"))])
    go("B1 staged moved", True{}, [N.ne("y", nx())], [N.ne("z", DF.fill_null(DF.col("y"), z()))])
    go("B1 staged borrowed", False{}, [N.ne("y", nx())], [N.ne("z", DF.fill_null(DF.col("y"), z()))])
    # the stored intermediates themselves keep P0 (before the fix y's null slot held -0.0: p0 BAD)
    go("B1 stored", False{}, [N.ne("y", nx()), N.ne("s", DF.sqrt(nx())), N.ne("a", DF.abs(x())), N.ne("j", DF.neg(DF.col("i")))], [])
    # sign-sensitive consumers of the filled value: group_by (-0.0 and 0.0 are one key; the group's
    # representative is its first row's value: +0.0 from the null row) and a stable sort
    R.four("B1 group_by", R.e_group(t(), [DF.alias(DF.fill_null(nx(), z()), "k")], [DF.alias(DF.len(), "n")]), DF.lazy_group_by(R.src("t", t()), [DF.alias(DF.fill_null(nx(), z()), "k")], [DF.alias(DF.len(), "n")]), R.env1("t", t()), R.env1("t", t()), R.env1("t", t()))
    R.four("B1 sort", R.e_sort(R.e_select(t(), [DF.alias(DF.fill_null(nx(), z()), "k")]), [DF.asc("k")]), DF.lazy_sort(DF.lazy_select(R.src("t", t()), [DF.alias(DF.fill_null(nx(), z()), "k")]), [DF.asc("k")]), R.env1("t", t()), R.env1("t", t()), R.env1("t", t()))
#|-- B1 neg-fill moved unfused
#|frame
#|height	4
#|width	1
#|col	f32	"a"
#|row	0x00000000
#|row	0x80000000
#|row	0x00000000
#|row	0xc0000000
#|p0 ok
#|-- B1 neg-fill moved eager same
#|-- B1 neg-fill moved raw same
#|-- B1 neg-fill moved opt same
#|-- B1 neg-fill moved full same
#|-- B1 neg-fill moved c0 same
#|-- B1 neg-fill moved c2 same
#|
#|-- B1 neg-fill borrowed unfused
#|frame
#|height	4
#|width	2
#|col	f32	"a"
#|col	f32	"x"
#|row	0x00000000	null
#|row	0x80000000	0x00000000
#|row	0x00000000	0x80000000
#|row	0xc0000000	0x40000000
#|p0 ok
#|-- B1 neg-fill borrowed eager same
#|-- B1 neg-fill borrowed raw same
#|-- B1 neg-fill borrowed opt same
#|-- B1 neg-fill borrowed full same
#|-- B1 neg-fill borrowed c0 same
#|-- B1 neg-fill borrowed c2 same
#|
#|-- B1 reciprocal unfused
#|frame
#|height	4
#|width	1
#|col	f32	"r"
#|row	0x7f800000
#|row	0xff800000
#|row	0x7f800000
#|row	0xbf000000
#|p0 ok
#|-- B1 reciprocal eager same
#|-- B1 reciprocal raw same
#|-- B1 reciprocal opt same
#|-- B1 reciprocal full same
#|-- B1 reciprocal c0 same
#|-- B1 reciprocal c2 same
#|
#|-- B1 fill negzero unfused
#|frame
#|height	4
#|width	1
#|col	f32	"a"
#|row	0x80000000
#|row	0x80000000
#|row	0x00000000
#|row	0xc0000000
#|p0 ok
#|-- B1 fill negzero eager same
#|-- B1 fill negzero raw same
#|-- B1 fill negzero opt same
#|-- B1 fill negzero full same
#|-- B1 fill negzero c0 same
#|-- B1 fill negzero c2 same
#|
#|-- B1 producers unfused
#|frame
#|height	4
#|width	6
#|col	f32	"neg"
#|col	f32	"sq"
#|col	f32	"ab"
#|col	f32	"m1"
#|col	f32	"s5"
#|col	f32	"zs"
#|row	null	0x00000000	0x00000000	0x00000000	0x00000000	0x00000000
#|row	0x80000000	0x80000000	0x00000000	0x80000000	0xc0a00000	0x00000000
#|row	0x00000000	0x00000000	0x00000000	0x00000000	0xc0a00000	0x00000000
#|row	0xc0000000	0x7fc00000	0x40000000	0xc0000000	0xc0400000	0xc0000000
#|p0 ok
#|-- B1 producers eager same
#|-- B1 producers raw same
#|-- B1 producers opt same
#|-- B1 producers full same
#|-- B1 producers c0 same
#|-- B1 producers c2 same
#|
#|-- B1 casts unfused
#|frame
#|height	4
#|width	2
#|col	str	"s"
#|col	f32	"f"
#|row	"n"	0x00000000
#|row	"-0"	0x00000000
#|row	"0"	0xc0a00000
#|row	"-2"	0x40400000
#|p0 ok
#|-- B1 casts eager same
#|-- B1 casts raw same
#|-- B1 casts opt same
#|-- B1 casts full same
#|-- B1 casts c0 same
#|-- B1 casts c2 same
#|
#|-- B1 when unfused
#|frame
#|height	4
#|width	2
#|col	f32	"w1"
#|col	f32	"w2"
#|row	0x00000000	0x00000000
#|row	0x00000000	0x80000000
#|row	0x00000000	0x00000000
#|row	0xc0000000	0x40000000
#|p0 ok
#|-- B1 when eager same
#|-- B1 when raw same
#|-- B1 when opt same
#|-- B1 when full same
#|-- B1 when c0 same
#|-- B1 when c2 same
#|
#|-- B1 i32 unfused
#|frame
#|height	4
#|width	2
#|col	i32	"a"
#|col	i32	"b"
#|row	0	0
#|row	0	0
#|row	-5	5
#|row	3	3
#|p0 ok
#|-- B1 i32 eager same
#|-- B1 i32 raw same
#|-- B1 i32 opt same
#|-- B1 i32 full same
#|-- B1 i32 c0 same
#|-- B1 i32 c2 same
#|
#|-- B1 staged fill-side unfused
#|frame
#|height	4
#|width	3
#|col	f32	"z"
#|col	f32	"q"
#|col	f32	"y"
#|row	0x00000000	0x7f800000	null
#|row	0x80000000	0xff800000	0x80000000
#|row	0x00000000	0x7f800000	0x00000000
#|row	0xc0800000	0xbf000000	0xc0000000
#|p0 ok
#|-- B1 staged fill-side eager same
#|-- B1 staged fill-side raw same
#|-- B1 staged fill-side opt same
#|-- B1 staged fill-side full same
#|-- B1 staged fill-side c0 same
#|-- B1 staged fill-side c2 same
#|
#|-- B1 staged moved unfused
#|frame
#|height	4
#|width	1
#|col	f32	"z"
#|row	0x00000000
#|row	0x80000000
#|row	0x00000000
#|row	0xc0000000
#|p0 ok
#|-- B1 staged moved eager same
#|-- B1 staged moved raw same
#|-- B1 staged moved opt same
#|-- B1 staged moved full same
#|-- B1 staged moved c0 same
#|-- B1 staged moved c2 same
#|
#|-- B1 staged borrowed unfused
#|frame
#|height	4
#|width	4
#|col	f32	"x"
#|col	i32	"i"
#|col	f32	"y"
#|col	f32	"z"
#|row	null	null	null	0x00000000
#|row	0x00000000	0	0x80000000	0x80000000
#|row	0x80000000	5	0x00000000	0x00000000
#|row	0x40000000	-3	0xc0000000	0xc0000000
#|p0 ok
#|-- B1 staged borrowed eager same
#|-- B1 staged borrowed raw same
#|-- B1 staged borrowed opt same
#|-- B1 staged borrowed full same
#|-- B1 staged borrowed c0 same
#|-- B1 staged borrowed c2 same
#|
#|-- B1 stored unfused
#|frame
#|height	4
#|width	6
#|col	f32	"x"
#|col	i32	"i"
#|col	f32	"y"
#|col	f32	"s"
#|col	f32	"a"
#|col	i32	"j"
#|row	null	null	null	null	null	null
#|row	0x00000000	0	0x80000000	0x80000000	0x00000000	0
#|row	0x80000000	5	0x00000000	0x00000000	0x00000000	-5
#|row	0x40000000	-3	0xc0000000	0x7fc00000	0x40000000	3
#|p0 ok
#|-- B1 stored eager same
#|-- B1 stored raw same
#|-- B1 stored opt same
#|-- B1 stored full same
#|-- B1 stored c0 same
#|-- B1 stored c2 same
#|
#|-- B1 group_by
#|frame
#|height	2
#|width	2
#|col	f32	"k"
#|col	u32	"n"
#|row	0x00000000	3
#|row	0xc0000000	1
#|raw same, opt same, full same
#|
#|-- B1 sort
#|frame
#|height	4
#|width	1
#|col	f32	"k"
#|row	0xc0000000
#|row	0x00000000
#|row	0x80000000
#|row	0x00000000
#|raw same, opt same, full same
#|
