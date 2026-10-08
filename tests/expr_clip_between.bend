# M3 clip(e, lo, hi) and is_between (DESIGN.md 15.2.6). clip: lo if x < lo, else hi if x > hi,
# else x; f32 with IEEE < / > (NaN passes, -0.0 is not clipped by 0.0); lo > hi gives lo below lo
# and hi otherwise (Polars clip(8, 2) of [1, 5, 10] = [8, 8, 2]); null stays null.
# is_between is sugar: (e >= lo) & (e <= hi), Gt / Lt for an open end, the comparisons' typing
# and the 15.5.2 relation (so NaN is above every bound); lo > hi gives false.
import Base
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/expr.bend as X
import ./../src/plan.bend as P
import ./regress/lib/rx.bend as R

def t() -> E.ResT(C.Frame):
  R.frame([
    R.mk("u", [R.u(1), R.u(5), R.u(10), R.null(), R.u(0), R.u(4294967295)], D.TU32{}),
    R.mk("i", [R.ineg(5), R.i(0), R.i(7), R.null(), R.ineg(2147483648), R.i(3)], D.TI32{}),
    R.mk("f", [R.f(R.nan()), R.f(R.nzero()), R.f(0.5), R.null(), R.f(R.ninf()), R.f(3.0)], D.TF32{}),
    R.mk("s", [R.s("a"), R.s("b"), R.s("c"), R.s("d"), R.s("e"), R.s("f")], D.TStr{})])

def env() -> P.Env:
  R.env1("t", t())

def src() -> P.Plan:
  R.src("t", t())

def clips() -> List<&2, X.Expr>:
  [DF.clip(DF.col("u"), DF.s_u32(2), DF.s_u32(8)), DF.alias(DF.clip(DF.col("u"), DF.s_u32(8), DF.s_u32(2)), "u_8_2"), DF.clip(DF.col("i"), R.ineg(1), R.i(4)), DF.clip(DF.col("f"), DF.s_f32(0.0), DF.s_f32(1.0))]

def i() -> X.Expr:
  DF.col("i")

def betw() -> List<&2, X.Expr>:
  [DF.is_between(DF.col("u"), DF.lit_u32(2), DF.lit_u32(8)), DF.alias(DF.is_between_closed(i(), DF.lit_i32(0), DF.lit_i32(3), DF.closed_both()), "both"), DF.alias(DF.is_between_closed(i(), DF.lit_i32(0), DF.lit_i32(3), DF.closed_left()), "left"), DF.alias(DF.is_between_closed(i(), DF.lit_i32(0), DF.lit_i32(3), DF.closed_right()), "right"), DF.alias(DF.is_between_closed(i(), DF.lit_i32(0), DF.lit_i32(3), DF.closed_neither()), "neither"), DF.alias(DF.is_between(DF.col("u"), DF.lit_u32(8), DF.lit_u32(2)), "lo_gt_hi"), DF.is_between(DF.col("f"), DF.lit_f32(0.0), DF.lit_f32(1.0))]

def bad(+e: X.Expr) -> IO(Unit):
  R.agree("clip error", R.e_select(t(), [e]), DF.lazy_select(src(), [e]), env(), env(), env())

def main() -> IO(Unit):
  do IO<Unit>:
    R.agree("clip", R.e_select(t(), clips()), DF.lazy_select(src(), clips()), env(), env(), env())
    R.agree("clip with_columns in place", R.e_with(t(), [DF.clip(DF.col("u"), DF.s_u32(2), DF.s_u32(8))]), DF.lazy_with_columns(src(), [DF.clip(DF.col("u"), DF.s_u32(2), DF.s_u32(8))]), env(), env(), env())
    bad(DF.clip(DF.col("s"), DF.s_u32(1), DF.s_u32(2)))
    bad(DF.clip(DF.col("u"), R.i(1), DF.s_u32(2)))
    bad(DF.clip(DF.col("u"), DF.s_u32(1), DF.s_null()))
    bad(DF.clip(DF.col("f"), DF.s_f32(1.0), DF.s_u32(2)))
    R.agree("is_between", R.e_select(t(), betw()), DF.lazy_select(src(), betw()), env(), env(), env())
    R.agree("is_between filter", R.e_filter(t(), DF.is_between(i(), DF.lit_i32(0), DF.lit_i32(3))), DF.lazy_filter(src(), DF.is_between(i(), DF.lit_i32(0), DF.lit_i32(3))), env(), env(), env())
    R.agree("is_between error", R.e_select(t(), [DF.is_between(DF.col("u"), DF.lit_i32(1), DF.lit_u32(2))]), DF.lazy_select(src(), [DF.is_between(DF.col("u"), DF.lit_i32(1), DF.lit_u32(2))]), env(), env(), env())
    IO.print(DF.explain(DF.lazy_select(src(), [DF.clip(DF.col("f"), DF.s_f32(0.0), DF.s_f32(1.0)), DF.is_between_closed(i(), DF.lit_i32(0), DF.lit_i32(3), DF.closed_left())])) ++ "\n")
#|-- clip
#|frame
#|height	6
#|width	4
#|col	u32	"u"
#|col	u32	"u_8_2"
#|col	i32	"i"
#|col	f32	"f"
#|row	2	8	-1	0x7fc00000
#|row	5	8	0	0x80000000
#|row	8	2	4	0x3f000000
#|row	null	null	null	null
#|row	2	8	-1	0x00000000
#|row	8	2	3	0x3f800000
#|raw=eager opt=eager full=eager
#|
#|-- clip with_columns in place
#|frame
#|height	6
#|width	4
#|col	u32	"u"
#|col	i32	"i"
#|col	f32	"f"
#|col	str	"s"
#|row	2	-5	0x7fc00000	"a"
#|row	5	0	0x80000000	"b"
#|row	8	7	0x3f000000	"c"
#|row	null	null	null	"d"
#|row	2	-2147483648	0xff800000	"e"
#|row	8	3	0x40400000	"f"
#|raw=eager opt=eager full=eager
#|
#|-- clip error
#|error	TypeMismatch in clip: expected numeric, got str
#|raw=eager opt=eager full=eager
#|
#|-- clip error
#|error	TypeMismatch in clip: expected u32, got i32
#|raw=eager opt=eager full=eager
#|
#|-- clip error
#|error	TypeMismatch in clip: expected u32, got null
#|raw=eager opt=eager full=eager
#|
#|-- clip error
#|error	TypeMismatch in clip: expected f32, got u32
#|raw=eager opt=eager full=eager
#|
#|-- is_between
#|frame
#|height	6
#|width	7
#|col	bool	"u"
#|col	bool	"both"
#|col	bool	"left"
#|col	bool	"right"
#|col	bool	"neither"
#|col	bool	"lo_gt_hi"
#|col	bool	"f"
#|row	false	false	false	false	false	false	false
#|row	true	true	true	false	false	false	true
#|row	false	false	false	false	false	false	true
#|row	null	null	null	null	null	null	null
#|row	false	false	false	false	false	false	false
#|row	false	true	false	true	false	false	false
#|raw=eager opt=eager full=eager
#|
#|-- is_between filter
#|frame
#|height	2
#|width	4
#|col	u32	"u"
#|col	i32	"i"
#|col	f32	"f"
#|col	str	"s"
#|row	5	0	0x80000000	"b"
#|row	4294967295	3	0x40400000	"f"
#|raw=eager opt=eager full=eager
#|
#|-- is_between error
#|error	TypeMismatch in ge: expected u32, got i32
#|raw=eager opt=eager full=eager
#|
#|SELECT [col("f").clip(0, 1), ((col("i") >= lit(0)) & (col("i") < lit(3)))]
#|  SOURCE t [u:u32, i:i32, f:f32, s:str]
