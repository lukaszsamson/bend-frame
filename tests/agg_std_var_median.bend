# M3 std / var / median (DESIGN.md 15.2.5, 15.5.4): f32 results for u32 / i32 / f32 inputs; ddof = 1
# two-pass std / var (null below two valid values; NaN or inf in the data -> NaN); median by the
# 15.5.2 order (NaN greatest), lo*0.5 + hi*0.5 for an even count. Eager select, global reductions
# in with_columns / filter, group_by (each group equals the eager kernel over its rows), the
# empty frame, nested aggregations and typing errors. Expected bits: bench/diff/oracle.reduce_
# (the contract's algorithm in numpy float32); the worked examples of 15.5.4 are among them
# ([1,2,4] -> std 0x3fc385f3; [3,1,2] -> 2; [4,1,2,3] -> 2.5; [1,null,3,10] -> 3; [1,NaN,3] -> 3;
# [-3e38, 3e38] -> 0.0; [3e38, 3e38] -> 3e38; [inf, -inf] -> NaN).
import Base
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/expr.bend as X
import ./../src/plan.bend as P
import ./regress/lib/rx.bend as R

def big() -> F32:
  300000000000000000000000000000000000000.0

def m() -> E.ResT(C.Frame):
  R.frame([
    R.mk("w", [R.f(1.0), R.f(2.0), R.f(4.0), R.null()], D.TF32{}),
    R.mk("a", [R.u(3), R.u(1), R.u(2), R.null()], D.TU32{}),
    R.mk("b", [R.f(4.0), R.f(1.0), R.f(2.0), R.f(3.0)], D.TF32{}),
    R.mk("c", [R.i(1), R.null(), R.i(3), R.i(10)], D.TI32{}),
    R.mk("d", [R.f(1.0), R.f(R.nan()), R.f(3.0), R.null()], D.TF32{}),
    R.mk("e", [R.f(F32.neg(big())), R.f(big()), R.null(), R.null()], D.TF32{}),
    R.mk("g", [R.null(), R.f(big()), R.null(), R.f(big())], D.TF32{}),
    R.mk("h", [R.f(R.inf()), R.null(), R.f(R.ninf()), R.null()], D.TF32{}),
    R.mk("k", [R.null(), R.null(), R.f(5.0), R.null()], D.TF32{}),
    R.mk("z", [R.null(), R.null(), R.null(), R.null()], D.TF32{}),
    R.mk("s", [R.s("p"), R.s("q"), R.s("r"), R.s("s")], D.TStr{})])

def menv() -> P.Env:
  R.env1("m", m())

def msrc() -> P.Plan:
  R.src("m", m())

def g() -> E.ResT(C.Frame):
  R.frame([
    R.mk("g", [R.s("a"), R.s("b"), R.s("a"), R.s("b"), R.s("a"), R.s("c"), R.s("c")], D.TStr{}),
    R.mk("v", [R.f(1.0), R.f(10.0), R.f(2.0), R.null(), R.f(4.0), R.f(R.nan()), R.f(5.0)], D.TF32{}),
    R.mk("v2", [R.ineg(1), R.i(2), R.ineg(3), R.i(4), R.null(), R.i(6), R.i(6)], D.TI32{}),
    R.mk("b", [R.b(True{}), R.b(False{}), R.b(True{}), R.b(False{}), R.b(True{}), R.b(False{}), R.b(True{})], D.TBool{})])

def genv() -> P.Env:
  R.env1("g", g())

def gsrc() -> P.Plan:
  R.src("g", g())

def g0() -> E.ResT(C.Frame):
  R.frame([R.mk("g", [], D.TStr{}), R.mk("v", [], D.TF32{})])

def three(+n: String) -> List<&2, X.Expr>:
  [DF.alias(DF.std(DF.col(n)), "std_" ++ n), DF.alias(DF.var(DF.col(n)), "var_" ++ n), DF.alias(DF.median(DF.col(n)), "med_" ++ n)]

def stats() -> List<&2, X.Expr>:
  List.concat(&2, X.Expr, [three("w"), three("a"), three("b"), three("c"), three("d"), three("e"), three("g"), three("h"), three("k"), three("z")])

def gaggs() -> List<&2, X.Expr>:
  [DF.alias(DF.std(DF.col("v")), "sd"), DF.alias(DF.var(DF.col("v")), "va"), DF.alias(DF.median(DF.col("v")), "md"), DF.alias(DF.std(DF.col("v2")), "sd2"), DF.alias(DF.var(DF.col("v2")), "va2"), DF.alias(DF.median(DF.col("v2")), "md2"), DF.alias(DF.median(DF.lit_u32(2)), "mlit"), DF.alias(DF.std(DF.lit_f32(1.0)), "slit")]

def v() -> X.Expr:
  DF.col("v")

def bad(+tag: String, +e: X.Expr) -> IO(Unit):
  R.agree(tag, R.e_select(g(), [e]), DF.lazy_select(gsrc(), [e]), genv(), genv(), genv())

def main() -> IO(Unit):
  do IO<Unit>:
    R.agree("stats select", R.e_select(m(), stats()), DF.lazy_select(msrc(), stats()), menv(), menv(), menv())
    R.agree("stats group_by", R.e_group(g(), [DF.col("g")], gaggs()), DF.lazy_group_by(gsrc(), [DF.col("g")], gaggs()), genv(), genv(), genv())
    R.agree("stats group_by bool key", R.e_group(g(), [DF.col("b")], [DF.alias(DF.median(v()), "md"), DF.alias(DF.std(DF.col("v2")), "sd2")]), DF.lazy_group_by(gsrc(), [DF.col("b")], [DF.alias(DF.median(v()), "md"), DF.alias(DF.std(DF.col("v2")), "sd2")]), genv(), genv(), genv())
    R.agree("median broadcast", R.e_with(g(), [DF.alias(DF.sub(v(), DF.median(v())), "dv")]), DF.lazy_with_columns(gsrc(), [DF.alias(DF.sub(v(), DF.median(v())), "dv")]), genv(), genv(), genv())
    R.agree("median filter", R.e_filter(g(), DF.gt(v(), DF.median(v()))), DF.lazy_filter(gsrc(), DF.gt(v(), DF.median(v()))), genv(), genv(), genv())
    R.agree("stats h0 select", R.e_select(g0(), three("v")), DF.lazy_select(R.src("g", g0()), three("v")), R.env1("g", g0()), R.env1("g", g0()), R.env1("g", g0()))
    R.agree("stats h0 group_by", R.e_group(g0(), [DF.col("g")], three("v")), DF.lazy_group_by(R.src("g", g0()), [DF.col("g")], three("v")), R.env1("g", g0()), R.env1("g", g0()), R.env1("g", g0()))
    bad("std of str", DF.std(DF.col("g")))
    bad("median of bool", DF.median(DF.col("b")))
    bad("var of a missing column", DF.var(DF.col("nope")))
    bad("nested std", DF.std(DF.sum(v())))
    R.agree("nested median in agg", R.e_group(g(), [DF.col("g")], [DF.median(DF.mean(v()))]), DF.lazy_group_by(gsrc(), [DF.col("g")], [DF.median(DF.mean(v()))]), genv(), genv(), genv())
    IO.print(DF.explain(DF.lazy_group_by(gsrc(), [DF.col("g")], three("v"))) ++ "\n")
#|-- stats select
#|frame
#|height	1
#|width	30
#|col	f32	"std_w"
#|col	f32	"var_w"
#|col	f32	"med_w"
#|col	f32	"std_a"
#|col	f32	"var_a"
#|col	f32	"med_a"
#|col	f32	"std_b"
#|col	f32	"var_b"
#|col	f32	"med_b"
#|col	f32	"std_c"
#|col	f32	"var_c"
#|col	f32	"med_c"
#|col	f32	"std_d"
#|col	f32	"var_d"
#|col	f32	"med_d"
#|col	f32	"std_e"
#|col	f32	"var_e"
#|col	f32	"med_e"
#|col	f32	"std_g"
#|col	f32	"var_g"
#|col	f32	"med_g"
#|col	f32	"std_h"
#|col	f32	"var_h"
#|col	f32	"med_h"
#|col	f32	"std_k"
#|col	f32	"var_k"
#|col	f32	"med_k"
#|col	f32	"std_z"
#|col	f32	"var_z"
#|col	f32	"med_z"
#|row	0x3fc385f3	0x40155556	0x40000000	0x3f800000	0x3f800000	0x40000000	0x3fa53f4e	0x3fd55555	0x40200000	0x409739e2	0x41b2aaab	0x40400000	0x7fc00000	0x7fc00000	0x40400000	0x7f800000	0x7f800000	0x00000000	0x7f800000	0x7f800000	0x7f61b1e6	0x7fc00000	0x7fc00000	0x7fc00000	null	null	0x40a00000	null	null	null
#|raw=eager opt=eager full=eager
#|
#|-- stats group_by
#|frame
#|height	3
#|width	9
#|col	str	"g"
#|col	f32	"sd"
#|col	f32	"va"
#|col	f32	"md"
#|col	f32	"sd2"
#|col	f32	"va2"
#|col	f32	"md2"
#|col	f32	"mlit"
#|col	f32	"slit"
#|row	"a"	0x3fc385f3	0x40155556	0x40000000	0x3fb504f3	0x40000000	0xc0000000	0x40000000	null
#|row	"b"	null	null	0x41200000	0x3fb504f3	0x40000000	0x40400000	0x40000000	null
#|row	"c"	0x7fc00000	0x7fc00000	0x7fc00000	0x00000000	0x00000000	0x40c00000	0x40000000	null
#|raw=eager opt=eager full=eager
#|
#|-- stats group_by bool key
#|frame
#|height	2
#|width	3
#|col	bool	"b"
#|col	f32	"md"
#|col	f32	"sd2"
#|row	true	0x40400000	0x409739e2
#|row	false	0x7fc00000	0x40000000
#|raw=eager opt=eager full=eager
#|
#|-- median broadcast
#|frame
#|height	7
#|width	5
#|col	str	"g"
#|col	f32	"v"
#|col	i32	"v2"
#|col	bool	"b"
#|col	f32	"dv"
#|row	"a"	0x3f800000	-1	true	0xc0600000
#|row	"b"	0x41200000	2	false	0x40b00000
#|row	"a"	0x40000000	-3	true	0xc0200000
#|row	"b"	null	4	false	null
#|row	"a"	0x40800000	null	true	0xbf000000
#|row	"c"	0x7fc00000	6	false	0x7fc00000
#|row	"c"	0x40a00000	6	true	0x3f000000
#|raw=eager opt=eager full=eager
#|
#|-- median filter
#|frame
#|height	3
#|width	4
#|col	str	"g"
#|col	f32	"v"
#|col	i32	"v2"
#|col	bool	"b"
#|row	"b"	0x41200000	2	false
#|row	"c"	0x7fc00000	6	false
#|row	"c"	0x40a00000	6	true
#|raw=eager opt=eager full=eager
#|
#|-- stats h0 select
#|frame
#|height	1
#|width	3
#|col	f32	"std_v"
#|col	f32	"var_v"
#|col	f32	"med_v"
#|row	null	null	null
#|raw=eager opt=eager full=eager
#|
#|-- stats h0 group_by
#|frame
#|height	0
#|width	4
#|col	str	"g"
#|col	f32	"std_v"
#|col	f32	"var_v"
#|col	f32	"med_v"
#|raw=eager opt=eager full=eager
#|
#|-- std of str
#|error	TypeMismatch in std: expected numeric, got str
#|raw=eager opt=eager full=eager
#|
#|-- median of bool
#|error	TypeMismatch in median: expected numeric, got bool
#|raw=eager opt=eager full=eager
#|
#|-- var of a missing column
#|error	ColumnNotFound: nope
#|raw=eager opt=eager full=eager
#|
#|-- nested std
#|error	InvalidOperation: nested aggregation: col("v").sum().std()
#|raw=eager opt=eager full=eager
#|
#|-- nested median in agg
#|error	InvalidOperation: nested aggregation in agg: col("v").mean().median()
#|raw=eager opt=eager full=eager
#|
#|GROUP_BY [col("g")] AGG [col("v").std().alias("std_v"), col("v").var().alias("var_v"), col("v").median().alias("med_v")] MAINTAIN_ORDER
#|  SOURCE g [g:str, v:f32, v2:i32, b:bool]
