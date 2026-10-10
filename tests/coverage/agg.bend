# T6 coverage: the aggregations (sum, mean, min, max, count, len, first, last, n_unique, std, var,
# median) as global reductions (select, with_columns, filter) and as group_by aggregates, over the
# nullable frame g below: null cells, an all-null group, a null key, single-row groups, zero rows
# (DESIGN.md 15.4 C7, C26: sum 0, count 0, the rest null), and the refusals. Every case is eager
# (DX.e_*) and lazy (DF.lazy_*: raw / opt / full) and the dumps agree (R.four).
# Expectations: DESIGN.md 15.2.5, 15.5.3, 15.5.4, confirmed by bench/coverage/agg.py (Polars 2.0.0);
# departures applied there: mean / std / var / median of u32 and i32 are f32 (Polars f64), sum over
# str / bool is refused, mean over bool is refused, an aggregation inside an aggregation is an error.
# The data is chosen so each variance and mean is exactly representable in f32 (the contract's f32
# accumulation then equals Polars' f64 result rounded to f32).
#@ cover sum,mean,min,max,count,len,first,last,n_unique,std,var,median success null empty invalid eager lazy
#@ cover group_by,lazy_group_by success null empty invalid eager lazy
#@ cover select,lazy_select,with_columns,lazy_with_columns,filter,lazy_filter success null empty eager lazy
#@ cover col,alias success null empty invalid eager lazy
#@ na sum,mean,min,max,count,len,first,last,n_unique,std,var,median zerocol -- a zero-column frame has no column to reduce (len() over it: tests/coverage/verbs_basic.bend)
import Base
import ./../../frame.bend as DF
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./../../src/expr.bend as X
import ./../diff/lib/dx.bend as DX
import ./../regress/lib/rx.bend as R
import ./lib/fx.bend as FX

# g (8 rows):  k str "a" "b" "a" null "b" "a" null "c"      v u32 1 2 4 null 8 2 3 null
#              w f32 1.5 2.5 null 4.0 0.5 3.5 2.0 1.0      i i32 -1 5 -3 2 null 7 -8 0
#              e f32 2 4 null 6 8 null 5 null              b bool T F T null F T null F
def g() -> E.ResT(C.Frame):
  R.frame([
    R.mk("k", [R.s("a"), R.s("b"), R.s("a"), R.null(), R.s("b"), R.s("a"), R.null(), R.s("c")], DF.t_str()),
    R.mk("v", [R.u(1), R.u(2), R.u(4), R.null(), R.u(8), R.u(2), R.u(3), R.null()], DF.t_u32()),
    R.mk("w", [R.f(1.5), R.f(2.5), R.null(), R.f(4.0), R.f(0.5), R.f(3.5), R.f(2.0), R.f(1.0)], DF.t_f32()),
    R.mk("i", [R.ineg(1), R.i(5), R.ineg(3), R.i(2), R.null(), R.i(7), R.ineg(8), R.i(0)], DF.t_i32()),
    R.mk("e", [R.f(2.0), R.f(4.0), R.null(), R.f(6.0), R.f(8.0), R.null(), R.f(5.0), R.null()], DF.t_f32()),
    R.mk("b", [R.b(True{}), R.b(False{}), R.b(True{}), R.null(), R.b(False{}), R.b(True{}), R.null(), R.b(False{})], DF.t_bool())])

def gz() -> E.ResT(C.Frame):
  R.frame([
    R.mk("k", [], DF.t_str()), R.mk("v", [], DF.t_u32()), R.mk("w", [], DF.t_f32()),
    R.mk("i", [], DF.t_i32()), R.mk("e", [], DF.t_f32()), R.mk("b", [], DF.t_bool())])

def envg() -> P.Env:
  R.env1("g", g())

def envz() -> P.Env:
  R.env1("gz", gz())

def srcg() -> P.Plan:
  R.src("g", g())

def srcz() -> P.Plan:
  R.src("gz", gz())

def c(+n: String) -> DF.Expr():
  DF.col(n)

def al(e: DF.Expr(), +n: String) -> DF.Expr():
  DF.alias(e, n)

def sel(+tag: String, +es: List<&2, DF.Expr()>) -> IO(Unit):
  R.four(tag, DX.e_select(g(), es), DF.lazy_select(srcg(), es), envg(), envg(), envg())

def selt(+tag: String, +es: List<&2, DF.Expr()>) -> IO(Unit):
  R.four(tag, DX.e_select(FX.t(), es), DF.lazy_select(FX.srct(), es), FX.envt(), FX.envt(), FX.envt())

def selz(+tag: String, +es: List<&2, DF.Expr()>) -> IO(Unit):
  R.four(tag, DX.e_select(gz(), es), DF.lazy_select(srcz(), es), envz(), envz(), envz())

def grp(+tag: String, +ks: List<&2, DF.Expr()>, +es: List<&2, DF.Expr()>) -> IO(Unit):
  R.four(tag, DX.e_group_by(g(), ks, es), DF.lazy_group_by(srcg(), ks, es), envg(), envg(), envg())

def grpz(+tag: String, +ks: List<&2, DF.Expr()>, +es: List<&2, DF.Expr()>) -> IO(Unit):
  R.four(tag, DX.e_group_by(gz(), ks, es), DF.lazy_group_by(srcz(), ks, es), envz(), envz(), envz())

def wth(+tag: String, +es: List<&2, DF.Expr()>) -> IO(Unit):
  R.four(tag, DX.e_with_columns(g(), es), DF.lazy_with_columns(srcg(), es), envg(), envg(), envg())

def flt(+tag: String, +e: DF.Expr()) -> IO(Unit):
  R.four(tag, DX.e_filter(g(), e), DF.lazy_filter(srcg(), e), envg(), envg(), envg())

# the ten reducers every dtype accepts, over column n (the numeric ones add mean and median)
def any10(+n: String) -> List<&2, DF.Expr()>:
  [al(DF.count(c(n)), n ++ "_count"), al(DF.len(), n ++ "_len"), al(DF.min(c(n)), n ++ "_min"), al(DF.max(c(n)), n ++ "_max"), al(DF.first(c(n)), n ++ "_first"), al(DF.last(c(n)), n ++ "_last"), al(DF.n_unique(c(n)), n ++ "_nuniq")]

def num(+n: String) -> List<&2, DF.Expr()>:
  [al(DF.sum(c(n)), n ++ "_sum"), al(DF.mean(c(n)), n ++ "_mean"), al(DF.count(c(n)), n ++ "_count"), al(DF.min(c(n)), n ++ "_min"), al(DF.max(c(n)), n ++ "_max"), al(DF.first(c(n)), n ++ "_first"), al(DF.last(c(n)), n ++ "_last"), al(DF.n_unique(c(n)), n ++ "_nuniq"), al(DF.median(c(n)), n ++ "_median")]

def spread(+n: String) -> List<&2, DF.Expr()>:
  [al(DF.std(c(n)), n ++ "_std"), al(DF.var(c(n)), n ++ "_var"), al(DF.median(c(n)), n ++ "_median")]

def cat(xs: List<&2, DF.Expr()>, ys: List<&2, DF.Expr()>) -> List<&2, DF.Expr()>:
  List.append(&2, X.Expr, xs, ys)

def main() -> IO(Unit):
  do IO<Unit>:
    sel("global reductions of u32 with nulls", num("v"))
    sel("global reductions of i32 with nulls", num("i"))
    sel("global reductions of f32 with nulls", num("w"))
    sel("global std var median of f32 with nulls", cat(spread("e"), [al(DF.sum(c("e")), "e_sum"), al(DF.mean(c("e")), "e_mean")]))
    sel("global min max count first last n_unique of str and bool", cat(any10("k"), any10("b")))
    selt("global reductions of f32 with NaN inf -0.0 and a null", cat(num("x"), [al(DF.std(c("x")), "x_std"), al(DF.var(c("x")), "x_var")]))
    sel("global len", [DF.len()])
    sel("a reduction broadcast beside a column", [c("v"), al(DF.sum(c("v")), "total"), al(DF.count(c("v")), "n")])
    wth("with_columns broadcasts a reduction", [al(DF.max(c("w")), "w_max"), al(DF.mean(c("e")), "e_mean")])
    flt("filter by a reduction", DF.gt(c("w"), DF.mean(c("w"))))
    grp("group_by str key, u32 aggregates", [c("k")], num("v"))
    grp("group_by str key, i32 aggregates", [c("k")], num("i"))
    grp("group_by str key, f32 aggregates", [c("k")], num("w"))
    grp("group_by str key, std var median", [c("k")], spread("e"))
    grp("group_by str key, std var median of w", [c("k")], spread("w"))
    grp("group_by str key, str and bool aggregates", [c("k")], cat(any10("b"), [al(DF.min(c("k")), "k_min")]))
    grp("group_by bool key and len", [c("b")], [DF.len(), al(DF.sum(c("v")), "v_sum")])
    selz("global reductions, zero rows", cat(num("v"), cat(spread("e"), any10("k"))))
    grpz("group_by, zero rows", [c("k")], cat(num("v"), spread("e")))
    sel("invalid sum of str", [DF.sum(c("k"))])
    sel("invalid sum of bool", [DF.sum(c("b"))])
    sel("invalid mean of bool", [DF.mean(c("b"))])
    sel("invalid std of str", [DF.std(c("k"))])
    sel("invalid var of bool", [DF.var(c("b"))])
    sel("invalid median of str", [DF.median(c("k"))])
    sel("invalid min of a missing column", [DF.min(c("nope"))])
    sel("invalid max of a missing column", [DF.max(c("nope"))])
    sel("invalid count of a missing column", [DF.count(c("nope"))])
    sel("invalid first of a missing column", [DF.first(c("nope"))])
    sel("invalid last of a missing column", [DF.last(c("nope"))])
    sel("invalid n_unique of a missing column", [DF.n_unique(c("nope"))])
    sel("invalid nested reduction sum of sum", [DF.sum(DF.sum(c("v")))])
    sel("invalid nested reduction mean of max", [DF.mean(DF.max(c("w")))])
    grp("invalid group_by aggregate that is no reduction", [c("k")], [c("v")])
    grp("invalid group_by no keys", [], [DF.sum(c("v"))])
    grp("invalid group_by key is a reduction", [DF.sum(c("v"))], [DF.len()])
    grp("invalid group_by nested reduction", [c("k")], [DF.sum(DF.sum(c("v")))])
    grp("invalid group_by sum of str", [c("k")], [DF.sum(c("k"))])
    grp("invalid group_by duplicate output names", [c("k")], [DF.sum(c("v")), DF.min(c("v"))])
#|-- global reductions of u32 with nulls
#|frame
#|height	1
#|width	9
#|col	u32	"v_sum"
#|col	f32	"v_mean"
#|col	u32	"v_count"
#|col	u32	"v_min"
#|col	u32	"v_max"
#|col	u32	"v_first"
#|col	u32	"v_last"
#|col	u32	"v_nuniq"
#|col	f32	"v_median"
#|row	20	0x40555555	6	1	8	1	null	6	0x40200000
#|raw same, opt same, full same
#|
#|-- global reductions of i32 with nulls
#|frame
#|height	1
#|width	9
#|col	i32	"i_sum"
#|col	f32	"i_mean"
#|col	u32	"i_count"
#|col	i32	"i_min"
#|col	i32	"i_max"
#|col	i32	"i_first"
#|col	i32	"i_last"
#|col	u32	"i_nuniq"
#|col	f32	"i_median"
#|row	2	0x3e924925	7	-8	7	-1	0	8	0x00000000
#|raw same, opt same, full same
#|
#|-- global reductions of f32 with nulls
#|frame
#|height	1
#|width	9
#|col	f32	"w_sum"
#|col	f32	"w_mean"
#|col	u32	"w_count"
#|col	f32	"w_min"
#|col	f32	"w_max"
#|col	f32	"w_first"
#|col	f32	"w_last"
#|col	u32	"w_nuniq"
#|col	f32	"w_median"
#|row	0x41700000	0x40092492	7	0x3f000000	0x40800000	0x3fc00000	0x3f800000	8	0x40000000
#|raw same, opt same, full same
#|
#|-- global std var median of f32 with nulls
#|frame
#|height	1
#|width	5
#|col	f32	"e_std"
#|col	f32	"e_var"
#|col	f32	"e_median"
#|col	f32	"e_sum"
#|col	f32	"e_mean"
#|row	0x400f1bbd	0x40a00000	0x40a00000	0x41c80000	0x40a00000
#|raw same, opt same, full same
#|
#|-- global min max count first last n_unique of str and bool
#|frame
#|height	1
#|width	14
#|col	u32	"k_count"
#|col	u32	"k_len"
#|col	str	"k_min"
#|col	str	"k_max"
#|col	str	"k_first"
#|col	str	"k_last"
#|col	u32	"k_nuniq"
#|col	u32	"b_count"
#|col	u32	"b_len"
#|col	bool	"b_min"
#|col	bool	"b_max"
#|col	bool	"b_first"
#|col	bool	"b_last"
#|col	u32	"b_nuniq"
#|row	6	8	"a"	"c"	"a"	"c"	4	6	8	false	true	true	false	3
#|raw same, opt same, full same
#|
#|-- global reductions of f32 with NaN inf -0.0 and a null
#|frame
#|height	1
#|width	11
#|col	f32	"x_sum"
#|col	f32	"x_mean"
#|col	u32	"x_count"
#|col	f32	"x_min"
#|col	f32	"x_max"
#|col	f32	"x_first"
#|col	f32	"x_last"
#|col	u32	"x_nuniq"
#|col	f32	"x_median"
#|col	f32	"x_std"
#|col	f32	"x_var"
#|row	0x7fc00000	0x7fc00000	6	0xc0000000	0x7f800000	0x3fc00000	0x80000000	6	0x3f400000	0x7fc00000	0x7fc00000
#|raw same, opt same, full same
#|
#|-- global len
#|frame
#|height	1
#|width	1
#|col	u32	"literal"
#|row	8
#|raw same, opt same, full same
#|
#|-- a reduction broadcast beside a column
#|frame
#|height	8
#|width	3
#|col	u32	"v"
#|col	u32	"total"
#|col	u32	"n"
#|row	1	20	6
#|row	2	20	6
#|row	4	20	6
#|row	null	20	6
#|row	8	20	6
#|row	2	20	6
#|row	3	20	6
#|row	null	20	6
#|raw same, opt same, full same
#|
#|-- with_columns broadcasts a reduction
#|frame
#|height	8
#|width	8
#|col	str	"k"
#|col	u32	"v"
#|col	f32	"w"
#|col	i32	"i"
#|col	f32	"e"
#|col	bool	"b"
#|col	f32	"w_max"
#|col	f32	"e_mean"
#|row	"a"	1	0x3fc00000	-1	0x40000000	true	0x40800000	0x40a00000
#|row	"b"	2	0x40200000	5	0x40800000	false	0x40800000	0x40a00000
#|row	"a"	4	null	-3	null	true	0x40800000	0x40a00000
#|row	null	null	0x40800000	2	0x40c00000	null	0x40800000	0x40a00000
#|row	"b"	8	0x3f000000	null	0x41000000	false	0x40800000	0x40a00000
#|row	"a"	2	0x40600000	7	null	true	0x40800000	0x40a00000
#|row	null	3	0x40000000	-8	0x40a00000	null	0x40800000	0x40a00000
#|row	"c"	null	0x3f800000	0	null	false	0x40800000	0x40a00000
#|raw same, opt same, full same
#|
#|-- filter by a reduction
#|frame
#|height	3
#|width	6
#|col	str	"k"
#|col	u32	"v"
#|col	f32	"w"
#|col	i32	"i"
#|col	f32	"e"
#|col	bool	"b"
#|row	"b"	2	0x40200000	5	0x40800000	false
#|row	null	null	0x40800000	2	0x40c00000	null
#|row	"a"	2	0x40600000	7	null	true
#|raw same, opt same, full same
#|
#|-- group_by str key, u32 aggregates
#|frame
#|height	4
#|width	10
#|col	str	"k"
#|col	u32	"v_sum"
#|col	f32	"v_mean"
#|col	u32	"v_count"
#|col	u32	"v_min"
#|col	u32	"v_max"
#|col	u32	"v_first"
#|col	u32	"v_last"
#|col	u32	"v_nuniq"
#|col	f32	"v_median"
#|row	"a"	7	0x40155555	3	1	4	1	2	3	0x40000000
#|row	"b"	10	0x40a00000	2	2	8	2	8	2	0x40a00000
#|row	null	3	0x40400000	1	3	3	null	3	2	0x40400000
#|row	"c"	0	null	0	null	null	null	null	1	null
#|raw same, opt same, full same
#|
#|-- group_by str key, i32 aggregates
#|frame
#|height	4
#|width	10
#|col	str	"k"
#|col	i32	"i_sum"
#|col	f32	"i_mean"
#|col	u32	"i_count"
#|col	i32	"i_min"
#|col	i32	"i_max"
#|col	i32	"i_first"
#|col	i32	"i_last"
#|col	u32	"i_nuniq"
#|col	f32	"i_median"
#|row	"a"	3	0x3f800000	3	-3	7	-1	7	3	0xbf800000
#|row	"b"	5	0x40a00000	1	5	5	5	null	2	0x40a00000
#|row	null	-6	0xc0400000	2	-8	2	2	-8	2	0xc0400000
#|row	"c"	0	0x00000000	1	0	0	0	0	1	0x00000000
#|raw same, opt same, full same
#|
#|-- group_by str key, f32 aggregates
#|frame
#|height	4
#|width	10
#|col	str	"k"
#|col	f32	"w_sum"
#|col	f32	"w_mean"
#|col	u32	"w_count"
#|col	f32	"w_min"
#|col	f32	"w_max"
#|col	f32	"w_first"
#|col	f32	"w_last"
#|col	u32	"w_nuniq"
#|col	f32	"w_median"
#|row	"a"	0x40a00000	0x40200000	2	0x3fc00000	0x40600000	0x3fc00000	0x40600000	3	0x40200000
#|row	"b"	0x40400000	0x3fc00000	2	0x3f000000	0x40200000	0x40200000	0x3f000000	2	0x3fc00000
#|row	null	0x40c00000	0x40400000	2	0x40000000	0x40800000	0x40800000	0x40000000	2	0x40400000
#|row	"c"	0x3f800000	0x3f800000	1	0x3f800000	0x3f800000	0x3f800000	0x3f800000	1	0x3f800000
#|raw same, opt same, full same
#|
#|-- group_by str key, std var median
#|frame
#|height	4
#|width	4
#|col	str	"k"
#|col	f32	"e_std"
#|col	f32	"e_var"
#|col	f32	"e_median"
#|row	"a"	null	null	0x40000000
#|row	"b"	0x403504f3	0x41000000	0x40c00000
#|row	null	0x3f3504f3	0x3f000000	0x40b00000
#|row	"c"	null	null	null
#|raw same, opt same, full same
#|
#|-- group_by str key, std var median of w
#|frame
#|height	4
#|width	4
#|col	str	"k"
#|col	f32	"w_std"
#|col	f32	"w_var"
#|col	f32	"w_median"
#|row	"a"	0x3fb504f3	0x40000000	0x40200000
#|row	"b"	0x3fb504f3	0x40000000	0x3fc00000
#|row	null	0x3fb504f3	0x40000000	0x40400000
#|row	"c"	null	null	0x3f800000
#|raw same, opt same, full same
#|
#|-- group_by str key, str and bool aggregates
#|frame
#|height	4
#|width	9
#|col	str	"k"
#|col	u32	"b_count"
#|col	u32	"b_len"
#|col	bool	"b_min"
#|col	bool	"b_max"
#|col	bool	"b_first"
#|col	bool	"b_last"
#|col	u32	"b_nuniq"
#|col	str	"k_min"
#|row	"a"	3	3	true	true	true	true	1	"a"
#|row	"b"	2	2	false	false	false	false	1	"b"
#|row	null	0	2	null	null	null	null	1	null
#|row	"c"	1	1	false	false	false	false	1	"c"
#|raw same, opt same, full same
#|
#|-- group_by bool key and len
#|frame
#|height	3
#|width	3
#|col	bool	"b"
#|col	u32	"literal"
#|col	u32	"v_sum"
#|row	true	3	7
#|row	false	3	10
#|row	null	2	3
#|raw same, opt same, full same
#|
#|-- global reductions, zero rows
#|frame
#|height	1
#|width	19
#|col	u32	"v_sum"
#|col	f32	"v_mean"
#|col	u32	"v_count"
#|col	u32	"v_min"
#|col	u32	"v_max"
#|col	u32	"v_first"
#|col	u32	"v_last"
#|col	u32	"v_nuniq"
#|col	f32	"v_median"
#|col	f32	"e_std"
#|col	f32	"e_var"
#|col	f32	"e_median"
#|col	u32	"k_count"
#|col	u32	"k_len"
#|col	str	"k_min"
#|col	str	"k_max"
#|col	str	"k_first"
#|col	str	"k_last"
#|col	u32	"k_nuniq"
#|row	0	null	0	null	null	null	null	0	null	null	null	null	0	0	null	null	null	null	0
#|raw same, opt same, full same
#|
#|-- group_by, zero rows
#|frame
#|height	0
#|width	13
#|col	str	"k"
#|col	u32	"v_sum"
#|col	f32	"v_mean"
#|col	u32	"v_count"
#|col	u32	"v_min"
#|col	u32	"v_max"
#|col	u32	"v_first"
#|col	u32	"v_last"
#|col	u32	"v_nuniq"
#|col	f32	"v_median"
#|col	f32	"e_std"
#|col	f32	"e_var"
#|col	f32	"e_median"
#|raw same, opt same, full same
#|
#|-- invalid sum of str
#|error	TypeMismatch in sum: expected numeric, got str
#|raw same, opt same, full same
#|
#|-- invalid sum of bool
#|error	TypeMismatch in sum: expected numeric, got bool
#|raw same, opt same, full same
#|
#|-- invalid mean of bool
#|error	TypeMismatch in mean: expected numeric, got bool
#|raw same, opt same, full same
#|
#|-- invalid std of str
#|error	TypeMismatch in std: expected numeric, got str
#|raw same, opt same, full same
#|
#|-- invalid var of bool
#|error	TypeMismatch in var: expected numeric, got bool
#|raw same, opt same, full same
#|
#|-- invalid median of str
#|error	TypeMismatch in median: expected numeric, got str
#|raw same, opt same, full same
#|
#|-- invalid min of a missing column
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|-- invalid max of a missing column
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|-- invalid count of a missing column
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|-- invalid first of a missing column
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|-- invalid last of a missing column
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|-- invalid n_unique of a missing column
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|-- invalid nested reduction sum of sum
#|error	InvalidOperation: nested aggregation: col("v").sum().sum()
#|raw same, opt same, full same
#|
#|-- invalid nested reduction mean of max
#|error	InvalidOperation: nested aggregation: col("w").max().mean()
#|raw same, opt same, full same
#|
#|-- invalid group_by aggregate that is no reduction
#|error	InvalidOperation: agg expects an aggregation: col("v")
#|raw same, opt same, full same
#|
#|-- invalid group_by no keys
#|error	InvalidOperation: group_by needs at least one key
#|raw same, opt same, full same
#|
#|-- invalid group_by key is a reduction
#|error	InvalidOperation: group_by key is an aggregation: col("v").sum()
#|raw same, opt same, full same
#|
#|-- invalid group_by nested reduction
#|error	InvalidOperation: nested aggregation in agg: col("v").sum().sum()
#|raw same, opt same, full same
#|
#|-- invalid group_by sum of str
#|error	TypeMismatch in sum: expected numeric, got str
#|raw same, opt same, full same
#|
#|-- invalid group_by duplicate output names
#|error	DuplicateColumn: v
#|raw same, opt same, full same
#|
