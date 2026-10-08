# B05-g (both reviews): no test checked that eager, raw-lazy and optimised-lazy agree on
# the same data. Every regression in tests/regress/ prints all three dumps; this file
# adds Fable's ten optimizer traps (REVIEW_FABLE.txt section 1: all agreed in the review)
# as permanent three-way checks. Expected dumps are Polars 2.0.0's answers for the same
# programs (regress_expect.py; no departure applies). Passes today.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

# t (the reviews' frame): a u32 (a null), b str, c f32 (a null), d bool (a null), e u32 zeros
def t() -> E.ResT(C.Frame):
  R.frame([
    R.mk("a", [R.u(1), R.u(2), R.null(), R.u(4), R.u(5), R.u(6)], D.TU32{}),
    R.mk("b", [R.s("x"), R.s("y"), R.s("z"), R.s("x"), R.s("y"), R.s("x")], D.TStr{}),
    R.mk("c", [R.f(0.5), R.f(1.5), R.f(2.5), R.null(), R.f(4.5), R.f(5.5)], D.TF32{}),
    R.mk("d", [R.b(True{}), R.b(False{}), R.b(True{}), R.b(True{}), R.null(), R.b(True{})], D.TBool{}),
    R.mk("e", [R.u(0), R.u(0), R.u(0), R.u(0), R.u(0), R.u(0)], D.TU32{})])

# u: b str (join key), label str, c f32 (clashes with t.c)
def u() -> E.ResT(C.Frame):
  R.frame([
    R.mk("b", [R.s("x"), R.s("y"), R.s("w"), R.s("x")], D.TStr{}),
    R.mk("label", [R.s("x1"), R.s("y1"), R.s("w1"), R.s("x2")], D.TStr{}),
    R.mk("c", [R.f(10.0), R.f(20.0), R.f(30.0), R.f(40.0)], D.TF32{})])

def env() -> P.Env:
  R.env1("t", t())

def env2() -> P.Env:
  R.env_add(R.env1("t", t()), "u", u())

def src() -> P.Plan:
  R.src("t", t())

def a() -> X.Expr:
  DF.col("a")

def u32(v: U32) -> X.Expr:
  DF.lit_u32(v)

def times(e: X.Expr, k: U32, n: String) -> X.Expr:
  DF.alias(DF.mul(e, u32(k)), n)

def main() -> IO(Unit):
  do IO<Unit>:
    # 1 with_columns that REPLACES a, then filter on a: the filter must not move
    R.three("B05-g trap1 replace-then-filter", R.e_filter(R.e_with(t(), [times(a(), 10, "a")]), DF.gt(a(), u32(2))), DF.lazy_filter(DF.lazy_with_columns(src(), [times(a(), 10, "a")]), DF.gt(a(), u32(2))), env(), env())
    # 2 select swapping a and e through aliases, then a > 0
    R.three("B05-g trap2 swap-aliases", R.e_filter(R.e_select(t(), [DF.alias(DF.col("e"), "a"), DF.alias(a(), "e")]), DF.gt(a(), u32(0))), DF.lazy_filter(DF.lazy_select(src(), [DF.alias(DF.col("e"), "a"), DF.alias(a(), "e")]), DF.gt(a(), u32(0))), env(), env())
    # 3 head over filter over head: neither head moves
    R.three("B05-g trap3 head-filter-head", R.e_head(R.e_filter(R.e_head(t(), 4), DF.col("d")), 3), DF.lazy_head(DF.lazy_filter(DF.lazy_head(src(), 4), DF.col("d")), 3), env(), env())
    # 4 head over with_columns over sort: the head stops at the sort
    R.three("B05-g trap4 head-with-sort", R.e_head(R.e_with(R.e_sort(t(), [DF.desc("a")]), [times(a(), 2, "n")]), 2), DF.lazy_head(DF.lazy_with_columns(DF.lazy_sort(src(), [DF.desc("a")]), [times(a(), 2, "n")]), 2), env(), env())
    # 5 a literal-only select: one row
    R.three("B05-g trap5 literal-select", R.e_select(t(), [DF.alias(u32(1), "one")]), DF.lazy_select(src(), [DF.alias(u32(1), "one")]), env(), env())
    # 6 a filter on the group key above group_by
    R.three("B05-g trap6 filter-over-group", R.e_filter(R.e_group(t(), [DF.col("b")], [DF.alias(DF.sum(a()), "s")]), DF.eq(DF.col("b"), DF.lit_str("x"))), DF.lazy_filter(DF.lazy_group_by(src(), [DF.col("b")], [DF.alias(DF.sum(a()), "s")]), DF.eq(DF.col("b"), DF.lit_str("x"))), env(), env())
    # 7 select(n) over with_columns(n = a * 2): projection keeps a
    R.three("B05-g trap7 select-over-with", R.e_select(R.e_with(t(), [times(a(), 2, "n")]), [DF.col("n")]), DF.lazy_select(DF.lazy_with_columns(src(), [times(a(), 2, "n")]), [DF.col("n")]), env(), env())
    # 8 filter on a where the select aliases c as a
    R.three("B05-g trap8 filter-through-alias", R.e_filter(R.e_select(t(), [DF.alias(DF.col("c"), "a")]), DF.gt(a(), DF.lit_f32(1.0))), DF.lazy_filter(DF.lazy_select(src(), [DF.alias(DF.col("c"), "a")]), DF.gt(a(), DF.lit_f32(1.0))), env(), env())
    # 9 two filters, the inner one reads the new column
    R.three("B05-g trap9 two-filters", R.e_filter(R.e_filter(R.e_with(t(), [times(a(), 2, "n")]), DF.gt(DF.col("n"), u32(4))), DF.gt(a(), u32(1))), DF.lazy_filter(DF.lazy_filter(DF.lazy_with_columns(src(), [times(a(), 2, "n")]), DF.gt(DF.col("n"), u32(4))), DF.gt(a(), u32(1))), env(), env())
    # 10 left join, is_null(right column), head
    R.three("B05-g trap10 left-join-null-head", R.e_head(R.e_filter(R.e_left(t(), u(), ["b"], ["b"]), DF.is_null(DF.col("label"))), 2), DF.lazy_head(DF.lazy_filter(DF.lazy_left_join(src(), R.src("u", u()), ["b"], ["b"]), DF.is_null(DF.col("label"))), 2), env2(), env2())
#|-- B05-g trap1 replace-then-filter eager
#|frame
#|height	5
#|width	5
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|col	bool	"d"
#|col	u32	"e"
#|row	10	"x"	0x3f000000	true	0
#|row	20	"y"	0x3fc00000	false	0
#|row	40	"x"	null	true	0
#|row	50	"y"	0x40900000	null	0
#|row	60	"x"	0x40b00000	true	0
#|
#|-- B05-g trap1 replace-then-filter raw
#|frame
#|height	5
#|width	5
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|col	bool	"d"
#|col	u32	"e"
#|row	10	"x"	0x3f000000	true	0
#|row	20	"y"	0x3fc00000	false	0
#|row	40	"x"	null	true	0
#|row	50	"y"	0x40900000	null	0
#|row	60	"x"	0x40b00000	true	0
#|
#|-- B05-g trap1 replace-then-filter opt
#|frame
#|height	5
#|width	5
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|col	bool	"d"
#|col	u32	"e"
#|row	10	"x"	0x3f000000	true	0
#|row	20	"y"	0x3fc00000	false	0
#|row	40	"x"	null	true	0
#|row	50	"y"	0x40900000	null	0
#|row	60	"x"	0x40b00000	true	0
#|
#|-- B05-g trap2 swap-aliases eager
#|frame
#|height	0
#|width	2
#|col	u32	"a"
#|col	u32	"e"
#|
#|-- B05-g trap2 swap-aliases raw
#|frame
#|height	0
#|width	2
#|col	u32	"a"
#|col	u32	"e"
#|
#|-- B05-g trap2 swap-aliases opt
#|frame
#|height	0
#|width	2
#|col	u32	"a"
#|col	u32	"e"
#|
#|-- B05-g trap3 head-filter-head eager
#|frame
#|height	3
#|width	5
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|col	bool	"d"
#|col	u32	"e"
#|row	1	"x"	0x3f000000	true	0
#|row	null	"z"	0x40200000	true	0
#|row	4	"x"	null	true	0
#|
#|-- B05-g trap3 head-filter-head raw
#|frame
#|height	3
#|width	5
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|col	bool	"d"
#|col	u32	"e"
#|row	1	"x"	0x3f000000	true	0
#|row	null	"z"	0x40200000	true	0
#|row	4	"x"	null	true	0
#|
#|-- B05-g trap3 head-filter-head opt
#|frame
#|height	3
#|width	5
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|col	bool	"d"
#|col	u32	"e"
#|row	1	"x"	0x3f000000	true	0
#|row	null	"z"	0x40200000	true	0
#|row	4	"x"	null	true	0
#|
#|-- B05-g trap4 head-with-sort eager
#|frame
#|height	2
#|width	6
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|col	bool	"d"
#|col	u32	"e"
#|col	u32	"n"
#|row	null	"z"	0x40200000	true	0	null
#|row	6	"x"	0x40b00000	true	0	12
#|
#|-- B05-g trap4 head-with-sort raw
#|frame
#|height	2
#|width	6
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|col	bool	"d"
#|col	u32	"e"
#|col	u32	"n"
#|row	null	"z"	0x40200000	true	0	null
#|row	6	"x"	0x40b00000	true	0	12
#|
#|-- B05-g trap4 head-with-sort opt
#|frame
#|height	2
#|width	6
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|col	bool	"d"
#|col	u32	"e"
#|col	u32	"n"
#|row	null	"z"	0x40200000	true	0	null
#|row	6	"x"	0x40b00000	true	0	12
#|
#|-- B05-g trap5 literal-select eager
#|frame
#|height	1
#|width	1
#|col	u32	"one"
#|row	1
#|
#|-- B05-g trap5 literal-select raw
#|frame
#|height	1
#|width	1
#|col	u32	"one"
#|row	1
#|
#|-- B05-g trap5 literal-select opt
#|frame
#|height	1
#|width	1
#|col	u32	"one"
#|row	1
#|
#|-- B05-g trap6 filter-over-group eager
#|frame
#|height	1
#|width	2
#|col	str	"b"
#|col	u32	"s"
#|row	"x"	11
#|
#|-- B05-g trap6 filter-over-group raw
#|frame
#|height	1
#|width	2
#|col	str	"b"
#|col	u32	"s"
#|row	"x"	11
#|
#|-- B05-g trap6 filter-over-group opt
#|frame
#|height	1
#|width	2
#|col	str	"b"
#|col	u32	"s"
#|row	"x"	11
#|
#|-- B05-g trap7 select-over-with eager
#|frame
#|height	6
#|width	1
#|col	u32	"n"
#|row	2
#|row	4
#|row	null
#|row	8
#|row	10
#|row	12
#|
#|-- B05-g trap7 select-over-with raw
#|frame
#|height	6
#|width	1
#|col	u32	"n"
#|row	2
#|row	4
#|row	null
#|row	8
#|row	10
#|row	12
#|
#|-- B05-g trap7 select-over-with opt
#|frame
#|height	6
#|width	1
#|col	u32	"n"
#|row	2
#|row	4
#|row	null
#|row	8
#|row	10
#|row	12
#|
#|-- B05-g trap8 filter-through-alias eager
#|frame
#|height	4
#|width	1
#|col	f32	"a"
#|row	0x3fc00000
#|row	0x40200000
#|row	0x40900000
#|row	0x40b00000
#|
#|-- B05-g trap8 filter-through-alias raw
#|frame
#|height	4
#|width	1
#|col	f32	"a"
#|row	0x3fc00000
#|row	0x40200000
#|row	0x40900000
#|row	0x40b00000
#|
#|-- B05-g trap8 filter-through-alias opt
#|frame
#|height	4
#|width	1
#|col	f32	"a"
#|row	0x3fc00000
#|row	0x40200000
#|row	0x40900000
#|row	0x40b00000
#|
#|-- B05-g trap9 two-filters eager
#|frame
#|height	3
#|width	6
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|col	bool	"d"
#|col	u32	"e"
#|col	u32	"n"
#|row	4	"x"	null	true	0	8
#|row	5	"y"	0x40900000	null	0	10
#|row	6	"x"	0x40b00000	true	0	12
#|
#|-- B05-g trap9 two-filters raw
#|frame
#|height	3
#|width	6
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|col	bool	"d"
#|col	u32	"e"
#|col	u32	"n"
#|row	4	"x"	null	true	0	8
#|row	5	"y"	0x40900000	null	0	10
#|row	6	"x"	0x40b00000	true	0	12
#|
#|-- B05-g trap9 two-filters opt
#|frame
#|height	3
#|width	6
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|col	bool	"d"
#|col	u32	"e"
#|col	u32	"n"
#|row	4	"x"	null	true	0	8
#|row	5	"y"	0x40900000	null	0	10
#|row	6	"x"	0x40b00000	true	0	12
#|
#|-- B05-g trap10 left-join-null-head eager
#|frame
#|height	1
#|width	7
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|col	bool	"d"
#|col	u32	"e"
#|col	str	"label"
#|col	f32	"c_right"
#|row	null	"z"	0x40200000	true	0	null	null
#|
#|-- B05-g trap10 left-join-null-head raw
#|frame
#|height	1
#|width	7
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|col	bool	"d"
#|col	u32	"e"
#|col	str	"label"
#|col	f32	"c_right"
#|row	null	"z"	0x40200000	true	0	null	null
#|
#|-- B05-g trap10 left-join-null-head opt
#|frame
#|height	1
#|width	7
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|col	bool	"d"
#|col	u32	"e"
#|col	str	"label"
#|col	f32	"c_right"
#|row	null	"z"	0x40200000	true	0	null	null
#|
