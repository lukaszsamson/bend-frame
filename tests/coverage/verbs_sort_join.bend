# T6 coverage: sort (with sort_key, asc, desc) and the four joins (inner, left, semi, anti) with their
# lazy twins, over the frames l, r below: null cells and null keys (a null key never matches), many-to-many
# matches, a colliding column name (`f` becomes `f_right`), zero rows on either side, and the refusals
# (a missing key, a key dtype mismatch, no keys, unequal key lists, a name collision after the suffix).
# Eager (DX.e_*) and lazy (DF.lazy_*, raw / opt / full collects) agree on every case (R.four).
# Expectations: DESIGN.md 15.2.3, 15.2.4, 15.5.2, confirmed by bench/coverage/verbs_sort_join.py (Polars
# 2.0.0; joins with maintain_order="left_right"); departures applied there: nulls sort first for both
# directions unless nulls_last, a missing key / mismatched key dtype is an error (Polars coerces some).
#@ cover sort,lazy_sort,sort_key,asc,desc success null empty invalid eager lazy zerocol
#@ cover inner_join,left_join,semi_join,anti_join,lazy_inner_join,lazy_left_join,lazy_semi_join,lazy_anti_join success null empty invalid eager lazy
#@ cover drop,rename,lazy_drop,lazy_rename success null empty invalid eager lazy
#@ na inner_join,left_join,semi_join,anti_join,lazy_inner_join,lazy_left_join,lazy_semi_join,lazy_anti_join zerocol -- a join needs a key column, a zero-column frame has none (the key-list refusal is covered)
import Base
import ./../../frame.bend as DF
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./../diff/lib/dx.bend as DX
import ./../regress/lib/rx.bend as R

# sort frame m: id u32 1..7   g str "x" "y" "x" null "y" "x" null   v f32 1.5 null 3.0 NaN NaN 0.0 -0.0
#               k bool T F null T null F T
def m() -> E.ResT(C.Frame):
  R.frame([
    R.mk("id", [R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7)], DF.t_u32()),
    R.mk("g", [R.s("x"), R.s("y"), R.s("x"), R.null(), R.s("y"), R.s("x"), R.null()], DF.t_str()),
    R.mk("v", [R.f(1.5), R.null(), R.f(3.0), R.f(R.nan()), R.f(R.nan()), R.f(0.0), R.f(R.nzero())], DF.t_f32()),
    R.mk("k", [R.b(True{}), R.b(False{}), R.null(), R.b(True{}), R.null(), R.b(False{}), R.b(True{})], DF.t_bool())])

def mz() -> E.ResT(C.Frame):
  R.frame([R.mk("id", [], DF.t_u32()), R.mk("g", [], DF.t_str()), R.mk("v", [], DF.t_f32()), R.mk("k", [], DF.t_bool())])

# l (6 rows): id u32 1..6   key str "a" "b" "a" null "c" "b"   f f32 1.5 2.5 null 4.5 5.5 6.5
def l() -> E.ResT(C.Frame):
  R.frame([
    R.mk("id", [R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6)], DF.t_u32()),
    R.mk("key", [R.s("a"), R.s("b"), R.s("a"), R.null(), R.s("c"), R.s("b")], DF.t_str()),
    R.mk("f", [R.f(1.5), R.f(2.5), R.null(), R.f(4.5), R.f(5.5), R.f(6.5)], DF.t_f32())])

# r (5 rows): key str "a" "b" "a" null "d"   g i32 10 20 30 40 50   f f32 null 0.5 1.5 2.5 3.5   rid u32 1 2 3 null 9
def r() -> E.ResT(C.Frame):
  R.frame([
    R.mk("key", [R.s("a"), R.s("b"), R.s("a"), R.null(), R.s("d")], DF.t_str()),
    R.mk("g", [R.i(10), R.i(20), R.i(30), R.i(40), R.i(50)], DF.t_i32()),
    R.mk("f", [R.null(), R.f(0.5), R.f(1.5), R.f(2.5), R.f(3.5)], DF.t_f32()),
    R.mk("rid", [R.u(1), R.u(2), R.u(3), R.null(), R.u(9)], DF.t_u32())])

def lz() -> E.ResT(C.Frame):
  R.frame([R.mk("id", [], DF.t_u32()), R.mk("key", [], DF.t_str()), R.mk("f", [], DF.t_f32())])

def rz() -> E.ResT(C.Frame):
  R.frame([R.mk("key", [], DF.t_str()), R.mk("g", [], DF.t_i32()), R.mk("f", [], DF.t_f32()), R.mk("rid", [], DF.t_u32())])

def em() -> P.Env:
  R.env1("m", m())

def emz() -> P.Env:
  R.env1("mz", mz())

def sm() -> P.Plan:
  R.src("m", m())

def smz() -> P.Plan:
  R.src("mz", mz())

def elr() -> P.Env:
  R.env_add(R.env1("l", l()), "r", r())

def elrz() -> P.Env:
  R.env_add(R.env1("l", l()), "rz", rz())

def elzr() -> P.Env:
  R.env_add(R.env1("lz", lz()), "r", r())

def sl() -> P.Plan:
  R.src("l", l())

def sr() -> P.Plan:
  R.src("r", r())

def slz() -> P.Plan:
  R.src("lz", lz())

def srz() -> P.Plan:
  R.src("rz", rz())

def srt(+tag: String, +ks: List<&2, DF.SortKey()>) -> IO(Unit):
  R.four(tag, DX.e_sort(m(), ks), DF.lazy_sort(sm(), ks), em(), em(), em())

def srtz(+tag: String, +ks: List<&2, DF.SortKey()>) -> IO(Unit):
  R.four(tag, DX.e_sort(mz(), ks), DF.lazy_sort(smz(), ks), emz(), emz(), emz())

def lo(+tag: String, +lk: List<&2, String>, +rk: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    R.four(tag ++ " inner", DX.e_inner_join(l(), r(), lk, rk), DF.lazy_inner_join(sl(), sr(), lk, rk), elr(), elr(), elr())
    R.four(tag ++ " left", DX.e_left_join(l(), r(), lk, rk), DF.lazy_left_join(sl(), sr(), lk, rk), elr(), elr(), elr())
    R.four(tag ++ " semi", DX.e_semi_join(l(), r(), lk, rk), DF.lazy_semi_join(sl(), sr(), lk, rk), elr(), elr(), elr())
    R.four(tag ++ " anti", DX.e_anti_join(l(), r(), lk, rk), DF.lazy_anti_join(sl(), sr(), lk, rk), elr(), elr(), elr())

def main() -> IO(Unit):
  do IO<Unit>:
    srt("sort ascending by f32: nulls first, NaN last, -0.0 ties 0.0", [DF.asc("v")])
    srt("sort descending by f32: nulls still first", [DF.desc("v")])
    srt("sort ascending, nulls last", [DF.sort_key("v", False{}, True{})])
    srt("sort descending, nulls last", [DF.sort_key("v", True{}, True{})])
    srt("sort by str then id descending", [DF.asc("g"), DF.desc("id")])
    srt("sort by str descending, nulls last, then bool", [DF.sort_key("g", True{}, True{}), DF.asc("k")])
    srt("sort by bool", [DF.asc("k")])
    srt("sort by no key is the identity", [])
    srtz("sort on zero rows", [DF.asc("v"), DF.desc("g")])
    R.four("sort on zero columns", DX.e_sort(R.zcols(3), []), DF.lazy_sort(R.src("z0", R.zcols(3)), []), R.env1("z0", R.zcols(3)), R.env1("z0", R.zcols(3)), R.env1("z0", R.zcols(3)))
    srtz("sort_key on zero rows", [DF.sort_key("v", True{}, True{})])
    srt("invalid sort_key on a missing column", [DF.sort_key("nope", False{}, False{})])
    srt("invalid sort missing column", [DF.asc("v"), DF.desc("nope")])
    srt("invalid sort first missing key wins", [DF.asc("nope2"), DF.asc("nope")])
    lo("on a str key", ["key"], ["key"])
    lo("on a u32 key against another name", ["id"], ["rid"])
    lo("on two keys", ["key", "id"], ["key", "rid"])
    R.four("inner join, zero rows on the right", DX.e_inner_join(l(), rz(), ["key"], ["key"]), DF.lazy_inner_join(sl(), srz(), ["key"], ["key"]), elrz(), elrz(), elrz())
    R.four("left join, zero rows on the right", DX.e_left_join(l(), rz(), ["key"], ["key"]), DF.lazy_left_join(sl(), srz(), ["key"], ["key"]), elrz(), elrz(), elrz())
    R.four("semi join, zero rows on the right", DX.e_semi_join(l(), rz(), ["key"], ["key"]), DF.lazy_semi_join(sl(), srz(), ["key"], ["key"]), elrz(), elrz(), elrz())
    R.four("anti join, zero rows on the right", DX.e_anti_join(l(), rz(), ["key"], ["key"]), DF.lazy_anti_join(sl(), srz(), ["key"], ["key"]), elrz(), elrz(), elrz())
    R.four("inner join, zero rows on the left", DX.e_inner_join(lz(), r(), ["key"], ["key"]), DF.lazy_inner_join(slz(), sr(), ["key"], ["key"]), elzr(), elzr(), elzr())
    R.four("left join, zero rows on the left", DX.e_left_join(lz(), r(), ["key"], ["key"]), DF.lazy_left_join(slz(), sr(), ["key"], ["key"]), elzr(), elzr(), elzr())
    R.four("semi join, zero rows on the left", DX.e_semi_join(lz(), r(), ["key"], ["key"]), DF.lazy_semi_join(slz(), sr(), ["key"], ["key"]), elzr(), elzr(), elzr())
    R.four("anti join, zero rows on the left", DX.e_anti_join(lz(), r(), ["key"], ["key"]), DF.lazy_anti_join(slz(), sr(), ["key"], ["key"]), elzr(), elzr(), elzr())
    R.four("join after drop and rename keeps the keys", DX.e_inner_join(DX.e_drop(l(), ["f"]), DX.e_rename(r(), [("g", "g2")]), ["key"], ["key"]), DF.lazy_inner_join(DF.lazy_drop(sl(), ["f"]), DF.lazy_rename(sr(), [("g", "g2")]), ["key"], ["key"]), elr(), elr(), elr())
    R.four("invalid inner join missing left key", DX.e_inner_join(l(), r(), ["nope"], ["key"]), DF.lazy_inner_join(sl(), sr(), ["nope"], ["key"]), elr(), elr(), elr())
    R.four("invalid left join missing right key", DX.e_left_join(l(), r(), ["key"], ["nope"]), DF.lazy_left_join(sl(), sr(), ["key"], ["nope"]), elr(), elr(), elr())
    R.four("invalid semi join key dtype mismatch", DX.e_semi_join(l(), r(), ["key"], ["rid"]), DF.lazy_semi_join(sl(), sr(), ["key"], ["rid"]), elr(), elr(), elr())
    R.four("invalid anti join no keys", DX.e_anti_join(l(), r(), [], []), DF.lazy_anti_join(sl(), sr(), [], []), elr(), elr(), elr())
    R.four("invalid inner join key lists of different lengths", DX.e_inner_join(l(), r(), ["key", "id"], ["key"]), DF.lazy_inner_join(sl(), sr(), ["key", "id"], ["key"]), elr(), elr(), elr())
    R.four("invalid left join f32 against u32 keys", DX.e_left_join(l(), r(), ["f"], ["rid"]), DF.lazy_left_join(sl(), sr(), ["f"], ["rid"]), elr(), elr(), elr())
    R.four("invalid inner join column collides after the suffix", DX.e_inner_join(l(), DX.e_rename(r(), [("g", "f_right")]), ["key"], ["key"]), DF.lazy_inner_join(sl(), DF.lazy_rename(sr(), [("g", "f_right")]), ["key"], ["key"]), elr(), elr(), elr())
#|-- sort ascending by f32: nulls first, NaN last, -0.0 ties 0.0
#|frame
#|height	7
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|row	2	"y"	null	false
#|row	6	"x"	0x00000000	false
#|row	7	null	0x80000000	true
#|row	1	"x"	0x3fc00000	true
#|row	3	"x"	0x40400000	null
#|row	4	null	0x7fc00000	true
#|row	5	"y"	0x7fc00000	null
#|raw same, opt same, full same
#|
#|-- sort descending by f32: nulls still first
#|frame
#|height	7
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|row	2	"y"	null	false
#|row	4	null	0x7fc00000	true
#|row	5	"y"	0x7fc00000	null
#|row	3	"x"	0x40400000	null
#|row	1	"x"	0x3fc00000	true
#|row	6	"x"	0x00000000	false
#|row	7	null	0x80000000	true
#|raw same, opt same, full same
#|
#|-- sort ascending, nulls last
#|frame
#|height	7
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|row	6	"x"	0x00000000	false
#|row	7	null	0x80000000	true
#|row	1	"x"	0x3fc00000	true
#|row	3	"x"	0x40400000	null
#|row	4	null	0x7fc00000	true
#|row	5	"y"	0x7fc00000	null
#|row	2	"y"	null	false
#|raw same, opt same, full same
#|
#|-- sort descending, nulls last
#|frame
#|height	7
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|row	4	null	0x7fc00000	true
#|row	5	"y"	0x7fc00000	null
#|row	3	"x"	0x40400000	null
#|row	1	"x"	0x3fc00000	true
#|row	6	"x"	0x00000000	false
#|row	7	null	0x80000000	true
#|row	2	"y"	null	false
#|raw same, opt same, full same
#|
#|-- sort by str then id descending
#|frame
#|height	7
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|row	7	null	0x80000000	true
#|row	4	null	0x7fc00000	true
#|row	6	"x"	0x00000000	false
#|row	3	"x"	0x40400000	null
#|row	1	"x"	0x3fc00000	true
#|row	5	"y"	0x7fc00000	null
#|row	2	"y"	null	false
#|raw same, opt same, full same
#|
#|-- sort by str descending, nulls last, then bool
#|frame
#|height	7
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|row	5	"y"	0x7fc00000	null
#|row	2	"y"	null	false
#|row	3	"x"	0x40400000	null
#|row	6	"x"	0x00000000	false
#|row	1	"x"	0x3fc00000	true
#|row	4	null	0x7fc00000	true
#|row	7	null	0x80000000	true
#|raw same, opt same, full same
#|
#|-- sort by bool
#|frame
#|height	7
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|row	3	"x"	0x40400000	null
#|row	5	"y"	0x7fc00000	null
#|row	2	"y"	null	false
#|row	6	"x"	0x00000000	false
#|row	1	"x"	0x3fc00000	true
#|row	4	null	0x7fc00000	true
#|row	7	null	0x80000000	true
#|raw same, opt same, full same
#|
#|-- sort by no key is the identity
#|frame
#|height	7
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|row	1	"x"	0x3fc00000	true
#|row	2	"y"	null	false
#|row	3	"x"	0x40400000	null
#|row	4	null	0x7fc00000	true
#|row	5	"y"	0x7fc00000	null
#|row	6	"x"	0x00000000	false
#|row	7	null	0x80000000	true
#|raw same, opt same, full same
#|
#|-- sort on zero rows
#|frame
#|height	0
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|raw same, opt same, full same
#|
#|-- sort on zero columns
#|frame
#|height	3
#|width	0
#|raw same, opt same, full same
#|
#|-- sort_key on zero rows
#|frame
#|height	0
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|raw same, opt same, full same
#|
#|-- invalid sort_key on a missing column
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|-- invalid sort missing column
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|-- invalid sort first missing key wins
#|error	ColumnNotFound: nope2
#|raw same, opt same, full same
#|
#|-- on a str key inner
#|frame
#|height	6
#|width	6
#|col	u32	"id"
#|col	str	"key"
#|col	f32	"f"
#|col	i32	"g"
#|col	f32	"f_right"
#|col	u32	"rid"
#|row	1	"a"	0x3fc00000	10	null	1
#|row	1	"a"	0x3fc00000	30	0x3fc00000	3
#|row	2	"b"	0x40200000	20	0x3f000000	2
#|row	3	"a"	null	10	null	1
#|row	3	"a"	null	30	0x3fc00000	3
#|row	6	"b"	0x40d00000	20	0x3f000000	2
#|raw same, opt same, full same
#|
#|-- on a str key left
#|frame
#|height	8
#|width	6
#|col	u32	"id"
#|col	str	"key"
#|col	f32	"f"
#|col	i32	"g"
#|col	f32	"f_right"
#|col	u32	"rid"
#|row	1	"a"	0x3fc00000	10	null	1
#|row	1	"a"	0x3fc00000	30	0x3fc00000	3
#|row	2	"b"	0x40200000	20	0x3f000000	2
#|row	3	"a"	null	10	null	1
#|row	3	"a"	null	30	0x3fc00000	3
#|row	4	null	0x40900000	null	null	null
#|row	5	"c"	0x40b00000	null	null	null
#|row	6	"b"	0x40d00000	20	0x3f000000	2
#|raw same, opt same, full same
#|
#|-- on a str key semi
#|frame
#|height	4
#|width	3
#|col	u32	"id"
#|col	str	"key"
#|col	f32	"f"
#|row	1	"a"	0x3fc00000
#|row	2	"b"	0x40200000
#|row	3	"a"	null
#|row	6	"b"	0x40d00000
#|raw same, opt same, full same
#|
#|-- on a str key anti
#|frame
#|height	2
#|width	3
#|col	u32	"id"
#|col	str	"key"
#|col	f32	"f"
#|row	4	null	0x40900000
#|row	5	"c"	0x40b00000
#|raw same, opt same, full same
#|
#|-- on a u32 key against another name inner
#|frame
#|height	3
#|width	6
#|col	u32	"id"
#|col	str	"key"
#|col	f32	"f"
#|col	str	"key_right"
#|col	i32	"g"
#|col	f32	"f_right"
#|row	1	"a"	0x3fc00000	"a"	10	null
#|row	2	"b"	0x40200000	"b"	20	0x3f000000
#|row	3	"a"	null	"a"	30	0x3fc00000
#|raw same, opt same, full same
#|
#|-- on a u32 key against another name left
#|frame
#|height	6
#|width	6
#|col	u32	"id"
#|col	str	"key"
#|col	f32	"f"
#|col	str	"key_right"
#|col	i32	"g"
#|col	f32	"f_right"
#|row	1	"a"	0x3fc00000	"a"	10	null
#|row	2	"b"	0x40200000	"b"	20	0x3f000000
#|row	3	"a"	null	"a"	30	0x3fc00000
#|row	4	null	0x40900000	null	null	null
#|row	5	"c"	0x40b00000	null	null	null
#|row	6	"b"	0x40d00000	null	null	null
#|raw same, opt same, full same
#|
#|-- on a u32 key against another name semi
#|frame
#|height	3
#|width	3
#|col	u32	"id"
#|col	str	"key"
#|col	f32	"f"
#|row	1	"a"	0x3fc00000
#|row	2	"b"	0x40200000
#|row	3	"a"	null
#|raw same, opt same, full same
#|
#|-- on a u32 key against another name anti
#|frame
#|height	3
#|width	3
#|col	u32	"id"
#|col	str	"key"
#|col	f32	"f"
#|row	4	null	0x40900000
#|row	5	"c"	0x40b00000
#|row	6	"b"	0x40d00000
#|raw same, opt same, full same
#|
#|-- on two keys inner
#|frame
#|height	3
#|width	5
#|col	u32	"id"
#|col	str	"key"
#|col	f32	"f"
#|col	i32	"g"
#|col	f32	"f_right"
#|row	1	"a"	0x3fc00000	10	null
#|row	2	"b"	0x40200000	20	0x3f000000
#|row	3	"a"	null	30	0x3fc00000
#|raw same, opt same, full same
#|
#|-- on two keys left
#|frame
#|height	6
#|width	5
#|col	u32	"id"
#|col	str	"key"
#|col	f32	"f"
#|col	i32	"g"
#|col	f32	"f_right"
#|row	1	"a"	0x3fc00000	10	null
#|row	2	"b"	0x40200000	20	0x3f000000
#|row	3	"a"	null	30	0x3fc00000
#|row	4	null	0x40900000	null	null
#|row	5	"c"	0x40b00000	null	null
#|row	6	"b"	0x40d00000	null	null
#|raw same, opt same, full same
#|
#|-- on two keys semi
#|frame
#|height	3
#|width	3
#|col	u32	"id"
#|col	str	"key"
#|col	f32	"f"
#|row	1	"a"	0x3fc00000
#|row	2	"b"	0x40200000
#|row	3	"a"	null
#|raw same, opt same, full same
#|
#|-- on two keys anti
#|frame
#|height	3
#|width	3
#|col	u32	"id"
#|col	str	"key"
#|col	f32	"f"
#|row	4	null	0x40900000
#|row	5	"c"	0x40b00000
#|row	6	"b"	0x40d00000
#|raw same, opt same, full same
#|
#|-- inner join, zero rows on the right
#|frame
#|height	0
#|width	6
#|col	u32	"id"
#|col	str	"key"
#|col	f32	"f"
#|col	i32	"g"
#|col	f32	"f_right"
#|col	u32	"rid"
#|raw same, opt same, full same
#|
#|-- left join, zero rows on the right
#|frame
#|height	6
#|width	6
#|col	u32	"id"
#|col	str	"key"
#|col	f32	"f"
#|col	i32	"g"
#|col	f32	"f_right"
#|col	u32	"rid"
#|row	1	"a"	0x3fc00000	null	null	null
#|row	2	"b"	0x40200000	null	null	null
#|row	3	"a"	null	null	null	null
#|row	4	null	0x40900000	null	null	null
#|row	5	"c"	0x40b00000	null	null	null
#|row	6	"b"	0x40d00000	null	null	null
#|raw same, opt same, full same
#|
#|-- semi join, zero rows on the right
#|frame
#|height	0
#|width	3
#|col	u32	"id"
#|col	str	"key"
#|col	f32	"f"
#|raw same, opt same, full same
#|
#|-- anti join, zero rows on the right
#|frame
#|height	6
#|width	3
#|col	u32	"id"
#|col	str	"key"
#|col	f32	"f"
#|row	1	"a"	0x3fc00000
#|row	2	"b"	0x40200000
#|row	3	"a"	null
#|row	4	null	0x40900000
#|row	5	"c"	0x40b00000
#|row	6	"b"	0x40d00000
#|raw same, opt same, full same
#|
#|-- inner join, zero rows on the left
#|frame
#|height	0
#|width	6
#|col	u32	"id"
#|col	str	"key"
#|col	f32	"f"
#|col	i32	"g"
#|col	f32	"f_right"
#|col	u32	"rid"
#|raw same, opt same, full same
#|
#|-- left join, zero rows on the left
#|frame
#|height	0
#|width	6
#|col	u32	"id"
#|col	str	"key"
#|col	f32	"f"
#|col	i32	"g"
#|col	f32	"f_right"
#|col	u32	"rid"
#|raw same, opt same, full same
#|
#|-- semi join, zero rows on the left
#|frame
#|height	0
#|width	3
#|col	u32	"id"
#|col	str	"key"
#|col	f32	"f"
#|raw same, opt same, full same
#|
#|-- anti join, zero rows on the left
#|frame
#|height	0
#|width	3
#|col	u32	"id"
#|col	str	"key"
#|col	f32	"f"
#|raw same, opt same, full same
#|
#|-- join after drop and rename keeps the keys
#|frame
#|height	6
#|width	5
#|col	u32	"id"
#|col	str	"key"
#|col	i32	"g2"
#|col	f32	"f"
#|col	u32	"rid"
#|row	1	"a"	10	null	1
#|row	1	"a"	30	0x3fc00000	3
#|row	2	"b"	20	0x3f000000	2
#|row	3	"a"	10	null	1
#|row	3	"a"	30	0x3fc00000	3
#|row	6	"b"	20	0x3f000000	2
#|raw same, opt same, full same
#|
#|-- invalid inner join missing left key
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|-- invalid left join missing right key
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|-- invalid semi join key dtype mismatch
#|error	TypeMismatch in join: expected str, got u32
#|raw same, opt same, full same
#|
#|-- invalid anti join no keys
#|error	InvalidOperation: join: no key columns
#|raw same, opt same, full same
#|
#|-- invalid inner join key lists of different lengths
#|error	InvalidOperation: join: left_on and right_on must have the same length
#|raw same, opt same, full same
#|
#|-- invalid left join f32 against u32 keys
#|error	TypeMismatch in join: expected f32, got u32
#|raw same, opt same, full same
#|
#|-- invalid inner join column collides after the suffix
#|error	DuplicateColumn: f_right
#|raw same, opt same, full same
#|
