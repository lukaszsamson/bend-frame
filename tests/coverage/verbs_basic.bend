# T6 coverage: the row and column verbs select, with_columns, filter, head, slice, tail, drop, rename,
# unique and concat_vertical with their lazy twins, over the frame m below: null cells (nullable
# columns, a null predicate row, a null key), zero rows, zero columns (a frame with a height and no
# columns, DESIGN.md 15.4 C22-C24) and the refusals. Eager (DX.e_*) and lazy (DF.lazy_*, collected
# raw / opt / full) agree on every case (R.four).
# Expectations: DESIGN.md 15.2.3, 15.2.4, 15.4, confirmed by bench/coverage/verbs_basic.py (Polars
# 2.0.0); departures applied there: rename / unique subset [] means every column, slice offsets are
# unsigned and clamped, a filter on a null predicate row drops it, concat_vertical needs equal schemas.
#@ cover select,with_columns,filter,head,slice,tail,drop,rename,unique,concat_vertical success null empty eager lazy zerocol
#@ cover lazy_select,lazy_with_columns,lazy_filter,lazy_head,lazy_slice,lazy_tail,lazy_drop,lazy_rename,lazy_unique,lazy_concat_vertical success null empty eager lazy zerocol
#@ cover select,with_columns,filter,drop,rename,unique,concat_vertical invalid
#@ cover lazy_select,lazy_with_columns,lazy_filter,lazy_drop,lazy_rename,lazy_unique,lazy_concat_vertical invalid
#@ na head,lazy_head invalid -- head takes any U32 and clamps to the height: no input can be refused (DESIGN 15.2.3)
#@ na slice,lazy_slice invalid -- an offset or length beyond the height is clamped, never an error (DESIGN 15.2.3)
#@ na tail,lazy_tail invalid -- tail takes any U32 and clamps to the height: no input can be refused (DESIGN 15.2.3)
#@ cover col,alias,lit_u32,lit_bool,len success null empty invalid eager lazy
#@ na lit_u32,lit_bool,len null -- a literal and len() hold no nulls of their own (a null column beside them is in the same cases)
import Base
import ./../../frame.bend as DF
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./../../src/expr.bend as X
import ./../diff/lib/dx.bend as DX
import ./../regress/lib/rx.bend as R

# m (7 rows):  id u32 1..7   g str "x" "y" "x" null "y" "x" null   v f32 1.5 null 3.0 NaN NaN 0.0 -0.0
#              k bool T F null T null F T
def m() -> E.ResT(C.Frame):
  R.frame([
    R.mk("id", [R.u(1), R.u(2), R.u(3), R.u(4), R.u(5), R.u(6), R.u(7)], DF.t_u32()),
    R.mk("g", [R.s("x"), R.s("y"), R.s("x"), R.null(), R.s("y"), R.s("x"), R.null()], DF.t_str()),
    R.mk("v", [R.f(1.5), R.null(), R.f(3.0), R.f(R.nan()), R.f(R.nan()), R.f(0.0), R.f(R.nzero())], DF.t_f32()),
    R.mk("k", [R.b(True{}), R.b(False{}), R.null(), R.b(True{}), R.null(), R.b(False{}), R.b(True{})], DF.t_bool())])

def mz() -> E.ResT(C.Frame):
  R.frame([R.mk("id", [], DF.t_u32()), R.mk("g", [], DF.t_str()), R.mk("v", [], DF.t_f32()), R.mk("k", [], DF.t_bool())])

# the same rows with different row values, for concat
def m2() -> E.ResT(C.Frame):
  R.frame([
    R.mk("id", [R.u(8), R.u(9)], DF.t_u32()),
    R.mk("g", [R.s("z"), R.null()], DF.t_str()),
    R.mk("v", [R.null(), R.f(2.5)], DF.t_f32()),
    R.mk("k", [R.null(), R.b(False{})], DF.t_bool())])

# a frame with 3 rows and no columns
def m0() -> E.ResT(C.Frame):
  R.zcols(3)

def em() -> P.Env:
  R.env1("m", m())

def emz() -> P.Env:
  R.env1("mz", mz())

def em0() -> P.Env:
  R.env1("m0", m0())

def em2() -> P.Env:
  R.env_add(R.env1("m", m()), "m2", m2())

def sm() -> P.Plan:
  R.src("m", m())

def smz() -> P.Plan:
  R.src("mz", mz())

def sm0() -> P.Plan:
  R.src("m0", m0())

def sm2() -> P.Plan:
  R.src("m2", m2())

def c(+n: String) -> DF.Expr():
  DF.col(n)

def al(e: DF.Expr(), +n: String) -> DF.Expr():
  DF.alias(e, n)

def lu(v: U32) -> DF.Expr():
  DF.lit_u32(v)

def sel(+tag: String, +es: List<&2, DF.Expr()>) -> IO(Unit):
  R.four(tag, DX.e_select(m(), es), DF.lazy_select(sm(), es), em(), em(), em())

def selz(+tag: String, +es: List<&2, DF.Expr()>) -> IO(Unit):
  R.four(tag, DX.e_select(mz(), es), DF.lazy_select(smz(), es), emz(), emz(), emz())

def sel0(+tag: String, +es: List<&2, DF.Expr()>) -> IO(Unit):
  R.four(tag, DX.e_select(m0(), es), DF.lazy_select(sm0(), es), em0(), em0(), em0())

def wth(+tag: String, +es: List<&2, DF.Expr()>) -> IO(Unit):
  R.four(tag, DX.e_with_columns(m(), es), DF.lazy_with_columns(sm(), es), em(), em(), em())

def wthz(+tag: String, +es: List<&2, DF.Expr()>) -> IO(Unit):
  R.four(tag, DX.e_with_columns(mz(), es), DF.lazy_with_columns(smz(), es), emz(), emz(), emz())

def wth0(+tag: String, +es: List<&2, DF.Expr()>) -> IO(Unit):
  R.four(tag, DX.e_with_columns(m0(), es), DF.lazy_with_columns(sm0(), es), em0(), em0(), em0())

def flt(+tag: String, +e: DF.Expr()) -> IO(Unit):
  R.four(tag, DX.e_filter(m(), e), DF.lazy_filter(sm(), e), em(), em(), em())

def fltz(+tag: String, +e: DF.Expr()) -> IO(Unit):
  R.four(tag, DX.e_filter(mz(), e), DF.lazy_filter(smz(), e), emz(), emz(), emz())

def flt0(+tag: String, +e: DF.Expr()) -> IO(Unit):
  R.four(tag, DX.e_filter(m0(), e), DF.lazy_filter(sm0(), e), em0(), em0(), em0())

def hd(+tag: String, +n: U32) -> IO(Unit):
  R.four(tag, DX.e_head(m(), n), DF.lazy_head(sm(), n), em(), em(), em())

def sl(+tag: String, +o: U32, +n: U32) -> IO(Unit):
  R.four(tag, DX.e_slice(m(), o, n), DF.lazy_slice(sm(), o, n), em(), em(), em())

def tl(+tag: String, +n: U32) -> IO(Unit):
  R.four(tag, DX.e_tail(m(), n), DF.lazy_tail(sm(), n), em(), em(), em())

def dr(+tag: String, +ns: List<&2, String>) -> IO(Unit):
  R.four(tag, DX.e_drop(m(), ns), DF.lazy_drop(sm(), ns), em(), em(), em())

def rn(+tag: String, +ps: List<&2, DF.RenamePair()>) -> IO(Unit):
  R.four(tag, DX.e_rename(m(), ps), DF.lazy_rename(sm(), ps), em(), em(), em())

def uq(+tag: String, +ns: List<&2, String>) -> IO(Unit):
  R.four(tag, DX.e_unique(m(), ns), DF.lazy_unique(sm(), ns), em(), em(), em())

def uqz(+tag: String, +ns: List<&2, String>) -> IO(Unit):
  R.four(tag, DX.e_unique(mz(), ns), DF.lazy_unique(smz(), ns), emz(), emz(), emz())

def uq0(+tag: String, +ns: List<&2, String>) -> IO(Unit):
  R.four(tag, DX.e_unique(m0(), ns), DF.lazy_unique(sm0(), ns), em0(), em0(), em0())

def main() -> IO(Unit):
  do IO<Unit>:
    sel("select reorders, aliases and keeps nulls", [al(c("v"), "value"), c("id"), c("g")])
    sel("select nothing is a frame of no rows and no columns", [])
    sel("select a literal alone is one row", [al(lu(1), "one")])
    sel("select a literal beside columns broadcasts", [c("id"), al(lu(9), "nine")])
    selz("select, zero rows", [c("v"), al(DF.len(), "n")])
    sel0("select a literal over a zero-column frame", [al(lu(1), "one")])
    sel0("select len over a zero-column frame", [DF.len()])
    sel("invalid select duplicate output", [c("id"), c("id")])
    sel("invalid select two unaliased literals", [lu(1), lu(2)])
    sel("invalid select missing column", [c("id"), c("nope")])
    wth("with_columns replaces in place and appends", [al(DF.cast_f32(c("id")), "id"), al(DF.add(c("id"), lu(10)), "id10")])
    wth("with_columns a literal is broadcast", [al(lu(7), "seven")])
    wth("with_columns nothing is the frame", [])
    wthz("with_columns on zero rows", [al(lu(7), "seven"), al(DF.cast_f32(c("id")), "idf")])
    wth0("with_columns on a zero-column frame keeps its height", [al(lu(1), "o")])
    wth("invalid with_columns duplicate output names", [al(lu(1), "x"), al(lu(2), "x")])
    wth("invalid with_columns type mismatch", [DF.add(c("id"), c("v"))])
    wth("invalid with_columns missing column", [DF.is_null(c("nope"))])
    flt("filter keeps true rows and drops null predicate rows", c("k"))
    flt("filter a comparison with nulls", DF.gt(c("v"), DF.lit_f32(1.0)))
    flt("filter a constant true", DF.lit_bool(True{}))
    flt("filter a constant false", DF.lit_bool(False{}))
    flt("filter a null predicate", DF.lit_null(DF.t_bool()))
    fltz("filter on zero rows", c("k"))
    flt0("filter true over a zero-column frame", DF.lit_bool(True{}))
    flt0("filter false over a zero-column frame", DF.lit_bool(False{}))
    flt("invalid filter u32 predicate", c("id"))
    flt("invalid filter missing column", DF.gt(c("nope"), lu(1)))
    hd("head 3", 3)
    hd("head 0", 0)
    hd("head more than the height", 100)
    sl("slice from 2, 3 rows", 2, 3)
    sl("slice past the end", 9, 3)
    sl("slice length past the end", 5, 100)
    sl("slice 0 rows", 3, 0)
    tl("tail 3", 3)
    tl("tail 0", 0)
    tl("tail more than the height", 100)
    R.four("head slice tail, zero rows", DX.e_tail(DX.e_slice(DX.e_head(mz(), 3), 1, 5), 2), DF.lazy_tail(DF.lazy_slice(DF.lazy_head(smz(), 3), 1, 5), 2), emz(), emz(), emz())
    R.four("head slice tail, zero columns", DX.e_tail(DX.e_slice(DX.e_head(m0(), 2), 1, 5), 4), DF.lazy_tail(DF.lazy_slice(DF.lazy_head(sm0(), 2), 1, 5), 4), em0(), em0(), em0())
    dr("drop one and several columns", ["v", "g"])
    dr("drop the same column twice", ["v", "v"])
    dr("drop every column keeps the height", ["id", "g", "v", "k"])
    R.four("drop on zero rows", DX.e_drop(mz(), ["g"]), DF.lazy_drop(smz(), ["g"]), emz(), emz(), emz())
    R.four("drop on zero columns", DX.e_drop(m0(), []), DF.lazy_drop(sm0(), []), em0(), em0(), em0())
    dr("invalid drop missing column", ["id", "nope"])
    rn("rename a column", [("v", "value")])
    rn("rename swaps two columns", [("id", "g"), ("g", "id")])
    rn("rename a column to itself", [("id", "id")])
    R.four("rename on zero rows", DX.e_rename(mz(), [("id", "key")]), DF.lazy_rename(smz(), [("id", "key")]), emz(), emz(), emz())
    rn("invalid rename missing column", [("nope", "x")])
    rn("invalid rename same column twice", [("id", "a"), ("id", "b")])
    rn("invalid rename onto an existing column", [("id", "g")])
    rn("invalid rename two to one name", [("id", "z"), ("g", "z")])
    uq("unique over every column keeps all distinct rows", [])
    uq("unique by a str key with a null key", ["g"])
    uq("unique by an f32 key: NaN equals NaN, -0.0 equals 0.0", ["v"])
    uq("unique by two keys", ["g", "k"])
    uqz("unique on zero rows", ["g"])
    uq0("unique on a zero-column frame keeps one row", [])
    uq("invalid unique missing column", ["g", "nope"])
    R.four("concat two frames with nulls", DX.e_concat_vertical([m(), m2()]), DF.lazy_concat_vertical([sm(), sm2()]), em2(), em2(), em2())
    R.four("concat the same frame three times", DX.e_concat_vertical([m2(), m2(), m2()]), DF.lazy_concat_vertical([sm2(), sm2(), sm2()]), em2(), em2(), em2())
    R.four("concat one frame", DX.e_concat_vertical([m2()]), DF.lazy_concat_vertical([sm2()]), em2(), em2(), em2())
    R.four("concat with a zero-row frame", DX.e_concat_vertical([mz(), m2(), mz()]), DF.lazy_concat_vertical([smz(), sm2(), smz()]), R.env_add(emz(), "m2", m2()), R.env_add(emz(), "m2", m2()), R.env_add(emz(), "m2", m2()))
    R.four("concat zero-column frames adds their heights", DX.e_concat_vertical([m0(), m0()]), DF.lazy_concat_vertical([sm0(), sm0()]), em0(), em0(), em0())
    R.four("invalid concat no inputs", DX.e_concat_vertical([]), DF.lazy_concat_vertical([]), em(), em(), em())
    R.four("invalid concat schema differs", DX.e_concat_vertical([m(), DX.e_drop(m2(), ["k"])]), DF.lazy_concat_vertical([sm(), DF.lazy_drop(sm2(), ["k"])]), em2(), em2(), em2())
    R.four("invalid concat column order differs", DX.e_concat_vertical([m(), DX.e_select(m2(), [c("g"), c("id"), c("v"), c("k")])]), DF.lazy_concat_vertical([sm(), DF.lazy_select(sm2(), [c("g"), c("id"), c("v"), c("k")])]), em2(), em2(), em2())
#|-- select reorders, aliases and keeps nulls
#|frame
#|height	7
#|width	3
#|col	f32	"value"
#|col	u32	"id"
#|col	str	"g"
#|row	0x3fc00000	1	"x"
#|row	null	2	"y"
#|row	0x40400000	3	"x"
#|row	0x7fc00000	4	null
#|row	0x7fc00000	5	"y"
#|row	0x00000000	6	"x"
#|row	0x80000000	7	null
#|raw same, opt same, full same
#|
#|-- select nothing is a frame of no rows and no columns
#|frame
#|height	0
#|width	0
#|raw same, opt same, full same
#|
#|-- select a literal alone is one row
#|frame
#|height	1
#|width	1
#|col	u32	"one"
#|row	1
#|raw same, opt same, full same
#|
#|-- select a literal beside columns broadcasts
#|frame
#|height	7
#|width	2
#|col	u32	"id"
#|col	u32	"nine"
#|row	1	9
#|row	2	9
#|row	3	9
#|row	4	9
#|row	5	9
#|row	6	9
#|row	7	9
#|raw same, opt same, full same
#|
#|-- select, zero rows
#|frame
#|height	0
#|width	2
#|col	f32	"v"
#|col	u32	"n"
#|raw same, opt same, full same
#|
#|-- select a literal over a zero-column frame
#|frame
#|height	1
#|width	1
#|col	u32	"one"
#|row	1
#|raw same, opt same, full same
#|
#|-- select len over a zero-column frame
#|frame
#|height	1
#|width	1
#|col	u32	"literal"
#|row	3
#|raw same, opt same, full same
#|
#|-- invalid select duplicate output
#|error	DuplicateColumn: id
#|raw same, opt same, full same
#|
#|-- invalid select two unaliased literals
#|error	DuplicateColumn: literal
#|raw same, opt same, full same
#|
#|-- invalid select missing column
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|-- with_columns replaces in place and appends
#|frame
#|height	7
#|width	5
#|col	f32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|col	u32	"id10"
#|row	0x3f800000	"x"	0x3fc00000	true	11
#|row	0x40000000	"y"	null	false	12
#|row	0x40400000	"x"	0x40400000	null	13
#|row	0x40800000	null	0x7fc00000	true	14
#|row	0x40a00000	"y"	0x7fc00000	null	15
#|row	0x40c00000	"x"	0x00000000	false	16
#|row	0x40e00000	null	0x80000000	true	17
#|raw same, opt same, full same
#|
#|-- with_columns a literal is broadcast
#|frame
#|height	7
#|width	5
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|col	u32	"seven"
#|row	1	"x"	0x3fc00000	true	7
#|row	2	"y"	null	false	7
#|row	3	"x"	0x40400000	null	7
#|row	4	null	0x7fc00000	true	7
#|row	5	"y"	0x7fc00000	null	7
#|row	6	"x"	0x00000000	false	7
#|row	7	null	0x80000000	true	7
#|raw same, opt same, full same
#|
#|-- with_columns nothing is the frame
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
#|-- with_columns on zero rows
#|frame
#|height	0
#|width	6
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|col	u32	"seven"
#|col	f32	"idf"
#|raw same, opt same, full same
#|
#|-- with_columns on a zero-column frame keeps its height
#|frame
#|height	3
#|width	1
#|col	u32	"o"
#|row	1
#|row	1
#|row	1
#|raw same, opt same, full same
#|
#|-- invalid with_columns duplicate output names
#|error	DuplicateColumn: x
#|raw same, opt same, full same
#|
#|-- invalid with_columns type mismatch
#|error	TypeMismatch in add: expected u32, got f32
#|raw same, opt same, full same
#|
#|-- invalid with_columns missing column
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|-- filter keeps true rows and drops null predicate rows
#|frame
#|height	3
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|row	1	"x"	0x3fc00000	true
#|row	4	null	0x7fc00000	true
#|row	7	null	0x80000000	true
#|raw same, opt same, full same
#|
#|-- filter a comparison with nulls
#|frame
#|height	4
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|row	1	"x"	0x3fc00000	true
#|row	3	"x"	0x40400000	null
#|row	4	null	0x7fc00000	true
#|row	5	"y"	0x7fc00000	null
#|raw same, opt same, full same
#|
#|-- filter a constant true
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
#|-- filter a constant false
#|frame
#|height	0
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|raw same, opt same, full same
#|
#|-- filter a null predicate
#|frame
#|height	0
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|raw same, opt same, full same
#|
#|-- filter on zero rows
#|frame
#|height	0
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|raw same, opt same, full same
#|
#|-- filter true over a zero-column frame
#|frame
#|height	3
#|width	0
#|raw same, opt same, full same
#|
#|-- filter false over a zero-column frame
#|frame
#|height	0
#|width	0
#|raw same, opt same, full same
#|
#|-- invalid filter u32 predicate
#|error	TypeMismatch in filter: expected bool, got u32
#|raw same, opt same, full same
#|
#|-- invalid filter missing column
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|-- head 3
#|frame
#|height	3
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|row	1	"x"	0x3fc00000	true
#|row	2	"y"	null	false
#|row	3	"x"	0x40400000	null
#|raw same, opt same, full same
#|
#|-- head 0
#|frame
#|height	0
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|raw same, opt same, full same
#|
#|-- head more than the height
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
#|-- slice from 2, 3 rows
#|frame
#|height	3
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|row	3	"x"	0x40400000	null
#|row	4	null	0x7fc00000	true
#|row	5	"y"	0x7fc00000	null
#|raw same, opt same, full same
#|
#|-- slice past the end
#|frame
#|height	0
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|raw same, opt same, full same
#|
#|-- slice length past the end
#|frame
#|height	2
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|row	6	"x"	0x00000000	false
#|row	7	null	0x80000000	true
#|raw same, opt same, full same
#|
#|-- slice 0 rows
#|frame
#|height	0
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|raw same, opt same, full same
#|
#|-- tail 3
#|frame
#|height	3
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|row	5	"y"	0x7fc00000	null
#|row	6	"x"	0x00000000	false
#|row	7	null	0x80000000	true
#|raw same, opt same, full same
#|
#|-- tail 0
#|frame
#|height	0
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|raw same, opt same, full same
#|
#|-- tail more than the height
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
#|-- head slice tail, zero rows
#|frame
#|height	0
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|raw same, opt same, full same
#|
#|-- head slice tail, zero columns
#|frame
#|height	1
#|width	0
#|raw same, opt same, full same
#|
#|-- drop one and several columns
#|frame
#|height	7
#|width	2
#|col	u32	"id"
#|col	bool	"k"
#|row	1	true
#|row	2	false
#|row	3	null
#|row	4	true
#|row	5	null
#|row	6	false
#|row	7	true
#|raw same, opt same, full same
#|
#|-- drop the same column twice
#|frame
#|height	7
#|width	3
#|col	u32	"id"
#|col	str	"g"
#|col	bool	"k"
#|row	1	"x"	true
#|row	2	"y"	false
#|row	3	"x"	null
#|row	4	null	true
#|row	5	"y"	null
#|row	6	"x"	false
#|row	7	null	true
#|raw same, opt same, full same
#|
#|-- drop every column keeps the height
#|frame
#|height	7
#|width	0
#|raw same, opt same, full same
#|
#|-- drop on zero rows
#|frame
#|height	0
#|width	3
#|col	u32	"id"
#|col	f32	"v"
#|col	bool	"k"
#|raw same, opt same, full same
#|
#|-- drop on zero columns
#|frame
#|height	3
#|width	0
#|raw same, opt same, full same
#|
#|-- invalid drop missing column
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|-- rename a column
#|frame
#|height	7
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"value"
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
#|-- rename swaps two columns
#|frame
#|height	7
#|width	4
#|col	u32	"g"
#|col	str	"id"
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
#|-- rename a column to itself
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
#|-- rename on zero rows
#|frame
#|height	0
#|width	4
#|col	u32	"key"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|raw same, opt same, full same
#|
#|-- invalid rename missing column
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|-- invalid rename same column twice
#|error	DuplicateColumn: id
#|raw same, opt same, full same
#|
#|-- invalid rename onto an existing column
#|error	DuplicateColumn: g
#|raw same, opt same, full same
#|
#|-- invalid rename two to one name
#|error	DuplicateColumn: z
#|raw same, opt same, full same
#|
#|-- unique over every column keeps all distinct rows
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
#|-- unique by a str key with a null key
#|frame
#|height	3
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|row	1	"x"	0x3fc00000	true
#|row	2	"y"	null	false
#|row	4	null	0x7fc00000	true
#|raw same, opt same, full same
#|
#|-- unique by an f32 key: NaN equals NaN, -0.0 equals 0.0
#|frame
#|height	5
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|row	1	"x"	0x3fc00000	true
#|row	2	"y"	null	false
#|row	3	"x"	0x40400000	null
#|row	4	null	0x7fc00000	true
#|row	6	"x"	0x00000000	false
#|raw same, opt same, full same
#|
#|-- unique by two keys
#|frame
#|height	6
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
#|raw same, opt same, full same
#|
#|-- unique on zero rows
#|frame
#|height	0
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|raw same, opt same, full same
#|
#|-- unique on a zero-column frame keeps one row
#|frame
#|height	1
#|width	0
#|raw same, opt same, full same
#|
#|-- invalid unique missing column
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|-- concat two frames with nulls
#|frame
#|height	9
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
#|row	8	"z"	null	null
#|row	9	null	0x40200000	false
#|raw same, opt same, full same
#|
#|-- concat the same frame three times
#|frame
#|height	6
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|row	8	"z"	null	null
#|row	9	null	0x40200000	false
#|row	8	"z"	null	null
#|row	9	null	0x40200000	false
#|row	8	"z"	null	null
#|row	9	null	0x40200000	false
#|raw same, opt same, full same
#|
#|-- concat one frame
#|frame
#|height	2
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|row	8	"z"	null	null
#|row	9	null	0x40200000	false
#|raw same, opt same, full same
#|
#|-- concat with a zero-row frame
#|frame
#|height	2
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	bool	"k"
#|row	8	"z"	null	null
#|row	9	null	0x40200000	false
#|raw same, opt same, full same
#|
#|-- concat zero-column frames adds their heights
#|frame
#|height	6
#|width	0
#|raw same, opt same, full same
#|
#|-- invalid concat no inputs
#|error	InvalidOperation: concat_vertical: no inputs
#|raw same, opt same, full same
#|
#|-- invalid concat schema differs
#|error	InvalidOperation: concat_vertical: input 1 schema [id:u32, g:str, v:f32] differs from input 0's [id:u32, g:str, v:f32, k:bool]
#|raw same, opt same, full same
#|
#|-- invalid concat column order differs
#|error	InvalidOperation: concat_vertical: input 1 schema [g:str, id:u32, v:f32, k:bool] differs from input 0's [id:u32, g:str, v:f32, k:bool]
#|raw same, opt same, full same
#|
