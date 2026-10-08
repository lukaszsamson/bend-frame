# M3 table verbs (DESIGN.md 15.2.3, 15.2.4): drop, rename, slice, tail, unique, semi / anti
# joins and concat_vertical, eager and lazy. Each case prints the eager dump, then whether raw
# lazy (Exec.run), DF.collect and DF.collect_full dump the same text (tests/regress/lib/rx.bend
# `four`). Cases: success, nulls (null keys, null cells through concat), NaN / -0.0 under
# unique, empty and zero-row inputs, every static error with its text.
import Base
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/expr.bend as X
import ./../src/plan.bend as P
import ./regress/lib/rx.bend as R

# a: u32 with nulls; b: str; c: f32 with NaN, -0.0 and 0.0 (unique treats them as group_by does)
def t() -> E.ResT(C.Frame):
  R.frame([R.mk("a", [R.u(1), R.u(2), R.null(), R.u(2), R.u(1), R.null()], D.TU32{}), R.mk("b", [R.s("x"), R.s("y"), R.s("z"), R.s("y"), R.s("x"), R.s("w")], D.TStr{}), R.mk("c", [R.f(1.5), R.f(R.nan()), R.f(R.nzero()), R.f(R.nan()), R.f(0.0), R.f(0.0)], D.TF32{})])

# a right side with a repeated key and a null key
def u() -> E.ResT(C.Frame):
  R.frame([R.mk("k", [R.u(2), R.u(2), R.u(7), R.null()], D.TU32{}), R.mk("v", [R.s("p"), R.s("q"), R.s("r"), R.s("s")], D.TStr{})])

# t's schema, no nulls anywhere
def x() -> E.ResT(C.Frame):
  R.frame([R.mk("a", [R.u(5), R.u(6)], D.TU32{}), R.mk("b", [R.s("p"), R.s("q")], D.TStr{}), R.mk("c", [R.f(2.0), R.f(3.0)], D.TF32{})])

def T() -> P.Plan:
  R.src("t", t())

def U() -> P.Plan:
  R.src("u", u())

def XP() -> P.Plan:
  R.src("x", x())

def et() -> P.Env:
  R.env1("t", t())

def etu() -> P.Env:
  R.env_add(R.env1("t", t()), "u", u())

def etx() -> P.Env:
  R.env_add(R.env1("t", t()), "x", x())

# ---- eager wrappers over a result (an error passes through) ----

def e_drop(r: E.ResT(C.Frame), ns: List<&2, String>) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.drop(f, ns)

def e_rename(r: E.ResT(C.Frame), ps: List<&2, DF.RenamePair()>) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.rename(f, ps)

def e_slice(r: E.ResT(C.Frame), o: U32, l: U32) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.slice(f, o, l)

def e_tail(r: E.ResT(C.Frame), n: U32) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.tail(f, n)

def e_unique(r: E.ResT(C.Frame), ns: List<&2, String>) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.unique(f, ns)

def e_semi.k(l: C.Frame, r: E.ResT(C.Frame), lo: List<&2, String>, ro: List<&2, String>) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.semi_join(l, f, lo, ro)

def e_semi(l: E.ResT(C.Frame), r: E.ResT(C.Frame), lo: List<&2, String>, ro: List<&2, String>) -> E.ResT(C.Frame):
  match l:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      e_semi.k(f, r, lo, ro)

def e_anti.k(l: C.Frame, r: E.ResT(C.Frame), lo: List<&2, String>, ro: List<&2, String>) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.anti_join(l, f, lo, ro)

def e_anti(l: E.ResT(C.Frame), r: E.ResT(C.Frame), lo: List<&2, String>, ro: List<&2, String>) -> E.ResT(C.Frame):
  match l:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      e_anti.k(f, r, lo, ro)

# concat of results: the first Fail wins, else DF.concat_vertical of the frames
def e_cat.go(rs: List<&1, E.ResT(C.Frame)>, acc: List<&1, C.Frame>) -> E.ResT(List<&1, C.Frame>):
  match rs:
    case Nil{}:
      Done{List.reverse(&1, C.Frame, acc)}
    case Fail{e} <> t:
      Fail{e}
    case Done{f} <> t:
      e_cat.go(t, f <> acc)

def e_cat.k(r: E.ResT(List<&1, C.Frame>)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{fs}:
      DF.concat_vertical(fs)

def e_cat(rs: List<&1, E.ResT(C.Frame)>) -> E.ResT(C.Frame):
  e_cat.k(e_cat.go(rs, Nil{}))

def nothing() -> X.Expr:
  DF.lit_bool(False{})

def main() -> IO(Unit):
  do IO<Unit>:
    R.four("drop b", e_drop(t(), ["b"]), DF.lazy_drop(T(), ["b"]), et(), et(), et())
    R.four("drop repeated name", e_drop(t(), ["b", "b", "a"]), DF.lazy_drop(T(), ["b", "b", "a"]), et(), et(), et())
    R.four("drop missing", e_drop(t(), ["b", "q"]), DF.lazy_drop(T(), ["b", "q"]), et(), et(), et())
    R.four("drop every column", e_drop(t(), ["a", "b", "c"]), DF.lazy_drop(T(), ["a", "b", "c"]), et(), et(), et())
    R.four("rename swap", e_rename(t(), [("a", "b"), ("b", "a")]), DF.lazy_rename(T(), [("a", "b"), ("b", "a")]), et(), et(), et())
    R.four("rename missing", e_rename(t(), [("a", "x"), ("q", "r")]), DF.lazy_rename(T(), [("a", "x"), ("q", "r")]), et(), et(), et())
    R.four("rename from twice", e_rename(t(), [("a", "x"), ("a", "y")]), DF.lazy_rename(T(), [("a", "x"), ("a", "y")]), et(), et(), et())
    R.four("rename collision", e_rename(t(), [("a", "c")]), DF.lazy_rename(T(), [("a", "c")]), et(), et(), et())
    R.four("slice 1 2", e_slice(t(), 1, 2), DF.lazy_slice(T(), 1, 2), et(), et(), et())
    R.four("slice clamped", e_slice(t(), 4, 10), DF.lazy_slice(T(), 4, 10), et(), et(), et())
    R.four("slice past the end", e_slice(t(), 10, 2), DF.lazy_slice(T(), 10, 2), et(), et(), et())
    R.four("slice max max", e_slice(t(), 4294967295, 4294967295), DF.lazy_slice(T(), 4294967295, 4294967295), et(), et(), et())
    R.four("tail 2", e_tail(t(), 2), DF.lazy_tail(T(), 2), et(), et(), et())
    R.four("tail 100", e_tail(t(), 100), DF.lazy_tail(T(), 100), et(), et(), et())
    R.four("unique every column", e_unique(t(), []), DF.lazy_unique(T(), []), et(), et(), et())
    R.four("unique a (null keys one group)", e_unique(t(), ["a"]), DF.lazy_unique(T(), ["a"]), et(), et(), et())
    R.four("unique c (NaN, -0.0 = 0.0)", e_unique(t(), ["c"]), DF.lazy_unique(T(), ["c"]), et(), et(), et())
    R.four("unique repeated name", e_unique(t(), ["b", "b"]), DF.lazy_unique(T(), ["b", "b"]), et(), et(), et())
    R.four("unique missing", e_unique(t(), ["a", "q"]), DF.lazy_unique(T(), ["a", "q"]), et(), et(), et())
    R.four("semi", e_semi(t(), u(), ["a"], ["k"]), DF.lazy_semi_join(T(), U(), ["a"], ["k"]), etu(), etu(), etu())
    R.four("anti", e_anti(t(), u(), ["a"], ["k"]), DF.lazy_anti_join(T(), U(), ["a"], ["k"]), etu(), etu(), etu())
    R.four("semi key dtype", e_semi(t(), u(), ["b"], ["k"]), DF.lazy_semi_join(T(), U(), ["b"], ["k"]), etu(), etu(), etu())
    R.four("anti no keys", e_anti(t(), u(), [], []), DF.lazy_anti_join(T(), U(), [], []), etu(), etu(), etu())
    R.four("semi zero-row left", e_semi(R.e_filter(t(), nothing()), u(), ["a"], ["k"]), DF.lazy_semi_join(DF.lazy_filter(T(), nothing()), U(), ["a"], ["k"]), etu(), etu(), etu())
    R.four("concat t t", e_cat([t(), t()]), DF.lazy_concat_vertical([T(), T()]), et(), et(), et())
    R.four("concat x t x", e_cat([x(), t(), x()]), DF.lazy_concat_vertical([XP(), T(), XP()]), etx(), etx(), etx())
    R.four("concat schema differs", e_cat([t(), e_drop(t(), ["c"])]), DF.lazy_concat_vertical([T(), DF.lazy_drop(T(), ["c"])]), et(), et(), et())
    R.four("concat input 2 differs", e_cat([t(), x(), e_drop(x(), ["a"])]), DF.lazy_concat_vertical([T(), XP(), DF.lazy_drop(XP(), ["a"])]), etx(), etx(), etx())
    R.four("concat one input", e_cat([x()]), DF.lazy_concat_vertical([XP()]), etx(), etx(), etx())
    R.four("concat no inputs", e_cat([]), DF.lazy_concat_vertical([]), et(), et(), et())
    R.four("unique zero rows", e_unique(R.e_filter(t(), nothing()), []), DF.lazy_unique(DF.lazy_filter(T(), nothing()), []), et(), et(), et())
    IO.print(DF.explain(DF.lazy_semi_join(DF.lazy_concat_vertical([DF.lazy_slice(T(), 1, 2), DF.lazy_tail(T(), 3), DF.lazy_unique(T(), [])]), DF.lazy_anti_join(DF.lazy_rename(DF.lazy_drop(U(), ["v"]), [("k", "a")]), T(), ["a"], ["a"]), ["a"], ["a"])) ++ "\n")
    IO.print(DF.explain(DF.lazy_concat_vertical([DF.lazy_concat_vertical([T(), XP()]), DF.lazy_unique(XP(), ["a", "b"])])) ++ "\n")
    IO.print(DF.explain(DF.optimize(DF.lazy_head(DF.lazy_drop(DF.lazy_head(T(), 5), ["b"]), 2))) ++ "\n")
    IO.print(DF.schema_show(DF.collect_schema(DF.lazy_rename(DF.lazy_drop(T(), ["b"]), [("c", "b")]))))
    IO.print(DF.schema_show(DF.collect_schema(DF.lazy_concat_vertical([T(), DF.lazy_drop(U(), ["q"]), DF.lazy_drop(T(), ["c"])]))))
    IO.print(DF.schema_show(DF.collect_schema(DF.lazy_concat_vertical([T(), DF.lazy_drop(T(), ["c"]), DF.lazy_drop(U(), ["q"])]))))
#|-- drop b
#|frame
#|height	6
#|width	2
#|col	u32	"a"
#|col	f32	"c"
#|row	1	0x3fc00000
#|row	2	0x7fc00000
#|row	null	0x80000000
#|row	2	0x7fc00000
#|row	1	0x00000000
#|row	null	0x00000000
#|raw same, opt same, full same
#|
#|-- drop repeated name
#|frame
#|height	6
#|width	1
#|col	f32	"c"
#|row	0x3fc00000
#|row	0x7fc00000
#|row	0x80000000
#|row	0x7fc00000
#|row	0x00000000
#|row	0x00000000
#|raw same, opt same, full same
#|
#|-- drop missing
#|error	ColumnNotFound: q
#|raw same, opt same, full same
#|
#|-- drop every column
#|frame
#|height	6
#|width	0
#|raw same, opt same, full same
#|
#|-- rename swap
#|frame
#|height	6
#|width	3
#|col	u32	"b"
#|col	str	"a"
#|col	f32	"c"
#|row	1	"x"	0x3fc00000
#|row	2	"y"	0x7fc00000
#|row	null	"z"	0x80000000
#|row	2	"y"	0x7fc00000
#|row	1	"x"	0x00000000
#|row	null	"w"	0x00000000
#|raw same, opt same, full same
#|
#|-- rename missing
#|error	ColumnNotFound: q
#|raw same, opt same, full same
#|
#|-- rename from twice
#|error	DuplicateColumn: a
#|raw same, opt same, full same
#|
#|-- rename collision
#|error	DuplicateColumn: c
#|raw same, opt same, full same
#|
#|-- slice 1 2
#|frame
#|height	2
#|width	3
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|row	2	"y"	0x7fc00000
#|row	null	"z"	0x80000000
#|raw same, opt same, full same
#|
#|-- slice clamped
#|frame
#|height	2
#|width	3
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|row	1	"x"	0x00000000
#|row	null	"w"	0x00000000
#|raw same, opt same, full same
#|
#|-- slice past the end
#|frame
#|height	0
#|width	3
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|raw same, opt same, full same
#|
#|-- slice max max
#|frame
#|height	0
#|width	3
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|raw same, opt same, full same
#|
#|-- tail 2
#|frame
#|height	2
#|width	3
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|row	1	"x"	0x00000000
#|row	null	"w"	0x00000000
#|raw same, opt same, full same
#|
#|-- tail 100
#|frame
#|height	6
#|width	3
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|row	1	"x"	0x3fc00000
#|row	2	"y"	0x7fc00000
#|row	null	"z"	0x80000000
#|row	2	"y"	0x7fc00000
#|row	1	"x"	0x00000000
#|row	null	"w"	0x00000000
#|raw same, opt same, full same
#|
#|-- unique every column
#|frame
#|height	5
#|width	3
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|row	1	"x"	0x3fc00000
#|row	2	"y"	0x7fc00000
#|row	null	"z"	0x80000000
#|row	1	"x"	0x00000000
#|row	null	"w"	0x00000000
#|raw same, opt same, full same
#|
#|-- unique a (null keys one group)
#|frame
#|height	3
#|width	3
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|row	1	"x"	0x3fc00000
#|row	2	"y"	0x7fc00000
#|row	null	"z"	0x80000000
#|raw same, opt same, full same
#|
#|-- unique c (NaN, -0.0 = 0.0)
#|frame
#|height	3
#|width	3
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|row	1	"x"	0x3fc00000
#|row	2	"y"	0x7fc00000
#|row	null	"z"	0x80000000
#|raw same, opt same, full same
#|
#|-- unique repeated name
#|frame
#|height	4
#|width	3
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|row	1	"x"	0x3fc00000
#|row	2	"y"	0x7fc00000
#|row	null	"z"	0x80000000
#|row	null	"w"	0x00000000
#|raw same, opt same, full same
#|
#|-- unique missing
#|error	ColumnNotFound: q
#|raw same, opt same, full same
#|
#|-- semi
#|frame
#|height	2
#|width	3
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|row	2	"y"	0x7fc00000
#|row	2	"y"	0x7fc00000
#|raw same, opt same, full same
#|
#|-- anti
#|frame
#|height	4
#|width	3
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|row	1	"x"	0x3fc00000
#|row	null	"z"	0x80000000
#|row	1	"x"	0x00000000
#|row	null	"w"	0x00000000
#|raw same, opt same, full same
#|
#|-- semi key dtype
#|error	TypeMismatch in join: expected str, got u32
#|raw same, opt same, full same
#|
#|-- anti no keys
#|error	InvalidOperation: join: no key columns
#|raw same, opt same, full same
#|
#|-- semi zero-row left
#|frame
#|height	0
#|width	3
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|raw same, opt same, full same
#|
#|-- concat t t
#|frame
#|height	12
#|width	3
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|row	1	"x"	0x3fc00000
#|row	2	"y"	0x7fc00000
#|row	null	"z"	0x80000000
#|row	2	"y"	0x7fc00000
#|row	1	"x"	0x00000000
#|row	null	"w"	0x00000000
#|row	1	"x"	0x3fc00000
#|row	2	"y"	0x7fc00000
#|row	null	"z"	0x80000000
#|row	2	"y"	0x7fc00000
#|row	1	"x"	0x00000000
#|row	null	"w"	0x00000000
#|raw same, opt same, full same
#|
#|-- concat x t x
#|frame
#|height	10
#|width	3
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|row	5	"p"	0x40000000
#|row	6	"q"	0x40400000
#|row	1	"x"	0x3fc00000
#|row	2	"y"	0x7fc00000
#|row	null	"z"	0x80000000
#|row	2	"y"	0x7fc00000
#|row	1	"x"	0x00000000
#|row	null	"w"	0x00000000
#|row	5	"p"	0x40000000
#|row	6	"q"	0x40400000
#|raw same, opt same, full same
#|
#|-- concat schema differs
#|error	InvalidOperation: concat_vertical: input 1 schema [a:u32, b:str] differs from input 0's [a:u32, b:str, c:f32]
#|raw same, opt same, full same
#|
#|-- concat input 2 differs
#|error	InvalidOperation: concat_vertical: input 2 schema [b:str, c:f32] differs from input 0's [a:u32, b:str, c:f32]
#|raw same, opt same, full same
#|
#|-- concat one input
#|frame
#|height	2
#|width	3
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|row	5	"p"	0x40000000
#|row	6	"q"	0x40400000
#|raw same, opt same, full same
#|
#|-- concat no inputs
#|error	InvalidOperation: concat_vertical: no inputs
#|raw same, opt same, full same
#|
#|-- unique zero rows
#|frame
#|height	0
#|width	3
#|col	u32	"a"
#|col	str	"b"
#|col	f32	"c"
#|raw same, opt same, full same
#|
#|SEMI JOIN ON [a = a]
#|  CONCAT
#|    SLICE 1 2
#|      SOURCE t [a:u32, b:str, c:f32]
#|    TAIL 3
#|      SOURCE t [a:u32, b:str, c:f32]
#|    UNIQUE []
#|      SOURCE t [a:u32, b:str, c:f32]
#|  ANTI JOIN ON [a = a]
#|    RENAME [k -> a]
#|      DROP [v]
#|        SOURCE u [k:u32, v:str]
#|    SOURCE t [a:u32, b:str, c:f32]
#|
#|CONCAT
#|  CONCAT
#|    SOURCE t [a:u32, b:str, c:f32]
#|    SOURCE x [a:u32, b:str, c:f32]
#|  UNIQUE [a, b]
#|    SOURCE x [a:u32, b:str, c:f32]
#|
#|HEAD 2
#|  DROP [b]
#|    HEAD 5
#|      SOURCE t [a:u32, b:str, c:f32]
#|
#|a:u32, b:f32
#|error: ColumnNotFound: q
#|error: InvalidOperation: concat_vertical: input 1 schema [a:u32, b:str] differs from input 0's [a:u32, b:str, c:f32]
