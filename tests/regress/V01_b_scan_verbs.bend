# V01-b (plans/REVIEW_V01_ASTRA.txt, "Tests": the generated suite builds in-memory frames, so
# the IO / materialisation boundary had little coverage): every lazy verb over DF.scan_csv
# (schema inferred from the file, frames read at collect) against the eager verb over
# DF.read_csv of the same file. Verbs: filter, select, with_columns, group_by, sort, head,
# slice, tail, unique, drop, rename, inner / left / semi / anti join (scan x scan), concat
# (one file scanned twice), and one multi-verb pipeline. Each case prints the eager dump once,
# then whether DF.collect_raw, DF.collect and DF.collect_full dump the same text.
# V01_scan_sales.csv: id u32, g str, v f32 (two empty cells: null), n u32 (one null); the last
# row repeats row 3. V01_scan_dim.csv: g str, label str (keys a, b, d).
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def sales() -> String:
  "tests/regress/data/V01_scan_sales.csv"

def dim() -> String:
  "tests/regress/data/V01_scan_dim.csv"

def gs() -> List<&2, String>:
  ["g"]

def big() -> X.Expr:
  DF.gt(DF.col("v"), DF.lit_f32(2.0))

def sel() -> List<&2, X.Expr>:
  [DF.col("g"), DF.alias(DF.add(DF.col("n"), DF.col("id")), "ni")]

def wc() -> List<&2, X.Expr>:
  [DF.alias(DF.mul(DF.col("v"), DF.lit_f32(2.0)), "v2"), DF.alias(DF.fill_null(DF.col("n"), DF.lit_u32(0)), "n")]

def keys() -> List<&2, X.Expr>:
  [DF.col("g")]

def aggs() -> List<&2, X.Expr>:
  [DF.alias(DF.sum(DF.col("n")), "n_sum"), DF.alias(DF.mean(DF.col("v")), "v_mean"), DF.alias(DF.count(DF.col("v")), "v_count"), DF.alias(DF.len(), "rows")]

def sk() -> List<&2, DF.SortKey()>:
  [DF.asc("g"), DF.desc("id")]

def a(r: E.ResT(C.Frame), +tag: String, +p: P.Plan) -> IO(Unit):
  R.agree("V01-b " ++ tag, r, p, DF.empty_env(), DF.empty_env(), DF.empty_env())

# one-input verbs: the eager verb `k` over a fresh read_csv, the lazy plan over the scan
def one(+tag: String, k: C.Frame -> E.ResT(C.Frame), +p: P.Plan) -> IO(Unit):
  do IO<Unit>:
    r : E.ResT(C.Frame) <- DF.read_csv(sales())
    a(DF.then(r, k), tag, p)

def e_semi.k(l: C.Frame, r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{fr}:
      DF.semi_join(l, fr, gs(), gs())

def e_semi(l: E.ResT(C.Frame), r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match l:
    case Fail{e}:
      Fail{e}
    case Done{fl}:
      e_semi.k(fl, r)

def e_anti.k(l: C.Frame, r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{fr}:
      DF.anti_join(l, fr, gs(), gs())

def e_anti(l: E.ResT(C.Frame), r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match l:
    case Fail{e}:
      Fail{e}
    case Done{fl}:
      e_anti.k(fl, r)

def e_cat.k(l: C.Frame, r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{fr}:
      DF.concat_vertical([l, fr])

def e_cat(l: E.ResT(C.Frame), r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match l:
    case Fail{e}:
      Fail{e}
    case Done{fl}:
      e_cat.k(fl, r)

def pipe(f: C.Frame) -> E.ResT(C.Frame):
  DF.then(DF.then(DF.then(DF.with_columns(f, wc()), g => DF.filter(g, DF.gt(DF.col("n"), DF.lit_u32(15)))), g => DF.group_by(g, keys(), aggs())), g => DF.sort(g, [DF.desc("g")]))

def lpipe(+s: P.Plan) -> P.Plan:
  DF.lazy_sort(DF.lazy_group_by(DF.lazy_filter(DF.lazy_with_columns(s, wc()), DF.gt(DF.col("n"), DF.lit_u32(15))), keys(), aggs()), [DF.desc("g")])

def run(+s: P.Plan, +d: P.Plan) -> IO(Unit):
  do IO<Unit>:
    IO.print(R.schema("V01-b sales scan", s))
    IO.print(R.schema("V01-b dim scan", d))
    one("filter", f => DF.filter(f, big()), DF.lazy_filter(s, big()))
    one("select", f => DF.select(f, sel()), DF.lazy_select(s, sel()))
    one("with_columns", f => DF.with_columns(f, wc()), DF.lazy_with_columns(s, wc()))
    one("group_by", f => DF.group_by(f, keys(), aggs()), DF.lazy_group_by(s, keys(), aggs()))
    one("sort", f => DF.sort(f, sk()), DF.lazy_sort(s, sk()))
    one("head", f => DF.head(f, 3), DF.lazy_head(s, 3))
    one("slice", f => DF.slice(f, 1, 3), DF.lazy_slice(s, 1, 3))
    one("tail", f => DF.tail(f, 2), DF.lazy_tail(s, 2))
    one("unique", f => DF.unique(f, []), DF.lazy_unique(s, []))
    one("unique subset", f => DF.unique(f, gs()), DF.lazy_unique(s, gs()))
    one("drop", f => DF.drop(f, ["v", "id"]), DF.lazy_drop(s, ["v", "id"]))
    one("rename", f => DF.rename(f, [("g", "grp"), ("n", "qty")]), DF.lazy_rename(s, [("g", "grp"), ("n", "qty")]))
    one("pipeline", f => pipe(f), lpipe(s))
    l1 : E.ResT(C.Frame) <- DF.read_csv(sales())
    r1 : E.ResT(C.Frame) <- DF.read_csv(dim())
    a(R.e_inner(l1, r1, gs(), gs()), "inner join", DF.lazy_inner_join(s, d, gs(), gs()))
    l2 : E.ResT(C.Frame) <- DF.read_csv(sales())
    r2 : E.ResT(C.Frame) <- DF.read_csv(dim())
    a(R.e_left(l2, r2, gs(), gs()), "left join", DF.lazy_left_join(s, d, gs(), gs()))
    l3 : E.ResT(C.Frame) <- DF.read_csv(sales())
    r3 : E.ResT(C.Frame) <- DF.read_csv(dim())
    a(e_semi(l3, r3), "semi join", DF.lazy_semi_join(s, d, gs(), gs()))
    l4 : E.ResT(C.Frame) <- DF.read_csv(sales())
    r4 : E.ResT(C.Frame) <- DF.read_csv(dim())
    a(e_anti(l4, r4), "anti join", DF.lazy_anti_join(s, d, gs(), gs()))
    l5 : E.ResT(C.Frame) <- DF.read_csv(sales())
    r5 : E.ResT(C.Frame) <- DF.read_csv(sales())
    a(e_cat(DF.then(l5, f => DF.head(f, 2)), r5), "concat", DF.lazy_concat_vertical([DF.lazy_head(s, 2), s]))

def go(rs: E.Res(P.Plan), rd: E.Res(P.Plan)) -> IO(Unit):
  match rs rd:
    case Done{s} Done{d}:
      run(s, d)
    case Fail{e} _:
      IO.print("scan failed: " ++ E.Err.show(e))
    case _ Fail{e}:
      IO.print("scan failed: " ++ E.Err.show(e))

def main() -> IO(Unit):
  do IO<Unit>:
    rs : E.Res(P.Plan) <- DF.scan_csv(sales())
    rd : E.Res(P.Plan) <- DF.scan_csv(dim())
    go(rs, rd)
#|-- V01-b sales scan schema
#|id:u32, g:str, v:f32, n:u32
#|
#|-- V01-b dim scan schema
#|g:str, label:str
#|
#|-- V01-b filter
#|frame
#|height	3
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	u32	"n"
#|row	2	"b"	0x40200000	null
#|row	4	"c"	0x40800000	40
#|row	5	"b"	0x40b00000	50
#|raw=eager opt=eager full=eager
#|
#|-- V01-b select
#|frame
#|height	6
#|width	2
#|col	str	"g"
#|col	u32	"ni"
#|row	"a"	11
#|row	"b"	null
#|row	"a"	33
#|row	"c"	44
#|row	"b"	55
#|row	"a"	33
#|raw=eager opt=eager full=eager
#|
#|-- V01-b with_columns
#|frame
#|height	6
#|width	5
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	u32	"n"
#|col	f32	"v2"
#|row	1	"a"	0x3fc00000	10	0x40400000
#|row	2	"b"	0x40200000	0	0x40a00000
#|row	3	"a"	null	30	null
#|row	4	"c"	0x40800000	40	0x41000000
#|row	5	"b"	0x40b00000	50	0x41300000
#|row	3	"a"	null	30	null
#|raw=eager opt=eager full=eager
#|
#|-- V01-b group_by
#|frame
#|height	3
#|width	5
#|col	str	"g"
#|col	u32	"n_sum"
#|col	f32	"v_mean"
#|col	u32	"v_count"
#|col	u32	"rows"
#|row	"a"	70	0x3fc00000	1	3
#|row	"b"	50	0x40800000	2	2
#|row	"c"	40	0x40800000	1	1
#|raw=eager opt=eager full=eager
#|
#|-- V01-b sort
#|frame
#|height	6
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	u32	"n"
#|row	3	"a"	null	30
#|row	3	"a"	null	30
#|row	1	"a"	0x3fc00000	10
#|row	5	"b"	0x40b00000	50
#|row	2	"b"	0x40200000	null
#|row	4	"c"	0x40800000	40
#|raw=eager opt=eager full=eager
#|
#|-- V01-b head
#|frame
#|height	3
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	u32	"n"
#|row	1	"a"	0x3fc00000	10
#|row	2	"b"	0x40200000	null
#|row	3	"a"	null	30
#|raw=eager opt=eager full=eager
#|
#|-- V01-b slice
#|frame
#|height	3
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	u32	"n"
#|row	2	"b"	0x40200000	null
#|row	3	"a"	null	30
#|row	4	"c"	0x40800000	40
#|raw=eager opt=eager full=eager
#|
#|-- V01-b tail
#|frame
#|height	2
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	u32	"n"
#|row	5	"b"	0x40b00000	50
#|row	3	"a"	null	30
#|raw=eager opt=eager full=eager
#|
#|-- V01-b unique
#|frame
#|height	5
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	u32	"n"
#|row	1	"a"	0x3fc00000	10
#|row	2	"b"	0x40200000	null
#|row	3	"a"	null	30
#|row	4	"c"	0x40800000	40
#|row	5	"b"	0x40b00000	50
#|raw=eager opt=eager full=eager
#|
#|-- V01-b unique subset
#|frame
#|height	3
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	u32	"n"
#|row	1	"a"	0x3fc00000	10
#|row	2	"b"	0x40200000	null
#|row	4	"c"	0x40800000	40
#|raw=eager opt=eager full=eager
#|
#|-- V01-b drop
#|frame
#|height	6
#|width	2
#|col	str	"g"
#|col	u32	"n"
#|row	"a"	10
#|row	"b"	null
#|row	"a"	30
#|row	"c"	40
#|row	"b"	50
#|row	"a"	30
#|raw=eager opt=eager full=eager
#|
#|-- V01-b rename
#|frame
#|height	6
#|width	4
#|col	u32	"id"
#|col	str	"grp"
#|col	f32	"v"
#|col	u32	"qty"
#|row	1	"a"	0x3fc00000	10
#|row	2	"b"	0x40200000	null
#|row	3	"a"	null	30
#|row	4	"c"	0x40800000	40
#|row	5	"b"	0x40b00000	50
#|row	3	"a"	null	30
#|raw=eager opt=eager full=eager
#|
#|-- V01-b pipeline
#|frame
#|height	3
#|width	5
#|col	str	"g"
#|col	u32	"n_sum"
#|col	f32	"v_mean"
#|col	u32	"v_count"
#|col	u32	"rows"
#|row	"c"	40	0x40800000	1	1
#|row	"b"	50	0x40b00000	1	1
#|row	"a"	60	null	0	2
#|raw=eager opt=eager full=eager
#|
#|-- V01-b inner join
#|frame
#|height	5
#|width	5
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	u32	"n"
#|col	str	"label"
#|row	1	"a"	0x3fc00000	10	"alpha"
#|row	2	"b"	0x40200000	null	"beta"
#|row	3	"a"	null	30	"alpha"
#|row	5	"b"	0x40b00000	50	"beta"
#|row	3	"a"	null	30	"alpha"
#|raw=eager opt=eager full=eager
#|
#|-- V01-b left join
#|frame
#|height	6
#|width	5
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	u32	"n"
#|col	str	"label"
#|row	1	"a"	0x3fc00000	10	"alpha"
#|row	2	"b"	0x40200000	null	"beta"
#|row	3	"a"	null	30	"alpha"
#|row	4	"c"	0x40800000	40	null
#|row	5	"b"	0x40b00000	50	"beta"
#|row	3	"a"	null	30	"alpha"
#|raw=eager opt=eager full=eager
#|
#|-- V01-b semi join
#|frame
#|height	5
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	u32	"n"
#|row	1	"a"	0x3fc00000	10
#|row	2	"b"	0x40200000	null
#|row	3	"a"	null	30
#|row	5	"b"	0x40b00000	50
#|row	3	"a"	null	30
#|raw=eager opt=eager full=eager
#|
#|-- V01-b anti join
#|frame
#|height	1
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	u32	"n"
#|row	4	"c"	0x40800000	40
#|raw=eager opt=eager full=eager
#|
#|-- V01-b concat
#|frame
#|height	8
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	u32	"n"
#|row	1	"a"	0x3fc00000	10
#|row	2	"b"	0x40200000	null
#|row	1	"a"	0x3fc00000	10
#|row	2	"b"	0x40200000	null
#|row	3	"a"	null	30
#|row	4	"c"	0x40800000	40
#|row	5	"b"	0x40b00000	50
#|row	3	"a"	null	30
#|raw=eager opt=eager full=eager
#|
