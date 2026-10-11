# v0.2 T5.3: the chunked runner (src/cexec.bend, DESIGN.md 16.5) against the reference runner
# (Exec.run_phys), operator by operator, at grain 2^2 (leaves of 4 rows: every frame here is many
# leaves) unless a line says otherwise. Each line: the reference's height (or error), [same] when
# DF.dump of the two answers is equal, and the chunked runner's counters: walks (per-leaf walks: 2 per
# filter, 1 per with_columns / select of expressions), flat (operators run by today's flat code behind
# the flatten boundary), cin / cout (conversions to / from chunks of a frame above 2^g rows; one-leaf
# frames move their buffers and are not counted). Frames: tests/lib/cxgen.bend t(n).
#  - q1 (Filter + plain Select root, F8), q2 (with_columns revenue), q3 (q2, group_by, sort), q4 (sort,
#    head: the Sort + Head root step), q5's join shape;
#  - filter over every dtype (Raw and Dictionary strings, masks, NaN / -0.0 / inf), a predicate with
#    nulls (a null row is dropped), a literal predicate, a Dictionary column in the predicate (flat);
#  - with_columns: a new column, an overwritten column, a literal-only column, an aggregation inside
#    (flat), a Str output (flat), overwriting a Dictionary column (flat), when / is_in / fill_null;
#  - select: expressions, plain columns (moved on the trees), a literal-only select (one row: flat), an
#    aggregation (flat), select([]) (flat);
#  - chains kept chunked: filter -> with_columns -> filter -> select -> head / slice / tail / drop /
#    rename; a frame of at most 2^g rows (nothing converted, no walk).
import Base
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/plan.bend as P
import ./../src/column.bend as C
import ./lib/cxgen.bend as T

def rev() -> DF.Expr():
  DF.mul(DF.mul(DF.cast_f32(DF.col("qty")), DF.col("price")), DF.sub(DF.lit_f32(1.0), DF.fill_null(DF.col("disc"), DF.lit_f32(0.0))))

def q1p(+n: U32) -> P.Plan:
  DF.lazy_select(DF.lazy_filter(T.srct(n), DF.and(DF.col("ok"), DF.gt(DF.col("qty"), DF.lit_u32(50)))), [DF.col("id"), DF.col("s"), DF.col("price")])

def q2p(+n: U32) -> P.Plan:
  DF.lazy_with_columns(T.srct(n), [DF.alias(rev(), "revenue")])

def q3p(+n: U32) -> P.Plan:
  DF.lazy_sort(DF.lazy_group_by(q2p(n), [DF.col("d")], [DF.alias(DF.sum(DF.col("revenue")), "rs"), DF.alias(DF.mean(DF.col("price")), "pm"), DF.alias(DF.len(), "c"), DF.alias(DF.max(DF.col("qty")), "qm")]), [DF.asc("d")])

def q4p(+n: U32) -> P.Plan:
  DF.lazy_head(DF.lazy_sort(T.srct(n), [DF.asc("d"), DF.desc("price"), DF.asc("id")]), 5)

def c(+tag: String, +n: U32, +p: P.Plan) -> String:
  T.cmp(tag, 2n, p, T.envt(n), T.envt(n))

def cg(+tag: String, +g: Nat, +n: U32, +p: P.Plan) -> String:
  T.cmp(tag, g, p, T.envt(n), T.envt(n))

def flt(+n: U32, +e: DF.Expr()) -> P.Plan:
  DF.lazy_filter(T.srct(n), e)

def wc(+n: U32, +es: List<&2, DF.Expr()>) -> P.Plan:
  DF.lazy_with_columns(T.srct(n), es)

def sel(+n: U32, +es: List<&2, DF.Expr()>) -> P.Plan:
  DF.lazy_select(T.srct(n), es)

def chain(+n: U32) -> P.Plan:
  DF.lazy_select(DF.lazy_filter(DF.lazy_with_columns(DF.lazy_filter(T.srct(n), DF.gt(DF.col("qty"), DF.lit_u32(20))), [DF.alias(DF.add(DF.col("qty"), DF.col("id")), "qi"), DF.alias(DF.mul(DF.col("price"), DF.lit_f32(2.0)), "p2")]), DF.lt(DF.col("qi"), DF.lit_u32(90))), [DF.col("qi"), DF.col("d"), DF.col("p2"), DF.col("s"), DF.col("n")])

def bigs.go(f: Nat, +i: U32, acc: List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  match f:
    case 0n:
      acc
    case 1n+p:
      bigs.go(p, U32.sub(i, 1), D.SStr{"v" ++ U32.show(U32.sub(i, 1))} <> acc)

def ints.go(f: Nat, +i: U32, acc: List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  match f:
    case 0n:
      acc
    case 1n+p:
      ints.go(p, U32.sub(i, 1), D.SU32{U32.sub(i, 1)} <> acc)

# 5000 rows: b a Dictionary of 5000 distinct entries (above CX.dcap() = 4096), i the row
def bigf() -> C.Frame:
  T.frame(C.Frame.from_columns([T.enc(T.mk("b", bigs.go(5000n, 5000, Nil{}), D.TStr{})), T.mk("i", ints.go(5000n, 5000, Nil{}), D.TU32{})]))

def big(+tag: String, +p: P.Plan) -> String:
  T.cmp(tag, 10n, p, T.env.k(DF.source("u", bigf())), T.env.k(DF.source("u", bigf())))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(c("q1", 37, q1p(37)))
    IO.print(c("q1 n=100", 100, q1p(100)))
    IO.print(c("q2", 37, q2p(37)))
    IO.print(c("q3", 37, q3p(37)))
    IO.print(c("q4", 37, q4p(37)))
    IO.print(c("q5 join", 37, DF.lazy_sort(DF.lazy_group_by(DF.lazy_inner_join(DF.lazy_filter(T.srct(37), DF.gt(DF.col("qty"), DF.lit_u32(30))), T.srct(37), ["id"], ["qty"]), [DF.col("d")], [DF.alias(DF.sum(DF.col("qty")), "qs")]), [DF.asc("d")])))
    IO.print(c("filter qty>40", 37, flt(37, DF.gt(DF.col("qty"), DF.lit_u32(40)))))
    IO.print(c("filter ok (nulls drop)", 37, flt(37, DF.col("ok"))))
    IO.print(c("filter price>2 (NaN)", 37, flt(37, DF.gt(DF.col("price"), DF.lit_f32(2.0)))))
    IO.print(c("filter n<0 (i32, nulls)", 37, flt(37, DF.lt(DF.col("n"), DF.lit_i32(0)))))
    IO.print(c("filter s==r2 (Raw str)", 37, flt(37, DF.eq(DF.col("s"), DF.lit_str("r2")))))
    IO.print(c("filter d==k1 (Dictionary: a Dict clone per lane)", 37, flt(37, DF.eq(DF.col("d"), DF.lit_str("k1")))))
    IO.print(c("filter lit true", 37, flt(37, DF.lit_bool(True{}))))
    IO.print(c("filter lit false", 37, flt(37, DF.lit_bool(False{}))))
    IO.print(c("filter is_null(disc)", 37, flt(37, DF.is_null(DF.col("disc")))))
    IO.print(c("filter qty>mean(qty) (aggregation hoisted)", 37, flt(37, DF.gt(DF.cast_f32(DF.col("qty")), DF.mean(DF.col("qty"))))))
    IO.print(c("wc new", 37, wc(37, [DF.alias(DF.add(DF.col("qty"), DF.lit_u32(1)), "q1")])))
    IO.print(c("wc overwrite qty", 37, wc(37, [DF.alias(DF.add(DF.col("qty"), DF.col("id")), "qty")])))
    IO.print(c("wc two, one overwrite", 37, wc(37, [DF.alias(DF.mul(DF.col("price"), DF.col("disc")), "pd"), DF.alias(DF.not(DF.col("ok")), "ok")])))
    IO.print(c("wc literal only", 37, wc(37, [DF.alias(DF.lit_u32(7), "seven")])))
    IO.print(c("wc agg inside (hoisted)", 37, wc(37, [DF.alias(DF.sub(DF.cast_f32(DF.col("qty")), DF.mean(DF.col("qty"))), "dq")])))
    IO.print(c("wc aggs over chunks (after a filter)", 37, DF.lazy_with_columns(flt(37, DF.gt(DF.col("qty"), DF.lit_u32(20))), [DF.alias(DF.sub(DF.col("price"), DF.mean(DF.col("price"))), "dp"), DF.alias(DF.add(DF.col("qty"), DF.sum(DF.col("id"))), "qs"), DF.alias(DF.len(), "n_rows"), DF.alias(DF.min(DF.col("s")), "smin"), DF.alias(DF.n_unique(DF.col("d")), "nu"), DF.alias(DF.first(DF.col("disc")), "f1")])))
    IO.print(c("wc null aggregation (max of all-null)", 37, DF.lazy_with_columns(flt(37, DF.is_null(DF.col("disc"))), [DF.alias(DF.max(DF.col("disc")), "mx"), DF.alias(DF.fill_null(DF.max(DF.col("disc")), DF.col("price")), "fx")])))
    IO.print(c("sel column + aggregation (rows)", 37, sel(37, [DF.col("id"), DF.alias(DF.mean(DF.col("qty")), "mq"), DF.alias(DF.when(DF.gt(DF.cast_f32(DF.col("qty")), DF.mean(DF.col("qty"))), DF.lit_u32(1), DF.lit_u32(0)), "above")])))
    IO.print(c("wc Raw str output", 37, wc(37, [DF.alias(DF.col("s"), "s2")])))
    IO.print(c("wc Dictionary outputs (leaf Dicts merged)", 37, wc(37, [DF.alias(DF.col("d"), "d2"), DF.alias(DF.when(DF.col("ok"), DF.col("d"), DF.lit_str("none")), "dw"), DF.alias(DF.eq(DF.col("d"), DF.lit_str("k2")), "isk2")])))
    IO.print(big("filter over a Dict of 5000 entries (flat)", DF.lazy_filter(T.srcu(bigf()), DF.eq(DF.col("b"), DF.lit_str("v17")))))
    IO.print(big("filter beside a Dict of 5000 entries (chunked)", DF.lazy_filter(T.srcu(bigf()), DF.gt(DF.col("i"), DF.lit_u32(4950)))))
    IO.print(c("wc overwrite Dictionary col (flat)", 37, wc(37, [DF.alias(DF.col("qty"), "d")])))
    IO.print(c("wc when / is_in / fill_null", 37, wc(37, [DF.alias(DF.when(DF.col("ok"), DF.col("qty"), DF.col("id")), "w"), DF.alias(DF.is_in(DF.col("qty"), [D.SU32{48}, D.SU32{85}]), "isin"), DF.alias(DF.fill_null(DF.col("n"), DF.lit_i32(99)), "nf")])))
    IO.print(c("wc reads Raw str", 37, wc(37, [DF.alias(DF.eq(DF.col("s"), DF.lit_str("r1")), "is_r1")])))
    IO.print(c("sel exprs", 37, sel(37, [DF.alias(DF.mul(DF.col("qty"), DF.lit_u32(2)), "q2"), DF.col("price"), DF.alias(DF.lit_u32(1), "one")])))
    IO.print(c("sel plain", 37, sel(37, [DF.col("d"), DF.col("id"), DF.col("s")])))
    IO.print(c("sel plain over chunks (trees moved)", 37, DF.lazy_select(q2p(37), [DF.col("revenue"), DF.col("d"), DF.col("id")])))
    IO.print(c("sel literal only (flat)", 37, sel(37, [DF.alias(DF.lit_u32(1), "one")])))
    IO.print(c("sel agg (flat)", 37, sel(37, [DF.alias(DF.sum(DF.col("qty")), "sq")])))
    IO.print(c("sel aggs over chunks (pruned, flat)", 37, DF.lazy_select(flt(37, DF.gt(DF.col("qty"), DF.lit_u32(20))), [DF.alias(DF.sum(DF.col("qty")), "sq"), DF.alias(DF.len(), "n"), DF.alias(DF.max(DF.col("d")), "dm")])))
    IO.print(c("sel [] (flat)", 37, sel(37, [])))
    IO.print(c("chain", 37, chain(37)))
    IO.print(c("chain n=200", 200, chain(200)))
    IO.print(c("chain + head 7", 37, DF.lazy_head(chain(37), 7)))
    IO.print(c("chain + slice 3 5", 37, DF.lazy_slice(chain(37), 3, 5)))
    IO.print(c("chain + tail 4", 37, DF.lazy_tail(chain(37), 4)))
    IO.print(c("chain + drop + rename", 37, DF.lazy_rename(DF.lazy_drop(chain(37), ["d", "n"]), [("qi", "x"), ("p2", "qi")])))
    IO.print(c("filter + sort (flat boundary)", 37, DF.lazy_sort(flt(37, DF.gt(DF.col("qty"), DF.lit_u32(40))), [DF.desc("price"), DF.asc("id")])))
    IO.print(c("filter + unique (flat boundary)", 37, DF.lazy_unique(DF.lazy_select(flt(37, DF.gt(DF.col("qty"), DF.lit_u32(10))), [DF.col("d"), DF.col("s")]), [])))
    IO.print(cg("q1 at grain 2^1", 1n, 37, q1p(37)))
    IO.print(cg("q2 at grain 2^3", 3n, 37, q2p(37)))
    IO.print(cg("q1 small frame (n <= 2^g)", 6n, 37, q1p(37)))
    IO.print(cg("q2 small frame (n <= 2^g)", 6n, 64, q2p(64)))
    IO.print(cg("chain small frame", 14n, 200, chain(200)))
#|q1: h=11 [same] walks=2 flat=0 cin=1 cout=1
#|q1 n=100: h=26 [same] walks=2 flat=0 cin=1 cout=1
#|q2: h=37 [same] walks=1 flat=0 cin=1 cout=1
#|q3: h=3 [same] walks=1 flat=2 cin=1 cout=1
#|q4: h=5 [same] walks=0 flat=1 cin=0 cout=0
#|q5 join: h=3 [same] walks=2 flat=3 cin=1 cout=1
#|filter qty>40: h=22 [same] walks=2 flat=0 cin=1 cout=1
#|filter ok (nulls drop): h=21 [same] walks=2 flat=0 cin=1 cout=1
#|filter price>2 (NaN): h=28 [same] walks=2 flat=0 cin=1 cout=1
#|filter n<0 (i32, nulls): h=16 [same] walks=2 flat=0 cin=1 cout=1
#|filter s==r2 (Raw str): h=5 [same] walks=2 flat=0 cin=1 cout=1
#|filter d==k1 (Dictionary: a Dict clone per lane): h=12 [same] walks=2 flat=0 cin=1 cout=1
#|filter lit true: h=37 [same] walks=2 flat=0 cin=1 cout=1
#|filter lit false: h=0 [same] walks=2 flat=0 cin=1 cout=1
#|filter is_null(disc): h=7 [same] walks=2 flat=0 cin=1 cout=1
#|filter qty>mean(qty) (aggregation hoisted): h=18 [same] walks=2 flat=0 cin=1 cout=1
#|wc new: h=37 [same] walks=1 flat=0 cin=1 cout=1
#|wc overwrite qty: h=37 [same] walks=1 flat=0 cin=1 cout=1
#|wc two, one overwrite: h=37 [same] walks=1 flat=0 cin=1 cout=1
#|wc literal only: h=37 [same] walks=1 flat=0 cin=1 cout=1
#|wc agg inside (hoisted): h=37 [same] walks=1 flat=0 cin=1 cout=1
#|wc aggs over chunks (after a filter): h=30 [same] walks=3 flat=0 cin=1 cout=2
#|wc null aggregation (max of all-null): h=7 [same] walks=3 flat=0 cin=1 cout=2
#|sel column + aggregation (rows): h=37 [same] walks=1 flat=0 cin=1 cout=1
#|wc Raw str output: h=37 [same] walks=1 flat=0 cin=1 cout=1
#|wc Dictionary outputs (leaf Dicts merged): h=37 [same] walks=1 flat=0 cin=1 cout=1
#|filter over a Dict of 5000 entries (flat): h=1 [same] walks=0 flat=1 cin=0 cout=0
#|filter beside a Dict of 5000 entries (chunked): h=49 [same] walks=2 flat=0 cin=1 cout=1
#|wc overwrite Dictionary col (flat): h=37 [same] walks=0 flat=1 cin=0 cout=0
#|wc when / is_in / fill_null: h=37 [same] walks=1 flat=0 cin=1 cout=1
#|wc reads Raw str: h=37 [same] walks=1 flat=0 cin=1 cout=1
#|sel exprs: h=37 [same] walks=1 flat=0 cin=1 cout=1
#|sel plain: h=37 [same] walks=0 flat=1 cin=0 cout=0
#|sel plain over chunks (trees moved): h=37 [same] walks=1 flat=0 cin=1 cout=1
#|sel literal only (flat): h=1 [same] walks=0 flat=1 cin=0 cout=0
#|sel agg (flat): h=1 [same] walks=0 flat=1 cin=0 cout=0
#|sel aggs over chunks (pruned, flat): h=1 [same] walks=2 flat=1 cin=1 cout=1
#|sel [] (flat): h=0 [same] walks=0 flat=1 cin=0 cout=0
#|chain: h=20 [same] walks=5 flat=0 cin=1 cout=1
#|chain n=200: h=24 [same] walks=5 flat=0 cin=1 cout=1
#|chain + head 7: h=7 [same] walks=5 flat=0 cin=1 cout=1
#|chain + slice 3 5: h=5 [same] walks=5 flat=0 cin=1 cout=1
#|chain + tail 4: h=4 [same] walks=5 flat=0 cin=1 cout=1
#|chain + drop + rename: h=20 [same] walks=5 flat=0 cin=1 cout=1
#|filter + sort (flat boundary): h=22 [same] walks=2 flat=1 cin=1 cout=1
#|filter + unique (flat boundary): h=9 [same] walks=2 flat=1 cin=1 cout=1
#|q1 at grain 2^1: h=11 [same] walks=2 flat=0 cin=1 cout=1
#|q2 at grain 2^3: h=37 [same] walks=1 flat=0 cin=1 cout=1
#|q1 small frame (n <= 2^g): h=11 [same] walks=0 flat=1 cin=0 cout=0
#|q2 small frame (n <= 2^g): h=64 [same] walks=0 flat=1 cin=0 cout=0
#|chain small frame: h=24 [same] walks=0 flat=3 cin=0 cout=0
