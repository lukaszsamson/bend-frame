# v0.2 T5.3: the chunked runner (src/cexec.bend) at chunk boundaries, against the reference runner.
#  - rows around leaf edges at grain 2^2: 0, 1, 3, 4, 5, 7, 8, 9, 15, 16, 17, 33 rows (q1, q2, a chain);
#  - selectivities 0 / 1 / 50 / 100 % over 100 rows (qty = (37 i + 11) mod 100 is a permutation of
#    0..99), all nine columns compacted, then a with_columns and a second filter on the ragged result;
#  - many tiny chunks: a concat of eight chunked 9-row frames at grain 2^1 (a tree of 40 leaves of 1-2
#    rows), filtered twice; a 1 %-selectivity filter leaving mostly empty leaves, then a with_columns;
#  - empty frames (0 rows through filter / with_columns / select / head), zero-column frames (drop of
#    every column, select([])), with_columns over a zero-column frame (flat);
#  - concat of differently chunked frames (chunked + flat, chunked + one-leaf, two ragged chunked frames
#    whose Dictionary columns have different dictionaries), a concat schema error (v0.1's text);
#  - a self join (the source used twice: the first use clones), a join of two chunked frames;
#  - pre-chunked sources (CX.run's pre list: the benchmark's inputs) read once and twice (a clone);
#  - the facade: DF.collect_with / DF.collect_raw_with against DF.collect / DF.collect_raw, including the
#    plan's static error and a missing source (the checks run before the runner, as in Exec.run).
import Base
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/plan.bend as P
import ./../src/schema.bend as S
import ./../src/exec.bend as Q
import ./../src/chunks.bend as CH
import ./../src/cexec.bend as QC
import ./lib/cxgen.bend as T

def q1p(+n: U32) -> P.Plan:
  DF.lazy_select(DF.lazy_filter(T.srct(n), DF.and(DF.col("ok"), DF.gt(DF.col("qty"), DF.lit_u32(50)))), [DF.col("id"), DF.col("s"), DF.col("price")])

def q2p(+n: U32) -> P.Plan:
  DF.lazy_with_columns(T.srct(n), [DF.alias(DF.mul(DF.cast_f32(DF.col("qty")), DF.col("price")), "r")])

def chain(+n: U32) -> P.Plan:
  DF.lazy_head(DF.lazy_filter(DF.lazy_with_columns(DF.lazy_filter(T.srct(n), DF.gt(DF.col("qty"), DF.lit_u32(20))), [DF.alias(DF.add(DF.col("qty"), DF.col("id")), "qi")]), DF.lt(DF.col("qi"), DF.lit_u32(90))), 1000)

def c(+tag: String, +g: Nat, +n: U32, +p: P.Plan) -> String:
  T.cmp(tag, g, p, T.envt(n), T.envt(n))

def edges.go(ns: List<&2, U32>) -> String:
  match ns:
    case Nil{}:
      ""
    case +n <> rest:
      c("q1 n=" ++ U32.show(n), 2n, n, q1p(n)) ++ "\n" ++ c("q2 n=" ++ U32.show(n), 2n, n, q2p(n)) ++ "\n" ++ c("chain n=" ++ U32.show(n), 2n, n, chain(n)) ++ "\n" ++ edges.go(rest)

def sel(+k: U32, +ge: Bool) -> P.Plan:
  DF.lazy_filter(DF.lazy_with_columns(DF.lazy_filter(T.srct(100), Bool.pick(DF.Expr(), ge, DF.ge(DF.col("qty"), DF.lit_u32(k)), DF.gt(DF.col("qty"), DF.lit_u32(k)))), [DF.alias(DF.mul(DF.col("qty"), DF.lit_u32(3)), "q3")]), DF.lt(DF.col("id"), DF.lit_u32(90)))

# a chunked 9-row frame (rows off .. off + 8): a filter that keeps every row makes it chunks
def tiny(+off: U32) -> P.Plan:
  DF.lazy_filter(T.srcu(T.tr(off, 9)), DF.lit_bool(True{}))

def env_u(+off: U32) -> P.Env:
  T.env.k(DF.source("u", T.tr(off, 9)))

def cmp_tiny(+tag: String, +p: P.Plan) -> String:
  T.cmp(tag, 1n, p, env_u(0), env_u(0))

def tinies() -> P.Plan:
  DF.lazy_concat_vertical([tiny(0), tiny(0), tiny(0), tiny(0), tiny(0), tiny(0), tiny(0), tiny(0)])

# t(37) and rows 5 .. 34 under "u" (its Dictionary column codes "k<i % 3>" from row 5: another order)
def env_tu() -> P.Env:
  T.env2(T.t(37), T.tr(5, 30))

def c2(+tag: String, +g: Nat, +p: P.Plan) -> String:
  T.cmp(tag, g, p, env_tu(), env_tu())

def srcu() -> P.Plan:
  T.srcu(T.tr(5, 30))

# ---- pre-chunked sources ----

def pre(+g: Nat) -> List<&1, QC.PNF>:
  QC.PNF{"t", CH.CFrame.of_frame(g, T.t(37))} <> Nil{}

def cmp_pre(+tag: String, +g: Nat, +p: P.Plan) -> String:
  T.cmp.b(tag, Q.Exec.run_phys(p, T.envt(37)), QC.CX.run(g, p, DF.empty_env(), pre(g)))

# ---- the facade (IO): collect_with / collect_raw_with ----

def io.cmp(+tag: String, +da: String, +db: String) -> String:
  Bool.pick(String, String.eq(da, db), tag ++ ": [same]", tag ++ ": [DIFF]\n" ++ da ++ "---\n" ++ db)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(String.trim_end(edges.go([0, 1, 3, 4, 5, 7, 8, 9, 15, 16, 17, 33])))
    IO.print(c("sel 0%", 2n, 100, sel(99, False{})))
    IO.print(c("sel 1%", 2n, 100, sel(98, False{})))
    IO.print(c("sel 50%", 2n, 100, sel(49, False{})))
    IO.print(c("sel 100%", 2n, 100, sel(0, True{})))
    IO.print(cmp_tiny("tiny chunks: concat of 8 chunked frames", tinies()))
    IO.print(cmp_tiny("tiny chunks: + filter + filter", DF.lazy_filter(DF.lazy_filter(tinies(), DF.gt(DF.col("qty"), DF.lit_u32(30))), DF.col("ok"))))
    IO.print(cmp_tiny("tiny chunks: + with_columns + head", DF.lazy_head(DF.lazy_with_columns(tinies(), [DF.alias(DF.add(DF.col("id"), DF.col("qty")), "x")]), 30)))
    IO.print(c("1% filter then with_columns (empty leaves)", 1n, 100, DF.lazy_with_columns(DF.lazy_filter(T.srct(100), DF.gt(DF.col("qty"), DF.lit_u32(98))), [DF.alias(DF.add(DF.col("id"), DF.lit_u32(1)), "x")])))
    IO.print(c("empty: filter", 2n, 0, DF.lazy_filter(T.srct(0), DF.gt(DF.col("qty"), DF.lit_u32(5)))))
    IO.print(c("empty: with_columns + select + head", 2n, 0, DF.lazy_head(DF.lazy_select(q2p(0), [DF.col("r"), DF.alias(DF.add(DF.col("id"), DF.lit_u32(1)), "x")]), 3)))
    IO.print(c("filter to empty, then with_columns + head", 2n, 37, DF.lazy_head(DF.lazy_with_columns(DF.lazy_filter(T.srct(37), DF.gt(DF.col("qty"), DF.lit_u32(200))), [DF.alias(DF.add(DF.col("id"), DF.lit_u32(1)), "x")]), 3)))
    IO.print(c("zero columns: drop every column (chunked)", 2n, 37, DF.lazy_drop(DF.lazy_filter(T.srct(37), DF.gt(DF.col("qty"), DF.lit_u32(30))), ["id", "qty", "price", "ok", "disc", "s", "d", "num", "n"])))
    IO.print(c("zero columns: + with_columns lit (flat) + head", 2n, 37, DF.lazy_head(DF.lazy_with_columns(DF.lazy_drop(DF.lazy_filter(T.srct(37), DF.gt(DF.col("qty"), DF.lit_u32(30))), ["id", "qty", "price", "ok", "disc", "s", "d", "num", "n"]), [DF.alias(DF.lit_u32(4), "four")]), 5)))
    IO.print(c("zero columns: select([]) after a filter", 2n, 37, DF.lazy_select(DF.lazy_filter(T.srct(37), DF.gt(DF.col("qty"), DF.lit_u32(30))), [])))
    IO.print(c2("concat chunked + flat", 2n, DF.lazy_concat_vertical([DF.lazy_filter(T.srct(37), DF.gt(DF.col("qty"), DF.lit_u32(40))), srcu()])))
    IO.print(c2("concat flat + chunked", 2n, DF.lazy_concat_vertical([T.srct(37), DF.lazy_filter(srcu(), DF.gt(DF.col("qty"), DF.lit_u32(40)))])))
    IO.print(c2("concat two ragged chunked (two dictionaries) + filter", 2n, DF.lazy_filter(DF.lazy_concat_vertical([DF.lazy_filter(T.srct(37), DF.gt(DF.col("qty"), DF.lit_u32(40))), DF.lazy_filter(srcu(), DF.lt(DF.col("qty"), DF.lit_u32(60)))]), DF.col("ok"))))
    IO.print(c2("concat chunked + one-leaf", 2n, DF.lazy_concat_vertical([DF.lazy_filter(T.srct(37), DF.gt(DF.col("qty"), DF.lit_u32(40))), DF.lazy_head(srcu(), 3)])))
    IO.print(c2("concat schema error", 2n, DF.lazy_concat_vertical([DF.lazy_filter(T.srct(37), DF.gt(DF.col("qty"), DF.lit_u32(40))), DF.lazy_drop(srcu(), ["n"])])))
    IO.print(c("self join after filters", 2n, 37, DF.lazy_inner_join(DF.lazy_filter(T.srct(37), DF.gt(DF.col("qty"), DF.lit_u32(40))), DF.lazy_filter(T.srct(37), DF.lt(DF.col("qty"), DF.lit_u32(60))), ["id"], ["id"])))
    IO.print(c2("join of two chunked frames + filter", 2n, DF.lazy_filter(DF.lazy_left_join(DF.lazy_filter(T.srct(37), DF.gt(DF.col("qty"), DF.lit_u32(10))), DF.lazy_with_columns(srcu(), [DF.alias(DF.mul(DF.col("id"), DF.lit_u32(2)), "id2")]), ["id"], ["id2"]), DF.gt(DF.col("id"), DF.lit_u32(3)))))
    IO.print(cmp_pre("pre-chunked q1", 2n, q1p(37)))
    IO.print(cmp_pre("pre-chunked sort (flat boundary)", 2n, DF.lazy_head(DF.lazy_sort(T.srct(37), [DF.desc("qty")]), 4)))
    IO.print(cmp_pre("pre-chunked self join (clone)", 2n, DF.lazy_inner_join(T.srct(37), DF.lazy_filter(T.srct(37), DF.gt(DF.col("qty"), DF.lit_u32(50))), ["id"], ["id"])))
    IO.print(cmp_pre("pre-chunked schema mismatch", 2n, DF.lazy_filter(P.Source{"t", S.Field{"id", D.TU32{}} <> Nil{}}, DF.lit_bool(True{}))))
    ra : E.ResT(C.Frame) <- DF.collect(chain(37), T.envt(37))
    rb : E.ResT(C.Frame) <- DF.collect_with(DF.engine_chunked_at(2n), chain(37), T.envt(37))
    IO.print(io.cmp("collect_with chain", DF.dump(ra), DF.dump(rb)))
    rc : E.ResT(C.Frame) <- DF.collect_raw(DF.lazy_filter(T.srct(37), DF.col("nope")), T.envt(37))
    rd : E.ResT(C.Frame) <- DF.collect_raw_with(DF.engine_chunked_at(2n), DF.lazy_filter(T.srct(37), DF.col("nope")), T.envt(37))
    IO.print(io.cmp("collect_raw_with static error", DF.dump(rc), DF.dump(rd)))
    re : E.ResT(C.Frame) <- DF.collect_raw(q1p(37), DF.empty_env())
    rf : E.ResT(C.Frame) <- DF.collect_raw_with(DF.engine_chunked_at(2n), q1p(37), DF.empty_env())
    IO.print(io.cmp("collect_raw_with missing source", DF.dump(re), DF.dump(rf)))
    rg : E.ResT(C.Frame) <- DF.collect_with(DF.engine_reference(), q2p(37), T.envt(37))
    rh : E.ResT(C.Frame) <- DF.collect_with(DF.engine_chunked(), q2p(37), T.envt(37))
    IO.print(io.cmp("collect_with reference vs default chunked (one leaf)", DF.dump(rg), DF.dump(rh)))
#|q1 n=0: h=0 [same] walks=0 flat=1 cin=0 cout=0
#|q2 n=0: h=0 [same] walks=0 flat=1 cin=0 cout=0
#|chain n=0: h=0 [same] walks=0 flat=4 cin=0 cout=0
#|q1 n=1: h=0 [same] walks=0 flat=1 cin=0 cout=0
#|q2 n=1: h=1 [same] walks=0 flat=1 cin=0 cout=0
#|chain n=1: h=0 [same] walks=0 flat=4 cin=0 cout=0
#|q1 n=3: h=1 [same] walks=0 flat=1 cin=0 cout=0
#|q2 n=3: h=3 [same] walks=0 flat=1 cin=0 cout=0
#|chain n=3: h=2 [same] walks=0 flat=4 cin=0 cout=0
#|q1 n=4: h=1 [same] walks=0 flat=1 cin=0 cout=0
#|q2 n=4: h=4 [same] walks=0 flat=1 cin=0 cout=0
#|chain n=4: h=3 [same] walks=0 flat=4 cin=0 cout=0
#|q1 n=5: h=2 [same] walks=2 flat=0 cin=1 cout=0
#|q2 n=5: h=5 [same] walks=1 flat=0 cin=1 cout=1
#|chain n=5: h=4 [same] walks=5 flat=0 cin=1 cout=1
#|q1 n=7: h=3 [same] walks=2 flat=0 cin=1 cout=0
#|q2 n=7: h=7 [same] walks=1 flat=0 cin=1 cout=1
#|chain n=7: h=5 [same] walks=5 flat=0 cin=1 cout=1
#|q1 n=8: h=4 [same] walks=2 flat=0 cin=1 cout=1
#|q2 n=8: h=8 [same] walks=1 flat=0 cin=1 cout=1
#|chain n=8: h=6 [same] walks=5 flat=0 cin=1 cout=1
#|q1 n=9: h=4 [same] walks=2 flat=0 cin=1 cout=0
#|q2 n=9: h=9 [same] walks=1 flat=0 cin=1 cout=1
#|chain n=9: h=6 [same] walks=5 flat=0 cin=1 cout=1
#|q1 n=15: h=5 [same] walks=2 flat=0 cin=1 cout=1
#|q2 n=15: h=15 [same] walks=1 flat=0 cin=1 cout=1
#|chain n=15: h=9 [same] walks=5 flat=0 cin=1 cout=1
#|q1 n=16: h=5 [same] walks=2 flat=0 cin=1 cout=1
#|q2 n=16: h=16 [same] walks=1 flat=0 cin=1 cout=1
#|chain n=16: h=10 [same] walks=5 flat=0 cin=1 cout=1
#|q1 n=17: h=5 [same] walks=2 flat=0 cin=1 cout=1
#|q2 n=17: h=17 [same] walks=1 flat=0 cin=1 cout=1
#|chain n=17: h=10 [same] walks=5 flat=0 cin=1 cout=1
#|q1 n=33: h=10 [same] walks=2 flat=0 cin=1 cout=1
#|q2 n=33: h=33 [same] walks=1 flat=0 cin=1 cout=1
#|chain n=33: h=18 [same] walks=5 flat=0 cin=1 cout=1
#|sel 0%: h=0 [same] walks=5 flat=0 cin=1 cout=0
#|sel 1%: h=1 [same] walks=5 flat=0 cin=1 cout=0
#|sel 50%: h=45 [same] walks=5 flat=0 cin=1 cout=1
#|sel 100%: h=90 [same] walks=5 flat=0 cin=1 cout=1
#|tiny chunks: concat of 8 chunked frames: h=72 [same] walks=16 flat=0 cin=8 cout=1
#|tiny chunks: + filter + filter: h=40 [same] walks=20 flat=0 cin=8 cout=1
#|tiny chunks: + with_columns + head: h=30 [same] walks=17 flat=0 cin=8 cout=1
#|1% filter then with_columns (empty leaves): h=1 [same] walks=3 flat=0 cin=1 cout=0
#|empty: filter: h=0 [same] walks=0 flat=1 cin=0 cout=0
#|empty: with_columns + select + head: h=0 [same] walks=0 flat=3 cin=0 cout=0
#|filter to empty, then with_columns + head: h=0 [same] walks=3 flat=0 cin=1 cout=0
#|zero columns: drop every column (chunked): h=26 [same] walks=2 flat=0 cin=1 cout=0
#|zero columns: + with_columns lit (flat) + head: h=5 [same] walks=2 flat=2 cin=1 cout=0
#|zero columns: select([]) after a filter: h=0 [same] walks=2 flat=1 cin=1 cout=1
#|concat chunked + flat: h=52 [same] walks=2 flat=0 cin=2 cout=1
#|concat flat + chunked: h=55 [same] walks=2 flat=0 cin=2 cout=1
#|concat two ragged chunked (two dictionaries) + filter: h=22 [same] walks=6 flat=0 cin=2 cout=1
#|concat chunked + one-leaf: h=25 [same] walks=2 flat=1 cin=1 cout=1
#|concat schema error: error: InvalidOperation: concat_vertical: input 1 schema [id:u32, qty:u32, price:f32, ok:bool, disc:f32, s:str, d:str, num:str] differs from input 0's [id:u32, qty:u32, price:f32, ok:bool, disc:f32, s:str, d:str, num:str, n:i32] [same] walks=2 flat=2 cin=1 cout=1
#|self join after filters: h=8 [same] walks=4 flat=1 cin=2 cout=2
#|join of two chunked frames + filter: h=29 [same] walks=5 flat=1 cin=3 cout=3
#|pre-chunked q1: h=11 [same] walks=2 flat=0 cin=0 cout=1
#|pre-chunked sort (flat boundary): h=4 [same] walks=0 flat=1 cin=0 cout=1
#|pre-chunked self join (clone): h=18 [same] walks=2 flat=1 cin=0 cout=2
#|pre-chunked schema mismatch: error: InvalidOperation: source t: data schema [id:u32, qty:u32, price:f32, ok:bool, disc:f32, s:str, d:str, num:str, n:i32] differs from the plan's [id:u32] [same] walks=0 flat=0 cin=0 cout=0
#|collect_with chain: [same]
#|collect_raw_with static error: [same]
#|collect_raw_with missing source: [same]
#|collect_with reference vs default chunked (one leaf): [same]
