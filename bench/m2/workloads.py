"""The FROZEN W0 workload list for the v0.2 performance milestone (plans/M_02.txt W0, section 5).

One place defines every workload; gen.py generates their inputs, run.py runs them and
expected.json (frozen from the BASELINE binary, `run.py freeze`) validates their results.
Adding a workload is fine; changing an existing one invalidates expected.json and every number
taken with it, so do that only deliberately (and re-freeze from the baseline).

A workload is: an op of bench/m2/driver.bend, an input file (+ aux file), a batch (inputs per
timed window: IO.now has 1 ms resolution), a param (filter threshold), the modes it is scheduled
in, and the key metric the summary ratios and scales (compute_ms for the queries, parse_ms for
the parse workload, e2e_ms in e2e mode).

Paths are relative to the repository root and live under the gitignored bench/data/.
"""
from dataclasses import dataclass, field
from typing import Optional

S1K = "bench/data/sales_1000.csv"
S100K = "bench/data/sales_100000.csv"
S1M = "bench/data/sales_1000000.csv"
PRODUCTS = "bench/data/products.csv"
NUNIQUE = "bench/data/m2/nunique_1048576.csv"

THREADS = (1, 4, 12)


@dataclass(frozen=True)
class W:
    id: str
    group: str
    op: str
    file: str
    aux: str = "-"
    rows: int = 0               # rows of the primary input
    batch: int = 1
    param: int = 0
    modes: tuple = ("phases",)  # modes scheduled by default (e2ecsv only in `freeze`/--modes)
    smoke: bool = False
    desc: str = ""
    csv_ok: bool = False        # an e2ecsv run is meaningful (small, fixed-precision output)

    @property
    def key(self) -> str:
        return "parse_ms" if self.op == "parse" else ("stages" if self.op == "stages" else "compute_ms")


def _batch(n, q):
    """scripts/bench.sh batch rule: sub-ms cells run `batch` collects (each over its own freshly
    parsed inputs) in one timed window."""
    if n == 1000:
        return 500 if q in ("q1", "q2") else 40
    if n == 100000:
        return 8 if q == "q2" else 1
    return 1  # 1M rows: one input per process (G4 RSS must not include batch copies; q2 ~ 10 ms is far above 1 ms)


def _build():
    ws = []
    qdesc = {
        "q1": "filter ok & qty>50, select id,region,price",
        "q2": "with_columns revenue = qty*price*(1-fill_null(discount,0))",
        "q3": "q2, group_by region (sum revenue, mean price, count, max qty), sort region",
        "q4": "sort region asc, price desc, id asc; head 10",
        "q5": "inner join products, group_by category sum qty, sort",
        "q6": "describe of id, qty, price, discount",
    }
    # q1-q6 at 1M rows (the frozen gate workloads): phases and end-to-end
    for q in ("q1", "q2", "q3", "q4", "q5", "q6"):
        ws.append(W(f"{q}_1m", "q1m", q, S1M, PRODUCTS, 1_000_000, _batch(1_000_000, q), 0,
                    ("phases", "e2e"), False, qdesc[q] + " (1M rows)", csv_ok=True))
    # CSV parse of the 41 MB file (parse = read + a full walk of every buffer; the result frame is hashed)
    ws.append(W("parse_1m", "parse", "parse", S1M, "-", 1_000_000, 1, 0, ("phases", "e2e"), False,
                "CSV parse of bench/data/sales_1000000.csv (41 MB)"))
    # filter selectivities on a numeric predicate: qty > K, qty uniform on 1..100
    for sel, k in ((0, 100), (1, 99), (50, 50), (100, 0)):
        ws.append(W(f"filter_sel{sel}_1m", "filter", "filter", S1M, "-", 1_000_000, 1, k, ("phases",), False,
                    f"filter qty > {k}: about {sel}% of 1M rows kept (all 7 columns compacted)"))
    # per-stage breakdown of q1-q6 (eager stages over one parse)
    ws.append(W("stages_1m", "stages", "stages", S1M, PRODUCTS, 1_000_000, 1, 0, ("stages",), False,
                "each eager stage of q1..q6 timed alone, 1M rows"))
    # n_unique over 2^20 distinct U32
    ws.append(W("nunique_1m", "nunique", "nunique", NUNIQUE, "-", 1 << 20, 1, 0, ("phases",), False,
                "select n_unique(x) over 2^20 distinct shuffled U32"))
    # distinct string keys, fixed key-length distribution (bench/hc.py: 8..14 letters + base-36 id)
    for n, tag in ((100_000, "100k"), (300_000, "300k"), (1_000_000, "1m")):
        for op in ("group", "unique", "join"):
            ws.append(W(f"str_{op}_{tag}", "str", op, f"bench/data/hc/t_{n}.csv",
                        f"bench/data/hc/dim_{n}.csv" if op == "join" else "-", n, 1, 0,
                        ("phases",), n == 100_000,
                        {"group": "group_by k: sum v, len (k all distinct)",
                         "unique": "select k, unique(k) (k all distinct)",
                         "join": "inner join dim on k (90% match)"}[op] + f", {n:,} rows"))
    # long shared prefix keys: 39-char common prefix + 6 digits (fixed length 45)
    for n, tag in ((100_000, "100k"), (300_000, "300k")):
        for op in ("group", "unique", "join"):
            ws.append(W(f"lp_{op}_{tag}", "lp", op, f"bench/data/m2/lp_t_{n}.csv",
                        f"bench/data/m2/lp_dim_{n}.csv" if op == "join" else "-", n, 1, 0,
                        ("phases",), n == 100_000 and op == "join",  # lp group/unique at 100k take seconds
                        {"group": "group_by k", "unique": "select k, unique(k)", "join": "inner join dim on k"}[op]
                        + f" over 45-char keys sharing a 39-char prefix, {n:,} rows"))
    # q1-q6 at 100k rows (scaling/smoke)
    for q in ("q1", "q2", "q3", "q4", "q5", "q6"):
        ws.append(W(f"{q}_100k", "q100k", q, S100K, PRODUCTS, 100_000, _batch(100_000, q), 0,
                    ("phases",), q != "q2", qdesc[q] + " (100k rows)", csv_ok=True))  # q2 x8 batch: slow for a smoke
    # small-input controls at 1k rows (batched windows)
    for q in ("q1", "q2", "q3", "q4", "q5", "q6"):
        ws.append(W(f"ctl_{q}_1k", "ctl", q, S1K, PRODUCTS, 1_000, _batch(1000, q), 0,
                    ("phases",), True, qdesc[q] + " (1k rows control, batched)", csv_ok=True))
    ws.append(W("stages_100k", "stages", "stages", S100K, PRODUCTS, 100_000, 1, 0, ("stages",), True,
                "each eager stage of q1..q6 timed alone, 100k rows"))
    return ws


WORKLOADS = _build()
BY_ID = {w.id: w for w in WORKLOADS}
assert len(BY_ID) == len(WORKLOADS)

# the stages of the `stages` mode, in order (driver.bend Stg.name)
STAGES = ("filter_q1", "select_q1", "withcols_q2", "groupby_q3", "sort_q3", "sort_q4", "head_q4",
          "join_q5", "groupby_q5", "sort_q5", "describe_q6")


def select(patterns=None, groups=None, smoke=False):
    import fnmatch
    out = []
    for w in WORKLOADS:
        if smoke and not w.smoke:
            continue
        if groups and w.group not in groups:
            continue
        if patterns and not any(fnmatch.fnmatch(w.id, p) for p in patterns):
            continue
        out.append(w)
    return out
