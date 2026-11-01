"""Polars twins of bench/tpch/queries.bend, and a checker for the Bend driver's outputs.

  uv run --project bench python bench/tpch/run_polars.py time  <dir> [repeats]     # best-of collect ms per query
  uv run --project bench python bench/tpch/run_polars.py check <dir> <bend_outdir> # compare bench/tpch/run.bend's CSVs

Set POLARS_MAX_THREADS=1 (before the run) for a one-thread comparison. Floats are compared with a
relative tolerance (Bend's f32 sums are compensated, Polars' are pairwise), everything else exactly.
"""
import json
import sys
import time
from pathlib import Path

import polars as pl

F32 = pl.Float32


def load(d: Path) -> dict[str, pl.DataFrame]:
    return {n: pl.read_csv(d / f"{n}.csv", schema_overrides=None).with_columns(pl.col(pl.Float64).cast(F32))
            for n in ["lineitem", "orders", "customer", "supplier", "nation", "region"]}


def c(n: str) -> pl.Expr:
    return pl.col(n)


def disc_price() -> pl.Expr:
    return c("l_extendedprice") * (1.0 - c("l_discount"))


def rng(n: str, lo: int, hi: int) -> pl.Expr:
    return (c(n) >= lo) & (c(n) < hi)


def q1(t):
    return (t["lineitem"].lazy().filter(c("l_shipdate") <= 19980902)
            .with_columns(disc_price().alias("disc_price"))
            .group_by("l_returnflag", "l_linestatus", maintain_order=True)
            .agg(c("l_quantity").sum().alias("sum_qty"), c("l_extendedprice").sum().alias("sum_base_price"),
                 c("disc_price").sum().alias("sum_disc_price"),
                 (c("disc_price") * (1.0 + c("l_tax"))).sum().alias("sum_charge"),
                 c("l_quantity").mean().cast(F32).alias("avg_qty"), c("l_extendedprice").mean().alias("avg_price"),
                 c("l_discount").mean().alias("avg_disc"), pl.len().alias("count_order"))
            .sort("l_returnflag", "l_linestatus"))


def q3(t):
    return (t["customer"].lazy().filter(c("c_mktsegment") == "BUILDING")
            .join(t["orders"].lazy().filter(c("o_orderdate") < 19950315), left_on="c_custkey", right_on="o_custkey")
            .join(t["lineitem"].lazy().filter(c("l_shipdate") > 19950315), left_on="o_orderkey", right_on="l_orderkey")
            .group_by("o_orderkey", "o_orderdate", "o_shippriority", maintain_order=True)
            .agg(disc_price().sum().alias("revenue"))
            .sort(["revenue", "o_orderdate"], descending=[True, False], maintain_order=True).head(10))


def q4(t):
    return (t["orders"].lazy().filter(rng("o_orderdate", 19930701, 19931001))
            .join(t["lineitem"].lazy().filter(c("l_commitdate") < c("l_receiptdate")),
                  left_on="o_orderkey", right_on="l_orderkey", how="semi")
            .group_by("o_orderpriority", maintain_order=True).agg(pl.len().alias("order_count"))
            .sort("o_orderpriority"))


def q5(t):
    return (t["region"].lazy().filter(c("r_name") == "ASIA")
            .join(t["nation"].lazy(), left_on="r_regionkey", right_on="n_regionkey")
            .join(t["customer"].lazy(), left_on="n_nationkey", right_on="c_nationkey")
            .join(t["orders"].lazy().filter(rng("o_orderdate", 19940101, 19950101)), left_on="c_custkey", right_on="o_custkey")
            .join(t["lineitem"].lazy(), left_on="o_orderkey", right_on="l_orderkey")
            .join(t["supplier"].lazy(), left_on=["l_suppkey", "n_nationkey"], right_on=["s_suppkey", "s_nationkey"])
            .group_by("n_name", maintain_order=True).agg(disc_price().sum().alias("revenue"))
            .sort("revenue", descending=True))


def q6(t):
    return (t["lineitem"].lazy()
            .filter(rng("l_shipdate", 19940101, 19950101) & c("l_discount").is_between(0.05, 0.07) & (c("l_quantity") < 24))
            .select((c("l_extendedprice") * c("l_discount")).sum().alias("revenue")))


def q10(t):
    return (t["customer"].lazy()
            .join(t["orders"].lazy().filter(rng("o_orderdate", 19931001, 19940101)), left_on="c_custkey", right_on="o_custkey")
            .join(t["lineitem"].lazy().filter(c("l_returnflag") == "R"), left_on="o_orderkey", right_on="l_orderkey")
            .join(t["nation"].lazy(), left_on="c_nationkey", right_on="n_nationkey")
            .group_by("c_custkey", "c_name", "c_acctbal", "n_name", maintain_order=True)
            .agg(disc_price().sum().alias("revenue"))
            .sort(["revenue", "c_custkey"], descending=[True, False]).head(20))


def q12(t):
    urgent = c("o_orderpriority").is_in(["1-URGENT", "2-HIGH"])
    return (t["orders"].lazy()
            .join(t["lineitem"].lazy().filter(c("l_shipmode").is_in(["MAIL", "SHIP"]) & (c("l_commitdate") < c("l_receiptdate"))
                                              & (c("l_shipdate") < c("l_commitdate")) & rng("l_receiptdate", 19940101, 19950101)),
                  left_on="o_orderkey", right_on="l_orderkey")
            .group_by("l_shipmode", maintain_order=True)
            .agg(pl.when(urgent).then(1).otherwise(0).cast(pl.UInt32).sum().alias("high_line_count"),
                 pl.when(urgent).then(0).otherwise(1).cast(pl.UInt32).sum().alias("low_line_count"))
            .sort("l_shipmode"))


def q13(t):
    return (t["customer"].lazy().join(t["orders"].lazy(), left_on="c_custkey", right_on="o_custkey", how="left")
            .group_by("c_custkey", maintain_order=True).agg(c("o_orderkey").count().cast(pl.UInt32).alias("c_count"))
            .group_by("c_count", maintain_order=True).agg(pl.len().alias("custdist"))
            .sort(["custdist", "c_count"], descending=[True, True]))


def q18(t):
    return (t["lineitem"].lazy().group_by("l_orderkey", maintain_order=True).agg(c("l_quantity").sum().alias("sum_qty"))
            .filter(c("sum_qty") > 250)
            .join(t["orders"].lazy(), left_on="l_orderkey", right_on="o_orderkey")
            .join(t["customer"].lazy(), left_on="o_custkey", right_on="c_custkey")
            .select("c_name", "o_custkey", "l_orderkey", "o_orderdate", "o_totalprice", "sum_qty")
            .sort(["o_totalprice", "o_orderdate", "l_orderkey"], descending=[True, False, False]).head(100))


QUERIES = {"q1": q1, "q3": q3, "q4": q4, "q5": q5, "q6": q6, "q10": q10, "q12": q12, "q13": q13, "q18": q18}


def time_all(d: Path, reps: int) -> None:
    t = load(d)
    for name, q in QUERIES.items():
        best = min(_timed(lambda: q(t).collect()) for _ in range(reps))
        print(json.dumps({"query": name, "ms": round(best, 2), "engine": "polars"}))


def _timed(f) -> float:
    t0 = time.perf_counter()
    f()
    return (time.perf_counter() - t0) * 1000


def fbad(x: pl.Series, y: pl.Series) -> pl.Series:
    """per row: do two float columns differ? null vs non-null differs; NaN equals NaN; an infinity
    equals only the same-signed infinity; NaN or an infinity never equals a finite value; finite
    pairs use a relative tolerance of 1e-4 (absolute below 1.0)"""
    x, y = x.cast(pl.Float64), y.cast(pl.Float64)
    xn, yn = x.is_null(), y.is_null()
    xnan, ynan = x.is_nan().fill_null(False), y.is_nan().fill_null(False)
    xinf, yinf = x.is_infinite().fill_null(False), y.is_infinite().fill_null(False)
    finite = ~(xn | yn | xnan | ynan | xinf | yinf)
    close = ((x - y).abs() <= 1e-4 * y.abs().clip(lower_bound=1.0)).fill_null(False)
    special_same = (xnan & ynan) | (xinf & yinf & (x == y).fill_null(False))
    return (
        pl.when(xn | yn).then(xn != yn)
        .when(finite).then(~close)
        .otherwise(~special_same)
    ).alias("bad")


def same(a: pl.DataFrame, b: pl.DataFrame) -> str | None:
    if a.columns != b.columns:
        return f"columns {a.columns} != {b.columns}"
    if a.height != b.height:
        return f"height {a.height} != {b.height}"
    for col in a.columns:
        x, y = a[col], b[col]
        if x.dtype.is_float() or y.dtype.is_float():
            bad = pl.select(fbad(x, y)).to_series()
        else:
            bad = (x.cast(pl.String) != y.cast(pl.String)).fill_null(x.is_null() != y.is_null())
        if bad.any():
            i = bad.arg_max()
            return f"{col} row {i}: bend {x[i]} polars {y[i]}"
    return None


def selftest() -> int:
    """the comparator's own cases (v0.3 review: Astra's four plus nulls and tolerance)"""
    inf, nan = float("inf"), float("nan")
    cases = [  # (bend, polars, expected equal)
        (0.0, inf, False), (-inf, inf, False), (inf, inf, True), (-inf, -inf, True), (nan, nan, True),
        (nan, 1.0, False), (1.0, nan, False), (inf, nan, False), (None, None, True), (None, 1.0, False),
        (1.0, None, False), (None, nan, False), (1.0, 1.00001, True), (1.0, 1.01, False),
        (1e6, 1e6 + 50, True), (1e6, 1e6 + 500, False), (0.0, -0.0, True), (0.0, 0.00005, True),
    ]
    fails = 0
    for got, want, eq in cases:
        r = same(pl.DataFrame({"x": [got]}, schema={"x": pl.Float64}), pl.DataFrame({"x": [want]}, schema={"x": pl.Float64}))
        if (r is None) != eq:
            print(f"selftest FAIL: bend {got!r} polars {want!r}: expected {'equal' if eq else 'different'}, got {r!r}")
            fails += 1
    r = same(pl.DataFrame({"s": ["a", None]}), pl.DataFrame({"s": ["a", "b"]}))
    if r is None:
        print("selftest FAIL: string null vs value compared equal")
        fails += 1
    print(f"selftest: {len(cases) + 1 - fails} / {len(cases) + 1} ok")
    return fails


def check(d: Path, out: Path) -> int:
    t, fails = load(d), 0
    for name, q in QUERIES.items():
        f = out / f"{name}.csv"
        if not f.exists():
            print(f"{name}: MISSING {f}")
            fails += 1
            continue
        want = q(t).collect()
        got = pl.read_csv(f, schema=want.schema) if want.height else pl.read_csv(f)
        why = same(got, want)
        print(f"{name}: {'ok' if why is None else 'DIFF ' + why} ({want.height} rows)")
        fails += why is not None
    return fails


if __name__ == "__main__":
    if sys.argv[1] == "selftest":
        sys.exit(selftest())
    mode, d = sys.argv[1], Path(sys.argv[2])
    if mode == "time":
        time_all(d, int(sys.argv[3]) if len(sys.argv) > 3 else 5)
    else:
        sys.exit(check(d, Path(sys.argv[3])))
