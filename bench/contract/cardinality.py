"""Polars 2.0.0 observations behind DESIGN.md 15.4 (cardinality decision table, C1-C27).

    cd bench && uv run python contract/cardinality.py

Each case runs the same program eagerly (DataFrame) and lazily (LazyFrame.collect) and
prints `C<n> <program>: eager <shape> <values> | lazy <shape> <values>` (or the
exception class). The contract's "Polars 2.0.0 (observed)" column is this output; the
bend-frame columns of the table are the contract and differ only where 15.4 says so
(C19: Polars' lazy engine does not apply a 1-row scalar predicate; C25: `lit(2).len()`).

Input: t = {a: u32 [1, 2, 3]} (h = 3, w = 1) unless the case says otherwise; z is the
zero-column frame of height 6 (every column of a 6-row frame dropped).
"""
import sys

import polars as pl

assert pl.__version__ == "2.0.0", pl.__version__

A = pl.col("a")


def t(h=3):
    return pl.DataFrame({"a": list(range(1, h + 1))}, schema={"a": pl.UInt32})


def z(h=6):
    return pl.DataFrame({"a": list(range(h))}, schema={"a": pl.UInt32}).drop("a")


def fmt(df):
    vals = {c: df.get_column(c).to_list() for c in df.columns}
    return f"{df.shape} {vals}" if df.height <= 12 else f"{df.shape}"


def run(f, df):
    try:
        return fmt(f(df))
    except Exception as e:  # noqa: BLE001 - the error class is the observation
        return f"{type(e).__name__}: {str(e).splitlines()[0]}"


def case(name, program, f, df_fn=t):
    eager = run(f, df_fn())
    lazy = run(lambda df: f(df.lazy()).collect(), df_fn())
    print(f"{name} {program}: eager {eager} | lazy {lazy}")


def main():
    print(f"polars {pl.__version__}")
    case("C1", "select([])", lambda d: d.select([]))
    case("C2", "select([lit 1 as one]), h=3", lambda d: d.select(pl.lit(1, pl.UInt32).alias("one")))
    case("C3", "select([lit 1 as one]), h=0", lambda d: d.select(pl.lit(1, pl.UInt32).alias("one")), lambda: t(0))
    case("C4", "head(0).select([lit 1])", lambda d: d.head(0).select(pl.lit(1, pl.UInt32).alias("one")))
    case("C5", "select([lit 1]).head(0)", lambda d: d.select(pl.lit(1, pl.UInt32).alias("one")).head(0))
    case("C6", "select([sum(a)])", lambda d: d.select(A.sum()))
    for op in ["sum", "mean", "min", "max", "first", "last", "count", "n_unique"]:
        case("C7", f"select([{op}(a)]), h=0", lambda d, op=op: d.select(getattr(A, op)()), lambda: t(0))
    case("C7", "select([len()]), h=0", lambda d: d.select(pl.len()), lambda: t(0))
    case("C8", "select([lit 1 as x, sum(a)])", lambda d: d.select(pl.lit(1, pl.UInt32).alias("x"), A.sum()))
    case("C9", "select([a, lit 1 as x])", lambda d: d.select(A, pl.lit(1, pl.UInt32).alias("x")))
    case("C10", "select([a, sum(a) as s])", lambda d: d.select(A, A.sum().alias("s")))
    case("C10", "select([a, sum(a) as s]), h=0", lambda d: d.select(A, A.sum().alias("s")), lambda: t(0))
    case("C11", "select([a - mean(a)])", lambda d: d.select(A - A.mean()))
    case("C12", "select([sum(a) + lit 1])", lambda d: d.select(A.sum() + pl.lit(1, pl.UInt32)))
    case("C13", "with_columns([sum(a) as s])", lambda d: d.with_columns(A.sum().alias("s")))
    case("C13", "with_columns([sum(a) as s]), h=0", lambda d: d.with_columns(A.sum().alias("s")), lambda: t(0))
    case("C14", "with_columns([lit 1 as s]), h=0", lambda d: d.with_columns(pl.lit(1, pl.UInt32).alias("s")), lambda: t(0))
    case("C15", "with_columns([])", lambda d: d.with_columns([]))
    case("C16", "filter(a > mean(a))", lambda d: d.filter(A > A.mean()))
    case("C17", "filter(sum(a) > 5)", lambda d: d.filter(A.sum() > 5))
    case("C17", "filter(sum(a) > 6)", lambda d: d.filter(A.sum() > 6))
    case("C18", "filter(lit true)", lambda d: d.filter(pl.lit(True)))
    case("C18", "filter(lit false)", lambda d: d.filter(pl.lit(False)))
    case("C19", "select([lit 1 as one]).filter(lit false)", lambda d: d.select(pl.lit(1, pl.UInt32).alias("one")).filter(pl.lit(False)))
    case("C19", "select([lit 1 as one]).filter(one == 2)", lambda d: d.select(pl.lit(1, pl.UInt32).alias("one")).filter(pl.col("one") == 2))
    case("C20", "filter(lit null::bool)", lambda d: d.filter(pl.lit(None, pl.Boolean)))
    case("C21", "filter(a > 1), h=0", lambda d: d.filter(A > 1), lambda: t(0))
    case("C22", "z.with_columns([lit 1 as o])", lambda d: d.with_columns(pl.lit(1, pl.UInt32).alias("o")), z)
    case("C23", "z.select([len()])", lambda d: d.select(pl.len()), z)
    case("C23", "z.select([lit 1])", lambda d: d.select(pl.lit(1, pl.UInt32)), z)
    case("C24", "z.head(2)", lambda d: d.head(2), z)
    case("C24", "z.filter(lit true)", lambda d: d.filter(pl.lit(True)), z)
    case("C24", "z.unique()", lambda d: d.unique(maintain_order=True), z)
    case("C24", "concat([z, z])", lambda d: pl.concat([d, d]), z)
    case("C25", "select([lit 2 .len()])", lambda d: d.select(pl.lit(2).len()))
    case("C26", "group_by(a).agg(count) on h=0", lambda d: d.group_by("a", maintain_order=True).agg(pl.col("a").count().alias("n")), lambda: t(0))
    case("C27", "select([a, a])", lambda d: d.select(A, A))
    case("C27", "select([lit 1, lit 2])", lambda d: d.select(pl.lit(1), pl.lit(2)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
