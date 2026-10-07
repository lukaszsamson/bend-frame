"""Canonical query set. Each qK(sales, products) takes LazyFrames and returns a LazyFrame."""
from pathlib import Path

import polars as pl

SALES_SCHEMA = {"id": pl.UInt32, "region": pl.String, "product": pl.String, "qty": pl.UInt32,
                "price": pl.Float32, "discount": pl.Float32, "ok": pl.Boolean}
PRODUCTS_SCHEMA = {"product": pl.String, "category": pl.String, "weight": pl.Float32}
F32 = pl.Float32


def load(sales_csv: Path, products_csv: Path) -> tuple[pl.LazyFrame, pl.LazyFrame]:
    """Eagerly parse the CSVs (parsing is not timed) and return LazyFrames."""
    return (pl.read_csv(sales_csv, schema=SALES_SCHEMA).lazy(),
            pl.read_csv(products_csv, schema=PRODUCTS_SCHEMA).lazy())


def revenue():
    return pl.col("qty").cast(F32) * pl.col("price") * (1 - pl.col("discount").fill_null(0.0))


def q1(sales, products):  # filter + project (file order preserved)
    return sales.filter(pl.col("ok") & (pl.col("qty") > 50)).select("id", "region", "price")


def q2(sales, products):  # with_columns
    return sales.with_columns(revenue().alias("revenue"))


def q3(sales, products):  # group_by + aggregations
    return (q2(sales, products).group_by("region")
            .agg(pl.col("revenue").sum().alias("revenue_sum"),
                 pl.col("price").mean().alias("price_mean"),
                 pl.len().alias("count"),
                 pl.col("qty").max().alias("qty_max"))
            .sort("region"))


def q4(sales, products):  # sort (id breaks ties so output is deterministic)
    return sales.sort(["region", "price", "id"], descending=[False, True, False]).head(10)


def q5(sales, products):  # inner join + group_by
    return (sales.join(products, on="product", how="inner")
            .group_by("category").agg(pl.col("qty").sum().alias("qty_sum"))
            .sort("category"))


def q6(sales, products):  # describe() over numeric columns
    return sales.select("id", "qty", "price", "discount").collect().describe().lazy()


QUERIES = {"q1": q1, "q2": q2, "q3": q3, "q4": q4, "q5": q5, "q6": q6}
