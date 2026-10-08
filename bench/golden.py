"""Run q1..q6 and write <out>/q<k>.csv (floats at 4 decimals).

Default (no options): bench/fixtures/tiny.csv -> bench/golden/q1..q6.csv, as before.
Other sizes: python golden.py --input data/sales_1000.csv --out golden/n1000
(--products defaults to products.csv next to the input; paths are relative to bench/).

q1, q2, q4, q5, q6 are Polars 2.0.0's answers. q3 is NOT: its f32 group sum and mean are the
reference of DESIGN.md 15.5.3 / plan T2.3, computed by `q3_reference` from the exact f32
inputs (the revenue column as Polars computes it in f32, the price column): the exact
(rational) sum of each group's values rounded to f32 once (round half to even), and
mean = that f32 sum / f32(count) in f32. bend-frame's Neumaier sum lands on the correctly
rounded value for these groups; Polars' f32 accumulation (lazy: sequential in row order) can
be an ulp away (tiny.csv `inland`: Polars 96373.4141, exact sum 96373.40442, f32 96373.4062).
"""
import argparse
from fractions import Fraction
from pathlib import Path

import numpy as np
import polars as pl

from queries import QUERIES, load, q2

HERE = Path(__file__).parent


def rel(p: str) -> Path:
    q = Path(p)
    return q if q.is_absolute() else HERE / q


def f32_round(x: Fraction) -> np.float32:
    """x rounded to the nearest f32, ties to even (finite x; one rounding, no f64 step)."""
    c = np.float32(float(x))  # within an ulp of the answer: check it and its neighbours
    cands = {c, np.nextafter(c, np.float32(np.inf)), np.nextafter(c, np.float32(-np.inf))}
    def key(v):
        even = int(np.array([v], dtype=np.float32).view(np.uint32)[0]) & 1
        return (abs(Fraction(float(v)) - x), even)
    return min(cands, key=key)


def q3_reference(sales: pl.LazyFrame, products: pl.LazyFrame) -> pl.DataFrame:
    """q3 with the 15.5.3 reference reductions (see the module docstring); same schema and order
    as queries.q3: region, revenue_sum f32, price_mean f32, count u32, qty_max u32, by region."""
    df = q2(sales, products).collect()
    rows = []
    for (region,), g in df.group_by("region", maintain_order=True):
        rev = [Fraction(v) for v in g.get_column("revenue").to_list() if v is not None]
        price = [Fraction(v) for v in g.get_column("price").to_list() if v is not None]
        s = f32_round(sum(rev, Fraction(0)))
        m = None if not price else float(np.float32(f32_round(sum(price, Fraction(0))) / np.float32(len(price))))
        rows.append({"region": region, "revenue_sum": float(s), "price_mean": m,
                     "count": g.height, "qty_max": g.get_column("qty").max()})
    schema = {"region": pl.String, "revenue_sum": pl.Float32, "price_mean": pl.Float32,
              "count": pl.UInt32, "qty_max": pl.UInt32}
    return pl.DataFrame(rows, schema=schema).sort("region")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--input", default="fixtures/tiny.csv", help="sales CSV")
    ap.add_argument("--products", help="products CSV (default: products.csv beside --input)")
    ap.add_argument("--out", default="golden", help="output directory")
    a = ap.parse_args()
    src = rel(a.input)
    out = rel(a.out)
    out.mkdir(parents=True, exist_ok=True)
    sales, products = load(src, rel(a.products) if a.products else src.parent / "products.csv")
    for name, q in QUERIES.items():
        res = q3_reference(sales, products) if name == "q3" else q(sales, products).collect()
        res.write_csv(out / f"{name}.csv", float_precision=4)
        print(f"wrote {out.relative_to(HERE) if out.is_relative_to(HERE) else out}/{name}.csv")
