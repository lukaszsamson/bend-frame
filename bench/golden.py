"""Run q1..q6 and write <out>/q<k>.csv (floats at 4 decimals).

Default (no options): bench/fixtures/tiny.csv -> bench/golden/q1..q6.csv, as before.
Other sizes: python golden.py --input data/sales_1000.csv --out golden/n1000
(--products defaults to products.csv next to the input; paths are relative to bench/).
"""
import argparse
from pathlib import Path

from queries import QUERIES, load

HERE = Path(__file__).parent


def rel(p: str) -> Path:
    q = Path(p)
    return q if q.is_absolute() else HERE / q


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
        q(sales, products).collect().write_csv(out / f"{name}.csv", float_precision=4)
        print(f"wrote {out.relative_to(HERE) if out.is_relative_to(HERE) else out}/{name}.csv")
