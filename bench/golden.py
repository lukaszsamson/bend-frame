"""Run q1..q6 on bench/fixtures/tiny.csv and write bench/golden/q<k>.csv (floats at 4 decimals)."""
from pathlib import Path

from queries import QUERIES, load

HERE = Path(__file__).parent
OUT = HERE / "golden"

if __name__ == "__main__":
    OUT.mkdir(exist_ok=True)
    sales, products = load(HERE / "fixtures/tiny.csv", HERE / "fixtures/products.csv")
    for name, q in QUERIES.items():
        q(sales, products).collect().write_csv(OUT / f"{name}.csv", float_precision=4)
        print(f"wrote golden/{name}.csv")
