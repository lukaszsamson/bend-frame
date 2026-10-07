"""Deterministic data generator. Usage: uv run --project bench python bench/gen.py [n ...]"""
import sys
from pathlib import Path

import numpy as np
import polars as pl

HERE = Path(__file__).parent
DATA, FIXTURES = HERE / "data", HERE / "fixtures"
SEED = 42
REGIONS = ["north", "south", "east", "west", "central", "coastal", "inland", "island"]
PRODUCTS = [f"prod_{i:02d}" for i in range(64)]
CATEGORIES = ["tools", "toys", "food", "books", "garden", "sports"]


def products() -> pl.DataFrame:
    rng = np.random.default_rng(SEED)
    return pl.DataFrame({
        "product": PRODUCTS,
        "category": [CATEGORIES[i % 6] for i in range(64)],
        "weight": (rng.integers(10, 5000, 64) / 100).astype(np.float32),
    })


def sales(n: int) -> pl.DataFrame:
    rng = np.random.default_rng(SEED + n)
    discount = rng.integers(0, 31, n) / 100
    is_null = rng.random(n) < 0.1
    if n == 20:  # tiny fixture: guarantee some nulls so fill_null is exercised
        is_null[[3, 8, 16]] = True
    return pl.DataFrame({
        "id": np.arange(n, dtype=np.uint32),
        "region": np.array(REGIONS)[rng.integers(0, 8, n)],
        "product": np.array(PRODUCTS)[rng.integers(0, 64, n)],
        "qty": rng.integers(1, 101, n, dtype=np.uint32),
        "price": (rng.integers(50, 50001, n) / 100).astype(np.float32),
        "discount": pl.Series(discount, dtype=pl.Float32).set(pl.Series(is_null), None),
        "ok": rng.random(n) < 0.5,
    })


def write(df: pl.DataFrame, path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    df.write_csv(path, float_precision=2)
    print(f"wrote {path.relative_to(HERE)} ({df.height} rows)")


if __name__ == "__main__":
    sizes = [int(float(a)) for a in sys.argv[1:]] or [1_000, 100_000, 1_000_000]
    write(products(), DATA / "products.csv")
    write(products(), FIXTURES / "products.csv")
    write(sales(20), FIXTURES / "tiny.csv")
    for n in sizes:
        write(sales(n), DATA / f"sales_{n}.csv")
