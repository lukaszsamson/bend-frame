"""Input generation for the W0 workloads (bench/m2/workloads.py). Deterministic; idempotent (a file that
exists with the expected sha256 is kept). Needs numpy/polars (the bench uv project):

  uv run --project bench python bench/m2/gen.py            # everything below -> bench/data/ (gitignored)
  uv run --project bench python bench/m2/gen.py --check    # only verify the sha256 of every file

Files (the sha256 values are frozen in bench/m2/inputs.json and checked by run.py before each run):
  bench/data/sales_{1000,100000,1000000}.csv, products.csv   bench/gen.py (seed 42): the q1-q6 inputs
  bench/data/hc/{t,dim}_{100000,300000,1000000}.csv           bench/hc.py gen: distinct-string keys
  bench/data/m2/nunique_1048576.csv                           2^20 distinct shuffled U32 (column x)
  bench/data/m2/lp_{t,dim}_{100000,300000}.csv                45-char keys with a 39-char shared prefix

hc keys: 8..14 random lowercase letters + a base-36 row id, so the key length distribution is the same at
100k, 300k and 1M rows (length 12..18, base-36 ids have 4 digits from 46,656 rows on).
lp keys: "customer_segment_internal_account_code_" (39 chars) + a 6-digit decimal id (shuffled rows), every key
distinct, a dim table with 90% of them plus n/10 absent keys (like hc).
nunique: x = perm(2^20) * 4093 + 7 (distinct, < 2^32, shuffled), one header line `x`.
"""
import hashlib
import json
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
BENCH = HERE.parent
ROOT = BENCH.parent
DATA = BENCH / "data"
M2 = DATA / "m2"
INPUTS = HERE / "inputs.json"
sys.path.insert(0, str(BENCH))

LP_PREFIX = "customer_segment_internal_account_code_"


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def gen_sales():
    import gen as g  # bench/gen.py
    g.write(g.products(), g.DATA / "products.csv")
    for n in (1_000, 100_000, 1_000_000):
        g.write(g.sales(n), g.DATA / f"sales_{n}.csv")


def gen_hc():
    import hc  # bench/hc.py
    for n in (100_000, 300_000, 1_000_000):
        hc.gen(n)


def gen_nunique():
    import numpy as np
    M2.mkdir(parents=True, exist_ok=True)
    rng = np.random.default_rng(20261011)
    x = rng.permutation(1 << 20).astype(np.uint64) * 4093 + 7
    assert x.max() < (1 << 32) and len(set(x.tolist())) == (1 << 20)
    (M2 / "nunique_1048576.csv").write_text("x\n" + "\n".join(map(str, x.tolist())) + "\n")


def gen_lp(n: int):
    M2.mkdir(parents=True, exist_ok=True)
    rng = random.Random(f"lp:{n}")
    ids = list(range(n))
    rng.shuffle(ids)
    keys = [f"{LP_PREFIX}{i:06d}" for i in ids]
    with open(M2 / f"lp_t_{n}.csv", "w") as f:
        f.write("k,v,x\n")
        for i, k in enumerate(keys):
            f.write(f"{k},{i % 1000},{(i % 977) / 8:.2f}\n")
    dim = [k for i, k in enumerate(keys) if i % 10 != 3]
    dim += [f"{LP_PREFIX}9{j:05d}" for j in range(n // 10)]  # absent: ids start with 9 and exceed n - 1
    rng.shuffle(dim)
    with open(M2 / f"lp_dim_{n}.csv", "w") as f:
        f.write("k,w\n")
        for i, k in enumerate(dim):
            f.write(f"{k},{(i * 7) % 100003}\n")


FILES = (
    [f"bench/data/sales_{n}.csv" for n in (1000, 100000, 1000000)] + ["bench/data/products.csv"]
    + [f"bench/data/hc/{k}_{n}.csv" for n in (100000, 300000, 1000000) for k in ("t", "dim")]
    + ["bench/data/m2/nunique_1048576.csv"]
    + [f"bench/data/m2/lp_{k}_{n}.csv" for n in (100000, 300000) for k in ("t", "dim")]
)


def hashes():
    return {p: sha256(ROOT / p) for p in FILES if (ROOT / p).exists()}


def check() -> int:
    want = json.loads(INPUTS.read_text()) if INPUTS.exists() else {}
    bad = 0
    for p in FILES:
        f = ROOT / p
        if not f.exists():
            print(f"MISSING {p}")
            bad += 1
        elif p in want and sha256(f) != want[p]:
            print(f"HASH MISMATCH {p}")
            bad += 1
        elif p not in want:
            print(f"unfrozen {p}")
    return bad


def main():
    if "--check" in sys.argv:
        sys.exit(1 if check() else 0)
    missing = [p for p in FILES if not (ROOT / p).exists()]
    if any(p.startswith("bench/data/sales") or p.endswith("products.csv") for p in missing):
        gen_sales()
    if any("/hc/" in p for p in missing):
        gen_hc()
    if any("nunique" in p for p in missing):
        gen_nunique()
    for n in (100_000, 300_000):
        if any(f"lp_t_{n}" in p or f"lp_dim_{n}" in p for p in missing):
            gen_lp(n)
    h = hashes()
    if "--freeze" in sys.argv:
        INPUTS.write_text(json.dumps(h, indent=1, sort_keys=True) + "\n")
        print(f"froze {len(h)} input hashes -> {INPUTS}")
    sys.exit(1 if check() else 0)


if __name__ == "__main__":
    main()
