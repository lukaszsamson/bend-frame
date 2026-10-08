"""Compare Bend's rendered result with a Polars golden CSV (floats were printed with 4 decimals).

usage: python check.py <bend.csv> <golden.csv> [--rtol 1e-5]
Strings/ints must match exactly; floats may differ by `rtol` (relative) because Bend sums f32 with
Kahan compensation and Polars with its own f32 summation order. Exit 0 = match (maybe approximately),
1 = mismatch. Prints "identical", or "ok (k float cells differ, max rel diff X)".
"""
import argparse
import sys


def cells(path):
    with open(path) as f:
        return [line.rstrip("\n").split(",") for line in f]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("bend")
    ap.add_argument("golden")
    ap.add_argument("--rtol", type=float, default=1e-5)
    a = ap.parse_args()
    x, y = cells(a.bend), cells(a.golden)
    if len(x) != len(y):
        print(f"MISMATCH: {len(x)} lines vs {len(y)}")
        return 1
    diffs, worst = 0, 0.0
    for i, (r1, r2) in enumerate(zip(x, y)):
        if len(r1) != len(r2):
            print(f"MISMATCH: line {i + 1}: {len(r1)} fields vs {len(r2)}")
            return 1
        for c1, c2 in zip(r1, r2):
            if c1 == c2:
                continue
            try:
                v1, v2 = float(c1), float(c2)
            except ValueError:
                print(f"MISMATCH: line {i + 1}: {c1!r} vs {c2!r}")
                return 1
            rel = abs(v1 - v2) / max(abs(v1), abs(v2), 1e-30)
            if rel > a.rtol:
                print(f"MISMATCH: line {i + 1}: {c1} vs {c2} (rel {rel:.2e})")
                return 1
            diffs, worst = diffs + 1, max(worst, rel)
    print("identical" if not diffs else f"ok ({diffs} float cells differ, max rel diff {worst:.1e})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
