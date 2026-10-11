"""The oracle's joins against a brute-force reference of the contract (finding d1588).

    cd bench && uv run python diff/tests/test_oracle_join.py     # also run by test_exit.py (make diff-driver-check)

Polars 2.0.0's EAGER `DataFrame.join` of an f32 key is wrong for NaN whenever a key Series carries the
SORTED_ASC flag (always true of a 1-row Series; also true of a column that came out of a sort or a join):
the sorted-merge path compares with IEEE `==`, so NaN never matches NaN. The lazy engine matches every NaN
with every NaN whatever the flag. The contract (DESIGN.md 15.5.2, "every NaN one key") is the lazy answer,
so `oracle.py` joins through `.lazy().collect()` (`oracle._pjoin`). This test pins that:

  1. the pinned shapes (the 1 x 1 NaN self join, the flagged 5-row column of case d1588) give the
     contract's row counts through the oracle's own join functions;
  2. a seeded fuzz of f32 keys (NaN of both signs and payloads, +-0.0, +-inf, null; plain, sorted and
     flag-forced columns, 0..8 rows) through inner / left / semi / anti equals a brute-force reference
     (NaN == NaN, -0.0 == 0.0, null never matches), row counts and the matched key positions;
  3. (informational, never a failure) whether Polars' eager path still disagrees with its lazy one: when
     this prints "eager path now agrees", the _pjoin note in oracle.py can be retired.
"""
from __future__ import annotations

import math
import random
import struct
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.append(str(HERE.parents[1]))

import polars as pl  # noqa: E402

import oracle  # noqa: E402

NAN = struct.unpack("<f", struct.pack("<I", 0x7FC00000))[0]
NEG_NAN = struct.unpack("<f", struct.pack("<I", 0xFFC00001))[0]
POOL = [NAN, NAN, 1.0, 2.0, 0.0, -0.0, math.inf, -math.inf, None, NEG_NAN]
FAILS: list = []


def key(v):
    if v is None:
        return None
    if math.isnan(v):
        return "nan"
    return 0.0 if v == 0 else v


def frame(vals, other, tag, mode):
    s = pl.Series("c", vals, dtype=pl.Float32)
    if mode in ("sort", "flag"):
        s = s.sort()
    if mode == "flag":
        s = s.set_sorted()
    return oracle.OF([pl.Series(tag, list(range(len(s))), dtype=pl.UInt32), s], len(s))


def run_join(how, lo, ro):
    schema = [("i", "u32"), ("c", "f32")] if how in ("semi", "anti") else [("i", "u32"), ("c", "f32"), ("j", "u32")]
    return oracle.JOINS[how + "_join"](lo, ro, (["c"], ["c"]), schema)


def expect(name, got, want):
    ok = got == want
    print(("ok   " if ok else "FAIL ") + name + ("" if ok else f": got {got} want {want}"))
    if not ok:
        FAILS.append(name)


def pinned():
    # 1 x 1 NaN self join: inner 1 (the eager Polars path says 0)
    one = oracle.OF([pl.Series("c", [NAN], dtype=pl.Float32)], 1)
    r = oracle.JOINS["inner_join"](one, one, (["c"], ["c"]), [("c", "f32")])
    expect("1x1 NaN inner", r.h, 1)
    # d1588: a column that came out of a join (flagged sorted), five NaN rows, against one NaN row
    t = pl.DataFrame({"s": [1, 2, 3, 4, 5], "k": [False] * 5})
    u = pl.DataFrame({"k": [False], "c": pl.Series([NAN], dtype=pl.Float32)})
    a = t.join(u, on="k", how="inner")
    assert a["c"].flags["SORTED_ASC"], "the premise (a join output is flagged) moved: update the note in oracle._pjoin"
    left = oracle.OF(a.get_columns(), a.height)
    right = oracle.OF(u.get_columns(), u.height)
    r = oracle.JOINS["inner_join"](left, right, (["c"], ["c"]), [("s", "i64"), ("k", "bool"), ("c", "f32"), ("k_right", "bool")])
    expect("d1588 5x1 flagged NaN inner", r.h, 5)
    # a sorted two-NaN column against itself: 2 x 2 = 4 matches for the NaNs plus the finite ones
    s = pl.Series("c", [2.0, NAN, 1.0, NAN], dtype=pl.Float32).sort()
    f = oracle.OF([s], 4)
    r = oracle.JOINS["inner_join"](f, f, (["c"], ["c"]), [("c", "f32")])
    expect("sorted [1,2,nan,nan] self inner", r.h, 6)


def fuzz(n=1500):
    rng = random.Random(1588)
    for it in range(n):
        nl, nr = rng.choice([0, 1, 1, 2, 3, 5, 8]), rng.choice([0, 1, 1, 2, 3, 5, 8])
        lv, rv = [rng.choice(POOL) for _ in range(nl)], [rng.choice(POOL) for _ in range(nr)]
        ml, mr = rng.choice(["plain", "sort", "flag"]), rng.choice(["plain", "sort", "flag"])
        l, r = frame(lv, None, "i", ml), frame(rv, None, "j", mr)
        lk, rk = l.cols[1].to_list(), r.cols[1].to_list()
        for how in ("inner", "left", "semi", "anti"):
            got = run_join(how, l, r)
            hit = [[j for j, b in enumerate(rk) if key(a) is not None and key(a) == key(b)] for a in lk]
            if how == "inner":
                want = sum(len(h) for h in hit)
            elif how == "left":
                want = sum(max(1, len(h)) for h in hit)
            elif how == "semi":
                want = sum(1 for h in hit if h)
            else:
                want = sum(1 for h in hit if not h)
            if got.h != want:
                FAILS.append((it, how, ml, mr, lk, rk, got.h, want))
                print("FAIL fuzz", FAILS[-1])
                return
            if how == "inner":
                pairs = sorted(zip(got.cols[0].to_list(), got.cols[2].to_list()))
                wantp = sorted((i, j) for i, h in enumerate(hit) for j in h)
                if pairs != wantp:
                    FAILS.append((it, how, ml, mr, "pairs"))
                    print("FAIL fuzz pairs", FAILS[-1])
                    return
    print(f"ok   fuzz: {n} frame pairs x inner/left/semi/anti against the brute-force contract")


def informational():
    one = pl.DataFrame({"c": pl.Series([NAN], dtype=pl.Float32)})
    eager = one.join(one, on="c", how="inner").height
    lazy = one.lazy().join(one.lazy(), on="c", how="inner").collect().height
    print(f"info: Polars {pl.__version__} 1x1 NaN inner join: eager {eager}, lazy {lazy}"
          + ("  (eager path now agrees)" if eager == lazy else "  (eager path still drops NaN matches)"))


def main():
    pinned()
    fuzz()
    informational()
    if FAILS:
        print(f"\ntest_oracle_join: {len(FAILS)} FAILED")
        return 1
    print("\ntest_oracle_join: ok")
    return 0


if __name__ == "__main__":
    sys.exit(main())
