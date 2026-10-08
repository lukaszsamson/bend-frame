"""Writes the hand-picked T2.3 regressions tests/diff/r0001..r0006.bend (python diff/reduce_regress.py).

Two are minimised defects found by `reduce.py --shrink` (fixed, NEW-T23-1/2; no xfail), four are pins of contract examples
that pass today (cancellation, non-finite data and the overflow guard, ten 0.1, describe std).
Expectations come from reduce_ref.py (the contract's step model, checked in the selftest against the
examples quoted in DESIGN.md 15.5.3/15.5.4), not from Bend's output.
"""
from __future__ import annotations

import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.append(str(HERE.parent))

import reduce_gen as G  # noqa: E402
import reduce_ref as R  # noqa: E402
import reduce_shrink as S  # noqa: E402

NAN, INF, NINF = float("nan"), float("inf"), float("-inf")


def case(xs, keys=None, valid=None):
    bits = [R.f2b(R.F(x)) for x in xs]
    n = len(bits)
    return {"id": "c00000", "cls": "regress", "n": n, "null_rate": 0.0, "bits": bits, "valid": valid or [True] * n,
            "keys": keys or [0] * n, "layout": "hand"}


REGS = [
    ("r0001", None, ("minmax", "desc", "max"), case([NAN, 1.0, 2.0]), ["desc"],
     "describe max of [NaN, 1, 2] must be 2 (and min 1): the min/max rule of 15.5.2 skips NaN; Polars 2.0.0 describe agrees.\n"
     "Fixed (NEW-T23-1): describe takes min/max from Eval.agg Min/Max (K.Kernel.fmin/fmax), not from the NaN-greatest sort."),
    ("r0002", None, ("minmax", "desc", "min"), case([0.0, -0.0]), ["desc"],
     "describe of [0.0, -0.0]: min must be -0.0 and max 0.0 (15.5.2: on a tie min answers -0.0, max 0.0, either input order; Polars the same).\n"
     "Fixed (NEW-T23-2): the extremes come from K.Kernel.fmin/fmax, not from the first / last of the stable sort."),
    ("r0003", None, ("pin", "sel+grp", "sum"),
     case([1e8, 1e16, 1.0, 0.5, -1e8, -1e16, 0.25, 7.0], keys=[0, 1, 0, 1, 0, 1, 0, 1], valid=[True] * 7 + [False]),
     ["sel_e", "sel_r", "sel_f", "grp_e", "grp_r", "grp_f"],
     "cancellation: group 0 = [1e8, 1, -1e8, 0.25] sums to 1.25 and group 1 = [1e16, 0.5, -1e16] to 0.5 (a naive f32 sum answers 0.25 / 0);\n"
     "the null row is skipped; eager, raw lazy and optimised lazy agree. The select sums all seven valid rows to 0.25, not the exact 1.75: c is itself\n"
     "an f32, and bound (1) (gamma^2 * sum|x| ~ 2.6e3 here) allows it; the step model, not the exact sum, is the contract."),
    ("r0004", None, ("pin", "sel+grp", "sum"),
     case([INF, 1.0, 1.0, INF, INF, NINF, NAN, 1.0, 3e38, 3e38, -3e38, -0.0, -0.0, 5.0, -0.0],
          keys=[0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 4, 5, 5, 6, 6]),
     ["sel_e", "sel_r", "sel_f", "grp_e", "grp_r", "grp_f"],
     "non-finite data per 15.5.3: [inf, 1] and [1, inf] -> inf, [inf, -inf] -> NaN, [NaN, 1] -> NaN; the guard makes an overflowing partial\n"
     "sum final ([3e38, 3e38, -3e38] -> inf although the exact sum is finite); sums of -0.0 are +0.0 (the accumulator starts at +0.0)."),
    ("r0005", None, ("pin", "sel+grp", "sum"),
     case([0.1] * 10, keys=[0] * 3 + [1] * 7),
     ["sel_e", "grp_e", "grp_f"],
     "ten 0.1: Neumaier gives 1.0 (0x3f800000; Polars' eager sum 0x3f800001); groups of 3 and 7 -> 0.3 and 0.7 correctly rounded."),
    ("r0006", None, ("pin", "desc", "std"),
     case([1.0, 99.0, 2.0, 4.0, 3.0], valid=[True, False, True, True, False]),
     ["desc"],
     "describe of [1, null, 2, 4, null]: mean 7/3, std by the two-pass step model (15.5.4). Note DESIGN.md 15.5.4 quotes the correctly rounded\n"
     "std 1.5275252 / var 2.3333333 as the correctly rounded values; the specified algorithm (squares rounded to f32) gives 1.5275253 (0x3fc385f3), one ulp above, inside bound (3)."),
]


def main():
    for name, xf, key, c, tags, note in REGS:
        text = S.test_text(c, key, "", xf, (), tags=tags, note=note)
        (S.TESTS / f"{name}.bend").write_text(text)
        print("wrote", S.TESTS / f"{name}.bend")


if __name__ == "__main__":
    main()
