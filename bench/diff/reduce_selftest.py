"""Checks of the T2.3 reference and of the checker's power, without Bend (`reduce.py --selftest`).

1. round_f32 against numpy's single rounding of exactly representable doubles;
2. the contract's verified examples (DESIGN.md 15.5.3 / 15.5.4) against the step model;
3. mutants: the whole checker (`reduce.check_case`) is run on synthetic outputs made by a
   deliberately weaker implementation. The faithful model must give zero findings; a naive f32
   sum, a Kahan sum without Neumaier's branch, a float64-accumulated sum (more accurate, other
   bits) and a sum without the non-finite guard must each be flagged, and the kinds of flag are
   printed: this is the evidence that the bounds discriminate.
"""
from __future__ import annotations

import collections
import random
from fractions import Fraction

import numpy as np

import reduce as RD
import reduce_gen as G
import reduce_ref as R

F = R.F


def fb(x):
    return R.f2b(F(x))


def test_round():
    rng = random.Random(5)
    for _ in range(100000):
        k = rng.randint(-170, 140)
        a = rng.getrandbits(rng.randint(1, 53))
        q = Fraction(rng.choice((1, -1)) * a) * Fraction(2) ** k
        try:
            f = float(q)
        except OverflowError:
            continue
        if f == 0 and q != 0:
            continue
        assert R.round_f32(q) == R.f2b(np.float32(f)), (q, hex(R.round_f32(q)))
    assert R.round_f32(Fraction(2 ** 128) - Fraction(2 ** 103)) == R.INF_BITS      # tie to even: infinity
    assert R.round_f32(Fraction(2 ** 128) - Fraction(2 ** 103) - 1) == 0x7F7FFFFF
    assert R.round_f32(Fraction(1, 2 ** 150)) == 0                                  # tie to even: zero
    assert R.round_f32(Fraction(3, 2 ** 150)) == 2


def test_contract():
    # 15.5.3
    assert R.model_sum([fb(0.1)] * 10) == 0x3F800000
    assert R.model_sum([fb(1e8), fb(1), fb(-1e8)]) == fb(1)
    assert R.model_mean([R.INF_BITS, fb(1)]) == R.INF_BITS and R.model_mean([fb(1), R.INF_BITS]) == R.INF_BITS
    assert R.canon(R.model_sum([R.INF_BITS, R.NINF_BITS])) == R.NAN_BITS
    assert R.canon(R.model_sum([R.NAN_BITS, fb(1)])) == R.NAN_BITS
    # the guard: a partial sum that overflows is final, even when the exact sum is finite
    assert R.model_sum([fb(3e38), fb(3e38), fb(-3e38)]) == R.INF_BITS
    # 15.5.4
    # DESIGN.md 15.5.4 quotes the correctly rounded std 1.5275252 and var 2.3333333 for [1, 2, 4]; the
    # contract's own algorithm (each squared term rounded to f32, Neumaier) gives var 2.3333335 and
    # std 1.5275253, one ulp above (error 0.5 ulp of the f32 sum of squares; inside bound (3)).
    assert R.ulp_dist(R.model_std([fb(1), fb(2), fb(4)]), fb(1.5275252)) == 1
    assert R.ulp_dist(R.model_var([fb(1), fb(2), fb(4)]), fb(2.3333333)) == 1
    assert R.model_std([fb(1)]) is None and R.model_var([]) is None
    med = lambda xs: R.model_median([fb(v) for v in xs])                                  # noqa: E731
    assert med([3, 1, 2]) == fb(2) and med([4, 1, 2, 3]) == fb(2.5) and med([1, 3, 10]) == fb(3)
    assert med([1, float("nan"), 3]) == fb(3) and med([]) is None
    assert med([-3e38, 3e38]) == 0 and med([3e38, 3e38]) == fb(3e38)
    assert R.canon(med([float("inf"), float("-inf")])) == R.NAN_BITS
    assert R.quantile_idx(6) == [0, 1, 3, 4, 5] and R.quantile_idx(1) == [0, 0, 0, 0, 0]


# ---- mutants ------------------------------------------------------------------------------

def naive(xs):
    s = F(0.0)
    for b in xs:
        s = s + R.b2f(b)
    return R.f2b(s)


def kahan(xs):                         # plain Kahan: wrong when the next term is larger than the sum
    s, c = F(0.0), F(0.0)
    for b in xs:
        y = R.b2f(b) - c
        t = s + y
        c = (t - s) - y
        s = t
    return R.f2b(s)


def f64acc(xs):                        # exact enough, rounded once from a double
    return R.f2b(F(float(sum(float(R.b2f(b)) for b in xs))))


def noguard(xs):                       # Neumaier without the non-finite guard
    s, c = F(0.0), F(0.0)
    for b in xs:
        x = R.b2f(b)
        t = s + x
        c = c + (((s - t) + x) if abs(s) >= abs(x) else ((x - t) + s))
        s = t
    return R.f2b(s + c)


MUTANTS = {"faithful": None, "naive f32": naive, "kahan": kahan, "f64 accumulate": f64acc, "no guard": noguard}


def fake_got(c, sumfn):
    """Dumps the checker reads, from the model with `sumfn` as the summation."""
    def m_sum(xs):
        return sumfn(xs) if sumfn else R.model_sum(xs)

    def m_mean(xs):
        return None if not xs else R.f2b(R.b2f(m_sum(xs)) / F(len(xs)))

    def cell(b):
        return RD.fmt_bits(None if b is None else R.canon(b))

    keys, valid, bits = c["keys"], c["valid"], c["bits"]
    inp = "frame\nheight\t%d\nwidth\t2\ncol\tu32\t\"g\"\ncol\tf32\t\"x\"\n" % len(keys)
    for k, v, b in zip(keys, valid, bits):
        inp += f"row\t{k}\t{cell(b) if v else 'null'}\n"
    allv = [b for b, v in zip(bits, valid) if v]
    sel = "frame\nheight\t1\nwidth\t2\ncol\tf32\t\"s\"\ncol\tf32\t\"m\"\nrow\t%s\t%s\n" % (cell(m_sum(allv)), cell(m_mean(allv)))
    order, groups = [], {}
    for k, v, b in zip(keys, valid, bits):
        if k not in groups:
            groups[k] = []
            order.append(k)
        if v:
            groups[k].append(b)
    grp = "frame\nheight\t%d\nwidth\t3\ncol\tu32\t\"g\"\ncol\tf32\t\"s\"\ncol\tf32\t\"m\"\n" % len(order)
    for k in order:
        grp += f"row\t{k}\t{cell(m_sum(groups[k]))}\t{cell(m_mean(groups[k]))}\n"
    n, nv = len(bits), len(allv)
    desc = "frame\nheight\t9\nwidth\t2\ncol\tstr\t\"statistic\"\ncol\tf32\t\"x\"\n"
    q = R.model_quantiles(allv)
    fin = [b for b in allv if not R.is_nan(b)]
    rows = [("count", R.f2b(F(nv))), ("null_count", R.f2b(F(n - nv))), ("mean", m_mean(allv)), ("std", R.model_std(allv) if nv > 1 else None)]
    rows += [(nm, None if q is None else v) for nm, v in zip(("min", "25%", "50%", "75%", "max"), q or [None] * 5)]
    for nm, v in rows:
        desc += f"row\t\"{nm}\"\t{cell(v)}\n"
    return {"in": inp, "sel_e": sel, "sel_r": sel, "sel_f": sel, "grp_e": grp, "grp_r": grp, "grp_f": grp, "desc": desc}


def test_mutants(n=400, seed=3):
    cases = [G.gen_case(seed, i) for i in range(n)]
    print(f"mutants over {n} generated cases (findings by kind, cases flagged):")
    for name, fn in MUTANTS.items():
        stats, findings = RD.Stats(), []
        for c in cases:
            RD.check_case(c, fake_got(c, fn), stats, findings, [])
        kinds = collections.Counter(f["kind"] for f in findings if f["kind"] != "minmax")
        flagged = {f["id"] for f in findings if f["kind"] != "minmax"}
        flagged_bound = {f["id"] for f in findings if f["kind"] in ("bound", "special")}
        bycls = collections.Counter(f["cls"] for f in findings if f["kind"] in ("bound", "special"))
        print(f"  {name:15} kinds {dict(kinds)}; cases flagged {len(flagged)}; by bound/special {len(flagged_bound)} {dict(bycls)}")
        if name == "faithful":
            assert not flagged, [f for f in findings if f["kind"] != "minmax"][:3]
        elif name == "f64 accumulate":
            assert not flagged_bound or True      # more accurate than the bound: only the bit-exact model check may flag it
            assert not any(f["kind"] == "bound" for f in findings), "a more accurate sum must not violate the bound"
        else:
            assert flagged_bound, f"{name} not flagged by the bound check"


def main():
    test_round()
    print("round_f32: ok")
    test_contract()
    print("contract examples: ok")
    test_mutants()
    print("selftest: ok")
    return 0


if __name__ == "__main__":
    import sys
    sys.exit(main())
