"""T2.3 case generator and Bend emitter: F32 vectors, group layouts, one Bend program per batch.

A case is one frame `t(g: u32, x: f32)` (x with nulls) and a group layout (g). The Bend program
of a case prints, under `-- <id> <tag>` headers (DF.dump, DESIGN.md 15.1):

    in      the input frame (checks that the literals parsed to the intended bits)
    sel_e   eager  select([x.sum(), x.mean() (+ std/var/median when the facade has them)])
    sel_r   raw lazy, `DF.collect_raw`        sel_f  fully optimised, `DF.collect_full`
    grp_e / grp_r / grp_f   the same aggregations under group_by(g)
    desc    DF.describe over the x column alone (count, null_count, mean, std, min, quantiles, max)

Vectors of up to 10k rows go in as chunks of 100 literals concatenated with List.concat: one
10k-element list literal overflows the interpreter's stack.
"""
from __future__ import annotations

import math
import random

import numpy as np

import emit
import model as M
import reduce_ref as R

CHUNK = 100
CLASSES = ("uniform", "wide", "cancel", "equal", "tinyhuge", "special", "zeros", "ints", "subnormal", "ordered")
CLASS_W = (20, 14, 16, 7, 10, 14, 4, 6, 4, 5)
NULL_RATES = (0.0, 0.0, 0.0, 0.0, 0.05, 0.1, 0.5, 0.9, 1.0)


def b(x) -> int:
    return R.f2b(np.float32(x))


def pick_n(rng: random.Random, big: float) -> int:
    r = rng.random()
    if r < 0.03:
        return 0
    if r < 0.06:
        return 1
    if r < 0.10:
        return rng.choice((2, 3))
    if r < 0.60:
        return rng.randint(4, 64)
    if r < 0.60 + 0.30 * (1 - big):
        return rng.randint(65, 1000)
    if r < 0.97:
        return rng.randint(1000, 3000)
    return rng.choice((5000, 8000, 10000))


def rand_f32(rng, emin, emax):
    """A random normal f32 with exponent in [emin, emax] and a random sign."""
    e = rng.randint(emin, emax)
    m = 1 + rng.getrandbits(23) / 2 ** 23
    x = np.float32(math.ldexp(m, e))
    return -x if rng.random() < 0.5 else x


def gen_values(rng: random.Random, cls: str, n: int):
    """f32 values (np.float32) of class cls."""
    if cls == "uniform":
        scale = rng.choice((1.0, 1.0, 1e3, 1e-3, 100.0))
        lo = 0.0 if rng.random() < 0.3 else -scale
        return [np.float32(rng.uniform(lo, scale)) for _ in range(n)]
    if cls == "wide":
        emax = rng.choice((10, 40, 80, 126))
        return [rand_f32(rng, -emax - 20 if emax < 126 else -126, emax) for _ in range(n)]
    if cls == "ints":
        return [np.float32(rng.randint(-1000, 1000)) for _ in range(n)]
    if cls == "equal":
        v = rng.choice((0.1, 1.0, 3.0, 1e8, 1.1754944e-38, 3.4e38, 7.0e-3, 123456.79, 16777217.0, 0.3))
        v = np.float32(v)
        v = -v if rng.random() < 0.3 else v
        return [v] * n
    if cls == "subnormal":
        return [np.float32(rng.choice((-1, 1)) * rng.randint(1, 2 ** 23 - 1) * 2.0 ** -149) for _ in range(n)]
    if cls == "zeros":
        pool = [np.float32(0.0), np.float32(-0.0), np.float32(1.0), np.float32(-1.0), np.float32(1e-45)]
        w = rng.choice(((8, 8, 1, 1, 1), (1, 1, 0, 0, 0), (0, 5, 0, 0, 0)))
        return [rng.choices(pool, w)[0] for _ in range(n)]
    if cls == "ordered":
        xs = sorted(np.float32(rng.uniform(-100, 100)) for _ in range(n))
        return xs if rng.random() < 0.5 else xs[::-1]
    if cls == "tinyhuge":
        tiny = rng.choice((1e-10, 1e-3, 1e-20, 1.0))
        huge = np.float32(rng.choice((1e8, 1e12, 1e20, 3e30)))
        if n == 0:
            return []
        xs = [np.float32(tiny * rng.uniform(0.5, 1.5)) * (1 if rng.random() < 0.8 else -1) for _ in range(n)]
        pos = rng.choice((0, n - 1, rng.randrange(n)))
        xs[pos] = huge if rng.random() < 0.7 else -huge
        return xs
    if cls == "cancel":
        return gen_cancel(rng, n)
    if cls == "special":
        xs = [np.float32(rng.uniform(-10, 10)) for _ in range(n)]
        if n == 0:
            return xs
        kind = rng.choice(("pinf", "ninf", "both", "nan", "negzero", "allnegzero", "mixed", "nan+inf"))
        k = rng.choice((1, 1, 2, max(1, n // 4)))
        pool = {"pinf": [np.float32(np.inf)], "ninf": [np.float32(-np.inf)], "both": [np.float32(np.inf), np.float32(-np.inf)],
                "nan": [np.float32(np.nan)], "negzero": [np.float32(-0.0)], "allnegzero": [np.float32(-0.0)],
                "mixed": [np.float32(np.inf), np.float32(-np.inf), np.float32(np.nan), np.float32(-0.0)],
                "nan+inf": [np.float32(np.nan), np.float32(np.inf)]}[kind]
        if kind == "allnegzero":
            return [np.float32(-0.0)] * n
        if kind == "both":                       # at least one of each
            xs[rng.randrange(n)] = pool[0]
            xs[rng.randrange(n)] = pool[1]
            return xs
        for _ in range(k):
            xs[rng.randrange(n)] = rng.choice(pool)
        return xs
    raise ValueError(cls)


def gen_cancel(rng, n):
    """Cancelling sums: [big, small.., -big], alternating signs, near-cancelling pairs."""
    if n == 0:
        return []
    style = rng.choice(("classic", "alt", "pairs", "ladder", "nearpair"))
    big = np.float32(rng.choice((1e8, 1e8, 1e10, 1e16, 1e30, 16777216.0)))
    if style == "classic":                         # [big, small, small, ..., -big], maybe shuffled
        xs = [big] + [np.float32(rng.choice((1.0, 1.0, 0.5, 0.1))) for _ in range(max(n - 2, 0))] + [-big]
        xs = xs[:max(n, 2)]
        if rng.random() < 0.5:
            rng.shuffle(xs)
        return xs[:n] if n >= 2 else xs[:1]
    if style == "alt":
        return [np.float32((-1) ** i) * big * np.float32(1 + rng.random() * 1e-3) if rng.random() < 0.9 else np.float32(1.0) * (-1) ** i
                for i in range(n)]
    if style == "pairs":
        xs = []
        while len(xs) < n:
            v = rand_f32(rng, -8, 40)
            xs += [v, -v]
            xs += [np.float32(rng.uniform(-1, 1))] if rng.random() < 0.5 else []
        xs = xs[:n]
        rng.shuffle(xs)
        return xs
    if style == "ladder":                          # descending magnitudes, alternating sign
        return [np.float32((-1) ** i * 2.0 ** (-i % 60) * 1e3) for i in range(n)]
    xs = []                                        # nearpair: x and -(x + 1 ulp)
    while len(xs) < n:
        v = rand_f32(rng, -10, 30)
        u = np.nextafter(abs(v), np.float32(np.inf)) * np.sign(v)
        xs += [v, -u]
    xs = xs[:n]
    if rng.random() < 0.5:
        rng.shuffle(xs)
    return xs


def gen_groups(rng: random.Random, n: int):
    """The u32 key per row and a layout label (group sizes: 1, 2, 3, small, n)."""
    if n == 0:
        return [], "empty"
    choices = [("one", 1), ("two", 2), ("three", 3), ("seven", 7), ("many", min(64, n)), ("half", max(1, min(n // 2, 2000))),
               ("each", min(n, 2000))]
    name, G = rng.choice(choices)
    pat = rng.choice(("mod", "rand", "blocks", "skew"))
    if pat == "mod":
        keys = [i % G for i in range(n)]
    elif pat == "rand":
        keys = [rng.randrange(G) for _ in range(n)]
    elif pat == "blocks":
        keys = [i * G // n for i in range(n)]
    else:                                          # one big group, the rest singletons
        keys = [0 if rng.random() < 0.8 else rng.randrange(1, G + 1) for _ in range(n)]
    # keys scrambled in id space too, so first-appearance order is not key order
    perm = list(range(max(keys) + 1))
    rng.shuffle(perm)
    return [perm[k] for k in keys], f"{name}/{pat}"


def gen_case(seed: int, index: int, only=None):
    rng = random.Random(f"{seed}:{index}")
    cls = rng.choices(CLASSES, CLASS_W)[0] if not only else rng.choice(only)
    n = pick_n(rng, 0.0)
    if cls == "cancel" and n == 1:
        n = 2
    if cls in ("tinyhuge", "special") and n < 2:
        n = rng.randint(2, 40)
    xs = gen_values(rng, cls, n)
    n = len(xs)
    rate = rng.choice(NULL_RATES) if cls != "special" or rng.random() < 0.5 else 0.0
    valid = [rng.random() >= rate for _ in range(n)]
    keys, layout = gen_groups(rng, n)
    return {"id": f"c{index:05d}", "seed": seed, "index": index, "cls": cls, "n": n, "null_rate": rate,
            "bits": [b(x) for x in xs], "valid": valid, "keys": keys, "layout": layout}


# ---- Bend emission ------------------------------------------------------------------------

def x_literal(bits: int, valid: bool) -> str:
    if not valid:
        return "DX.n()"
    if R.is_nan(bits):
        return "DX.f(DX.nan())"
    if bits == R.INF_BITS:
        return "DX.f(DX.inf())"
    if bits == R.NINF_BITS:
        return "DX.f(DX.ninf())"
    if bits == 0:
        return "DX.f(0.0)"
    if bits == 0x80000000:
        return "DX.f(DX.nzero())"
    v = float(R.b2f(bits))
    t = M.f32_text(abs(v))
    return f"DX.f({t})" if v > 0 else f"DX.f(F32.neg({t}))"


def chunked(pfx: str, name: str, items) -> tuple[str, str]:
    """(defs, expr): a list of Scalar literals as chunk defs + List.concat (or [] when empty)."""
    if not items:
        return "", "[]"
    defs, refs = [], []
    for k in range(0, len(items), CHUNK):
        nm = f"{pfx}{name}{k // CHUNK}"
        defs.append(f"def {nm}() -> List<&2, D.Scalar>:\n  [" + ", ".join(items[k:k + CHUNK]) + "]\n")
        refs.append(f"{nm}()")
    if len(refs) == 1:
        return "\n".join(defs), refs[0]
    return "\n".join(defs), "List.concat(&2, D.Scalar, [" + ", ".join(refs) + "])"


def aggs_expr(extra) -> str:
    col = 'DF.col("x")'
    items = [f'DF.alias(DF.sum({col}), "s")', f'DF.alias(DF.mean({col}), "m")']
    for nm in extra:
        items.append(f'DF.alias(DF.{nm}({col}), "{nm}")')
    return "[" + ", ".join(items) + "]"


def available_aggs():
    """std / var / median reductions the facade defines (empty until the AggOps land)."""
    fac = M.facade_defs()
    return [n for n in ("std", "var", "median") if n in fac]


def case_program(c, extra=()) -> tuple[str, str]:
    """(defs, step lines) of one case."""
    pfx = f"{c['id']}_"
    gs = [f"DX.u({k})" for k in c["keys"]]
    xs = [x_literal(bt, v) for bt, v in zip(c["bits"], c["valid"])]
    d1, ge = chunked(pfx, "g", gs)
    d2, xe = chunked(pfx, "x", xs)
    defs = d1 + "\n" + d2 + f"\ndef {pfx}f() -> DF.ResT(DF.Frame()):\n  DX.frame([DX.cu32(\"g\", {ge}), DX.cf32(\"x\", {xe})])\n"
    t = c["id"]
    f = f"{pfx}f()"
    aggs = aggs_expr(extra)
    sel_p = f'DF.lazy_select(DX.src("t", {f}), {aggs})'
    grp_p = f'DF.lazy_group_by(DX.src("t", {f}), [DF.col("g")], {aggs})'
    env = f'DX.env1("t", {f})'
    steps = [
        f'    IO.print(DX.show("{t}", "in", {f}))',
        f'    IO.print(DX.show("{t}", "sel_e", DX.e_select({f}, {aggs})))',
        f'    LZ.raw("{t}", "sel_r", {sel_p}, {env})',
        f'    LZ.full("{t}", "sel_f", {sel_p}, {env})',
        f'    IO.print(DX.show("{t}", "grp_e", DX.e_group_by({f}, [DF.col("g")], {aggs})))',
        f'    LZ.raw("{t}", "grp_r", {grp_p}, {env})',
        f'    LZ.full("{t}", "grp_f", {grp_p}, {env})',
        f'    IO.print(DX.show("{t}", "desc", DF.describe(DX.e_select({f}, [DF.col("x")]))))',
    ]
    return defs, "\n".join(steps)


LZ_DEFS = """
def lz_raw(+tag: String, +how: String, +p: P.Plan, e: P.Env) -> IO(Unit):
  do IO<Unit>:
    r : E.ResT(C.Frame) <- DF.collect_raw(p, e)
    IO.print(DX.show(tag, how, r))

def lz_full(+tag: String, +how: String, +p: P.Plan, e: P.Env) -> IO(Unit):
  do IO<Unit>:
    r : E.ResT(C.Frame) <- DF.collect_full(p, e)
    IO.print(DX.show(tag, how, r))
"""


def program(cases, header: str, extra=()) -> str:
    """One Bend program running every case. `header` = imports of frame.bend, dx.bend (paths)."""
    parts = [header, LZ_DEFS.replace("LZ.", "")]
    steps = []
    for c in cases:
        d, s = case_program(c, extra)
        parts.append(d)
        steps.append(s.replace("LZ.raw", "lz_raw").replace("LZ.full", "lz_full"))
    parts.append("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(steps) + "\n")
    return "\n".join(parts)


def header_for(scratch) -> str:
    import os
    rel = os.path.relpath(M.ROOT, scratch)
    return (f"import Base\nimport {rel}/frame.bend as DF\nimport {rel}/tests/diff/lib/dx.bend as DX\n"
            f"import {rel}/src/dtype.bend as D\nimport {rel}/src/err.bend as E\nimport {rel}/src/column.bend as C\n"
            f"import {rel}/src/plan.bend as P\n")
