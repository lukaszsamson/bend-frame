"""Seeded generator of typed differential cases (plans/M_01.txt T3).

    python gen.py --seed 1 --n 20 --out /tmp/cases     write dNNNN.bend files (+ cases.json)
    python gen.py --lib                                 regenerate tests/diff/lib/dx.bend
    python gen.py --seed 1 --n 3 --show                 print the cases as text

Every case is a pair (input frames, plan) over the facade surface; the three runs of
emit.py (eager, raw-lazy, optimised-lazy) and the oracle (oracle.py) take it from there.
Case (seed, index) is a pure function of the two numbers: random.Random(f"{seed}:{index}").

The grammar is table driven (model.EXPRS, model.VERBS; `needs` names the facade defs a row
requires, detected in frame.bend, so a verb that lands switches itself on; --all forces every
row on, for exercising the oracle ahead of the facade). About 12 % of the cases are
"invalid": type errors, unknown columns, bad keys, duplicate names; the oracle gives their
expected error text from the contract's typing rules.
"""
from __future__ import annotations

import argparse
import json
import math
import random
import sys
from pathlib import Path

import emit
import model as M
from model import Case, Col, Ex, Frame, Pl, col, lit, alias

HERE = Path(__file__).resolve().parent
ROOT = M.ROOT

NAMES = ["a", "b", "c", "d", "k", "x", "y", "s", "v", "m"]
ALIASES = ["r", "o1", "o2", "z", "w", "a", "x", "k", "n"]
ROWS = [0, 0, 0, 1, 1, 1, 2, 2, 3, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64]

STR_POOL = ["", "a", "b", "ab", "abc", "A", " ", "x y", "a\tb", 'q"t', "café", "α", "zz", "B", "ba"]
STR_NUM = ["0", "1", "2", "-3", "7", "1.5", "-2.25", "10", "abc", "", "nan", "inf", "100"]
U32_POOL = [0, 1, 2, 3, 5, 7, 10, 100, 255, 65535, 16777217, 2**31 - 1, 2**31, 2**32 - 1, 4294967294]
I32_POOL = [0, 1, -1, 2, -2, 5, -7, 100, -100, 65536, M.I32_MAX, M.I32_MIN, M.I32_MIN + 1, 2**24 + 1]
F32_NICE = [0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 0.25, 7.0, 10.0, 100.0, 0.1, 0.2, 0.3, 1e8, 16777216.0, 4294967296.0,
            2147483648.0, 4294967040.0, 2147483520.0, 1e-3, 123456.0]
F32_SPECIAL = [float("nan"), float("inf"), float("-inf"), -0.0, 0.0]
F32_CAST = [0.5, -0.5, 1.9, -1.9, 2.5, 4294967296.0, -2147483648.0, 2147483648.0, 4294967040.0, 2147483520.0, 1.0, 0.0, -1.0]


class Gen:
    def __init__(self, seed, index, all_=False, features=None):
        self.rng = random.Random(f"{seed}:{index}")
        self.seed = seed
        self.index = index
        self.all = all_
        self.features = features or set()
        self.err = 0.0           # per-node probability of an injected error (invalid cases)
        self.ops = [n for n in M.EXPRS if M.op_available(n, all_)]
        self.verbs = [n for n in M.VERBS if M.verb_available(n, all_)]
        self.fresh = 0

    # ---- scalars ------------------------------------------------------------------------
    def r(self):
        return self.rng.random()

    def pick(self, xs):
        return self.rng.choice(xs)

    def value(self, dt, style="wide"):
        r = self.rng
        if dt == "bool":
            return r.random() < 0.5
        if dt == "u32":
            return self.pick(U32_POOL) if r.random() < 0.6 else r.randrange(0, 200)
        if dt == "i32":
            return self.pick(I32_POOL) if r.random() < 0.5 else r.randrange(-100, 100)
        if dt == "f32":
            x = r.random()
            if x < 0.2:
                return self.pick(F32_SPECIAL)
            if x < 0.55:
                return M.f32(self.pick(F32_NICE) * self.pick([1, 1, -1]))
            if x < 0.8:
                return M.f32(r.randrange(-40, 41) / 8)
            return M.f32(self.pick(F32_CAST))
        if style == "num":
            return self.pick(STR_NUM)
        return self.pick(STR_POOL)

    def small_domain(self, dt, style):
        k = self.rng.randint(1, 4)
        return [self.value(dt, style) for _ in range(k)]

    # ---- frames -------------------------------------------------------------------------
    def column(self, name, dt, n):
        r = self.rng
        null_rate = r.choices([0.0, 0.1, 0.5, 1.0], [45, 25, 20, 10])[0]
        style = "num" if (dt == "str" and r.random() < 0.35) else "wide"
        dom = self.small_domain(dt, style) if r.random() < 0.5 else None
        vals = []
        for _ in range(n):
            if r.random() < null_rate:
                vals.append(None)
            else:
                vals.append(self.pick(dom) if dom else self.value(dt, style))
        return Col(name, dt, vals)

    def nrows(self):
        x = self.r()
        if "deep" in self.features and x < 0.15:
            return self.pick([100, 127, 128, 129, 255, 256, 257, 300])
        return self.pick(ROWS) if x < 0.8 else self.rng.randint(0, 64)

    def frame(self, schema, n=None):
        n = self.nrows() if n is None else n
        return Frame([self.column(nm, dt, n) for nm, dt in schema], n)

    def schema(self):
        k = self.rng.choices([1, 2, 3, 4, 5], [10, 25, 30, 20, 15])[0]
        names = self.rng.sample(NAMES, k)
        dts = [self.pick(M.DTYPES) for _ in range(k)]
        if k >= 3 and self.r() < 0.6:   # make an arithmetic-friendly frame
            dts[0] = self.pick(["u32", "i32", "f32"])
            dts[1] = dts[0] if self.r() < 0.6 else dts[1]
        return list(zip(names, dts))

    # ---- expressions ----------------------------------------------------------------------
    def lit_of(self, dt):
        if self.r() < 0.12:
            return lit(dt, None)
        v = self.value(dt)
        return lit(dt, v)

    def col_of(self, dt, schema):
        cs = [n for n, t in schema if t == dt]
        if cs:
            return col(self.pick(cs))
        return None

    def other_dtype(self, dt):
        return self.pick([d for d in M.DTYPES if d != dt])

    def terminal(self, dt, schema):
        r = self.rng
        c = self.col_of(dt, schema)
        if c is not None and r.random() < 0.85:
            return c
        if c is None and schema and r.random() < 0.6:
            srcs = [n for n, t in schema if M.cast_ok(t, dt)]
            if srcs:
                return Ex("cast", (col(self.pick(srcs)),), (dt,))
        return self.lit_of(dt)

    def expr(self, dt, schema, depth, red_ok=True, in_agg=False):
        r = self.rng
        if self.err and r.random() < self.err * 0.4:
            if r.random() < 0.3:
                return col("nope" if r.random() < 0.5 else self.pick(NAMES))
            dt = self.other_dtype(dt)
        # terminal?
        if depth <= 0 or r.random() < 0.18:
            return self.terminal(dt, schema)
        cands = []
        for n in self.ops:
            spec = M.EXPRS[n]
            if spec.red and (not red_ok or in_agg):
                continue
            if spec.sigs(dt):
                w = 3
                if spec.red:
                    w = 1.2 if "noreductions" not in self.features else 0.0
                if n == "cast" or n == "try_cast":
                    w = 2
                cands.append((n, w))
        if not cands:
            c = self.col_of(dt, schema)
            return c if c is not None else self.lit_of(dt)
        n = r.choices([c[0] for c in cands], [c[1] for c in cands])[0]
        return self.build(n, dt, schema, depth, red_ok, in_agg)

    def build(self, n, dt, schema, depth, red_ok, in_agg):
        spec = M.EXPRS[n]
        r0 = self.rng
        sigs = spec.sigs(dt)
        have = {t for _, t in schema}
        sig = r0.choices(sigs, [1 + 3 * sum(1 for t in s_ if t in have) for s_ in sigs])[0]
        in_agg2 = in_agg or spec.red
        args = tuple(self.expr(t, schema, depth - 1, red_ok, in_agg2) for t in sig)
        r = self.rng
        p = ()
        if n in ("cast", "try_cast"):
            p = (dt,)
        elif n == "is_in":
            at = sig[0]
            p = (at, tuple(self.value(at) for _ in range(r.randint(0, 4))))
            if at == "f32":
                p = (at, tuple(self.pick(F32_SPECIAL + [1.0, 0.5]) if r.random() < 0.6 else self.value(at) for _ in p[1]))
        elif n == "clip":
            at = sig[0]
            p = (at, self.value(at), self.value(at))
        elif n in ("contains_literal", "starts_with", "ends_with"):
            p = (self.pick(["", "a", "b", "ab", " ", "a\tb"]),)
        return Ex(n, args, p)

    def casty(self, dt, schema, depth):
        """An expression of dtype dt that goes through a cast (to exercise 15.5.5)."""
        src = self.pick([d for d in M.DTYPES if M.cast_ok(d, dt)])
        return Ex(self.pick(["cast", "cast", "try_cast"] if "try_cast" in self.ops else ["cast"]),
                  (self.expr(src, schema, depth),), (dt,))

    # ---- plans ------------------------------------------------------------------------------
    def alias_name(self, taken):
        pool = [a for a in ALIASES if a not in taken]
        if self.r() < 0.07 or not pool:
            return self.pick(ALIASES)       # a repeated name on purpose
        return self.pick(pool)

    def named(self, e, taken):
        """Give e a name that is not yet taken (aliasing when needed), except by `err` chance."""
        nm = M.name_of(e)
        if nm in taken:
            if self.r() < 0.05:
                return e
            e = alias(e, self.alias_name(taken))
        elif e.op != "col" and self.r() < 0.6:
            e = alias(e, self.alias_name(taken))
        taken.add(M.name_of(e))
        return e

    def gen_select(self, schema):
        r = self.rng
        k = r.choices([1, 2, 3, 4], [30, 35, 25, 10])[0]
        taken, es = set(), []
        for _ in range(k):
            t = self.pick([t for _, t in schema]) if schema and r.random() < 0.8 else self.pick(M.DTYPES)
            x = r.random()
            if x < 0.3 and schema:
                e = col(self.pick([n for n, _ in schema]))
            elif x < 0.45:
                e = self.casty(t, schema, 2)
            else:
                e = self.expr(t, schema, r.choice([1, 2, 2, 3]))
            es.append(self.named(e, taken))
        if r.random() < 0.03:
            es = []
        return (tuple(es),)

    def gen_with(self, schema):
        r = self.rng
        k = r.choices([1, 2, 3], [55, 30, 15])[0]
        taken, es = set(), []
        for _ in range(k):
            t = self.pick([t for _, t in schema]) if schema else "u32"
            e = self.casty(t, schema, 2) if r.random() < 0.15 else self.expr(t, schema, r.choice([1, 2, 2, 3]))
            if r.random() < 0.3 and schema:
                e = alias(e, self.pick([n for n, _ in schema]))     # replaces an existing column
                taken.add(M.name_of(e))
            else:
                e = self.named(e, taken | {n for n, _ in schema}) if r.random() < 0.8 else self.named(e, taken)
            es.append(e)
        if r.random() < 0.02:
            es = []
        return (tuple(es),)

    def gen_filter(self, schema):
        return (self.expr("bool", schema, self.pick([1, 2, 2, 3])),)

    def gen_sort(self, schema):
        r = self.rng
        k = r.choices([1, 2, 3], [55, 30, 15])[0]
        ns = [n for n, _ in schema]
        keys = []
        for _ in range(k):
            n = self.pick(ns) if ns else "a"
            if self.err and r.random() < self.err:
                n = "nope"
            keys.append((n, r.random() < 0.4, r.random() < 0.4))
        return (tuple(keys),)

    def gen_group(self, schema):
        r = self.rng
        ns = [n for n, _ in schema]
        nk = r.choices([1, 2], [75, 25])[0]
        keys = []
        for _ in range(nk):
            keys.append(col(self.pick(ns)) if ns and r.random() < 0.85 else self.expr(self.pick(M.DTYPES), schema, 1, red_ok=False))
        taken = {M.name_of(k) for k in keys}
        aggs = []
        reds = [n for n in self.ops if M.EXPRS[n].red]
        for _ in range(r.choices([1, 2, 3, 4], [30, 35, 25, 10])[0]):
            op = self.pick(reds)
            spec = M.EXPRS[op]
            if op == "len":
                e = Ex("len")
            else:
                # an input dtype that the op accepts
                ok = [t for t in M.DTYPES if self.try_type(Ex(op, (lit(t, None),), ()))]
                t = self.pick(ok)
                if self.err and r.random() < self.err:
                    t = self.pick(M.DTYPES)
                inner = self.expr(t, schema, r.choice([0, 1, 1, 2]), red_ok=False, in_agg=True)
                e = Ex(op, (inner,), ())
            e = alias(e, self.alias_name(taken)) if r.random() < 0.85 else e
            taken.add(M.name_of(e))
            aggs.append(e)
        if self.err and r.random() < self.err:
            if r.random() < 0.5:
                keys = []
            else:
                aggs.append(self.expr(self.pick(M.DTYPES), schema, 1, red_ok=False))
        return (tuple(keys), tuple(aggs))

    @staticmethod
    def try_type(e):
        try:
            M.analyse(e, [])
            return True
        except M.TErr:
            return False

    def gen_head(self, schema):
        return (self.pick([0, 1, 2, 3, 5, 10, 100]),)

    def gen_slice(self, schema):
        return (self.pick([0, 0, 1, 2, 3, 10, 100]), self.pick([0, 1, 2, 3, 10, 100]))

    def gen_names(self, schema):
        ns = [n for n, _ in schema]
        k = self.rng.randint(0, min(2, len(ns)))
        out = self.rng.sample(ns, k) if ns else []
        if self.err and self.r() < self.err:
            out.append("nope")
        return (tuple(out),)

    def gen_rename(self, schema):
        ns = [n for n, _ in schema]
        k = self.rng.randint(0, min(2, len(ns)))
        pairs = []
        for a in self.rng.sample(ns, k) if ns else []:
            pairs.append((a, self.pick(ALIASES + ns)))
        if self.err and self.r() < self.err:
            # a missing `from`, or a `from` named twice
            pairs.append(("nope", "x") if not pairs or self.r() < 0.5 else (pairs[0][0], "y"))
        return (tuple(pairs),)

    def gen_join_keys(self, ls, rs):
        r = self.rng
        pairs = [(a, b) for a, ta in ls for b, tb in rs if ta == tb]
        if not pairs or (self.err and r.random() < self.err):
            lo = (self.pick([n for n, _ in ls] or ["a"]),)
            ro = (self.pick([n for n, _ in rs] or ["a"]),)
            if r.random() < 0.3:
                lo, ro = (), ()
            return lo, ro
        eq = [p for p in pairs if p[0] == p[1]]
        k = r.choices([1, 2], [80, 20])[0]
        chosen = []
        for _ in range(k):
            p = self.pick(eq) if eq and r.random() < 0.7 else self.pick(pairs)
            if all(p[0] != q[0] and p[1] != q[1] for q in chosen):   # Polars refuses repeated key names
                chosen.append(p)
        return tuple(a for a, _ in chosen), tuple(b for _, b in chosen)

    def verb_params(self, verb, schema):
        return {
            "select": self.gen_select, "with_columns": self.gen_with, "filter": self.gen_filter,
            "sort": self.gen_sort, "group_by": self.gen_group, "head": self.gen_head,
            "tail": self.gen_head, "slice": self.gen_slice, "drop": self.gen_names,
            "unique": self.gen_names, "rename": self.gen_rename,
        }[verb](schema)

    def plan(self, sources: dict, depth: int, allow_join=True) -> Pl:
        """A plan over the named sources (name -> schema), at most `depth` verbs on top of a source."""
        r = self.rng
        names = list(sources)
        src = names[0] if len(names) == 1 else ("t" if r.random() < 0.8 else self.pick(names))
        pl = Pl("source", (src,))
        cur = list(sources[src])
        for _ in range(depth):
            usable = [v for v in self.verbs if M.VERBS[v].nin == 1 or (allow_join and M.VERBS[v].nin == 2 and "u" in sources)
                      or (allow_join and M.VERBS[v].nin == -1)]
            if not usable:
                break
            v = r.choices(usable, [M.VERBS[x].weight for x in usable])[0]
            spec = M.VERBS[v]
            if spec.nin == 1:
                p = self.verb_params(v, cur)
                npl = Pl(v, p, (pl,))
            elif spec.nin == 2:
                rname = "u" if (r.random() < 0.85 or "noselfjoin" in self.features) else "t"   # "t" twice: a self join (B04-b)
                right = self.plan({rname: sources[rname]}, self.pick([0, 0, 1]), allow_join=False)
                try:
                    rs = M.plan_schema(right, sources)
                except M.TErr:
                    right = Pl("source", (rname,))
                    rs = list(sources[rname])
                lo, ro = self.gen_join_keys(cur, rs)
                npl = Pl(v, (lo, ro), (pl, right))
            else:
                # concat_vertical: the current plan and one or two more inputs, each the same plan
                # again (its sources read several times) or a short plan over a source (often
                # another schema: an error, kept only in invalid cases)
                kids = [pl]
                for _ in range(r.choice([1, 1, 2])):
                    if r.random() < 0.6:
                        kids.append(pl)
                    else:
                        rname = "u" if "u" in sources and r.random() < 0.7 else names[0]
                        kids.append(self.plan({rname: sources[rname]}, self.pick([0, 0, 1]), allow_join=False))
                npl = Pl(v, (), tuple(kids))
            try:
                cur = M.plan_schema(npl, sources)
            except M.TErr:
                if self.err:
                    return npl
                continue          # a valid case never keeps an erroring verb
            pl = npl
        return pl


def gen_case(seed: int, index: int, all_=False, features=None) -> Case:
    g = Gen(seed, index, all_, features)
    r = g.rng
    kind = "invalid" if r.random() < 0.12 else "valid"
    g.err = 0.25 if kind == "invalid" else 0.0
    ts = g.schema()
    inputs = {"t": g.frame(ts)}
    # u: shares t's schema (concat, same-name keys) or only some columns
    x = r.random()
    if x < 0.25:
        us = list(ts)
    elif x < 0.8:
        us = [c for c in ts if r.random() < 0.6] or [ts[0]]
        extra = [(n, t) for n, t in g.schema() if n not in {a for a, _ in us}]
        us = us + extra[: r.randint(0, 2)]
        r.shuffle(us)
    else:
        us = g.schema()
    inputs["u"] = g.frame(us)
    depth = r.choices([1, 2, 3, 4], [30, 30, 25, 15])[0]
    if "deep" in g.features:
        depth = r.choices([2, 3, 4, 5, 6], [15, 25, 25, 20, 15])[0]
    sources = {k: v.schema for k, v in inputs.items()}
    pl = g.plan(sources, depth)
    # keep only the sources the plan reads
    used = set(M.plan_sources(pl))
    inputs = {k: v for k, v in inputs.items() if k in used}
    c = Case(f"d{index:04d}", seed, inputs, pl, kind)
    return c


# ---- text view -----------------------------------------------------------------------------

def plan_text(pl: Pl, ind=0) -> str:
    pad = "  " * ind
    if pl.verb == "source":
        return f"{pad}source {pl.p[0]}"
    ps = []
    for x in pl.p:
        if isinstance(x, tuple) and x and isinstance(x[0], Ex):
            ps.append("[" + ", ".join(M.show(e) for e in x) + "]")
        elif isinstance(x, Ex):
            ps.append(M.show(x))
        else:
            ps.append(str(x))
    head = f"{pad}{pl.verb}({'; '.join(ps)})"
    return head + "".join("\n" + plan_text(k, ind + 1) for k in pl.kids)


def frame_text(f: Frame) -> str:
    lines = [f"  height {f.height}: " + ", ".join(f"{c.name}:{c.dtype}" for c in f.cols)]
    for i in range(min(f.height, 6)):
        lines.append("    " + " | ".join("null" if c.vals[i] is None else M.show_scalar(c.dtype, c.vals[i]) for c in f.cols))
    return "\n".join(lines)


def case_text(c: Case) -> str:
    out = [f"{c.id} ({c.kind})"]
    for k, f in c.inputs.items():
        out.append(f" {k}:\n{frame_text(f)}")
    out.append(plan_text(c.plan))
    return "\n".join(out)


# ---- tests/diff/lib/dx.bend ------------------------------------------------------------------

DX_STATIC = open(HERE / "dx_static.bend").read() if (HERE / "dx_static.bend").exists() else ""


def lib_text(all_=False) -> str:
    from dxlib import build
    return build(all_)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--n", type=int, default=10)
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--out")
    ap.add_argument("--lib", action="store_true")
    ap.add_argument("--show", action="store_true")
    ap.add_argument("--all", action="store_true", help="use every table row whether or not the facade has it")
    a = ap.parse_args(argv)
    if a.lib:
        (ROOT / "tests/diff/lib/dx.bend").write_text(lib_text(a.all))
        print("wrote tests/diff/lib/dx.bend")
        return 0
    cases = [gen_case(a.seed, i, a.all) for i in range(a.start, a.start + a.n)]
    if a.show:
        for c in cases:
            print(case_text(c))
            print(" static:", M.case_static(c))
            print()
    if a.out:
        out = Path(a.out)
        out.mkdir(parents=True, exist_ok=True)
        for c in cases:
            (out / f"{c.id}.bend").write_text(emit.HEADER.replace("./../../frame.bend", "./../../frame.bend") +
                                             "\n" + emit.case_defs(c) + "\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + emit.case_step(c) + "\n")
        (out / "cases.json").write_text(json.dumps([c.to_json() for c in cases]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
