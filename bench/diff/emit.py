"""Bend emission of generated cases (tests/diff/dNNNN.bend and run.py's batch programs).

A case is emitted as defs `<pfx>f_<src>()` (the input frames, built from literals), `<pfx>eager()`,
`<pfx>plan()` and a main step `DX.three("<tag>", eager, plan, env, env)` that prints the dumps of
the eager, raw-lazy and optimised-lazy runs under the headers `-- <tag> eager|raw|opt`. Only the
facade (DF.*) and the adapter tests/diff/lib/dx.bend (DX.*) are used.
"""
from __future__ import annotations

from model import *  # noqa: F401,F403
import model as M


def bs(s: str) -> str:
    """A Bend String expression for s (ASCII escapes inline, other code points via DX.ch)."""
    parts, cur = [], ""
    for ch in s:
        o = ord(ch)
        if ch == '"':
            cur += '\\"'
        elif ch == "\\":
            cur += "\\\\"
        elif ch == "\n":
            cur += "\\n"
        elif ch == "\t":
            cur += "\\t"
        elif 32 <= o < 127:
            cur += ch
        else:
            parts.append('"' + cur + '"')
            parts.append(f"DX.ch({o})")
            cur = ""
    parts.append('"' + cur + '"')
    parts = [p for p in parts if p != '""'] or ['""']
    return " ++ ".join(parts) if len(parts) > 1 else parts[0]


def f32_expr(x: float) -> str:
    if math.isnan(x):
        return "DX.nan()"
    if math.isinf(x):
        return "DX.inf()" if x > 0 else "DX.ninf()"
    if x == 0:
        return "DX.nzero()" if math.copysign(1.0, x) < 0 else "0.0"
    t = f32_text(abs(x))
    return t if x > 0 else f"F32.neg({t})"


def scalar(dt, v) -> str:
    """A D.Scalar expression (DX.u(..) etc.)."""
    if v is None:
        return "DX.n()"
    if dt == "bool":
        return f"DX.b({'True' if v else 'False'}{{}})"
    if dt == "u32":
        return f"DX.u({v})"
    if dt == "i32":
        return f"DX.i({v})" if v >= 0 else f"DX.ineg({-v})"
    if dt == "f32":
        return f"DX.f({f32_expr(v)})"
    return f"DX.s({bs(v)})"


def tdt(dt) -> str:
    return f"DX.t_{dt}()"


def fn(name: str) -> str:
    """DF.<name> when the facade has it, else the DX shim."""
    return f"DF.{name}" if name in facade_defs() else f"DX.{name}"


def expr(e: Ex) -> str:
    o = e.op
    if o == "col":
        return f"DF.col({bs(e.p[0])})"
    if o == "lit":
        dt, v = e.p
        if v is None:
            return f"{fn('lit_null')}({tdt(dt)})"
        if dt == "bool":
            return f"DF.lit_bool({'True' if v else 'False'}{{}})"
        if dt == "u32":
            return f"DF.lit_u32({v})"
        if dt == "i32":
            return f"DF.lit_i32({v})" if v >= 0 else f"DF.lit_i32_neg({-v})"
        if dt == "f32":
            return f"DF.lit_f32({f32_expr(v)})"
        return f"DF.lit_str({bs(v)})"
    a = [expr(x) for x in e.args]
    if o == "alias":
        return f"DF.alias({a[0]}, {bs(e.p[0])})"
    if o in ("cast", "try_cast"):
        return f"{fn(o)}({a[0]}, {tdt(e.p[0])})"
    if o == "is_in":
        return f"{fn(o)}({a[0]}, [{', '.join(scalar(e.p[0], v) for v in e.p[1])}])"
    if o == "clip":
        return f"{fn(o)}({a[0]}, {scalar(e.p[0], e.p[1])}, {scalar(e.p[0], e.p[2])})"
    if o in ("contains_literal", "starts_with", "ends_with"):
        return f"{fn(o)}({a[0]}, {bs(e.p[0])})"
    return f"{fn(o)}({', '.join(a)})"


def exprs(es) -> str:
    return "[" + ", ".join(expr(e) for e in es) + "]"


def names(ns) -> str:
    return "[" + ", ".join(bs(n) for n in ns) + "]"


def skeys(ks) -> str:
    return "[" + ", ".join(f"DF.sort_key({bs(n)}, {'True' if d else 'False'}{{}}, {'True' if nl else 'False'}{{}})" for n, d, nl in ks) + "]"


def pairs(ps) -> str:
    return "[" + ", ".join(f"({bs(a)}, {bs(b)})" for a, b in ps) + "]"


# per verb: how its parameters print (Pl.p layout in model.py)
VERB_PARAMS = {
    "select": lambda p: [exprs(p[0])],
    "with_columns": lambda p: [exprs(p[0])],
    "filter": lambda p: [expr(p[0])],
    "sort": lambda p: [skeys(p[0])],
    "group_by": lambda p: [exprs(p[0]), exprs(p[1])],
    "head": lambda p: [str(p[0])],
    "tail": lambda p: [str(p[0])],
    "slice": lambda p: [str(p[0]), str(p[1])],
    "inner_join": lambda p: [names(p[0]), names(p[1])],
    "left_join": lambda p: [names(p[0]), names(p[1])],
    "semi_join": lambda p: [names(p[0]), names(p[1])],
    "anti_join": lambda p: [names(p[0]), names(p[1])],
    "drop": lambda p: [names(p[0])],
    "rename": lambda p: [pairs(p[0])],
    "unique": lambda p: [names(p[0])],
    "concat_vertical": lambda p: [],
}

# Bend parameter declarations of DX's eager wrappers (same keys)
VERB_DECLS = {
    "select": [("es", "List<&2, X.Expr>")],
    "with_columns": [("es", "List<&2, X.Expr>")],
    "filter": [("pred", "X.Expr")],
    "sort": [("ks", "List<&2, O.SortKey>")],
    "group_by": [("keys", "List<&2, X.Expr>"), ("aggs", "List<&2, X.Expr>")],
    "head": [("n", "U32")],
    "tail": [("n", "U32")],
    "slice": [("off", "U32"), ("len", "U32")],
    "inner_join": [("lo", "List<&2, String>"), ("ro", "List<&2, String>")],
    "left_join": [("lo", "List<&2, String>"), ("ro", "List<&2, String>")],
    "semi_join": [("lo", "List<&2, String>"), ("ro", "List<&2, String>")],
    "anti_join": [("lo", "List<&2, String>"), ("ro", "List<&2, String>")],
    "drop": [("ns", "List<&2, String>")],
    "rename": [("ps", "List<&2, DF.RenamePair()>")],
    "unique": [("ns", "List<&2, String>")],
    "concat_vertical": [],
}


def frame_def(pfx: str, name: str, f: Frame) -> str:
    cols = []
    for c in f.cols:
        cols.append(f"DX.c{c.dtype}({bs(c.name)}, [" + ", ".join(scalar(c.dtype, v) for v in c.vals) + "])")
    return f"def {pfx}f_{name}() -> DF.ResT(DF.Frame()):\n  DX.frame([" + ", ".join(cols) + "])\n"


def eager_expr(pl: Pl, pfx: str) -> str:
    if pl.verb == "source":
        return f"{pfx}f_{pl.p[0]}()"
    kids = [eager_expr(k, pfx) for k in pl.kids]
    if pl.verb == "concat_vertical":
        return f"DX.e_concat_vertical([{', '.join(kids)}])"
    return f"DX.e_{pl.verb}({', '.join(kids + VERB_PARAMS[pl.verb](pl.p))})"


def lazy_expr(pl: Pl, pfx: str) -> str:
    if pl.verb == "source":
        return f"DX.src({bs(pl.p[0])}, {pfx}f_{pl.p[0]}())"
    kids = [lazy_expr(k, pfx) for k in pl.kids]
    lz = VERBS[pl.verb].lazy or f"lazy_{pl.verb}"
    if pl.verb == "concat_vertical":
        return f"DF.{lz}([{', '.join(kids)}])"
    return f"DF.{lz}({', '.join(kids + VERB_PARAMS[pl.verb](pl.p))})"


def env_expr(case: Case, pfx: str) -> str:
    used = []
    for s in plan_sources(case.plan):
        if s not in used:
            used.append(s)
    if len(used) == 1:
        return f"DX.env1({bs(used[0])}, {pfx}f_{used[0]}())"
    if len(used) == 2:
        return f"DX.env2({bs(used[0])}, {pfx}f_{used[0]}(), {bs(used[1])}, {pfx}f_{used[1]}())"
    raise ValueError("more than two sources")


def case_defs(case: Case, pfx: str = "") -> str:
    out = []
    used = sorted(set(plan_sources(case.plan)))
    for n in used:
        out.append(frame_def(pfx, n, case.inputs[n]))
    out.append(f"def {pfx}eager() -> DF.ResT(DF.Frame()):\n  {eager_expr(case.plan, pfx)}\n")
    out.append(f"def {pfx}plan() -> DF.Plan():\n  {lazy_expr(case.plan, pfx)}\n")
    return "\n".join(out)


def case_step(case: Case, pfx: str = "", indent: str = "    ") -> str:
    env = env_expr(case, pfx)
    return f'{indent}DX.four("{case.id}", {pfx}eager(), {pfx}plan(), {env}, {env}, {env})'


HEADER = """import Base
import ./../../frame.bend as DF
import ./lib/dx.bend as DX
"""


def program(cases, pfx_of=lambda i, c: f"c{i}_") -> str:
    """One Bend program running every case (a batch for run.py)."""
    parts = [HEADER]
    steps = []
    for i, c in enumerate(cases):
        pfx = pfx_of(i, c)
        parts.append(case_defs(c, pfx))
        steps.append(case_step(c, pfx))
    parts.append("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(steps) + "\n")
    return "\n".join(parts)
