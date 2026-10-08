"""Failure classification: map a (minimised) failing case to a DESIGN.md 15.10 defect ID, or NEW.

A rule is (ID, text, predicate(ctx)); the first rule that matches names the failure. Rules look at
the case (which operators it uses, its verbs), the actual dumps and the oracle's expected dump.
They are applied to MINIMISED cases, where the cause is usually one operator, so simple
predicates are precise; every group in the report is also reviewed by hand. A failure no rule
claims is NEW (the valuable output): its label is the coarse signature of the mismatch, which is
what the shrinker preserves.
"""
from __future__ import annotations

import math
import re

import sys
from pathlib import Path as _P

sys.path.append(str(_P(__file__).resolve().parents[1]))
import check  # noqa: E402
import model as M

CMP = {"eq", "ne", "lt", "le", "gt", "ge"}


def parse(text):
    try:
        return check.parse_dump(text)
    except Exception:  # noqa: BLE001
        return ("bad", text)


def diffkind(d: str) -> str:
    if d.startswith("frame dump vs error dump") or d.startswith("error dump vs frame dump"):
        return "frame-vs-error"
    if d.startswith("error text"):
        return "errtext"
    if d.startswith("height"):
        return "height"
    if d.startswith("width"):
        return "width"
    if d.startswith("columns"):
        return "cols"
    if d.startswith("rows:"):
        return "rows"
    if d.startswith("malformed"):
        return "malformed"
    m = re.match(r"row \d+, column .* \((\w+)\)", d)
    if m:
        return "cell:" + m.group(1)
    return "other"


class Ctx:
    def __init__(self, case, rec, got, exp):
        self.case, self.rec, self.got, self.exp = case, rec, got, exp
        self.ops = set()
        self.verbs = set()
        for n in M.plan_nodes(case.plan):
            self.verbs.add(n.verb)
            for x in n.p:
                items = x if isinstance(x, tuple) else (x,)
                for e in items:
                    if isinstance(e, M.Ex):
                        self.ops |= M.expr_ops(e)
        self.exp_eager = exp[1]["eager"] if exp and exp[0] == "ok" else None
        self.exp_lazy = exp[1]["lazy"] if exp and exp[0] == "ok" else None
        self.nan_data = any(c.dtype == "f32" and any(v is not None and (math.isnan(v) or math.isinf(v) or v == 0) for v in c.vals)
                            for f in case.inputs.values() for c in f.cols)

    def actual(self, how):
        return self.got[how] if self.got else ""

    def any_actual(self, pat):
        return any(re.search(pat, self.actual(h)) for h in ("eager", "raw", "opt", "full"))

    def kinds(self):
        return {k: diffkind(v[0]) for k, v in self.rec["diffs"].items() if v}

    def expected_error(self):
        e = self.exp_eager or ""
        return e[len("error\t"):].rstrip("\n") if e.startswith("error\t") else None

    def actual_is_frame(self, how="eager"):
        return self.actual(how).startswith("frame\n")


def r_b04a(c: Ctx):
    return c.any_actual(r"aggregation in (select|with_columns|filter) \(v1")


def r_b04b(c: Ctx):
    return c.any_actual(r"source not in env \(or used twice\)")


def r_cast(from_to):
    def f(c: Ctx):
        e = c.expected_error()
        m = re.match(r"InvalidOperation: cast (\w+) to (\w+): row", e or "")
        return bool(m) and (m.group(1), m.group(2)) in from_to and c.actual_is_frame("eager")
    return f


def r_div_typing(c: Ctx):
    e = c.expected_error() or ""
    return e.startswith("TypeMismatch in div: expected f32") and c.actual_is_frame("eager")


def r_f32cmp(c: Ctx):
    return bool(CMP & c.ops) and c.nan_data and "f32" in str(c.case.sources())


def r_b01b(c: Ctx):
    sel_empty = any(n.verb == "select" and not n.p[0] for n in M.plan_nodes(c.case.plan))
    return sel_empty and c.cls.startswith("T2.1 eager!=raw") and "height" in (c.rec["diffs"].get(c.cls) or [""])[0]


def r_b04j(c: Ctx):
    """the optimizer moved a filter/sort/head across a fallible cast: a different row (or none) fails"""
    if c.cls != "T2.1 raw!=opt" or "cast" not in c.ops and "try_cast" not in c.ops:
        return False
    return "cast" in c.actual("raw") or "cast" in c.actual("opt")


def r_stack(c: Ctx):
    """interpreter-only: a result of ~2^15 rows or more overflows the machine stack (native is fine)"""
    return c.cls == "crash" and "stack overflow" in " ".join(c.rec["diffs"].get("crash", []))


def r_new1(c: Ctx):
    """eager runs the data (a failing cast) before the verb's static DuplicateColumn check"""
    if c.cls not in ("T2.2 eager", "T2.1 eager!=raw"):
        return False
    e = c.actual("eager")
    want = c.exp_eager if c.cls == "T2.2 eager" else c.actual("raw")
    return e.startswith("error\tInvalidOperation: cast ") and (want or "").startswith("error\tDuplicateColumn")


RULES = [
    ("NEW-1", "eager select/group_by evaluate the data (a failing cast) before the DuplicateColumn check that lazy and the contract report first", r_new1),
    ("NEW-2", "interpreter stack overflow on a result of >= ~2^15 rows (dump/join); the native binary is fine", r_stack),
    ("B04-a", "lazy refuses reductions in select/with_columns/filter that eager accepts", r_b04a),
    ("B01-b", "lazy Select{[]} keeps the input height, eager answers (0, 0)", r_b01b),
    ("B04-j", "the optimizer changes which row a strict cast fails on (filter merge / pushdown across a cast)", r_b04j),
    ("B04-b", "a Source used twice (self-join) fails at collect", r_b04b),
    ("B03-f", "`/` accepted on integer columns (contract: TypeMismatch, use floor_div / cast)", r_div_typing),
    ("B03-e", "cast f32 -> u32 of negative / huge / NaN answers 0 instead of an error", r_cast({("f32", "u32")})),
    ("B03-m", "cast f32 -> i32 out of range / u32 <-> i32 retag silently", r_cast({("f32", "i32"), ("u32", "i32"), ("i32", "u32")})),
    ("B03-p", "cast str -> number/bool nulls failures instead of an error", r_cast({("str", "u32"), ("str", "i32"), ("str", "f32"), ("str", "bool")})),
]


def identify(case, rec, got, exp, cls):
    c = Ctx(case, rec, got, exp)
    c.cls = cls
    for id_, text, pred in RULES:
        try:
            if pred(c):
                return id_
        except Exception:  # noqa: BLE001
            continue
    return None


def signature(rec, cls):
    d = rec["diffs"].get(cls) or [""]
    return f"{cls} {diffkind(d[0])}"


def label(case, rec, got, exp, cls):
    """(defect ID or None, signature) of one symptom class of a record, or None if absent."""
    if cls not in rec["classes"]:
        return None
    return (identify(case, rec, got, exp, cls), signature(rec, cls))
