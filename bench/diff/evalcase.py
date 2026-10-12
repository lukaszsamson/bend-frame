"""Evaluate cases against Bend and the oracle (shared by run.py and shrink.py)."""
from __future__ import annotations

from pathlib import Path

import bendrun
import sys
from pathlib import Path as _P

sys.path.append(str(_P(__file__).resolve().parents[1]))
import check  # noqa: E402
import model as M


def compare(a: str, b: str):
    try:
        return check.compare_dumps(a, b)
    except check.DumpError as e:
        return [f"malformed dump: {e}"]


def oracle_result(case):
    """('ok', {'eager','lazy','admissible'}) | ('uncertain', why) | ('oracle_error', why)."""
    import oracle
    try:
        return ("ok", oracle.expected(case))
    except oracle.Uncertain as e:
        return ("uncertain", str(e))
    except Exception as e:  # noqa: BLE001  an oracle bug must be visible, never a silent pass
        return ("oracle_error", f"{type(e).__name__}: {e}")


def evaluate(case, got, exp):
    """The record of one case: classes (empty = everything agrees) and the diffs.

    One class per independent symptom, so one defect is not reported three times:
      T2.2 eager        the eager dump differs from the oracle's
      T2.1 eager!=raw   the raw lazy run differs from the eager run (admissible programs only)
      T2.1 raw!=opt     the default-optimised run (DF.collect) differs from the raw one (DF.collect_raw)
      T2.1 raw!=full    the fully optimised run (DF.collect_full) differs from the raw one
      T2.2 lazy         (only where eager and lazy legitimately differ) a lazy run differs from the oracle's lazy dump
      G1 ..             (--chunked) the chunked engine differs from the reference run (raw / opt)
    A lazy result that equals the eager one is not reported against the oracle again: it is the
    same defect."""
    out = {"id": case.id, "classes": [], "diffs": {}}
    if got is None:
        return out
    e, r, o, fu = got["eager"], got["raw"], got["opt"], got["full"]
    ok = exp is not None and exp[0] == "ok"
    inadm = ok and not exp[1]["admissible"]

    def add(cls, d):
        if d:
            out["classes"].append(cls)
            out["diffs"][cls] = d[:6]

    if ok:
        add("T2.2 eager", compare(e, exp[1]["eager"]))
    if not inadm:
        add("T2.1 eager!=raw", compare(e, r) if e != r else [])
    else:
        for how, txt in (("raw", r), ("opt", o), ("full", fu)):
            add(f"T2.2 lazy {how}", compare(txt, exp[1]["lazy"]))
    add("T2.1 raw!=opt", compare(r, o) if r != o else [])
    add("T2.1 raw!=full", compare(r, fu) if r != fu else [])
    # G1 (v0.2 T5.3, run.py --chunked): the chunked engine against the reference, exactly (the same
    # comparator: only the contract's NaN-payload rule); grains 2^0 / 2^2 / 2^4 on the plan as written,
    # 2^14 through collect
    if "c2" in got:
        add("G1 raw!=chunked0", compare(r, got["c0"]) if r != got["c0"] else [])
        add("G1 raw!=chunked2", compare(r, got["c2"]) if r != got["c2"] else [])
        add("G1 raw!=chunked4", compare(r, got["c4"]) if r != got["c4"] else [])
        add("G1 opt!=chunked14", compare(o, got["c14"]) if o != got["c14"] else [])
    add("P0", p0_diffs(got))
    return out


def p0_diffs(got) -> list:
    """Post-review B1: the null-slot invariant of every result (eager, every lazy run, every chunked
    grain): src/p0.bend's report, printed after each dump, must be "ok" (every null slot holds the dtype
    default; validity and bool words 0/1). A dump never shows a null slot, so all engines can agree on a
    result whose slots are dirty (v0.2's F32 neg wrote -0.0 under its nulls); this class catches the
    dirty slot itself, before an operation that reads it (F4's fill side, the chunked u32 sum) turns it
    into a wrong value. A missing report (an old dx.bend, a cut-off run) is a failure too."""
    reps = got.get(bendrun.P0_KEY, {})
    out = []
    for how in [k for k in got if k != bendrun.P0_KEY]:
        rep = reps.get(how)
        if rep is None:
            out.append(f"{how}: no p0 report")
        elif rep != "ok":
            out.append(f"{how}: p0 {rep}"[:400])
    return out


def check_cases(cases, scratch: Path, mode="interp", tag="chk", timeout=120.0):
    """[(record, got, exp)] for each case (one Bend program for all of them)."""
    res, crashes, _ = bendrun.run_cases(cases, scratch, mode, timeout, tag)
    out = []
    for c in cases:
        exp = oracle_result(c)
        if c.id in crashes:
            out.append(({"id": c.id, "classes": ["crash"], "diffs": {"crash": [crashes[c.id][:300]]}}, None, exp))
            continue
        got = res.get(c.id)
        rec = evaluate(c, got, exp)
        if exp[0] == "oracle_error":
            rec["classes"].append("oracle error")
            rec["diffs"]["oracle"] = [exp[1]]
        out.append((rec, got, exp))
    return out
