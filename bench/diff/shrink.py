"""Minimise a failing case, and write it as a permanent regression test.

    python shrink.py FAILURES.json CASE_ID [--write]    shrink one failure of a run (e.g. d0010)
    python shrink.py --case case.json [--write]

A candidate keeps going while it still fails with the SAME LABEL (classify.label: the defect ID a
rule gives it, else the coarse signature of the mismatch), so shrinking a NEW failure cannot
drift into a known defect or another failure. Candidates per round: drop a plan node, drop a
list element (expression, key, name, agg), replace a subexpression by a child / a literal / a
column, simplify a literal, drop rows (halves, then singly), drop columns, null or simplify
cells. All candidates of a round run as ONE Bend program (about a second); the smallest one that
keeps the label wins the round.

--write emits tests/diff/dNNNN.bend: the case as facade calls and the three printed dumps, with
the oracle's expected dumps as `#|` lines, and `#! xfail <ID>` while the failure stands (the
defect ID, or NEW-<n> for one DESIGN.md 15.10 does not list).
"""
from __future__ import annotations

import argparse
import collections
import json
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import classify
import emit
import evalcase
import model as M
from model import Case, Col, Ex, Frame, Pl

MAX_ROUNDS = 40


def ex_size(e):
    return 1 + sum(ex_size(a) for a in e.args)


def plan_size(pl):
    s = 20
    for x in pl.p:
        items = x if isinstance(x, tuple) else (x,)
        for e in items:
            if isinstance(e, Ex):
                s += 3 * ex_size(e)
            else:
                s += 1
    return s + sum(plan_size(k) for k in pl.kids)


def size(c: Case):
    return plan_size(c.plan) * 4 + sum(f.height * max(1, len(f.cols)) + 5 * len(f.cols) for f in c.inputs.values())


# ---- expression variants ---------------------------------------------------------------------

SMALL = {"bool": [True, False], "u32": [0, 1], "i32": [0, 1], "f32": [0.0, 1.0], "str": ["", "a"]}


def ex_variants(e: Ex, schema):
    """Smaller / simpler expressions in place of e."""
    o = e.op
    out = []
    if o == "lit":
        dt, v = e.p
        if v is not None:
            out.append(Ex("lit", (), (dt, None)))
            for s in SMALL[dt]:
                if s != v:
                    out.append(Ex("lit", (), (dt, s)))
        return out
    if o == "col":
        return out
    try:
        dt, _k = M.analyse(e, schema)
    except M.TErr:
        dt = None
    if o == "alias":
        out.append(e.args[0])
    else:
        out.extend(e.args)
    if dt is not None and o != "alias":
        cs = [n for n, t in schema if t == dt]
        for n in cs[:2]:
            out.append(M.col(n))
        for s in SMALL[dt][:1]:
            out.append(Ex("lit", (), (dt, s)))
    if o == "is_in" and e.p[1]:
        out.append(Ex(o, e.args, (e.p[0], e.p[1][:-1])))
    for i, a in enumerate(e.args):
        for v in ex_variants(a, schema):
            out.append(Ex(o, e.args[:i] + (v,) + e.args[i + 1:], e.p))
    return out


def list_variants(items, schema, allow_empty=True):
    out = []
    for i in range(len(items)):
        if allow_empty or len(items) > 1:
            out.append(items[:i] + items[i + 1:])
        for v in ex_variants(items[i], schema):
            out.append(items[:i] + (v,) + items[i + 1:])
    return out


def param_variants(verb, p, schema):
    """Variants of a verb's parameter tuple."""
    out = []
    if verb in ("select", "with_columns"):
        for es in list_variants(p[0], schema):
            out.append((es,))
    elif verb == "filter":
        for v in ex_variants(p[0], schema):
            out.append((v,))
    elif verb == "group_by":
        keys, aggs = p
        for ks in list_variants(keys, schema, False):
            out.append((ks, aggs))
        for ags in list_variants(aggs, schema):
            out.append((keys, ags))
    elif verb == "sort":
        ks = p[0]
        for i in range(len(ks)):
            out.append((ks[:i] + ks[i + 1:],))
            if ks[i][1] or ks[i][2]:
                out.append((ks[:i] + ((ks[i][0], False, False),) + ks[i + 1:],))
    elif verb in ("head", "tail"):
        for n in (0, 1, 2, p[0] // 2):
            if n < p[0]:
                out.append((n,))
    elif verb == "slice":
        for o_ in (0, p[0] // 2):
            if o_ < p[0]:
                out.append((o_, p[1]))
        for n in (0, 1, p[1] // 2):
            if n < p[1]:
                out.append((p[0], n))
    elif verb in ("inner_join", "left_join", "semi_join", "anti_join"):
        lo, ro = p
        for i in range(len(lo)):
            out.append((lo[:i] + lo[i + 1:], ro[:i] + ro[i + 1:]))
    elif verb in ("drop", "unique"):
        ns = p[0]
        for i in range(len(ns)):
            out.append((ns[:i] + ns[i + 1:],))
    elif verb == "rename":
        ps = p[0]
        for i in range(len(ps)):
            out.append((ps[:i] + ps[i + 1:],))
    return out


def plan_variants(pl: Pl, sources):
    out = []
    if pl.verb == "source":
        return out
    for k in pl.kids:                       # drop this node
        out.append(k)
    try:
        ins = [M.plan_schema(k, sources) for k in pl.kids]
    except M.TErr:
        ins = None
    if ins is not None:
        sch = ins[0] if ins else []
        for p in param_variants(pl.verb, pl.p, sch):
            out.append(Pl(pl.verb, p, pl.kids))
    for i, k in enumerate(pl.kids):
        for v in plan_variants(k, sources):
            out.append(Pl(pl.verb, pl.p, pl.kids[:i] + (v,) + pl.kids[i + 1:]))
    return out


def prune_inputs(case_inputs, plan):
    used = set(M.plan_sources(plan))
    return {k: v for k, v in case_inputs.items() if k in used}


def frame_variants(f: Frame):
    out = []
    h = f.height
    # drop rows: ddmin chunks (halves, quarters, ..., single rows), and keep-only-one-row
    if h > 1:
        step = h // 2
        seen = set()
        while step >= 1:
            for lo in range(0, h, step):
                keep = tuple(i for i in range(h) if not lo <= i < lo + step)
                if keep and keep not in seen:
                    seen.add(keep)
                    out.append(sub_rows(f, list(keep)))
            step //= 2
        for i in range(min(h, 8)):
            out.append(sub_rows(f, [i]))
    for ci in range(len(f.cols)):
        if len(f.cols) > 1:
            out.append(Frame([c for j, c in enumerate(f.cols) if j != ci], h))
        c = f.cols[ci]
        if any(v is not None for v in c.vals):
            out.append(replace_col(f, ci, Col(c.name, c.dtype, [None] * h)))
            nn = [v for v in c.vals if v is not None]
            if len(set(M.val_key(c.dtype, v) for v in nn)) > 1:
                out.append(replace_col(f, ci, Col(c.name, c.dtype, [nn[0] if v is not None else None for v in c.vals])))
    return out


def sub_rows(f, keep):
    return Frame([Col(c.name, c.dtype, [c.vals[i] for i in keep]) for c in f.cols], len(keep))


def replace_col(f, ci, col):
    cols = list(f.cols)
    cols[ci] = col
    return Frame(cols, f.height)


def case_variants(case: Case):
    seen, out = set(), []

    def add(c):
        key = json.dumps(c.to_json(), sort_keys=True)
        if key not in seen and key != base:
            seen.add(key)
            out.append(c)

    base = json.dumps(case.to_json(), sort_keys=True)
    sources = case.sources()
    for pl in plan_variants(case.plan, sources):
        add(Case(case.id, case.seed, prune_inputs(case.inputs, pl), pl, case.kind))
    for name, f in case.inputs.items():
        for nf in frame_variants(f):
            add(Case(case.id, case.seed, {**case.inputs, name: nf}, case.plan, case.kind))
    out.sort(key=size)
    return out


# ---- the loop ------------------------------------------------------------------------------------

def labels_of(cases, scratch, tag, mode="interp", cls=None):
    """[(label, rec, got, exp)] for candidate cases (ids renumbered inside one program);
    label is for the symptom class `cls` (None: the first class of the record)."""
    named = [Case(f"d{i:04d}", c.seed, c.inputs, c.plan, c.kind) for i, c in enumerate(cases)]
    res = evalcase.check_cases(named, scratch, mode, tag)
    out = []
    for c, (rec, got, exp) in zip(named, res):
        k = cls or (rec["classes"][0] if rec["classes"] else None)
        out.append((classify.label(c, rec, got, exp, k) if k else None, rec, got, exp))
    return out


def same_label(lab, lab0):
    """A known defect ID is preserved by its ID alone; a NEW failure by its whole signature."""
    if lab is None or lab0 is None:
        return False
    return lab[0] == lab0[0] if lab0[0] else lab == lab0


def shrink(case: Case, scratch: Path, tag="s", mode="interp", verbose=False, max_rounds=MAX_ROUNDS, cls=None, budget=90.0):
    """(minimal case, its label, rounds). The label of `case` must be non-empty (it fails)."""
    (lab0, rec0, got0, exp0), = labels_of([case], scratch, tag + "i", mode, cls)
    cls = cls or (rec0["classes"][0] if rec0["classes"] else None)
    if lab0 is None:
        return case, None, 0
    cur = case
    t_end = time.time() + budget
    rnd = 0
    for rnd in range(max_rounds):
        if time.time() > t_end:
            break
        cands = case_variants(cur)
        if not cands:
            break
        found = None
        for k in range(0, len(cands), 100):
            chunk = cands[k:k + 100]
            labs = labels_of(chunk, scratch, f"{tag}r{rnd}c{k}", mode, cls)
            for c, (lab, *_rest) in zip(chunk, labs):
                if same_label(lab, lab0):
                    found = c
                    break
            if found is not None:
                break
        if found is None:
            break
        if verbose:
            print(f"  round {rnd}: size {size(cur)} -> {size(found)}", flush=True)
        cur = found
    return Case(case.id, case.seed, cur.inputs, cur.plan, case.kind), lab0, rnd


# ---- permanent regressions --------------------------------------------------------------------------

def next_test_number(tests_dir: Path):
    nums = [int(p.stem[1:]) for p in tests_dir.glob("d[0-9][0-9][0-9][0-9].bend")]
    return max(nums, default=0) + 1


def regression_text(case: Case, exp_ok: dict, xfail: str | None, note: str) -> str:
    tag = case.id
    lines = []
    if xfail:
        lines.append(f"#! xfail {xfail}")
    lines.append("# Generated by bench/diff (gen.py -> run.py -> shrink.py): a minimised failing case.")
    for ln in note.splitlines():
        lines.append("# " + ln)
    lines.append("# Expected dumps: bench/diff/oracle.py (Polars 2.0.0 + the contract's departures, DESIGN.md 15).")
    head = "\n".join(lines) + "\n"
    body = emit.HEADER + "\n" + emit.case_defs(case) + "\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + emit.case_step(case) + "\n"
    exp = []
    for how, want in (("eager", exp_ok["eager"]), ("raw", exp_ok["lazy"]), ("opt", exp_ok["lazy"]), ("full", exp_ok["lazy"])):
        exp.append(f"#|-- {tag} {how}")
        for ln in want.rstrip("\n").split("\n"):
            exp.append("#|" + ln)
        exp.append("#|")
    return head + body + "\n".join(exp[:-1]) + "\n"


def case_note(case: Case, label, rec) -> str:
    import gen
    txt = gen.case_text(case)
    out = [f"label: {label[0] or 'NEW'}  {label[1]}"]
    for k, v in rec["diffs"].items():
        out.append(f"{k}: {v[0]}")
    out.append("")
    out.extend(txt.splitlines())
    return "\n".join(out)


def write_regression(case: Case, label, rec, exp, xfail, tests_dir: Path):
    n = next_test_number(tests_dir)
    c2 = Case(f"d{n:04d}", case.seed, case.inputs, case.plan, case.kind)
    path = tests_dir / f"d{n:04d}.bend"
    path.write_text(regression_text(c2, exp[1], xfail, case_note(case, label, rec)))
    return path


# ---- grouping: one minimal representative per failure label ---------------------------------------------

def group_and_shrink(failures, scratch: Path, out_json: Path, summary: dict, quiet=False, jobs=6, mode="interp", budget=90.0):
    """Label every (failing case, symptom class), shrink one representative per label, write the
    JSON report. Called by run.py."""
    units = []   # (failure record, case, class)
    for f in failures:
        c = Case.from_json(f["case"])
        for cls in f["classes"]:
            units.append((f, c, cls))
    groups = collections.defaultdict(list)
    # label in bulk
    by_cls = collections.defaultdict(list)
    for u in units:
        by_cls[u[2]].append(u)
    for cls, us in by_cls.items():
        for k in range(0, len(us), 200):
            chunk = us[k:k + 200]
            labs = labels_of([u[1] for u in chunk], scratch / "label", f"l{abs(hash(cls)) % 10**5}_{k}", mode, cls)
            for (f, c, _), (lab, rec, got, exp) in zip(chunk, labs):
                if lab is None:
                    lab = (None, f"{cls} (not reproduced in the labelling run)")
                groups[(cls, lab[0] or lab[1])].append((f, c, lab))
    reps = {key: min(items, key=lambda it: size(it[1])) for key, items in groups.items()}

    def work(item):
        key, (f, c, lab) = item
        return key, shrink(c, scratch / "shrink", f"s{abs(hash(key)) % 10**6}", mode, cls=key[0], budget=budget)

    done = {}
    with ThreadPoolExecutor(max_workers=jobs) as ex:
        for key, res in ex.map(work, list(reps.items())):
            done[key] = res
    report = []
    for key, items in sorted(groups.items(), key=lambda kv: -len(kv[1])):
        cls, _ = key
        mc, mlab, rounds = done[key]
        rep_lab = reps[key][2]
        (lab2, rec, got, exp), = labels_of([mc], scratch / "final", f"fin{abs(hash(key)) % 10**6}", mode, cls)
        report.append({
            "class": cls, "id": rep_lab[0], "signature": rep_lab[1], "count": len(items),
            "example_ids": [f["id"] for f, _, _ in items[:8]],
            "minimal": mc.to_json(), "minimal_text": __import__("gen").case_text(mc),
            "minimal_label": [lab2[0], lab2[1]] if lab2 else None,
            "diffs": rec["diffs"] if rec else {},
            "actual": got, "expected": exp[1] if exp and exp[0] == "ok" else None,
            "size": size(mc), "rounds": rounds,
        })
    out_json.write_text(json.dumps({"summary": summary, "groups": report, "failures": failures}, indent=1))
    by_id = collections.Counter()
    for g in report:
        by_id[g["id"] or "NEW"] += g["count"]
    print("\nfailure groups (count, defect, class):")
    for g in report:
        print(f"  {g['count']:4d}  {g['id'] or 'NEW':6s}  {g['signature']}   [{g['example_ids'][0]}, shrunk to size {g['size']}]")
    print("\nsymptoms by defect:", dict(by_id))
    return report


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("failures", nargs="?")
    ap.add_argument("id", nargs="?")
    ap.add_argument("--case")
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--scratch")
    ap.add_argument("--mode", default="interp")
    ap.add_argument("--tests-dir", help="where --write puts the test (default tests/diff of this tree)")
    ap.add_argument("--cls", help="the symptom class to preserve (default: the first)")
    a = ap.parse_args(argv)
    if a.case:
        case = Case.from_json(json.loads(Path(a.case).read_text()))
    else:
        j = json.loads(Path(a.failures).read_text())
        fs = j["failures"] if "failures" in j else j
        case = Case.from_json(next(f for f in fs if f["id"] == a.id)["case"])
    scratch = Path(a.scratch) if a.scratch else M.ROOT / "build/diff/shrink"
    mc, lab, rounds = shrink(case, scratch, mode=a.mode, verbose=True, cls=a.cls)
    if lab is None:
        print("the case does not fail")
        return 2
    (lab2, rec, got, exp), = labels_of([mc], scratch, "fin", a.mode, a.cls)
    import gen
    print(gen.case_text(mc))
    print("label:", lab2)
    for k, v in rec["diffs"].items():
        print(" ", k, v[:2])
    if a.write:
        xf = lab2[0] or "NEW"
        p = write_regression(mc, lab2, rec, exp, xf, Path(a.tests_dir) if a.tests_dir else M.ROOT / "tests/diff")
        print("wrote", p)
    return 0


if __name__ == "__main__":
    sys.exit(main())
