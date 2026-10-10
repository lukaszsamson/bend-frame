"""T2.3: F32 reductions against an exact (integer / Fraction) reference, with calibrated bounds.

    cd bench && uv run python diff/reduce.py --seed 1 --n 2000        # make diff-reduce
    uv run python diff/run.py --reductions --seed 1 --n 2000          # the same, through run.py
    uv run python diff/reduce.py --selftest                           # the reference's own checks
    uv run python diff/reduce.py --seed 1 --n 2000 --shrink --write   # minimise failures, write tests/diff/r*.bend

What is checked per case (bench/diff/README.md, "T2.3"; contract DESIGN.md 15.5.3 / 15.5.4):
  * the input frame dumps back to the intended bits (the literals parsed right);
  * eager select [sum, mean], eager group_by(g) [sum, mean] at several group sizes, and describe
    (mean, std, count, null_count, min, 25/50/75 %, max) of the x column;
  * the raw-lazy and fully optimised lazy runs print the same text as the eager run;
  * every value: equal to the contract's step model (bit exact), non-finite data against IEEE's
    order-independent answer, finite data within the derived error bound of the exactly rounded
    reference (reduce_ref.py: the derivation), 1-2 ulp when the data are well conditioned;
  * how often the answer is exactly the correctly rounded f32 of the exact result.
Std/Var/Median aggregations (DF.std, DF.var, DF.median) are generated and checked as soon as the
facade defines them (`reduce_gen.available_aggs`); until then describe is the only std source.
"""
from __future__ import annotations

import argparse
import collections
import json
import os
import re
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.append(str(HERE.parent))

import bendrun  # noqa: E402
import model as M  # noqa: E402
import reduce_gen as G  # noqa: E402
import reduce_ref as R  # noqa: E402

HDR = re.compile(r"^-- (c\d+) (\w+)$", re.M)
TAGS = ("in", "sel_e", "sel_r", "sel_f", "grp_e", "grp_r", "grp_f", "desc")
DEFECT_KINDS = ("bound", "special", "null", "err", "lazy", "order", "shape", "model", "tight", "minmax")


# ---- running ------------------------------------------------------------------------------

def parse_output(out: str) -> dict:
    res: dict = {}
    pos = [(m.start(), m.end(), m.group(1), m.group(2)) for m in HDR.finditer(out)]
    for i, (s, e, cid, tag) in enumerate(pos):
        end = pos[i + 1][0] if i + 1 < len(pos) else len(out)
        body = out[e + 1:end]
        res.setdefault(cid, {})[tag] = body.rstrip("\n") + "\n" if body.strip() else body
    return res


def run_batch(cases, scratch: Path, tag: str, extra, timeout, depth=0):
    scratch.mkdir(parents=True, exist_ok=True)
    path = scratch / f"{tag}.bend"
    path.write_text(G.program(cases, G.header_for(scratch), extra))
    out, rc, secs = bendrun.run_file(path, "interp", timeout)
    got = parse_output(out)
    done = {c["id"] for c in cases if len(got.get(c["id"], {})) == len(TAGS)}
    if rc != 0 and got:
        done.discard(list(got)[-1])                  # the last one may be cut off
    if rc == 0 and len(done) == len(cases):
        return got, {}
    if not got and "stack overflow" not in out and "memory fault" not in out and rc != "timeout":
        raise bendrun.BendError(f"bend could not run {path}: exit {rc}\n{out[-800:]}")
    missing = [c for c in cases if c["id"] not in done]
    res = {k: v for k, v in got.items() if k in done}
    crashes = {}
    if len(cases) == 1 or len(missing) == 1 and len(cases) == 1:
        crashes[cases[0]["id"]] = f"exit {rc}: " + out[-500:]
        return res, crashes
    mid = max(len(missing) // 2, 1)
    for k, part in enumerate((missing[:mid], missing[mid:])):
        if part:
            r2, c2 = run_batch(part, scratch, f"{tag}{k}", extra, timeout, depth + 1)
            res.update(r2)
            crashes.update(c2)
    return res, crashes


def batches(cases, max_rows=20000, max_cases=60):
    cur, rows = [], 0
    for c in cases:
        if cur and (rows + c["n"] > max_rows or len(cur) >= max_cases):
            yield cur
            cur, rows = [], 0
        cur.append(c)
        rows += c["n"]
    if cur:
        yield cur


def run_all(cases, scratch: Path, extra, jobs=6, timeout=400.0):
    bl = list(batches(sorted(cases, key=lambda c: c["n"])))
    results, crashes = {}, {}

    def one(a):
        k, b = a
        return run_batch(b, scratch, f"b{k:03d}", extra, timeout)

    with ThreadPoolExecutor(max_workers=jobs) as ex:
        for r, c in ex.map(one, list(enumerate(bl))):
            results.update(r)
            crashes.update(c)
    return results, crashes


# ---- dumps --------------------------------------------------------------------------------

def parse_dump(text: str) -> dict:
    lines = text.split("\n")
    if lines and lines[0].startswith("error\t"):
        return {"error": lines[0][6:]}
    d = {"cols": [], "rows": []}
    for ln in lines:
        if ln.startswith("height\t"):
            d["height"] = int(ln.split("\t")[1])
        elif ln.startswith("col\t"):
            _, dt, nm = ln.split("\t", 2)
            d["cols"].append((dt, nm.strip('"')))
        elif ln.startswith("row"):
            d["rows"].append(ln.split("\t")[1:])
    return d


def cell_bits(cell: str):
    return None if cell == "null" else R.canon(int(cell, 16))


def fmt_bits(b):
    return "null" if b is None else f"0x{b:08x}"


# ---- the checks ---------------------------------------------------------------------------

class Stats:
    cur = ""

    def __init__(self):
        self.t = collections.defaultdict(lambda: {"n": 0, "exact": 0, "maxulp": 0, "maxratio": 0.0, "bad": 0, "model": 0, "hist": collections.Counter()})

    def add(self, key, ulp=None, ratio=None, exact=None, bad=False, model_bad=False):
        s = self.t[key]
        s["n"] += 1
        s["bad"] += bool(bad)
        s["model"] += bool(model_bad)
        if exact is not None:
            s["exact"] += bool(exact)
        if ulp is not None:
            s["maxulp"] = max(s["maxulp"], ulp)
            s["hist"]["0" if ulp == 0 else "1" if ulp == 1 else "2" if ulp == 2 else "3-8" if ulp <= 8 else ">8"] += 1
        if ratio is not None:
            s["maxratio"] = max(s["maxratio"], ratio)
            if ratio >= s.get("worst", (0,))[0]:
                s["worst"] = (ratio, self.cur)


def category(xs, ex: "R.Exact | None"):
    if not xs:
        return "empty"
    if any(not R.is_finite(b) for b in xs):
        return "special"
    k = ex.kappa()
    if ex.S == 0:
        return "plain" if ex.A == 0 else "cancel"
    return "cancel" if k > 16 else "plain"


class Judge:
    def __init__(self, cid, cls, stats, findings):
        self.cid, self.cls, self.stats, self.findings = cid, cls, stats, findings

    def find(self, kind, path, q, where, detail):
        self.findings.append({"id": self.cid, "cls": self.cls, "kind": kind, "path": path, "q": q, "where": where, "detail": detail})

    # one value: q in sum mean std var median
    def judge(self, q, path, where, xs, cell, ex_cache):
        n = len(xs)
        model_fn = {"sum": R.model_sum, "mean": R.model_mean, "std": R.model_std, "var": R.model_var, "median": R.model_median}[q]
        model = model_fn(xs)
        got = cell_bits(cell)
        if "ex" not in ex_cache:
            ex_cache["ex"] = R.Exact(xs) if all(R.is_finite(b) for b in xs) else None
        ex = ex_cache["ex"]
        cat = category(xs, ex)
        skey = (cat, q, path)
        if model is None:                                 # null expected
            ok = got is None
            self.stats.add(skey, bad=not ok)
            if not ok:
                self.find("null", path, q, where, f"expected null, got {fmt_bits(got)}")
            return
        model = R.canon(model)
        if got is None:
            self.stats.add(skey, bad=True)
            self.find("null", path, q, where, f"unexpected null (model {fmt_bits(model)})")
            return
        bad = False
        model_bad = got != model
        if model_bad:
            self.find("model", path, q, where, f"got {fmt_bits(got)} model {fmt_bits(model)} n={n}")
        # IEEE special rule (independent of the order)
        sp = None
        if cat == "special":
            if q in ("sum", "mean"):
                sp = R.special_sum(xs)
            elif q in ("std", "var") and n >= 2:
                sp = R.NAN_BITS
        if sp is not None:
            if got != sp:
                bad = True
                self.find("special", path, q, where, f"got {fmt_bits(got)} IEEE {fmt_bits(sp)}")
            self.stats.add(skey, bad=bad, model_bad=model_bad)
            return
        if cat == "special":                              # median of non-finite data: the model is the definition
            self.stats.add(skey, bad=False, model_bad=model_bad)
            return
        if not R.is_finite(model):                        # finite data, the guard answered inf/NaN: model is the contract
            self.stats.add((("overflow",) + skey[1:]), bad=model_bad, model_bad=model_bad)
            return
        # finite data, finite answer: exact reference and the bound
        ulp = ratio = None
        if q == "sum":
            exact, bound = ex.sum, ex.sum_bound()
            rn = R.units_to_f32(ex.S)
        elif q == "mean":
            exact, bound = ex.mean, ex.mean_bound()
            rn = R.round_f32(ex.mean)
        elif q in ("var", "std"):
            mhat = R.model_mean(xs)
            ve = ex.var_exact(mhat)
            vb = ex.var_bound(mhat)
            if q == "var":
                exact, bound, rn = ve, vb, R.round_f32(ve)
            else:
                exact = None
                rn = R.frac_sqrt_bits(ve)
                # compare in float via Fractions of the (exact) bound formula
                bound = R.std_bound(ve, vb, float(R.val(got)) if R.is_finite(got) else 0.0)
        else:                                             # median
            s = R.sort_valid(xs)
            if n % 2:
                exact = R.val(s[(n - 1) // 2])
            else:
                exact = (R.val(s[n // 2 - 1]) + R.val(s[n // 2])) / 2
            rn = R.round_f32(exact)
            bound = abs(exact) * 2 * R.U + Fraction(4, 1 << 149)
        if not R.is_finite(got):
            bad = True
            self.find("bound", path, q, where, f"got {fmt_bits(got)}, exact finite {float(exact if exact is not None else 0):.9g}")
            self.stats.add(skey, bad=True, model_bad=model_bad)
            return
        if q == "std":
            # |sqrt-based bound| around sqrt(var_exact): exact std is irrational; use the rounded value
            # (error of the rounding is < 1 ulp of rn, added to the bound)
            err = abs(R.val(got) - R.val(rn))
            bound = bound + Fraction(1, 1) * abs(R.val(rn)) * R.U * 2
        else:
            err = abs(R.val(got) - exact)
        ulp = R.ulp_dist(got, rn)
        ratio = float(err / bound) if bound > 0 else (0.0 if err == 0 else float("inf"))
        if err > bound:
            bad = True
            self.find("bound", path, q, where, f"got {fmt_bits(got)} rn {fmt_bits(rn)} ulp {ulp} err/bound {ratio:.3g} n={n}")
        # tight tier: well conditioned and short -> within 1 ulp (sum) / 2 ulp (mean) of the correctly rounded value
        if q in ("sum", "mean") and cat == "plain" and n <= 256 and ex.S != 0 and ex.kappa() <= 2:
            tol = 1 if q == "sum" else 2
            if ulp > tol:
                self.find("tight", path, q, where, f"got {fmt_bits(got)} rn {fmt_bits(rn)} ulp {ulp} (> {tol}) n={n}")
        self.stats.add(skey, ulp=ulp, ratio=ratio, exact=(got == rn or (got & 0x7FFFFFFF) == 0 and (rn & 0x7FFFFFFF) == 0), bad=bad, model_bad=model_bad)


def check_case(c, got, stats, findings, extra):
    cid = c["id"]
    J = Judge(cid, c["cls"], stats, findings)
    stats.cur = cid
    n = c["n"]
    xs_all = [bt if v else None for bt, v in zip(c["bits"], c["valid"])]
    if "in" not in got:
        J.find("shape", "-", "-", "-", "no output")
        return
    # input frame
    d = parse_dump(got["in"])
    exp_rows = [[str(k), fmt_bits(R.canon(bt)) if v else "null"] for k, bt, v in zip(c["keys"], c["bits"], c["valid"])]
    if d.get("rows") != exp_rows:
        i = next((i for i, (a, b) in enumerate(zip(d.get("rows", []), exp_rows)) if a != b), None)
        J.find("infra", "in", "-", "-", f"input frame mismatch at row {i}: {d.get('rows', [None])[i] if i is not None else '-'} vs {exp_rows[i] if i is not None else '-'}")
        return
    # lazy == eager
    for e, l in (("sel_e", "sel_r"), ("sel_e", "sel_f"), ("grp_e", "grp_r"), ("grp_e", "grp_f")):
        if got[e] != got[l]:
            J.find("lazy", l, "-", "-", f"{l} differs from {e}")
    # groups
    order, groups = [], {}
    for k, v, bt in zip(c["keys"], c["valid"], c["bits"]):
        if k not in groups:
            groups[k] = []
            order.append(k)
        if v:
            groups[k].append(bt)
    valid = [bt for bt, v in zip(c["bits"], c["valid"]) if v]
    qs = ["sum", "mean"] + list(extra)
    # eager select
    d = parse_dump(got["sel_e"])
    if "error" in d:
        J.find("err", "sel", "-", "-", d["error"])
    elif d.get("height") != 1 or [x[1] for x in d["cols"]] != ["s", "m"] + list(extra) or len(d["rows"]) != 1:
        J.find("shape", "sel", "-", "-", f"shape {d.get('height')} {d['cols']}")
    else:
        cache = {}
        for q, cell in zip(qs, d["rows"][0]):
            J.judge(q, "sel", "all", valid, cell, cache)
    # eager group_by
    d = parse_dump(got["grp_e"])
    if "error" in d:
        J.find("err", "grp", "-", "-", d["error"])
    elif d.get("height") != len(order) or len(d["rows"]) != len(order):
        J.find("shape", "grp", "-", "-", f"height {d.get('height')} vs {len(order)} groups")
    else:
        for gi, (k, row) in enumerate(zip(order, d["rows"])):
            if row[0] != str(k):
                J.find("order", "grp", "-", gi, f"group {gi} key {row[0]} expected {k}")
                break
            cache = {}
            for q, cell in zip(qs, row[1:]):
                J.judge(q, "grp", f"g{gi}", groups[k], cell, cache)
    # describe
    d = parse_dump(got["desc"])
    if "error" in d:
        J.find("err", "desc", "-", "-", d["error"])
        return
    rows = {r[0].strip('"'): r[1] for r in d["rows"]}
    nv = len(valid)
    cache = {}
    if rows.get("count") != fmt_bits(R.f2b(R.F(nv))) or rows.get("null_count") != fmt_bits(R.f2b(R.F(n - nv))):
        J.find("shape", "desc", "count", "-", f"count {rows.get('count')} null_count {rows.get('null_count')} for {nv}/{n}")
    if nv:
        J.judge("mean", "desc", "all", valid, rows["mean"], cache)
        J.judge("std", "desc", "all", valid, rows["std"], cache)
        # the quantile rows: nearest rank over the 15.5.2-sorted valid cells (min and max follow 15.5.2's
        # min/max rule instead, checked below)
        qv = R.model_quantiles(valid)
        for nm, exp in zip(("min", "25%", "50%", "75%", "max"), qv):
            if nm in ("min", "max"):
                continue
            gb = cell_bits(rows[nm])
            ok = gb == R.canon(exp) or (gb is not None and (gb & 0x7FFFFFFF) == 0 and (exp & 0x7FFFFFFF) == 0)
            stats.add(("order", nm, "desc"), bad=not ok)
            if not ok:
                J.find("order", "desc", nm, "all", f"got {fmt_bits(gb)} expected {fmt_bits(R.canon(exp))} (nearest rank, 15.5.2 order) n={nv}")
            elif gb != R.canon(exp):
                stats.add(("order-zero-sign", nm, "desc"), bad=False)
        # describe min/max = the contract's min/max aggregation (NaN skipped, -0.0 < 0.0 on ties, 15.5.2)
        cmin, cmax = R.model_minmax(valid)
        for nm, e in (("min", cmin), ("max", cmax)):
            gb = cell_bits(rows[nm])
            if gb != R.canon(e):
                stats.add(("describe-vs-AggOp", nm, "desc"), bad=False)
                J.find("minmax", "desc", nm, "all", f"describe {nm} {fmt_bits(gb)} vs contract min/max (15.5.2) {fmt_bits(R.canon(e))}")
            else:
                stats.add(("describe-vs-AggOp", nm, "desc"), bad=False)
    else:
        for nm in ("mean", "std", "min", "25%", "50%", "75%", "max"):
            if rows.get(nm) != "null":
                J.find("null", "desc", nm, "all", f"expected null, got {rows.get(nm)}")


# ---- report -------------------------------------------------------------------------------

def report(stats, findings, cases, summary):
    print("\n== exactness and ulp (finite answers within bound) ==")
    print(f"{'category':9} {'q':7} {'path':5} {'n':>6} {'==RN':>7} {'%exact':>7} {'max ulp':>8} {'max err/bound':>14}  {'0/1/2/3-8/>8 ulp':>20} {'bad':>4} {'model!=':>7}")
    for k in sorted(stats.t):
        s = stats.t[k]
        h = s["hist"]
        pe = "" if not s["n"] else f"{100.0 * s['exact'] / s['n']:.1f}"
        print(f"{k[0]:9} {k[1]:7} {k[2]:5} {s['n']:>6} {s['exact']:>7} {pe:>7} {s['maxulp']:>8} {s['maxratio']:>14.3g}  "
              f"{h['0']}/{h['1']}/{h['2']}/{h['3-8']}/{h['>8']:>12} {s['bad']:>4} {s['model']:>7}")
    worst = sorted(((s["worst"][0], s["worst"][1], k) for k, s in stats.t.items() if "worst" in s), reverse=True)[:6]
    print("\ntightest bound uses (err/bound, case, key):", [(round(r, 4), c, k) for r, c, k in worst])
    by_kind = collections.Counter(f["kind"] for f in findings)
    print("\nfindings by kind:", dict(by_kind) or "none")
    summary["findings_by_kind"] = dict(by_kind)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--n", type=int, default=2000)
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--jobs", type=int, default=6)
    ap.add_argument("--timeout", type=float, default=400.0)
    ap.add_argument("--classes", default="", help="comma list of generator classes (default: all)")
    ap.add_argument("--max-n", type=int, default=0, help="skip cases with more rows (0: no cap)")
    ap.add_argument("--out", help="findings JSON (default build/diff/reduce/seed<seed>/findings.json)")
    ap.add_argument("--shrink", action="store_true", help="minimise the first failing case of each defect group")
    ap.add_argument("--write", action="store_true", help="with --shrink: write tests/diff/rNNNN.bend (xfail NEW-<n>)")
    ap.add_argument("--xfail", help="with --write: the `#! xfail` id (default NEW-T23-<k>)")
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--show", action="store_true", help="print the generated cases only")
    a = ap.parse_args(argv)
    if a.selftest:
        import reduce_selftest
        return reduce_selftest.main()
    only = [c for c in a.classes.split(",") if c] or None
    scratch = M.ROOT / f"build/diff/reduce/seed{a.seed}"
    import shutil
    shutil.rmtree(scratch, ignore_errors=True)
    scratch.mkdir(parents=True, exist_ok=True)
    cases = [G.gen_case(a.seed, i, only) for i in range(a.start, a.start + a.n)]
    if a.max_n:
        cases = [c for c in cases if c["n"] <= a.max_n]
    if a.show:
        for c in cases[:30]:
            print(c["id"], c["cls"], "n", c["n"], "nulls", c["null_rate"], c["layout"], [R.b2f(b).item() for b in c["bits"][:6]])
        return 0
    extra = G.available_aggs()
    t0 = time.time()
    res, crashes = run_all(cases, scratch, extra, jobs=a.jobs, timeout=a.timeout)
    t_bend = time.time() - t0
    stats, findings = Stats(), []
    for c in cases:
        if c["id"] in crashes:
            findings.append({"id": c["id"], "cls": c["cls"], "kind": "crash", "path": "-", "q": "-", "where": "-", "detail": crashes[c["id"]][:300]})
            continue
        got = res.get(c["id"])
        if not got:
            findings.append({"id": c["id"], "cls": c["cls"], "kind": "shape", "path": "-", "q": "-", "where": "-", "detail": "no output"})
            continue
        check_case(c, got, stats, findings, extra)
    summary = {"seed": a.seed, "n": len(cases), "extra_aggs": extra, "bend_s": round(t_bend, 1),
               "classes": dict(collections.Counter(c["cls"] for c in cases)),
               "rows_total": sum(c["n"] for c in cases), "max_rows": max((c["n"] for c in cases), default=0),
               "crashes": len(crashes)}
    print(json.dumps(summary, indent=1))
    report(stats, findings, cases, summary)
    out = Path(a.out) if a.out else scratch / "findings.json"
    out.write_text(json.dumps({"summary": summary, "findings": findings}, indent=1))
    # group the findings
    groups = collections.defaultdict(list)
    for f in findings:
        groups[(f["kind"], f["path"], f["q"])].append(f)
    for k, fs in sorted(groups.items()):
        print(f"\n[{k[0]}] path={k[1]} q={k[2]}: {len(fs)} findings in {len({f['id'] for f in fs})} cases; classes {dict(collections.Counter(f['cls'] for f in fs))}")
        for f in fs[:3]:
            print("   ", f["id"], f["cls"], f["where"], f["detail"][:200])
    print(f"\ntotal {time.time() - t0:.1f}s; findings: {out}")
    if a.shrink:
        import reduce_shrink
        reduce_shrink.run(cases, findings, scratch, extra, a)
    # Every finding fails the run, whatever its kind (DEFECT_KINDS only names the known kinds; a kind
    # added later must not become a silent pass). There is no known-findings allowlist.
    if findings:
        print(f"FAIL: {len(findings)} finding(s)")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
