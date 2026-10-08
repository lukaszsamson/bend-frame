"""Minimise a failing T2.3 case (delta debugging on rows) and write tests/diff/rNNNN.bend.

    uv run python diff/reduce.py --seed 1 --n 2000 --shrink [--write] [--xfail NEW-7]

One representative per (kind, path, quantity) group of findings is minimised by dropping rows
(values, validity and keys together) while the SAME kind of finding survives a fresh Bend run.
The written test prints the failing path's dump(s) and expects what the CONTRACT gives (the
step model of reduce_ref.py; describe's min/max by the min/max rule of 15.5.2), never what
Bend printed; a defect therefore fails it and the file carries `#! xfail <ID>`.
"""
from __future__ import annotations

import collections
from pathlib import Path

import bendrun
import model as M
import reduce as RD
import reduce_gen as G
import reduce_ref as R

TESTS = M.ROOT / "tests" / "diff"
SHRINK_KINDS = ("bound", "special", "null", "err", "lazy", "order", "shape", "model", "tight", "minmax")


def sub_case(c, idx):
    return {**c, "n": len(idx), "bits": [c["bits"][i] for i in idx], "valid": [c["valid"][i] for i in idx], "keys": [c["keys"][i] for i in idx]}


def still_fails(c, key, scratch: Path, extra, counter=[0]):
    counter[0] += 1
    d = scratch / "shrink"
    try:
        res, crashes = RD.run_batch([c], d, f"s{counter[0]:04d}", extra, 120.0)
    except bendrun.BendError:
        return False
    got = res.get(c["id"])
    if not got:
        return False
    stats, findings = RD.Stats(), []
    RD.check_case(c, got, stats, findings, extra)
    return any((f["kind"], f["path"], f["q"]) == key for f in findings)


def ddmin(c, key, scratch, extra, budget=120):
    idx = list(range(c["n"]))
    k = 2
    tries = 0
    while len(idx) >= 2 and tries < budget:
        size = max(len(idx) // k, 1)
        chunks = [idx[i:i + size] for i in range(0, len(idx), size)]
        for ch in chunks:
            rest = [i for i in idx if i not in set(ch)]
            tries += 1
            if rest and still_fails(sub_case(c, rest), key, scratch, extra):
                idx = rest
                k = max(k - 1, 2)
                break
        else:
            if size == 1:
                break
            k = min(k * 2, len(idx))
    # simplify the keys: all rows in one group when that still fails
    small = sub_case(c, idx)
    one = {**small, "keys": [0] * small["n"], "layout": "one"}
    if still_fails(one, key, scratch, extra):
        small = one
    return small


# ---- the expected dumps of the contract ---------------------------------------------------

def hexcell(b):
    return "null" if b is None else f"0x{R.canon(b):08x}"


def expected(c, tag, extra=()):
    keys, valid, bits = c["keys"], c["valid"], c["bits"]
    allv = [b for b, v in zip(bits, valid) if v]
    order, groups = [], {}
    for k, v, b in zip(keys, valid, bits):
        if k not in groups:
            groups[k] = []
            order.append(k)
        if v:
            groups[k].append(b)

    def vals(xs):
        out = [R.model_sum(xs), R.model_mean(xs)]
        for q in extra:
            out.append({"std": R.model_std, "var": R.model_var, "median": R.model_median}[q](xs))
        return out

    cols = '\ncol\tf32\t"s"\ncol\tf32\t"m"' + "".join(f'\ncol\tf32\t"{q}"' for q in extra)
    w = 2 + len(extra)
    if tag in ("sel_e", "sel_r", "sel_f"):
        return f"frame\nheight\t1\nwidth\t{w}{cols}\nrow\t" + "\t".join(hexcell(x) for x in vals(allv)) + "\n"
    if tag in ("grp_e", "grp_r", "grp_f"):
        s = f'frame\nheight\t{len(order)}\nwidth\t{w + 1}\ncol\tu32\t"g"{cols}\n'
        for k in order:
            s += f"row\t{k}\t" + "\t".join(hexcell(x) for x in vals(groups[k])) + "\n"
        return s
    if tag == "desc":
        n, nv = len(bits), len(allv)
        fin = [b for b in allv if not R.is_nan(b)]
        q = R.model_quantiles(allv) or [None] * 5
        if fin:
            q = list(q)
            q[0] = min(fin, key=lambda b: (R.fword_key(b), b >> 31 == 0))
            q[4] = max(fin, key=lambda b: (R.fword_key(b), b >> 31 != 0))
        rows = [("count", R.f2b(R.F(nv))), ("null_count", R.f2b(R.F(n - nv))), ("mean", R.model_mean(allv)),
                ("std", R.model_std(allv))] + list(zip(("min", "25%", "50%", "75%", "max"), q))
        s = 'frame\nheight\t9\nwidth\t2\ncol\tstr\t"statistic"\ncol\tf32\t"x"\n'
        for nm, v in rows:
            s += f'row\t"{nm}"\t{hexcell(v)}\n'
        return s
    raise ValueError(tag)


def test_text(c, key, detail, xfail, extra=(), tags=None, note=""):
    paths = {"sel": ["sel_e", "sel_r", "sel_f"], "grp": ["grp_e", "grp_r", "grp_f"], "desc": ["desc"]}
    tags = tags or paths.get(key[1], ["sel_e", "grp_e", "desc"])
    cc = {**c, "id": "c00000"}
    d, steps = G.case_program(cc, extra)
    keep = []
    for ln in steps.split("\n"):
        if any(f'"{t}"' in ln for t in tags):
            keep.append(ln)
    hdr = ("import Base\nimport ./../../frame.bend as DF\nimport ./lib/dx.bend as DX\nimport ./../../src/dtype.bend as D\n"
           "import ./../../src/err.bend as E\nimport ./../../src/column.bend as C\nimport ./../../src/plan.bend as P\n")
    prog = hdr + G.LZ_DEFS.replace("LZ.", "") + "\n" + d + "\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(
        ln.replace("LZ.raw", "lz_raw").replace("LZ.full", "lz_full") for ln in keep) + "\n"
    exp = ""
    for t in tags:
        exp += f"-- c00000 {t}\n" + expected(cc, t, extra) + "\n"
    head = (f"#! xfail {xfail}\n" if xfail else "") + (
        "# T2.3 regression (bench/diff/reduce_regress.py, minimised by reduce.py --shrink): expectation = the contract\n"
        f"# (reduce_ref.py step model, DESIGN.md 15.5.3 / 15.5.4), never Bend's output. Kind: {key[0]} {key[1]} {key[2]}\n"
        + (f"# {detail}\n" if detail else "") + "".join(f"# {ln}\n" for ln in note.split("\n") if ln) + "#\n")
    return head + prog + "\n" + "".join(f"#|{ln}\n" for ln in exp.rstrip("\n").split("\n"))


def next_number():
    nums = [int(p.stem[1:]) for p in TESTS.glob("r[0-9][0-9][0-9][0-9].bend")]
    return max(nums, default=0) + 1


def run(cases, findings, scratch: Path, extra, args):
    byid = {c["id"]: c for c in cases}
    groups = collections.defaultdict(list)
    for f in findings:
        if f["kind"] in SHRINK_KINDS and f["id"] in byid:
            groups[(f["kind"], f["path"], f["q"])].append(f)
    k = 0
    for key, fs in sorted(groups.items()):
        c0 = min((byid[f["id"]] for f in fs), key=lambda c: c["n"])
        print(f"\nshrinking {key}: {len(fs)} findings; smallest case {c0['id']} n={c0['n']}")
        small = ddmin(c0, key, scratch, extra)
        print(f"  -> {small['n']} rows: bits {[hex(b) for b in small['bits']]} valid {small['valid']} keys {small['keys']}")
        k += 1
        if args.write:
            xf = getattr(args, "xfail", None) or f"NEW-T23-{k}"
            path = TESTS / f"r{next_number():04d}.bend"
            detail = next((f["detail"] for f in fs if f["id"] == c0["id"]), "")
            path.write_text(test_text(small, key, detail, xf, extra))
            print(f"  wrote {path} (xfail {xf})")
