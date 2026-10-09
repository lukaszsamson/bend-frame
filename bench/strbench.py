"""M4 string-experiment runner (plans/M_01.txt section 5): build/strbench and build/bench over a
matrix, ONE measurement per process, the storages interleaved within each repetition (A/B/C,
order rotated per repetition) so a load change hits all of them alike. Every run records the
1-minute load average and the peak RSS (/usr/bin/time -l). Results: JSON lines.

  uv run --project bench python bench/strbench.py ops   --files short_8_1000000 ... --ops parse sort ...
  uv run --project bench python bench/strbench.py q     --sizes 1000000 --queries q1 q3 ...
  uv run --project bench python bench/strbench.py table results.jsonl   # medians, spread, ratios
  uv run --project bench python bench/strbench.py table --wide results.jsonl   # storages side by side
  uv run --project bench python bench/strbench.py pivot --enc auto ops.jsonl   # data x op speed-ups
Common: --encs raw dict auto  --threads 1 12  --reps 5  --out bench/results/m4/xxx.jsonl
q / scan also take the enc "master": build/bench_master / build/scanbench_master, built from the
master branch before M4 (bench/m4.sh MASTER=<tree>), to separate the reader's effect (master vs
raw) from the dictionary's (raw vs dict / auto). q with the query "parse" times the read itself.
"""
import argparse
import json
import os
import re
import statistics
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def load1() -> float:
    return os.getloadavg()[0]


def run(cmd, env_extra):
    env = dict(os.environ)
    env.update(env_extra)
    t = time.time()
    p = subprocess.run(["/usr/bin/time", "-l"] + cmd, cwd=ROOT, env=env, capture_output=True, text=True)
    wall = time.time() - t
    rss = None
    m = re.search(r"(\d+)\s+maximum resident set size", p.stderr)
    if m:
        rss = int(m.group(1))
    line = next((l for l in p.stdout.splitlines() if l.startswith("{")), None)
    rec = json.loads(line) if line else {"error": (p.stdout + p.stderr)[-300:]}
    rec["rss"] = rss
    rec["wall"] = round(wall, 3)
    return rec


def thr_args(t):
    return [] if t == "default" else ["--threads", str(t)]


def ops_mode(a):
    out = open(a.out, "a")
    for f in a.files:
        csv = f"bench/data/str/{f}.csv"
        dim = f"bench/data/str/dim_{f}.csv"
        for op in a.ops:
            for th in a.threads:
                for rep in range(a.reps):
                    encs = a.encs[rep % len(a.encs):] + a.encs[:rep % len(a.encs)]
                    for e in encs:
                        cmd = [f"./{a.bin}/strbench"] + thr_args(th) + [csv, op, e] + ([dim] if op == "join" else [])
                        l0 = load1()
                        rec = run(cmd, {})
                        rec.update({"file": f, "threads": th, "rep": rep, "load1": l0})
                        out.write(json.dumps(rec) + "\n")
                        out.flush()
                        print(f"{f} {op} {e} t={th} rep={rep}: {rec.get('ms')} ms (parse {rec.get('parse_ms')}) rss={rec['rss']} load={l0:.1f}", flush=True)


def q_mode(a):
    out = open(a.out, "a")
    for n in a.sizes:
        csv = f"bench/data/sales_{n}.csv"
        for q in a.queries:
            for th in a.threads:
                for rep in range(a.reps):
                    encs = a.encs[rep % len(a.encs):] + a.encs[:rep % len(a.encs)]
                    for e in encs:
                        batch = "1"
                        if int(n) <= 1000:
                            batch = "40"
                        if a.batch:
                            batch = str(a.batch)
                        # "master": build/bench_master, bench/main.bend built from master (the
                        # pre-M4 whole-file reader, Raw strings); BF_STR does not reach it
                        exe = f"./{a.bin}/bench_master" if e == "master" else f"./{a.bin}/bench"
                        cmd = [exe] + thr_args(th) + [csv, q, "1", batch, str(th)]
                        l0 = load1()
                        rec = run(cmd, {"BF_STR": e})
                        rec.update({"enc": e, "n": int(n), "q": q, "threads": th, "rep": rep, "load1": l0, "batch": int(batch)})
                        out.write(json.dumps(rec) + "\n")
                        out.flush()
                        print(f"{q} n={n} {e} t={th} rep={rep}: {rec.get('seconds')} s rss={rec['rss']} load={l0:.1f}", flush=True)


def scan_mode(a):
    out = open(a.out, "a")
    for n in a.sizes:
        csv = f"bench/data/sales_{n}.csv"
        for q in a.queries:
            for th in a.threads:
                for rep in range(a.reps):
                    encs = a.encs[rep % len(a.encs):] + a.encs[:rep % len(a.encs)]
                    for e in encs:
                        cmd = [f"./{a.bin}/scanbench_{e}"] + thr_args(th) + [csv, q]
                        l0 = load1()
                        rec = run(cmd, {})
                        rec.update({"enc": e, "n": int(n), "q": "scan+" + q, "threads": th, "rep": rep, "load1": l0})
                        out.write(json.dumps(rec) + "\n")
                        out.flush()
                        print(f"scan {q} n={n} {e} t={th} rep={rep}: {rec.get('ms')} ms rss={rec['rss']} load={l0:.1f}", flush=True)


def med(xs):
    return statistics.median(xs) if xs else None


def table_mode(a):
    recs = [json.loads(l) for p in a.files for l in open(p) if l.strip()]
    groups = {}
    for r in recs:
        if "error" in r:
            print("ERROR", r)
            continue
        if "op" in r:
            key = (r["file"], r["op"], r["threads"])
            val = r["ms"]
        elif str(r.get("q", "")).startswith("scan+"):
            key = (f"sales_{r['n']}", r["q"], r["threads"])
            val = r["ms"]
        elif r.get("query") == "parse":
            key = (f"sales_{r['n']}", "parse", r["threads"])
            val = r["read_ms"] + r["first_walk_ms"]
        else:
            key = (f"sales_{r['n']}", r["q"], r["threads"])
            val = r["seconds"] * 1000
        groups.setdefault(key, {}).setdefault(r["enc"], []).append((val, r.get("rss"), r.get("load1")))
    if a.wide:
        return wide_table(groups)
    print("| data | op | threads | enc | median ms | min-max ms | n | peak RSS MB (median) | load (median) | x vs raw |")
    print("|---|---|---|---|---:|---:|---:|---:|---:|---:|")
    for key in sorted(groups):
        g = groups[key]
        base = med([v for v, _, _ in g.get("raw", [])])
        for e in ("master", "raw", "dict", "auto"):
            if e not in g:
                continue
            vs = [v for v, _, _ in g[e]]
            rss = med([r for _, r, _ in g[e] if r])
            ld = med([l for _, _, l in g[e] if l is not None])
            m = med(vs)
            ratio = (base / m) if (base and m) else None
            print(f"| {key[0]} | {key[1]} | {key[2]} | {e} | {m:.1f} | {min(vs):.0f}-{max(vs):.0f} | {len(vs)} | {rss / 1e6 if rss else 0:.0f} | {ld:.1f} | {('%.2fx' % ratio) if ratio else '-'} |")


def wide_table(groups):
    """One row per (data, op, threads): each storage's median ms [min-max], the speed-up of
    auto and dict over raw (raw median / median), master over raw for the reader's effect
    (raw median / master median: above 1x the branch's Raw is faster), each storage's peak RSS
    (MB, median, /usr/bin/time -l) and the median 1-minute load of the cell's runs."""
    encs = [e for e in ("master", "raw", "auto", "dict") if any(e in g for g in groups.values())]
    hdr = ["data", "op", "thr"] + [f"{e} ms" for e in encs] + ["auto x", "dict x"]
    if "master" in encs:
        hdr.append("raw vs master")
    hdr += ["peak RSS MB " + "/".join(encs), "load"]
    print("| " + " | ".join(hdr) + " |")
    print("|" + "---|" * 3 + "---:|" * (len(hdr) - 3))
    for key in sorted(groups, key=lambda k: (k[0], k[1], str(k[2]))):
        g = groups[key]
        cells = [key[0], key[1], "1" if key[2] == "1" else "12"]
        m = {}
        for e in encs:
            vs = [v for v, _, _ in g.get(e, [])]
            if vs:
                m[e] = med(vs)
                f = ".0f" if m[e] >= 10 else (".1f" if m[e] >= 1 else ".2f")
                cells.append(f"{m[e]:{f}} [{min(vs):{f}}-{max(vs):{f}}]")
            else:
                cells.append("-")
        def x(a, b):
            return f"{m[a] / m[b]:.2f}x" if a in m and b in m and m[b] > 0 else "-"
        cells += [x("raw", "auto"), x("raw", "dict")]
        if "master" in encs:
            cells.append(x("master", "raw"))
        rss = [med([r for _, r, _ in g.get(e, []) if r]) for e in encs]
        cells.append("/".join(f"{r / 1e6:.0f}" if r else "-" for r in rss))
        cells.append(f"{med([l for e in g for _, _, l in g[e] if l is not None]):.1f}")
        print("| " + " | ".join(cells) + " |")


def pivot_table(a):
    """One row per (data, threads), one column per op: raw median / <a.enc> median (above 1x the
    storage is faster); the raw median in ms under it in brackets."""
    recs = [json.loads(l) for p in a.files for l in open(p) if l.strip()]
    vals = {}
    ops = []
    for r in recs:
        if "error" in r or "op" not in r:
            continue
        if r["op"] not in ops:
            ops.append(r["op"])
        vals.setdefault((r["file"], r["threads"]), {}).setdefault(r["op"], {}).setdefault(r["enc"], []).append(r["ms"])
    print("| data | thr | " + " | ".join(ops) + " |")
    print("|---|---|" + "---:|" * len(ops))
    for key in sorted(vals, key=lambda k: (k[0], str(k[1]))):
        cells = [key[0], "1" if key[1] == "1" else "12"]
        for op in ops:
            g = vals[key].get(op, {})
            raw, e = med(g.get("raw", [])), med(g.get(a.enc, []))
            if raw is None or e is None:
                cells.append("-")
            elif e == 0 or raw == 0:
                cells.append(f"({raw:.0f}/{e:.0f} ms)")
            else:
                cells.append(f"{raw / e:.2f}x ({raw:.0f})")
        print("| " + " | ".join(cells) + " |")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["ops", "q", "scan", "table", "pivot"])
    ap.add_argument("--enc", default="auto", help="pivot: the storage compared with raw")
    ap.add_argument("files", nargs="*")
    ap.add_argument("--files", dest="files2", nargs="*", default=[])
    ap.add_argument("--ops", nargs="*", default=["parse"])
    ap.add_argument("--sizes", nargs="*", default=["1000000"])
    ap.add_argument("--queries", nargs="*", default=["q1", "q3", "q4", "q5"])
    ap.add_argument("--encs", nargs="*", default=["raw", "dict", "auto"])
    ap.add_argument("--threads", nargs="*", default=["1", "default"])
    ap.add_argument("--reps", type=int, default=5)
    ap.add_argument("--out", default="bench/results/m4/runs.jsonl")
    ap.add_argument("--batch", type=int, default=0, help="q: collects per timed window (default 40 at n <= 1000, else 1)")
    ap.add_argument("--wide", action="store_true", help="table: one row per cell, the storages side by side")
    ap.add_argument("--bin", default="build", help="directory of the binaries (a frozen copy keeps rebuilds out of a run)")
    a = ap.parse_args()
    a.files = a.files + a.files2
    Path(ROOT / a.out).parent.mkdir(parents=True, exist_ok=True)
    a.out = str(ROOT / a.out)
    {"ops": ops_mode, "q": q_mode, "scan": scan_mode, "table": table_mode, "pivot": pivot_table}[a.mode](a)


if __name__ == "__main__":
    main()
