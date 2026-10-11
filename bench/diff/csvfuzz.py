"""W6.4: CSV fuzz harness, the v0.2 reader against the v0.1 reader (plans/M_02.txt W6, DESIGN.md 17.6).

    make csv-fuzz SEED=1 N=1000              # cd bench && uv run python diff/csvfuzz.py --seed 1 --n 1000
    make csv-fuzz-smoke                      # fixed seed, small N, strict
    python3 bench/diff/csvfuzz.py --seed 1 --n 200 --show c000017     # print both readers' full texts

Each case (bench/diff/csvgen.py: a file plus a read spec: header flag, explicit dtypes or inference with
infer_rows, Str storage rule, separator, row cap) is written to build/csvfuzz/seed<SEED>/ and read by the
native runner build/csvfuzz/runner (bench/diff/csvfuzz.bend) with the v0.1 reader (Csv.read_full, the
reference) and with the v0.2 reader (Csv.read_v02_full) at piece sizes 1, 2, 3, 7, 64, 4096 and 245760
(the default). The comparison is EXACT: DF.dump (values, validity, F32 bits, string contents, column names,
dtypes, order, error text and line) plus the Str storage (Raw, or Dictionary with its size and a hash of
its codes). Cases are run in batches in parallel native processes; a batch that crashes or times out is
rerun case by case. Every failure is shrunk (lines, then bytes, then the spec) to a minimal file and
written to build/csvfuzz/seed<SEED>/failures.json (hex of the file, spec, piece, both texts). Exit status
1 on any failure (difference, crash, timeout), else 0. There is no allowlist.

Counts are reported per generator tag (the features of csvgen.py's docstring) and per outcome of the v0.1
reader (a frame, or the error kind with its text normalised), so that a run shows what it covered.
"""
from __future__ import annotations

import argparse
import collections
import concurrent.futures as cf
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import csvgen as G  # noqa: E402

ROOT = Path(G.ROOT)
BEND = os.environ.get("BEND", str(Path.home() / ".bend/bin/bend"))
RUNNER_SRC = ROOT / "bench/diff/csvfuzz.bend"
RUNNER = ROOT / "build/csvfuzz/runner"
LINE = re.compile(r"^(c\w+|s\w+): (ok|DIFF) (.*)$")


def runner_inputs():
    files = [RUNNER_SRC, ROOT / "frame.bend", ROOT / "tests/lib/v02cmp.bend", ROOT / "bench/w6/hx.bend", ROOT / "bench/w6/cmp.bend"]
    files += sorted((ROOT / "src").glob("*.bend"))
    return files


def build_runner(force=False):
    RUNNER.parent.mkdir(parents=True, exist_ok=True)
    if not force and RUNNER.exists() and RUNNER.stat().st_mtime >= max(p.stat().st_mtime for p in runner_inputs()):
        return
    t = time.time()
    r = subprocess.run([BEND, str(RUNNER_SRC), "-o", str(RUNNER)], capture_output=True, text=True, cwd=ROOT)
    if r.returncode != 0 or not RUNNER.exists():
        sys.exit("csvfuzz: cannot build the runner:\n" + r.stdout + r.stderr)
    print(f"runner built in {time.time() - t:.1f}s")


def run_manifest(lines, tag, workdir, timeout):
    """run one manifest through the runner: ({id: (status, text)}, raw output, exit code or 'timeout')"""
    workdir.mkdir(parents=True, exist_ok=True)
    mp = workdir / f"{tag}.manifest"
    mp.write_text("\n".join(lines) + "\n")
    try:
        r = subprocess.run([str(RUNNER), str(mp)], capture_output=True, text=True, errors="replace", timeout=timeout, cwd=ROOT, stdin=subprocess.DEVNULL)
        out, code = r.stdout + r.stderr, r.returncode
    except subprocess.TimeoutExpired as e:
        out = (e.stdout.decode("utf-8", "replace") if isinstance(e.stdout, bytes) else (e.stdout or "")) + (e.stderr.decode("utf-8", "replace") if isinstance(e.stderr, bytes) else (e.stderr or ""))
        code = "timeout"
    res = {}
    for ln in out.splitlines():
        m = LINE.match(ln)
        if m:
            res[m.group(1)] = (m.group(2), m.group(3))
    return res, out, code


def run_cases(items, workdir, tag, timeout=300, per_case_timeout=120):
    """items: [(id, path, spec, pieces)] -> {id: (status, text)}; status ok | DIFF | crash | timeout"""
    lines = [G.manifest_line(i, p, s, pcs) for i, p, s, pcs in items]
    res, out, code = run_manifest(lines, tag, workdir, timeout)
    missing = [it for it in items if it[0] not in res]
    if missing and (code != 0 or len(missing) < len(items)):
        # a crash or timeout lost the rest of the batch: one process per missing case
        for n, it in enumerate(missing):
            r1, o1, c1 = run_manifest([G.manifest_line(*[it[0], it[1], it[2], it[3]])], f"{tag}.one{n}", workdir, per_case_timeout)
            if it[0] in r1:
                res[it[0]] = r1[it[0]]
            else:
                res[it[0]] = ("timeout" if c1 == "timeout" else "crash", f"exit {c1}: " + o1.strip()[-300:])
    for it in items:
        res.setdefault(it[0], ("crash", f"no output (exit {code}): " + out.strip()[-300:]))
    return res


def norm_outcome(text: str) -> str:
    t = text.strip()
    if t.startswith("frame"):
        m = re.search(r"height (\d+)", t)
        return "frame" + (" (0 rows)" if m and m.group(1) == "0" else "")
    t = re.sub(r'"[^"]*"', '"..."', t)
    t = re.sub(r"\[[^\]]*\]", "[...]", t)
    t = re.sub(r"\d+", "#", t)
    return t[:90]


def parse_diff_piece(text: str):
    m = re.search(r"piece (\d+):", text)
    return int(m.group(1)) if m else None


# ---------------------------------------------------------------------------------------------------------------
# shrinking

class Shrinker:
    def __init__(self, workdir: Path, jobs: int, budget: float, per_case_timeout=120):
        self.dir = workdir
        workdir.mkdir(parents=True, exist_ok=True)
        self.jobs = jobs
        self.budget = budget
        self.n = 0
        self.t0 = time.time()
        self.timeout = per_case_timeout

    def left(self):
        return self.budget - (time.time() - self.t0)

    def test_many(self, cands, spec, piece):
        """cands: [bytes] under spec at one piece -> [fails?]; one batch per job"""
        items = []
        for data in cands:
            self.n += 1
            cid = f"s{self.n:07d}"
            p = self.dir / f"{cid}.csv"
            p.write_bytes(data)
            items.append((cid, os.path.relpath(p, ROOT), spec, [piece]))
        out = {}
        per = max(1, (len(items) + self.jobs - 1) // self.jobs)
        chunks = [items[i:i + per] for i in range(0, len(items), per)]
        with cf.ThreadPoolExecutor(self.jobs) as ex:
            futs = [ex.submit(run_cases, ch, self.dir, f"sh{self.n}_{k}", 120, self.timeout) for k, ch in enumerate(chunks)]
            for f in futs:
                out.update(f.result())
        res = [out[it[0]][0] in ("DIFF", "crash", "timeout") for it in items]
        for it in items:
            try:
                os.remove(ROOT / it[1])
            except OSError:
                pass
        return res

    def fails(self, data, spec, piece):
        return self.test_many([data], spec, piece)[0]

    def spec_variants(self, spec, piece):
        v = []
        base = dict(spec)

        def add(**kw):
            s = dict(base)
            s.update(kw)
            if s != base:
                v.append(s)
        add(cap=G.DEFAULT_CAP)
        add(enc="A")
        add(enc="R")
        add(enc="D")
        add(inf=100)
        add(inf=0)
        add(hdr=1 - base["hdr"])
        add(sep=44)
        add(schema="-")
        sch = base["schema"]
        if sch != "-":
            add(schema="S" * len(sch))
            for i in range(len(sch)):
                if len(sch) > 1:
                    add(schema=sch[:i] + sch[i + 1:])
            for i, ch in enumerate(sch):
                if ch != "S":
                    add(schema=sch[:i] + "S" + sch[i + 1:])
        return v

    def shrink(self, data, spec, piece):
        spec = dict(spec)
        # the smallest piece that still fails is the best repro
        for p in (1, 2, 3, 7):
            if p < piece and self.left() > 0 and self.fails(data, spec, p):
                piece = p
                break
        changed = True
        rounds = 0
        while changed and self.left() > 0 and rounds < 40:
            changed = False
            rounds += 1
            # spec first (cheap), then lines, then bytes
            vs = self.spec_variants(spec, piece)
            if vs:
                # all variants in parallel (the specs differ per item)
                res = self.test_variants(data, vs, piece)
                for s, f in zip(vs, res):
                    if f:
                        spec = s
                        changed = True
                        break
            for unit in ("lines", "bytes"):
                n = self.reduce(data, spec, piece, unit)
                if n != data:
                    data = n
                    changed = True
        return data, spec, piece

    def test_variants(self, data, specs, piece):
        items = []
        for s in specs:
            self.n += 1
            cid = f"s{self.n:07d}"
            p = self.dir / f"{cid}.csv"
            p.write_bytes(data)
            items.append((cid, os.path.relpath(p, ROOT), s, [piece]))
        out = {}
        per = max(1, (len(items) + self.jobs - 1) // self.jobs)
        chunks = [items[i:i + per] for i in range(0, len(items), per)]
        with cf.ThreadPoolExecutor(self.jobs) as ex:
            futs = [ex.submit(run_cases, ch, self.dir, f"sv{self.n}_{k}", 120, self.timeout) for k, ch in enumerate(chunks)]
            for f in futs:
                out.update(f.result())
        for it in items:
            try:
                os.remove(ROOT / it[1])
            except OSError:
                pass
        return [out[it[0]][0] in ("DIFF", "crash", "timeout") for it in items]

    def units(self, data, unit):
        if unit == "bytes":
            return [data[i:i + 1] for i in range(len(data))]
        out, cur = [], b""
        for i in range(len(data)):
            cur += data[i:i + 1]
            if data[i:i + 1] == b"\n":
                out.append(cur)
                cur = b""
        if cur:
            out.append(cur)
        return out

    def reduce(self, data, spec, piece, unit):
        """delta debugging over units; candidates are tested in parallel batches, the smallest failing wins"""
        us = self.units(data, unit)
        chunk = max(1, len(us) // 2)
        while chunk >= 1 and self.left() > 0 and len(us) > 0:
            starts = list(range(0, len(us), chunk))
            if len(starts) > 96:
                step = len(starts) / 96.0
                starts = [starts[int(i * step)] for i in range(96)]
            cands = [b"".join(us[:s] + us[s + chunk:]) for s in starts]
            res = self.test_many(cands, spec, piece)
            best = None
            for s, c, f in zip(starts, cands, res):
                if f and (best is None or len(c) < len(best[1])):
                    best = (s, c)
            if best is not None:
                us = us[:best[0]] + us[best[0] + chunk:]
                if not us:
                    break
                continue
            if chunk == 1:
                break
            chunk = max(1, chunk // 2)
        return b"".join(us)


def show_case(data: bytes, spec: dict, piece: int, workdir: Path, tag="show"):
    workdir.mkdir(parents=True, exist_ok=True)
    p = workdir / f"{tag}.csv"
    p.write_bytes(data)
    mp = workdir / f"{tag}.manifest"
    mp.write_text(G.manifest_line(tag.replace("-", "x"), os.path.relpath(p, ROOT), spec, [piece]) + "\n")
    r = subprocess.run([str(RUNNER), str(mp), "show"], capture_output=True, text=True, errors="replace", timeout=300, cwd=ROOT, stdin=subprocess.DEVNULL)
    return r.stdout + r.stderr


# ---------------------------------------------------------------------------------------------------------------

def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--n", type=int, default=1000)
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--jobs", type=int, default=min(8, os.cpu_count() or 4))
    ap.add_argument("--batch", type=int, default=100, help="cases per runner process")
    ap.add_argument("--no-shrink", action="store_true")
    ap.add_argument("--shrink-secs", type=float, default=120.0, help="budget per failure")
    ap.add_argument("--max-shrink", type=int, default=8, help="shrink at most this many failures (the others are listed unshrunk)")
    ap.add_argument("--keep", action="store_true", help="keep the case files of passing batches")
    ap.add_argument("--rebuild", action="store_true", help="rebuild the native runner")
    ap.add_argument("--runner", help="a prebuilt runner binary (csvfuzz_mut.py runs mutants of src/ this way); no rebuild")
    ap.add_argument("--show", metavar="ID", help="print the full v0.1 and v0.2 texts of one generated case (first piece of --pieces)")
    ap.add_argument("--pieces", default=",".join(str(p) for p in G.PIECES))
    ap.add_argument("--out")
    ap.add_argument("--scratch", help="work directory (default build/csvfuzz/seed<SEED>); case files must live under the repository root")
    ap.add_argument("--strict", action="store_true", help="accepted for symmetry with make diff-smoke: any failure always exits 1")
    a = ap.parse_args(argv)
    pieces = [int(x) for x in a.pieces.split(",")]
    if a.runner:
        global RUNNER
        RUNNER = Path(a.runner).resolve()
    else:
        build_runner(a.rebuild)
    scratch = Path(a.scratch).resolve() if a.scratch else ROOT / f"build/csvfuzz/seed{a.seed}"
    scratch.mkdir(parents=True, exist_ok=True)
    out_json = Path(a.out) if a.out else scratch / "failures.json"

    if a.show:
        idx = int(a.show.lstrip("c"))
        c = G.gen_case(a.seed, idx)
        print(c.spec(), c.tags)
        print(show_case(c.data, c.spec(), pieces[0], scratch, "show"))
        return 0

    t0 = time.time()
    idxs = list(range(a.start, a.start + a.n))
    tagc = collections.Counter()
    outc = collections.Counter()
    cross = collections.Counter()
    failures = []
    nruns = 0
    nbytes = 0
    done = 0

    def work(bi, chunk):
        d = scratch / f"b{bi:05d}"
        d.mkdir(parents=True, exist_ok=True)
        items, cases = [], {}
        for i in chunk:
            c = G.gen_case(a.seed, i)
            p = d / f"{c.id}.csv"
            p.write_bytes(c.data)
            items.append((c.id, os.path.relpath(p, ROOT), c.spec(), c.pieces or pieces))
            cases[c.id] = c
        res = run_cases(items, d, "run")
        return d, cases, res

    batches = [idxs[i:i + a.batch] for i in range(0, len(idxs), a.batch)]
    with cf.ThreadPoolExecutor(a.jobs) as ex:
        futs = [ex.submit(work, bi, ch) for bi, ch in enumerate(batches)]
        for fu in cf.as_completed(futs):
            d, cases, res = fu.result()
            bad = False
            for cid, c in cases.items():
                st, text = res[cid]
                nbytes += len(c.data)
                for t in c.tags:
                    tagc[t] += 1
                if st == "ok":
                    m = re.match(r"(\d+) \| (.*)$", text)
                    nruns += int(m.group(1)) if m else 0
                    o = norm_outcome(m.group(2)) if m else "?"
                    outc[o] += 1
                    for t in c.tags:
                        if t in ("ragged_short", "ragged_long", "mal_unterminated", "mal_midquote", "mal_afterclose", "mal_crafter", "bad_cell", "competing", "late", "invalid_utf8", "empty", "header_only"):
                            cross[(t, o.split(":")[0][:40])] += 1
                else:
                    bad = True
                    failures.append({"id": cid, "status": st, "text": text, "case": c})
            done += len(cases)
            if not bad and not a.keep:
                for f in d.glob("*.csv"):
                    f.unlink()
            sys.stdout.write(f"\r{done}/{len(idxs)} cases, {len(failures)} failing, {time.time() - t0:.0f}s ")
            sys.stdout.flush()
    print()
    t_run = time.time() - t0

    # ---- shrink
    records = []
    t1 = time.time()
    failures.sort(key=lambda f: f["id"])
    seen = {}
    for n, f in enumerate(failures):
        c = f["case"]
        piece = parse_diff_piece(f["text"]) or pieces[0]
        rec = {"id": f["id"], "status": f["status"], "first_difference": f["text"][:400], "piece": piece, "spec": c.spec(), "tags": c.tags, "file_hex": c.data.hex(), "file_len": len(c.data)}
        if not a.no_shrink and n < a.max_shrink and f["status"] == "DIFF":
            sh = Shrinker(scratch / "shrink", a.jobs, a.shrink_secs)
            data, spec, piece = sh.shrink(c.data, c.spec(), piece)
            rec.update({"shrunk_hex": data.hex(), "shrunk_len": len(data), "shrunk_spec": spec, "shrunk_piece": piece, "shrunk_file_repr": repr(data)})
            txt = show_case(data, spec, piece, scratch / "shrink", "min-" + f["id"])
            rec["shrunk_texts"] = txt[:3000]
            key = hashlib.sha1(data + json.dumps(spec, sort_keys=True).encode()).hexdigest()[:10]
            rec["group"] = key
            seen.setdefault(key, []).append(f["id"])
        records.append(rec)
    t_shrink = time.time() - t1

    # ---- report
    kinds = collections.Counter(r["status"] for r in records)
    summary = {
        "seed": a.seed, "n": a.n, "start": a.start, "pieces": pieces, "runs_compared": nruns,
        "failing_cases": len(failures), "by_status": dict(kinds), "bytes": nbytes,
        "runtime_s": {"run": round(t_run, 1), "shrink": round(t_shrink, 1), "total": round(time.time() - t0, 1)},
        "groups": {k: v for k, v in seen.items()},
    }
    out_json.write_text(json.dumps({"summary": summary, "tags": dict(tagc), "outcomes": dict(outc), "failures": records}, indent=1))
    print(json.dumps(summary, indent=1))
    print("coverage by generator tag:")
    line = []
    for t, v in sorted(tagc.items()):
        line.append(f"{t}={v}")
    print("  " + " ".join(line))
    print("outcome of the v0.1 reader (the reference), cases:")
    for o, v in outc.most_common():
        print(f"  {v:6d}  {o}")
    print("error-injecting tags x outcome:")
    for (t, o), v in sorted(cross.items()):
        print(f"  {t:18s} {o:60s} {v}")
    if failures:
        print(f"FAIL: {len(failures)} failing case(s), report: {out_json}")
        for r in records:
            print(f"  {r['id']} {r['status']} piece {r['piece']}: {r['first_difference'][:160]}")
            if "shrunk_file_repr" in r:
                print(f"    minimal: spec {r['shrunk_spec']} piece {r['shrunk_piece']} file {r['shrunk_file_repr'][:200]}")
        return 1
    print(f"ok: {len(idxs)} cases x {len(pieces)} pieces, {nruns} reads compared, {time.time() - t0:.0f}s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
