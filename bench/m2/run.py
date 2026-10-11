"""W0 benchmark runner for the v0.2 performance milestone (plans/M_02.txt sections 0 and 5).

  uv run --project bench python bench/m2/run.py build [baseline|candidate|both] [--force]
  uv run --project bench python bench/m2/run.py freeze [--only GLOB ...]       # expected outputs from the BASELINE
  uv run --project bench python bench/m2/run.py run --label NAME [--smoke] [--procs 5] [--threads 1 4 12]
          [--only GLOB ...] [--group G ...] [--modes phases e2e ...] [--binaries baseline candidate]
          [--engine v01] [--resume] [--require-quiet 2] [--timeout S]
  uv run --project bench python bench/m2/run.py summary results/NAME.jsonl [...] [--max-load X] [--raw]
  uv run --project bench python bench/m2/run.py micro --label NAME [--procs 3] [--threads 1 4 12]
  uv run --project bench python bench/m2/run.py list                          # the frozen workload list

Only the standard library is needed (the `uv run` form is the documented one; python3 works too).

A CELL is (binary, workload, mode, threads). `run` executes every cell `--procs` times, each in a FRESH
process, INTERLEAVED: for each workload and mode, repetition by repetition, the (binary, threads)
combinations are visited round-robin with the starting point rotated per repetition (never blocked by
binary or by thread count). One JSONL record per process goes to bench/m2/results/<label>.jsonl:
command, commit + dirty flags + source hashes of src/ and frame.bend, the build info of the binary, bend
version, workload id and input sha256, engine selector, threads, the driver's phase timings, peak RSS
(/usr/bin/time -l; wait4 rusage as a fallback; method recorded), load averages before and after, the
validation against the expected output frozen from the baseline (checked after the clock), timestamp.
Gate numbers are accepted only from a quiet pre-run machine (README: acceptance rules); nothing here
rejects a sample after seeing it: invalid RESULTS (wrong hash) are flagged, slow samples are kept.
"""
import argparse
import datetime
import fnmatch
import hashlib
import json
import os
import platform
import re
import statistics
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))
import workloads as WL  # noqa: E402

BEND = os.path.expanduser(os.environ.get("BEND", "~/.bend/bin/bend"))
BUILD = ROOT / "build" / "m2"
BIN = {"baseline": BUILD / "baseline" / "driver", "candidate": BUILD / "candidate" / "driver"}
RESULTS = HERE / "results"
EXPECTED = HERE / "expected.json"
INPUTS = HERE / "inputs.json"
BASELINE_COMMIT = "3612482"


# ---------------------------------------------------------------------------------------------
# environment, hashing, git
# ---------------------------------------------------------------------------------------------

def sh(cmd, cwd=ROOT, timeout=60):
    try:
        p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
        return p.stdout.strip() if p.returncode == 0 else None
    except Exception:
        return None


def sha256_file(path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def src_hash(root: Path) -> str:
    """sha256 over (relative path, content sha256) of frame.bend and src/**/*.bend under root."""
    h = hashlib.sha256()
    files = [root / "frame.bend"] + sorted((root / "src").rglob("*.bend"))
    for f in files:
        h.update(str(f.relative_to(root)).encode() + b"\0" + sha256_file(f).encode() + b"\n")
    return h.hexdigest()


def git_info() -> dict:
    head = sh(["git", "rev-parse", "HEAD"])
    status = sh(["git", "status", "--porcelain"]) or ""
    lines = [l for l in status.splitlines() if not l[3:].startswith(("build/", "bench/m2/results/"))]
    src = [l for l in lines if l[3:].startswith(("src/", "frame.bend", "bench/m2/driver.bend"))]
    return {"head": head, "dirty": bool(lines), "dirty_src": bool(src),
            "src_hash": src_hash(ROOT), "driver_hash": sha256_file(HERE / "driver.bend")}


def build_info(which: str):
    p = BUILD / which / "BUILD.json"
    return json.loads(p.read_text()) if p.exists() else None


def bend_version() -> str:
    return sh([BEND, "version"]) or "unknown"


def loadavg():
    try:
        return [round(x, 2) for x in os.getloadavg()]
    except OSError:
        return None


def now_iso():
    return datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")


def top_cpu(n=6):
    out = sh(["ps", "-Ao", "pcpu=,pid=,comm=", "-r"])
    return out.splitlines()[:n] if out else []


# ---------------------------------------------------------------------------------------------
# build
# ---------------------------------------------------------------------------------------------

def cmd_build(a):
    which = ["baseline", "candidate"] if a.which == "both" else [a.which]
    for w in which:
        if w == "baseline":
            args = ["bash", str(HERE / "baseline.sh")] + (["--force"] if a.force else [])
        else:
            args = ["bash", str(HERE / "baseline.sh"), "--candidate"] + (["--force"] if a.force else [])
        rc = subprocess.call(args, cwd=ROOT)
        if rc != 0:
            sys.exit(rc)


def check_binaries(binaries, allow_stale):
    gi = git_info()
    for b in binaries:
        if not BIN[b].exists():
            sys.exit(f"missing {BIN[b]}: run `make m2-baseline` (baseline) / `run.py build candidate`")
        bi = build_info(b)
        if bi is None:
            print(f"warning: no BUILD.json for {b}", file=sys.stderr)
            continue
        if b == "candidate" and (bi.get("src_hash") != gi["src_hash"] or bi.get("driver_hash") != gi["driver_hash"]):
            msg = (f"candidate binary is STALE: built from src hash {str(bi.get('src_hash'))[:12]}, checkout is "
                   f"{gi['src_hash'][:12]} (driver {str(bi.get('driver_hash'))[:12]} vs {gi['driver_hash'][:12]})")
            if allow_stale:
                print("warning: " + msg, file=sys.stderr)
            else:
                sys.exit(msg + "\nrebuild with `python3 bench/m2/run.py build candidate` (or --allow-stale)")
    return gi


# ---------------------------------------------------------------------------------------------
# one process
# ---------------------------------------------------------------------------------------------

_TIME_OK = None


def time_l_ok() -> bool:
    global _TIME_OK
    if _TIME_OK is None:
        try:
            p = subprocess.run(["/usr/bin/time", "-l", "true"], capture_output=True, text=True, timeout=20)
            _TIME_OK = p.returncode == 0 and "maximum resident set size" in p.stderr
        except Exception:
            _TIME_OK = False
    return _TIME_OK


def parse_time_l(stderr: str) -> dict:
    d = {}
    for key, pat in (("rss_bytes", r"(\d+)\s+maximum resident set size"),
                     ("instructions", r"(\d+)\s+instructions retired"),
                     ("cycles", r"(\d+)\s+cycles elapsed"),
                     ("peak_footprint", r"(\d+)\s+peak memory footprint"),
                     ("page_reclaims", r"(\d+)\s+page reclaims"),
                     ("page_faults", r"(\d+)\s+page faults")):
        m = re.search(pat, stderr)
        if m:
            d[key] = int(m.group(1))
    m = re.search(r"([\d.]+)\s+real\s+([\d.]+)\s+user\s+([\d.]+)\s+sys", stderr)
    if m:
        d["real_s"], d["usr_s"], d["sys_s"] = float(m.group(1)), float(m.group(2)), float(m.group(3))
    return d


def run_process(argv, env, timeout):
    """-> dict(rc, stdout, stderr, wall_s, rss_*...)."""
    e = dict(os.environ)
    e.update(env or {})
    t0 = time.time()
    if time_l_ok():
        p = subprocess.run(["/usr/bin/time", "-l"] + argv, cwd=ROOT, env=e, capture_output=True, text=True, timeout=timeout)
        r = {"rc": p.returncode, "stdout": p.stdout, "stderr": p.stderr, "rss_method": "usr_bin_time_l"}
        r.update(parse_time_l(p.stderr))
    else:
        # fallback: the child's own rusage from wait4 (ru_maxrss is bytes on macOS); no instruction counts
        import tempfile
        with tempfile.TemporaryFile("w+") as fo, tempfile.TemporaryFile("w+") as fe:
            pr = subprocess.Popen(argv, cwd=ROOT, env=e, stdout=fo, stderr=fe)
            deadline = time.time() + timeout
            ru = None
            status = None
            while True:
                pid, status, ru = os.wait4(pr.pid, os.WNOHANG)
                if pid:
                    break
                if time.time() > deadline:
                    pr.kill()
                    pid, status, ru = os.wait4(pr.pid, 0)
                    break
                time.sleep(0.02)
            fo.seek(0)
            fe.seek(0)
            r = {"rc": os.waitstatus_to_exitcode(status), "stdout": fo.read(), "stderr": fe.read(),
                 "rss_method": "wait4_rusage"}
            if ru is not None:
                r["rss_bytes"] = int(ru.ru_maxrss)
                r["usr_s"], r["sys_s"] = round(ru.ru_utime, 3), round(ru.ru_stime, 3)
    r["wall_s"] = round(time.time() - t0, 3)
    return r


def last_json(stdout: str):
    for line in reversed(stdout.splitlines()):
        if line.startswith("{"):
            try:
                return json.loads(line)
            except json.JSONDecodeError:
                return None
    return None


def argv_for(w, mode, binary, threads, outp):
    a = [str(BIN[binary])]
    if threads:
        a += ["--threads", str(threads)]
    aux = "-" if w.aux == "-" else str(ROOT / w.aux)
    return a + [mode if mode != "stages" else "stages", w.op, str(ROOT / w.file), aux, str(w.batch), str(w.param), str(outp)]


def load_expected():
    return json.loads(EXPECTED.read_text()) if EXPECTED.exists() else {}


def store_expected(wid, entry):
    """read-modify-write of expected.json under a lock (several `freeze` processes may run at once)"""
    import fcntl
    with open(HERE / ".expected.lock", "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        exp = load_expected()
        exp[wid] = entry
        tmp = EXPECTED.with_suffix(".tmp")
        tmp.write_text(json.dumps(exp, indent=1, sort_keys=True) + "\n")
        os.replace(tmp, EXPECTED)


def validate(w, mode, drv, expected, outp):
    """-> (valid True/False/None, detail)."""
    ex = expected.get(w.id)
    if drv is None:
        return False, {"reason": "no result line"}
    if ex is None:
        return None, {"reason": "no expected output frozen for this workload"}
    if mode == "stages":
        bad = []
        for s in WL.STAGES:
            for k in ("rows", "chk"):
                got = drv.get(f"{s}_{k}")
                want = ex.get("stages", {}).get(f"{s}_{k}")
                if want is None:
                    return None, {"reason": f"stage {s} not frozen"}
                if got != want:
                    bad.append(f"{s}_{k}: {got} != {want}")
        return (not bad), ({"reason": "; ".join(bad)} if bad else {})
    bad = []
    for k in ("chk", "rows"):
        if drv.get(k) != ex.get(k):
            bad.append(f"{k}: {drv.get(k)} != {ex.get(k)}")
    if drv.get("has_dump") and ex.get("has_dump") and drv.get("dump") != ex.get("dump"):
        bad.append(f"dump: {drv.get('dump')} != {ex.get('dump')}")
    if mode == "e2ecsv" and ex.get("csv_sha256"):
        sha = sha256_file(outp) if Path(outp).exists() else None
        if sha != ex["csv_sha256"]:
            bad.append(f"csv sha256 {str(sha)[:12]} != {ex['csv_sha256'][:12]}")
    return (not bad), ({"reason": "; ".join(bad)} if bad else {})


def one(w, mode, binary, threads, rep, a, ctx):
    outp = BUILD / "out" / f"{os.getpid()}_{w.id}_{binary}_{threads}_{rep}.csv"
    outp.parent.mkdir(parents=True, exist_ok=True)
    argv = argv_for(w, mode, binary, threads, outp)
    env = {"BF_ENGINE": a.engine}
    lb = loadavg()
    r = run_process(argv, env, a.timeout)
    la = loadavg()
    drv = last_json(r["stdout"])
    valid, vdetail = validate(w, mode, drv, ctx["expected"], outp) if r["rc"] == 0 else (False, {"reason": f"rc {r['rc']}"})
    if mode == "e2ecsv" and outp.exists():
        outp.unlink()
    err = None
    if drv is None or r["rc"] != 0:
        err = (r["stdout"] + r["stderr"])[-400:]
    rec = {
        "type": "proc", "label": a.label, "ts": now_iso(), "ts_epoch": round(time.time(), 3),
        "binary": binary, "engine": a.engine, "workload": w.id, "group": w.group, "op": w.op, "mode": mode,
        "threads": threads, "rep": rep, "batch": w.batch, "rows_in": w.rows, "key": w.key,
        "command": argv, "env": env,
        "input_sha256": ctx["inputs"].get(w.id, {}),
        "commit": ctx["commit"], "build": ctx["builds"].get(binary), "bend_version": ctx["bend_version"],
        "driver": drv, "rc": r["rc"], "wall_s": r["wall_s"],
        "rss_bytes": r.get("rss_bytes"), "rss_method": r.get("rss_method"),
        "usr_s": r.get("usr_s"), "sys_s": r.get("sys_s"), "real_s": r.get("real_s"),
        "instructions": r.get("instructions"), "cycles": r.get("cycles"), "peak_footprint": r.get("peak_footprint"),
        "page_reclaims": r.get("page_reclaims"), "page_faults": r.get("page_faults"),
        "load_before": lb, "load_after": la,
        "valid": valid, "validation": vdetail, "error": err,
    }
    return rec


def inputs_of(w, hashes):
    d = {}
    for rel in (w.file, w.aux):
        if rel != "-":
            d[rel] = hashes.get(rel) or (sha256_file(ROOT / rel) if (ROOT / rel).exists() else None)
    return d


def check_inputs():
    """The input files must match the frozen hashes (bench/m2/inputs.json)."""
    want = json.loads(INPUTS.read_text()) if INPUTS.exists() else {}
    got = {}
    for rel, sha in want.items():
        f = ROOT / rel
        if not f.exists():
            sys.exit(f"missing input {rel}: run `uv run --project bench python bench/m2/gen.py`")
        got[rel] = sha256_file(f)
        if got[rel] != sha:
            sys.exit(f"input {rel} differs from the frozen sha256 (bench/m2/inputs.json)")
    return got


# ---------------------------------------------------------------------------------------------
# run
# ---------------------------------------------------------------------------------------------

def meta_record(a, gi, ws):
    return {
        "type": "meta", "label": a.label, "ts": now_iso(), "args": {k: v for k, v in vars(a).items() if k != "f"},
        "machine": {"platform": platform.platform(), "model": sh(["sysctl", "-n", "hw.model"]),
                    "ncpu": os.cpu_count(), "memsize": sh(["sysctl", "-n", "hw.memsize"]),
                    "python": sys.version.split()[0]},
        "bend": bend_version(), "commit": gi, "builds": {b: build_info(b) for b in BIN},
        "load": loadavg(), "top_cpu": top_cpu(), "therm": sh(["pmset", "-g", "therm"]),
        "batt": sh(["pmset", "-g", "batt"]), "rss_method": "usr_bin_time_l" if time_l_ok() else "fallback",
        "workloads": [w.id for w in ws], "provisional": bool(a.provisional),
        "notes": a.note,
    }


def modes_for(w, requested):
    if w.op == "stages":
        return ["stages"]
    return [m for m in (requested or list(w.modes)) if m in ("phases", "e2e") or (m == "e2ecsv" and w.csv_ok)]


def cmd_run(a):
    RESULTS.mkdir(parents=True, exist_ok=True)
    ws = WL.select(a.only, a.group, a.smoke)
    if not ws:
        sys.exit("no workload selected")
    binaries = a.binaries
    gi = check_binaries(binaries, a.allow_stale)
    hashes = check_inputs()
    if a.require_quiet is not None:
        deadline = time.time() + a.wait
        while (loadavg() or [0])[0] > a.require_quiet:
            if time.time() > deadline:
                if a.provisional:
                    print(f"warning: load {loadavg()} > {a.require_quiet}: this run is PROVISIONAL (gates not evaluable)",
                          file=sys.stderr)
                    break
                sys.exit(f"machine not quiet: load {loadavg()} > {a.require_quiet}; not a gate run. Wait (--wait S), "
                         f"or run anyway as --provisional")
            time.sleep(10)
    threads = a.threads or ([1, 12] if a.smoke else list(WL.THREADS))
    procs = a.procs if a.procs is not None else (1 if a.smoke else 5)
    out = RESULTS / f"{a.label}.jsonl"
    done = set()
    if out.exists() and a.resume:
        for line in open(out):
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            if r.get("type") == "proc":
                done.add((r["workload"], r["mode"], r["binary"], r["threads"], r["rep"]))
    elif out.exists() and not a.resume:
        sys.exit(f"{out} exists: pick another --label or pass --resume")
    ctx = {"expected": load_expected(), "commit": gi, "bend_version": bend_version(),
           "builds": {b: build_info(b) for b in BIN},
           "inputs": {w.id: inputs_of(w, hashes) for w in ws}}
    f = open(out, "a")
    if not (a.resume and done):
        f.write(json.dumps(meta_record(a, gi, ws)) + "\n")
        f.flush()
    combos = [(b, t) for b in binaries for t in threads]
    total = 0
    for w in ws:
        modes = modes_for(w, a.modes)
        for mode in modes:
            for rep in range(procs):
                k = rep % len(combos)
                for b, t in combos[k:] + combos[:k]:
                    if (w.id, mode, b, t, rep) in done:
                        continue
                    rec = one(w, mode, b, t, rep, a, ctx)
                    f.write(json.dumps(rec) + "\n")
                    f.flush()
                    os.fsync(f.fileno())
                    total += 1
                    ms = metric(rec, "e2e_ms" if mode in ("e2e", "e2ecsv") else ("parse_ms" if w.op == "stages" else w.key))
                    ms = round(ms, 3) if ms is not None else None
                    flag = "" if rec["valid"] else (" INVALID " + json.dumps(rec["validation"]) if rec["valid"] is False else " (unfrozen)")
                    print(f"{w.id:16} {mode:6} {b:9} t={t:<2} rep={rep} {w.key if mode == 'phases' else mode}{'/in' if w.batch > 1 else ''}={ms} "
                          f"rss={(rec['rss_bytes'] or 0) / 1e6:.0f}MB wall={rec['wall_s']}s load={rec['load_before'][0] if rec['load_before'] else '?'}{flag}",
                          flush=True)
    f.close()
    print(f"{total} processes -> {out}")


# ---------------------------------------------------------------------------------------------
# freeze: expected outputs from the BASELINE binary
# ---------------------------------------------------------------------------------------------

def cmd_freeze(a):
    gi = check_binaries(["baseline"], True)
    check_inputs()
    ws = WL.select(a.only, a.group, False)
    if not a.force:
        have = load_expected()
        ws = [w for w in ws if w.id not in have]
    env = {"BF_ENGINE": "v01"}

    def go(w, mode, t, outp=None):
        argv = argv_for(w, mode, "baseline", t, outp or (BUILD / "out" / "freeze.csv"))
        (BUILD / "out").mkdir(parents=True, exist_ok=True)
        r = run_process(argv, env, a.timeout)
        d = last_json(r["stdout"])
        if r["rc"] != 0 or d is None:
            sys.exit(f"freeze: {w.id} {mode} t={t} failed: {(r['stdout'] + r['stderr'])[-300:]}")
        return d

    for w in ws:
        e = {"frozen_from": {"binary": "baseline", "build": build_info("baseline"), "ts": now_iso(),
                             "load": loadavg(), "threads": [1, 12]}}
        if w.op == "stages":
            d1, d12 = go(w, "stages", 1), go(w, "stages", 12)
            st = {}
            for s in WL.STAGES:
                for k in ("rows", "chk"):
                    st[f"{s}_{k}"] = d1[f"{s}_{k}"]
                    if d1[f"{s}_{k}"] != d12[f"{s}_{k}"]:
                        sys.exit(f"freeze: {w.id} stage {s} {k} differs between 1 and 12 threads")
            e["stages"] = st
            store_expected(w.id, e)
            print(f"froze {w.id}", flush=True)
            continue
        d1, d12 = go(w, "phases", 1), go(w, "phases", 12)
        for k in ("chk", "rows", "dump", "has_dump"):
            if d1[k] != d12[k]:
                sys.exit(f"freeze: {w.id} {k} differs between 1 and 12 threads ({d1[k]} vs {d12[k]})")
        e.update({"chk": d1["chk"], "rows": d1["rows"], "has_dump": d1["has_dump"], "dump": d1["dump"]})
        if "e2e" in w.modes:
            de = go(w, "e2e", 1)
            if de["chk"] != d1["chk"] or de["rows"] != d1["rows"]:
                sys.exit(f"freeze: {w.id} e2e result differs from phases")
        if w.csv_ok and not a.no_csv:
            outp = BUILD / "out" / f"freeze_{w.id}.csv"
            dc = go(w, "e2ecsv", 1, outp)
            if dc["chk"] != d1["chk"]:
                sys.exit(f"freeze: {w.id} e2ecsv result differs from phases")
            e["csv_sha256"] = sha256_file(outp)
            e["csv_bytes"] = outp.stat().st_size
            outp.unlink()
        store_expected(w.id, e)
        print(f"froze {w.id}: chk={e['chk']} rows={e['rows']}" + (f" dump={e['dump']}" if e["has_dump"] else "")
              + (f" csv={e['csv_sha256'][:12]}" if "csv_sha256" in e else ""), flush=True)


# ---------------------------------------------------------------------------------------------
# summary
# ---------------------------------------------------------------------------------------------

def read_records(paths):
    recs, metas = [], []
    for p in paths:
        for line in open(p):
            line = line.strip()
            if not line:
                continue
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            (recs if r.get("type") == "proc" else metas).append(r)
    return recs, metas


def metric(r, name):
    d = r.get("driver") or {}
    v = d.get(name)
    if v is None:
        return None
    if name.endswith("_ms") and not any(name.startswith(s) for s in WL.STAGES):
        return v / max(1, r.get("batch") or 1)
    return v


def fmt(x, nd=1):
    if x is None:
        return "-"
    if x >= 1000:
        return f"{x:,.0f}"
    if x >= 100:
        return f"{x:.0f}"
    if x >= 10:
        return f"{x:.1f}"
    return f"{x:.2f}" if x >= 1 else f"{x:.3f}"


def med(xs):
    xs = [x for x in xs if x is not None]
    return statistics.median(xs) if xs else None


def cell_stats(rs, name):
    xs = [metric(r, name) for r in rs]
    xs = [x for x in xs if x is not None]
    if not xs:
        return None
    return {"med": statistics.median(xs), "min": min(xs), "max": max(xs), "n": len(xs), "raw": xs}


def cmd_summary(a):
    recs, metas = read_records(a.files)
    if a.max_load is not None:
        recs = [r for r in recs if (r["load_before"] or [0])[0] <= a.max_load]
    bad = [r for r in recs if r["valid"] is False or r["rc"] != 0]
    ok = [r for r in recs if r["valid"] is not False and r["rc"] == 0 and r.get("driver")]
    cells = {}
    for r in ok:
        cells.setdefault((r["workload"], r["mode"], r["threads"], r["binary"]), []).append(r)
    ids = []
    for r in ok:
        k = (r["workload"], r["mode"])
        if k not in ids:
            ids.append(k)
    order = {w.id: i for i, w in enumerate(WL.WORKLOADS)}
    ids.sort(key=lambda k: (order.get(k[0], 99), k[1]))
    threads = sorted({r["threads"] for r in ok})
    labels = sorted({r["label"] for r in ok})
    print(f"# W0 summary: {', '.join(labels)}")
    print()
    for m in metas:
        print(f"- run `{m['label']}`: {m['ts']}, commit {str(m['commit']['head'])[:10]} dirty={m['commit']['dirty']} "
              f"src {m['commit']['src_hash'][:10]}, bend {m['bend']}, load at start {m['load']}, provisional={m.get('provisional')}")
    allload = [r["load_before"][0] for r in recs if r["load_before"]] + [r["load_after"][0] for r in recs if r["load_after"]]
    if allload:
        print(f"- load (1 min) before/after every process: min {min(allload):.1f} median {statistics.median(allload):.1f} max {max(allload):.1f}")
    print(f"- {len(ok)} valid processes, {len(bad)} invalid/failed" + (f" (load <= {a.max_load})" if a.max_load is not None else ""))
    for r in bad[:20]:
        print(f"  - INVALID {r['workload']} {r['mode']} {r['binary']} t={r['threads']} rep={r['rep']}: {r['validation'].get('reason') or r['error']}")
    print()

    # ---- 1. timings and candidate/baseline ratios
    print("## Timings (ms; median [min..max] n) and candidate/baseline ratio")
    print()
    print("key metric per row: compute_ms (queries), parse_ms (parse), e2e_ms (e2e); ms per input for batched controls")
    print()
    print("| workload | mode | metric | thr | baseline | candidate | ratio c/b | load max |")
    print("|---|---|---|---:|---|---|---:|---:|")
    for wid, mode in ids:
        if mode == "stages":
            continue
        name = "e2e_ms" if mode in ("e2e", "e2ecsv") else WL.BY_ID[wid].key
        for t in threads:
            b = cell_stats(cells.get((wid, mode, t, "baseline"), []), name)
            c = cell_stats(cells.get((wid, mode, t, "candidate"), []), name)
            if not b and not c:
                continue
            ld = max([r["load_before"][0] for k in ("baseline", "candidate") for r in cells.get((wid, mode, t, k), []) if r["load_before"]] or [0])
            ratio = f"{c['med'] / b['med']:.2f}" if (b and c and b["med"]) else "-"
            f1 = lambda s: f"{fmt(s['med'])} [{fmt(s['min'])}..{fmt(s['max'])}] n={s['n']}" if s else "-"
            print(f"| {wid} | {mode} | {name} | {t} | {f1(b)} | {f1(c)} | {ratio} | {ld:.0f} |")
    print()

    # ---- 2. phases (G6)
    print("## Phases (G6): medians in ms per input (parse = read + walk; prep = input-preservation clone; compute; check = output/validation hash)")
    print()
    print("| workload | binary | thr | read | walk | parse | prep | compute | check | compute+check | e2e (e2e mode) | rss MB (phases) | rss MB (e2e) |")
    print("|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for wid, mode in ids:
        if mode != "phases":
            continue
        for bn in ("baseline", "candidate"):
            for t in threads:
                rs = cells.get((wid, "phases", t, bn), [])
                if not rs:
                    continue
                g = lambda n: med([metric(r, n) for r in rs])
                cc = med([(metric(r, "compute_ms") or 0) + (metric(r, "check_ms") or 0) for r in rs])
                es = cells.get((wid, "e2e", t, bn), [])
                e = med([metric(r, "e2e_ms") for r in es])
                rp = med([r["rss_bytes"] for r in rs])
                re_ = med([r["rss_bytes"] for r in es])
                print(f"| {wid} | {bn} | {t} | {fmt(g('read_ms'))} | {fmt(g('walk_ms'))} | {fmt(g('parse_ms'))} | {fmt(g('prep_ms'))} | "
                      f"{fmt(g('compute_ms'))} | {fmt(g('check_ms'))} | {fmt(cc)} | {fmt(e)} | {fmt(rp / 1e6 if rp else None, 0)} | {fmt(re_ / 1e6 if re_ else None, 0)} |")
    print()

    # ---- 3. scaling and serial fraction (G2 feasibility)
    print("## Thread scaling (G2): speedup = median(1 thread) / median(N threads); serial fraction s from Amdahl with N = 12")
    print()
    print("s = (1/S - 1/12) / (1 - 1/12) from the 12-thread speedup S; 1/s is the speedup even infinite parallelism would give at that serial fraction. Today nothing forks, so S ~ 1 (s ~ 1) is expected at the baseline; G2 needs S >= 3 (q1-q6 compute) and >= 4 (parse), i.e. s <= 1/3 (parse: 1/4 is not enough: needs s <= ~0.2).")
    print()
    print("| workload | mode | binary | metric | T1 | T4 | T12 | S4 | S12 | s | 1/s |")
    print("|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|")
    for wid, mode in ids:
        if mode == "stages":
            continue
        name = "e2e_ms" if mode in ("e2e", "e2ecsv") else WL.BY_ID[wid].key
        for bn in ("baseline", "candidate"):
            m = {t: (cell_stats(cells.get((wid, mode, t, bn), []), name) or {}).get("med") for t in (1, 4, 12)}
            if m[1] is None or m[12] is None:
                continue
            s4 = m[1] / m[4] if m[4] else None
            s12 = m[1] / m[12] if m[12] else None
            sf = ((1 / s12 - 1 / 12) / (1 - 1 / 12)) if s12 else None
            print(f"| {wid} | {mode} | {bn} | {name} | {fmt(m[1])} | {fmt(m[4])} | {fmt(m[12])} | "
                  f"{('%.2f' % s4) if s4 else '-'} | {('%.2f' % s12) if s12 else '-'} | {('%.2f' % sf) if sf is not None else '-'} | {('%.1f' % (1 / sf)) if sf and sf > 0 else 'inf'} |")
    print()

    # ---- 4. stages
    st_ids = [wid for wid, mode in ids if mode == "stages"]
    if st_ids:
        print("## Stage breakdown of q1-q6 (eager stages, each alone; medians in ms)")
        print()
        for wid in st_ids:
            for bn in ("baseline", "candidate"):
                rs1 = cells.get((wid, "stages", 1, bn), [])
                if not rs1:
                    continue
                print(f"### {wid}, {bn}")
                print()
                print("| stage | " + " | ".join(f"{t}t ms" for t in threads) + " | share of 1t sum | S12 |")
                print("|---|" + "---:|" * len(threads) + "---:|---:|")
                tot1 = sum((cell_stats(rs1, f"{s}_ms") or {"med": 0})["med"] for s in WL.STAGES)
                for s in WL.STAGES:
                    row = []
                    for t in threads:
                        cs = cell_stats(cells.get((wid, "stages", t, bn), []), f"{s}_ms")
                        row.append(cs["med"] if cs else None)
                    m1 = row[threads.index(1)] if 1 in threads else None
                    m12 = row[threads.index(12)] if 12 in threads else None
                    share = f"{100 * m1 / tot1:.0f}%" if (m1 is not None and tot1) else "-"
                    sp = f"{m1 / m12:.2f}" if (m1 and m12) else "-"
                    print(f"| {s} | " + " | ".join(fmt(x) for x in row) + f" | {share} | {sp} |")
                print(f"| (sum of stages) | " + " | ".join(
                    fmt(sum((cell_stats(cells.get((wid, 'stages', t, bn), []), f'{s}_ms') or {'med': 0})['med'] for s in WL.STAGES)) for t in threads) + " | | |")
                pm = {t: (cell_stats(cells.get((wid, "stages", t, bn), []), "parse_ms") or {}).get("med") for t in threads}
                print()
                print("parse (read + walk) ms: " + ", ".join(f"{t}t {fmt(pm[t])}" for t in threads))
                print()

    # ---- 5. raw samples
    if a.raw:
        print("## Raw samples (ms per input; one value per process, in rep order)")
        print()
        for (wid, mode, t, bn), rs in sorted(cells.items(), key=lambda kv: (order.get(kv[0][0], 99), kv[0][1], kv[0][2], kv[0][3])):
            if mode == "stages":
                continue
            name = "e2e_ms" if mode in ("e2e", "e2ecsv") else WL.BY_ID[wid].key
            rs = sorted(rs, key=lambda r: r["rep"])
            xs = [metric(r, name) for r in rs]
            ld = [r["load_before"][0] if r["load_before"] else None for r in rs]
            print(f"- {wid} {mode} {bn} t={t} {name}: {[round(x, 2) if x is not None else None for x in xs]}  load1 {ld}")
        print()


# ---------------------------------------------------------------------------------------------
# micro probes (bench/micro)
# ---------------------------------------------------------------------------------------------

MICRO = {"ops": ["select", "headselect", "move", "nunique", "unique"], "maps": ["flat", "par", "pipeline"]}


def cmd_micro(a):
    RESULTS.mkdir(parents=True, exist_ok=True)
    mdir = BUILD / "micro"
    mdir.mkdir(parents=True, exist_ok=True)
    for name in MICRO:
        src = ROOT / "bench" / "micro" / f"{name}.bend"
        exe = mdir / name
        if a.rebuild or not exe.exists() or exe.stat().st_mtime < src.stat().st_mtime:
            print(f"building {src.name}")
            rc = subprocess.call([BEND, str(src), "-o", str(exe)], cwd=ROOT)
            if rc != 0:
                sys.exit(rc)
    out = RESULTS / f"micro-{a.label}.jsonl"
    f = open(out, "a")
    gi = git_info()
    combos = [(n, m, t) for n, ms in MICRO.items() for m in ms for t in a.threads]
    for rep in range(a.procs):
        k = rep % len(combos)
        for n, m, t in combos[k:] + combos[:k]:
            argv = [str(mdir / n), "--threads", str(t), m]
            lb = loadavg()
            r = run_process(argv, {}, a.timeout)
            la = loadavg()
            mm = re.search(r"ms=(\d+)", r["stdout"])
            lines = [l for l in r["stdout"].splitlines() if not l.startswith(m + " ms=")]
            rec = {"type": "proc", "label": a.label, "bench": n, "mode": m, "threads": t, "rep": rep,
                   "ts": now_iso(), "command": argv, "ms": int(mm.group(1)) if mm else None,
                   "check": "\n".join(lines).strip(), "rc": r["rc"], "rss_bytes": r.get("rss_bytes"),
                   "rss_method": r.get("rss_method"), "load_before": lb, "load_after": la,
                   "commit": gi, "bend_version": bend_version()}
            f.write(json.dumps(rec) + "\n")
            f.flush()
            print(f"{n:5} {m:11} t={t:<2} rep={rep} ms={rec['ms']} rc={r['rc']} load={lb[0] if lb else '?'}")
    f.close()
    # all samples of a (bench, mode) must agree on the printed check lines
    recs = [json.loads(l) for l in open(out)]
    by = {}
    for r in recs:
        by.setdefault((r["bench"], r["mode"]), set()).add(r["check"])
    for k, v in sorted(by.items()):
        print(f"{k[0]} {k[1]}: {'check lines identical in all processes' if len(v) == 1 else 'CHECK LINES DIFFER: ' + str(v)}")
    print("medians (ms): ")
    cells = {}
    for r in recs:
        cells.setdefault((r["bench"], r["mode"], r["threads"]), []).append(r["ms"])
    for k, v in sorted(cells.items()):
        v = [x for x in v if x is not None]
        print(f"  {k[0]} {k[1]} t={k[2]}: median {statistics.median(v) if v else None} raw {v}")


def cmd_list(a):
    if a.md:
        print("| id | group | op | input | aux | rows | batch | param | modes | smoke | what |")
        print("|---|---|---|---|---|---:|---:|---:|---|---|---|")
        for w in WL.WORKLOADS:
            print(f"| {w.id} | {w.group} | {w.op} | `{w.file.replace('bench/data/', '')}` | "
                  f"{('`' + w.aux.replace('bench/data/', '') + '`') if w.aux != '-' else '-'} | {w.rows:,} | {w.batch} | {w.param or '-'} | "
                  f"{', '.join(w.modes)} | {'yes' if w.smoke else ''} | {w.desc} |")
        return
    if a.inputs:
        h = json.loads(INPUTS.read_text())
        print("| file (under bench/data/) | bytes | sha256 |")
        print("|---|---:|---|")
        for k, v in sorted(h.items()):
            print(f"| `{k.replace('bench/data/', '')}` | {(ROOT / k).stat().st_size:,} | `{v}` |")
        return
    for w in WL.WORKLOADS:
        print(f"{w.id:18} {w.group:8} op={w.op:8} modes={','.join(w.modes):12} batch={w.batch:<4} smoke={int(w.smoke)} {w.desc}")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sp = ap.add_subparsers(dest="cmd", required=True)
    b = sp.add_parser("build")
    b.add_argument("which", nargs="?", default="both", choices=["baseline", "candidate", "both"])
    b.add_argument("--force", action="store_true")
    b.set_defaults(f=cmd_build)
    r = sp.add_parser("run")
    r.add_argument("--label", required=True)
    r.add_argument("--smoke", action="store_true")
    r.add_argument("--procs", type=int)
    r.add_argument("--threads", type=int, nargs="+")
    r.add_argument("--only", nargs="+")
    r.add_argument("--group", nargs="+")
    r.add_argument("--modes", nargs="+")
    r.add_argument("--binaries", nargs="+", default=["baseline", "candidate"], choices=["baseline", "candidate"])
    r.add_argument("--engine", default="v01")
    r.add_argument("--resume", action="store_true")
    r.add_argument("--require-quiet", type=float, default=None)
    r.add_argument("--wait", type=int, default=0, help="seconds to wait for --require-quiet")
    r.add_argument("--provisional", action="store_true", help="label the run provisional (machine not quiet)")
    r.add_argument("--note", default="")
    r.add_argument("--timeout", type=int, default=3600)
    r.add_argument("--allow-stale", action="store_true")
    r.set_defaults(f=cmd_run)
    fz = sp.add_parser("freeze")
    fz.add_argument("--only", nargs="+")
    fz.add_argument("--group", nargs="+")
    fz.add_argument("--no-csv", action="store_true")
    fz.add_argument("--force", action="store_true", help="re-freeze workloads that already have an expected entry")
    fz.add_argument("--timeout", type=int, default=3600)
    fz.set_defaults(f=cmd_freeze)
    s = sp.add_parser("summary")
    s.add_argument("files", nargs="+")
    s.add_argument("--max-load", type=float)
    s.add_argument("--raw", action="store_true")
    s.set_defaults(f=cmd_summary)
    m = sp.add_parser("micro")
    m.add_argument("--label", required=True)
    m.add_argument("--procs", type=int, default=3)
    m.add_argument("--threads", type=int, nargs="+", default=[1, 4, 12])
    m.add_argument("--rebuild", action="store_true")
    m.add_argument("--timeout", type=int, default=1800)
    m.set_defaults(f=cmd_micro)
    l = sp.add_parser("list")
    l.add_argument("--md", action="store_true", help="markdown table of the workloads")
    l.add_argument("--inputs", action="store_true", help="markdown table of the input files and sha256")
    l.set_defaults(f=cmd_list)
    a = ap.parse_args()
    a.f(a)


if __name__ == "__main__":
    main()
