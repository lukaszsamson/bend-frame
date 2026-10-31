"""W0 benchmark runner for the v0.2 performance milestone (plans/M_02.txt sections 0 and 5).

  uv run --project bench python bench/m2/run.py build [baseline|candidate|both] [--force]
  uv run --project bench python bench/m2/run.py freeze [--only GLOB ...]       # expected outputs from the BASELINE
  uv run --project bench python bench/m2/run.py run --label NAME [--smoke] [--procs 5] [--threads 1 4 12]
          [--only GLOB ...] [--group G ...] [--modes phases e2e ...] [--binaries baseline candidate]
          [--engine reference] [--resume] [--require-quiet 2] [--timeout S]
  uv run --project bench python bench/m2/run.py summary results/NAME.jsonl [...] [--max-load X] [--raw]
  uv run --project bench python bench/m2/run.py micro --label NAME [--procs 3] [--threads 1 4 12]
  uv run --project bench python bench/m2/run.py list                          # the frozen workload list
  uv run --project bench python bench/m2/run.py build baseline|candidate|both --instrument   # G6 instrumented binaries
  uv run --project bench python bench/m2/run.py g6 --label NAME [--smoke] [--only GLOB ...]  # G6: copy/alloc table
  uv run --project bench python bench/m2/run.py g6report results/g6-NAME.jsonl [-o out.md]   # re-render the table
  (run --instrument: any `run` against the instrumented binaries; the records are marked and never timed)

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
import instrument as IN  # noqa: E402

BEND = os.path.expanduser(os.environ.get("BEND", "~/.bend/bin/bend"))
BUILD = ROOT / "build" / "m2"
BIN = {"baseline": BUILD / "baseline" / "driver", "candidate": BUILD / "candidate" / "driver"}
INSTRUMENT = False     # G6: run the instrumented binaries (build/m2/<which>-g6): counters, never timings


def set_instrument(on: bool):
    """Rebind BIN to the G6 instrumented binaries (bench/m2/instrument.py). Every function that finds a binary or its
    BUILD.json goes through BIN, so the runner, the staleness check and the records follow."""
    global INSTRUMENT
    INSTRUMENT = on
    for k in ("baseline", "candidate"):
        BIN[k] = BUILD / (k + ("-g6" if on else "")) / "driver"
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


def driver_hash() -> str:
    """sha256 of driver.bend followed by engine.bend (the CSV reader shim, W6.3): baseline.sh's `dh`."""
    h = hashlib.sha256()
    for n in ("driver.bend", "engine.bend"):
        h.update((HERE / n).read_bytes())
    return h.hexdigest()


def git_info() -> dict:
    head = sh(["git", "rev-parse", "HEAD"])
    status = sh(["git", "status", "--porcelain"]) or ""
    lines = [l for l in status.splitlines() if not l[3:].startswith(("build/", "bench/m2/results/"))]
    src = [l for l in lines if l[3:].startswith(("src/", "frame.bend", "bench/m2/driver.bend", "bench/m2/engine.bend"))]
    return {"head": head, "dirty": bool(lines), "dirty_src": bool(src),
            "src_hash": src_hash(ROOT), "driver_hash": driver_hash()}


def build_info(which: str):
    p = BIN[which].parent / "BUILD.json"
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
        if getattr(a, "instrument", False):
            args.append("--instrument")
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
        if INSTRUMENT:
            if not bi.get("instrument"):
                sys.exit(f"{BIN[b]} is not an instrumented build (BUILD.json lacks instrument): "
                         f"`python3 bench/m2/run.py build {b} --instrument`")
            ih = sha256_file(HERE / "instrument.py")
            if bi.get("instrument_hash") != ih:
                sys.exit(f"{b} instrumented binary is STALE: instrument.py changed; rebuild with `build {b} --instrument`")
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
        a += ["+RTS", "--threads", str(threads), "-RTS"]
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


# ---------------------------------------------------------------------------------------------
# G6 instrumentation: parse the counters the instrumented binary prints at every IO.now
# ---------------------------------------------------------------------------------------------

# cumulative counters (phase value = difference of two snapshots) and gauges (value at the end of the phase)
G6_CUM = ("alloc_bytes", "allocs", "free_bytes", "frees", "blk_bytes", "blks", "copy_bytes", "copies", "node_bytes",
          "nodes", "half_bytes", "halves", "minflt", "majflt")
G6_GAUGE = ("live", "peak_live", "maxrss", "bump")


def g6_snaps(stderr: str):
    """-> ([dict], [dict]): the snapshots (`BF_G6 now|end k=v ...`, in order, the last is the `end` line) and the call-site
    records (`BF_G6 site k=N kind=copy|node|half line=L bytes=B n=C`: what the sites moved since the previous snapshot,
    printed before snapshot N)."""
    snaps, sites = [], []
    for line in stderr.splitlines():
        if not line.startswith("BF_G6 "):
            continue
        parts = line.split()
        if parts[1] == "site":
            d = dict(tok.partition("=")[::2] for tok in parts[2:])
            sites.append({"k": int(d["k"]), "kind": d["kind"], "line": int(d["line"]), "bytes": int(d["bytes"]), "n": int(d["n"])})
            continue
        d = {"tag": parts[1]}
        for tok in parts[2:]:
            k, _, v = tok.partition("=")
            d[k] = int(v)
        snaps.append(d)
    return snaps, sites


_RESOLVERS = {}


def resolver_for(binary):
    """instrument.Resolver over the patched C of an instrumented binary (cached), or None."""
    if binary not in _RESOLVERS:
        c = BIN[binary].parent / "driver-g6.c"
        _RESOLVERS[binary] = IN.Resolver(c) if c.exists() else None
    return _RESOLVERS[binary]


def g6_boundaries(mode, op):
    """Windows between consecutive IO.now snapshots in the driver's modes (bench/m2/driver.bend), as
    (name, from snapshot, to snapshot) and the number of IO.now calls the mode makes.
    phases: t0 read t1 walk t2 prep t3 compute t4 check t5 (then the process tail up to `end`);
    e2e / e2ecsv: t0 e2e t1; stages: t0 read t1 walk t2, then per stage its own pair (the clones and hashes
    between stages are outside every window). Snapshot index -1 is the `end` line."""
    if mode == "phases":
        return [("read", 0, 1), ("walk", 1, 2), ("prep", 2, 3), ("compute", 3, 4), ("check", 4, 5), ("tail", 5, -1)], 6
    if mode in ("e2e", "e2ecsv"):
        return [("e2e", 0, 1), ("tail", 1, -1)], 2
    if mode == "stages":
        w = [("read", 0, 1), ("walk", 1, 2)]
        for k, name in enumerate(WL.STAGES):
            w.append((name, 3 + 2 * k, 4 + 2 * k))
        return w, 3 + 2 * len(WL.STAGES)
    return [], None


def g6_derive(stderr: str, mode, op, resolver=None):
    """-> {"snaps": n, "phases": {name: {cumulative deltas, gauges at the end}}, "total": the end line, "error": str|None}.
    A snapshot count that differs from the driver's IO.now count is an error, never a silent misattribution."""
    sn, sites = g6_snaps(stderr)
    if not sn:
        return {"error": "no BF_G6 lines (not an instrumented binary?)", "phases": {}, "total": None, "snaps": 0}
    end = sn[-1] if sn[-1]["tag"] == "end" else None
    nows = [x for x in sn if x["tag"] == "now"]
    wins, want = g6_boundaries(mode, op)
    err = None
    if end is None:
        err = "no end line (the process did not exit normally)"
    if want is not None and len(nows) != want:
        err = f"{len(nows)} IO.now snapshots, expected {want} for mode {mode}"
    phases = {}
    if err is None:
        for name, i, j in wins:
            a_, b_ = nows[i], (end if j == -1 else nows[j])
            ph = {k: b_[k] - a_[k] for k in G6_CUM}
            ph.update({k + "_end": b_[k] for k in G6_GAUGE if k in b_})
            ph["live_start"] = a_["live"]
            lo, hi = i, (len(nows) if j == -1 else j)
            agg = {}
            for st in sites:
                if lo < st["k"] <= hi:
                    e_ = agg.setdefault((st["kind"], st["line"]), [0, 0])
                    e_[0] += st["bytes"]
                    e_[1] += st["n"]
            ph["sites"] = sorted(([k, ln, b, n, (resolver.where(ln) if resolver else None)] for (k, ln), (b, n) in agg.items()),
                                 key=lambda x: -x[2])
            phases[name] = ph
    return {"snaps": len(nows), "phases": phases, "total": end, "error": err}


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
    g6 = g6_derive(r["stderr"], mode, w.op, resolver_for(binary)) if INSTRUMENT else None
    if g6 is not None and g6["error"] and not err:
        err = "G6: " + g6["error"]
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
    if INSTRUMENT:
        # an instrumented binary's wall time, RSS and driver *_ms are NEVER gate or perf data
        rec["instrument"] = True
        rec["timing_valid"] = False
        rec["g6"] = g6
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
    if INSTRUMENT:
        print("INSTRUMENTED RUN (G6): counters only; the timings of these records are not valid and not used by `summary`",
              file=sys.stderr)
    if a.require_quiet is not None and not INSTRUMENT:
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
    ninstr = sum(1 for r in recs if r.get("instrument"))
    if ninstr:
        # instrumented runs (G6) are for counters only: never in a timing table (use `g6report`)
        print(f"<!-- {ninstr} instrumented (G6) records ignored: their timings are not valid; see `run.py g6report` -->")
        recs = [r for r in recs if not r.get("instrument")]
        if not recs:
            print("no timed records in these files (all instrumented)")
            return
    if a.max_load is not None:
        recs = [r for r in recs if (r["load_before"] or [0])[0] <= a.max_load]
    bad =[r for r in recs if r["valid"] is False or r["rc"] != 0]
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
            argv = [str(mdir / n), "+RTS", "--threads", str(t), "-RTS", m]
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


# ---------------------------------------------------------------------------------------------
# G6: the copy / allocation table (instrumented binaries; counts, never timings)
# ---------------------------------------------------------------------------------------------

G6_DEFAULT = ["q?_1m", "parse_1m", "str_*"]
G6_SMOKE = ["q?_100k", "str_*_100k"]
G6_CFG_ORDER = ["baseline", "v01", "reference", "v02", "chunked", "v02,chunked"]
G6_CFG_NAME = {"baseline": "baseline 3612482", "v01": "candidate v0.1 reader", "reference": "candidate reference (default reader)",
               "v02": "candidate v02 reader", "chunked": "candidate chunked", "v02,chunked": "candidate v02,chunked"}


def g6_cfg(r):
    """The engine combination of a record: baseline (it ignores BF_ENGINE), v01, reference, v02, chunked, v02,chunked.
    A candidate record with the token `v01` read with the v0.1 reader (before W8 the token-less reference did too, and
    the records of g6-master-prov carry `v01` for it); `reference` is the candidate's DEFAULT reader (v0.2 since W8)
    with the reference executor."""
    if r["binary"] == "baseline":
        return "baseline"
    toks = set((r.get("engine") or "").split(","))
    o, v, c = "v01" in toks, "v02" in toks, "chunked" in toks
    if o:
        return "v01"
    return "v02,chunked" if (v and c) else "v02" if v else "chunked" if c else "reference"


def g6_good(recs):
    return [r for r in recs if r.get("instrument") and r.get("g6") and not r["g6"].get("error") and r.get("rc") == 0]


def g6_cells(recs):
    """-> {(workload, cfg): {"phases": {name: {field: median}}, "total": {...}, "n": reps, "nondet": [fields that differ
    between repetitions], "valid": bool|None, "rows": int}}. The counts are exact; a spread between repetitions is reported."""
    by = {}
    for r in g6_good(recs):
        by.setdefault((r["workload"], g6_cfg(r)), []).append(r)
    out = {}
    for k, rs in by.items():
        phases, nondet, wob = {}, set(), {}
        for name in rs[0]["g6"]["phases"]:
            ph = {}
            for f in rs[0]["g6"]["phases"][name]:
                if f == "sites":
                    ph[f] = rs[0]["g6"]["phases"][name][f]
                    continue
                xs = [x["g6"]["phases"][name][f] for x in rs]
                ph[f] = statistics.median(xs)
                if len(set(xs)) > 1 and f not in ("minflt", "majflt", "maxrss_end", "bump_end", "peak_live_end"):
                    if name == "tail":
                        # the JSON print + process exit after the last snapshot: a few allocations (~100 B) wobble
                        wob[f] = max(wob.get(f, 0), max(xs) - min(xs))
                    else:
                        nondet.add(f"{name}.{f}")
            phases[name] = ph
        tot = {f: statistics.median([x["g6"]["total"][f] for x in rs]) for f in rs[0]["g6"]["total"] if f != "tag"}
        out[k] = {"phases": phases, "total": tot, "n": len(rs), "nondet": sorted(nondet), "tail_wobble": wob,
                  "valid": None if any(x["valid"] is None for x in rs) else all(x["valid"] for x in rs),
                  "rows": (rs[0].get("driver") or {}).get("rows"), "rows_in": rs[0]["rows_in"], "rec": rs[0]}
    return out


def _mb(x):
    if x is None:
        return "-"
    if x == 0:
        return "0"
    m = x / 1e6
    return f"{m:,.0f}" if m >= 1000 else f"{m:,.1f}" if m >= 100 else f"{m:.2f}"


def _n(x):
    return "-" if x is None else f"{x:,.0f}"


def _csv_shape(rel):
    """(columns, data rows) of a CSV file under the repo (header line + newline count)."""
    p = ROOT / rel
    if rel == "-" or not p.exists():
        return None, None
    with open(p, "rb") as f:
        head = f.readline().decode("utf-8", "replace")
        n = head.count(",") + 1
        rows = sum(chunk.count(b"\n") for chunk in iter(lambda: f.read(1 << 22), b""))
    return n, rows


def g6_render(recs, metas, cstats, note=""):
    cells = g6_cells(recs)
    wids = []
    for (w, c) in cells:
        if w not in wids:
            wids.append(w)
    order = {w.id: i for i, w in enumerate(WL.WORKLOADS)}
    wids.sort(key=lambda w: order.get(w, 99))
    cfgs = lambda w: [c for c in G6_CFG_ORDER if (w, c) in cells]
    P = lambda w, c, ph, f: (cells[(w, c)]["phases"].get(ph) or {}).get(f)
    sumf = lambda w, c, phs, fs: sum((P(w, c, ph, f) or 0) for ph in phs for f in fs)
    L = []
    pm = [m for m in metas if m.get("type") == "meta"]
    m0 = pm[0] if pm else {}
    L.append(f"# G6 instrumentation: copy and allocation accounting ({m0.get('label', '?')})")
    L.append("")
    L.append("**Counts, never timings.** Instrumented binaries (`bench/m2/instrument.py`: the emitted C patched with relaxed "
             "atomic counters, a `BF_G6` line per `IO.now`) at 1 thread; every number below is exact and deterministic "
             "(see the determinism line). Their wall times, RSS and driver `*_ms` fields are not valid and are not used "
             "anywhere. Counts do not depend on machine load. Reproduce with `make m2-g6 LABEL=x` (it builds the instrumented "
             "binaries first).")
    L.append("")
    if m0:
        c = m0.get("commit") or {}
        L.append(f"- run `{m0.get('label')}`: {m0.get('ts')}, candidate commit `{str(c.get('head'))[:10]}` dirty={c.get('dirty')} "
                 f"src `{str(c.get('src_hash'))[:10]}`, bend {m0.get('bend')}")
        for b, bi in (m0.get("builds") or {}).items():
            if bi:
                L.append(f"- {b}: commit `{str(bi.get('commit'))[:10]}`, src `{str(bi.get('src_hash'))[:10]}`, instrument.py "
                         f"`{str(bi.get('instrument_hash'))[:10]}`, binary `{str(bi.get('binary_sha256'))[:10]}`")
    nd = sorted({f"{w}/{c}:{f}" for (w, c), v in cells.items() for f in v["nondet"]})
    reps = max((v["n"] for v in cells.values()), default=0)
    wob_n = sum(1 for v in cells.values() if v["tail_wobble"])
    wob_a = max((v["tail_wobble"].get("allocs", 0) for v in cells.values()), default=0)
    wob_b = max((v["tail_wobble"].get("alloc_bytes", 0) for v in cells.values()), default=0)
    if reps > 1 and not nd:
        det = (f"counters identical across repetitions in every phase of every cell (read, walk, prep, compute, check)"
               + (f"; the exit tail (JSON print + process exit, after the last snapshot) differs by at most {wob_a:,.0f} allocations / "
                  f"{wob_b:,.0f} bytes in {wob_n} cells, so whole-process totals are exact to that" if wob_n else ""))
    elif nd:
        det = f"COUNTERS DIFFER between repetitions: {', '.join(nd[:12])}"
    else:
        det = "one repetition per cell: determinism not re-checked in this run"
    L.append(f"- {sum(v['n'] for v in cells.values())} instrumented processes, {len(cells)} cells, {reps} repetition(s) per cell; " + det)
    bad = [(w, c) for (w, c), v in cells.items() if v["valid"] is False]
    L.append("- every result validated against `expected.json`" + (f"; INVALID: {bad}" if bad else ": all valid")
             + "; configs: `baseline` = the pinned 3612482 binary (it ignores `BF_ENGINE`: its three engine combinations are one "
               "run), `v01` / `reference` / `v02` / `v02,chunked` = the candidate with `BF_ENGINE` `v01` (the v0.1 reader) / "
               "without a reader token (the default reader: v0.2 since W8, v0.1 before) / `v02` / `v02,chunked`")
    if note:
        L.append(f"- note: {note}")
    L.append("")
    L.append("Counters (bytes are exact, MB = 10^6 bytes): **copy** = `blk_copy` (`Array.clone`, `Column.clone`, `DF.clone`: a full "
             "O(n) copy of one array block); **fork copy** = `blk_node` + `blk_half` (an array rebuilt out of, or matched into, "
             "its halves: each copies the data it moves); **alloc** = every heap allocation (array blocks AND constructor / task "
             "nodes), `allocs` their number; **live** = allocated minus freed at the end of the phase (the retained heap); "
             "**minflt** = `getrusage` soft page faults in the phase (a 16 KiB page each on this machine). Phases are the driver's "
             "`IO.now` windows: read, walk (first walk of every buffer), prep (the input-preservation clone), compute "
             "(`DF.collect` / describe), check (the content hash, which consumes the result and frees the kept inputs).")
    L.append("")

    def table(title, head, rowf, intro=None):
        L.append(f"## {title}")
        L.append("")
        if intro:
            L.append(intro)
            L.append("")
        L.append("| " + " | ".join(head) + " |")
        L.append("|" + "|".join("---" if i < 2 else "---:" for i in range(len(head))) + "|")
        for w in wids:
            for c in cfgs(w):
                row = rowf(w, c)
                if row:
                    L.append(f"| {w} | {G6_CFG_NAME[c]} | " + " | ".join(row) + " |")
        L.append("")

    CP, FK, AL = ("copy_bytes",), ("node_bytes", "half_bytes"), ("alloc_bytes",)
    table("1. Compute phase", ["workload", "config", "copy MB", "fork copy MB", "alloc MB", "allocs", "minflt", "live after MB", "result rows"],
          lambda w, c: [_mb(P(w, c, "compute", "copy_bytes")), _mb(sumf(w, c, ["compute"], FK)), _mb(P(w, c, "compute", "alloc_bytes")),
                        _n(P(w, c, "compute", "allocs")), _n(P(w, c, "compute", "minflt")), _mb(P(w, c, "compute", "live_end")),
                        _n(cells[(w, c)]["rows"])],
          "The engine's own work (optimizer + executor, or the eager describe for q6), over the cloned inputs. `copy MB` is what "
          "the plan copies that a move or a borrow could in principle avoid; `alloc MB` is all fresh storage, including the outputs.")
    table("2. Preparation and output phases", ["workload", "config", "prep copy MB", "prep alloc MB", "check alloc MB", "check copy MB", "check allocs"],
          lambda w, c: [_mb(P(w, c, "prep", "copy_bytes")), _mb(P(w, c, "prep", "alloc_bytes")), _mb(P(w, c, "check", "alloc_bytes")),
                        _mb(P(w, c, "check", "copy_bytes")), _n(P(w, c, "check", "allocs"))],
          "prep is the input-preservation clone (`DF.clone` of every input: the copy Polars does not make because its inputs are "
          "shared); check is the content hash (a streaming fold: it should copy nothing). Both are harness phases, outside `compute`.")

    def parse_row(w, c):
        rec = cells[(w, c)]["rec"]
        phs = ["read", "walk"]
        live = P(w, c, "walk", "live_end")
        wl = WL.BY_ID.get(w)
        lo = None
        if wl is not None and live is not None:
            lo = 0
            for rel in (wl.file, wl.aux):
                ncol, nrow = _csv_shape(rel)
                if ncol:
                    lo += 4 * ncol * nrow
        return [_mb(sumf(w, c, phs, CP)), _mb(sumf(w, c, phs, FK)), _mb(sumf(w, c, phs, AL)), _n(sumf(w, c, phs, ("allocs",))),
                _n(sumf(w, c, phs, ("minflt",))), _mb(live), _mb(lo), (f"{live / lo:.2f}" if (lo and live is not None) else "-")]
    table("3. Parse (read + walk)", ["workload", "config", "copy MB", "fork copy MB", "alloc MB", "allocs", "minflt", "retained after parse MB",
                                    "flat lower bound MB", "retained / bound"], parse_row,
          "`retained after parse` is the live heap once the input frames exist (primary + aux, before the preservation clone). The "
          "`flat lower bound` is 4 bytes x columns x rows of the CSV files: one U32 / F32 / dictionary code per cell, string payload "
          "NOT included, so string workloads exceed 1.0 legitimately; array blocks are power-of-two sized (1M rows occupy 2^20 slots, "
          "+4.9%), which is most of the 1.20 of the sales file (its dictionary column adds the rest). `alloc MB` of the v0.1 reader counts every cons cell of the "
          "intermediate character lists; the v0.2 reader (`v02` rows, and since W8 the `reference` rows) shows what removing them saves.")

    def tot_row(w, c):
        t = cells[(w, c)]["total"]
        return [_mb(t["alloc_bytes"]), _n(t["allocs"]), _mb(t["copy_bytes"]), _mb(t["node_bytes"] + t["half_bytes"]),
                _mb(t["peak_live"]), _n(t["minflt"]), _mb(t["live"])]
    table("4. Whole process", ["workload", "config", "alloc MB", "allocs", "copy MB", "fork copy MB", "peak live MB", "minflt", "live at exit MB"],
          tot_row, "Totals at process exit (all phases; the exit line is printed from an `atexit` handler: live at exit is 0 when "
                   "every allocation was freed, which is how the accounting is self-checked). `peak live` is the high-water mark of the "
                   "retained heap (the G4 quantity; the arena can be larger).")

    # copy sources: the call sites that copied, per workload and config (compute phase, parse for the readers)
    src_rows = []
    for w in wids:
        per = {}
        for c in cfgs(w):
            for ph in ("compute", "read", "walk"):
                agg = {}
                for (kind, line, b, n, where) in ((cells[(w, c)]["phases"].get(ph) or {}).get("sites") or []):
                    e_ = agg.setdefault((kind, where or f"line {line}"), [0, 0])
                    e_[0] += b
                    e_[1] += n
                per[(c, ph)] = sorted(((k, v[0], v[1]) for k, v in agg.items() if v[0] >= 100_000), key=lambda x: -x[1])
        for c in cfgs(w):
            for ph in ("compute", "read", "walk"):
                rows = per[(c, ph)]
                # a config's rows are omitted when its phase is identical to the candidate reference's
                if c in ("v02", "chunked", "v02,chunked") and (w, "reference") in cells and rows == per.get(("reference", ph)):
                    continue
                for ((kind, where), b, n) in rows:
                    src_rows.append((w, c, ph, kind, b, n, where))
    if src_rows:
        L.append("## 5. Copy sources (call sites of `blk_copy` / `blk_node` / `blk_half`, at least 0.1 MB)")
        L.append("")
        L.append("Each row is one C call site (`bench/m2/instrument.py` wraps the three runtime entries with `__LINE__`), resolved to "
                 "the enclosing Bend function: `FID` names are `module path + Bend def`, `spin_N <- FID` is a flat loop traced up "
                 "the static call graph to the nearest Bend function(s) that contain it (a spin shared by several callers lists "
                 "up to three). `copy` = `Array.clone` and friends, `node` / `half` = array rebuilt from / matched into halves. "
                 "The prep phase (the harness's input-preservation `DF.clone`) is omitted, and so are the rows of a `v02` / `chunked` / "
                 "`v02,chunked` config whose phase is identical to the candidate reference's (a phase with no row has no site of 0.1 MB "
                 "or more).")
        L.append("")
        L.append("| workload | config | phase | kind | MB | calls | where |")
        L.append("|---|---|---|---|---:|---:|---|")
        for (w, c, ph, kind, b, n, where) in src_rows:
            L.append(f"| {w} | {G6_CFG_NAME[c]} | {ph} | {kind} | {_mb(b)} | {_n(n)} | `{where}` |")
        L.append("")

    # chunked: conversion cost
    rows5 = []
    for w in wids:
        if (w, "v02,chunked") in cells and (w, "v02") in cells:
            base = "v02"
        elif (w, "chunked") in cells and (w, "reference") in cells:
            base = "reference"
        else:
            continue
        ch = "v02,chunked" if base == "v02" else "chunked"
        d = lambda f, fs=None: (sumf(w, ch, ["compute"], fs or (f,)) - sumf(w, base, ["compute"], fs or (f,)))
        cs = cstats.get(w)
        rows5.append((w, d("copy_bytes"), d("x", FK), d("alloc_bytes"), d("allocs", ("allocs",)), d("minflt", ("minflt",)), cs))
    if rows5:
        L.append("## 6. Chunk conversions (`BF_ENGINE=chunked`)")
        L.append("")
        L.append("The chunked executor converts flat env frames to chunk trees (`of_frame`) and back (`to_frame`) inside the compute "
                 "window. The facade does not expose `CStats` (`collect_with` drops it), so the conversion cost is read off the counters: the "
                 "compute phase of `v02,chunked` minus the compute phase of `v02` (same reader, same frames; the reference executor). "
                 "The conversions do not use `blk_copy` / `blk_node` / `blk_half` (cuts and joins are fresh blocks), so they show as "
                 "extra **alloc** bytes and allocations, not as copy bytes; the extra also contains whatever the chunked leaves allocate "
                 "beyond the reference's operators. The `CStats` columns are the runner's own counters of conversions (count / "
                 "LOGICAL bytes = 4 x rows x columns converted) from `bench/m2/cstats.bend`, the same plan at the same grain "
                 "(`-` = no CStats record; q4 and the string ops run flat, 0 conversions). q6 and parse do not collect.")
        L.append("")
        L.append("| workload | extra copy MB | extra fork copy MB | extra alloc MB | extra allocs | extra minflt | CStats in (n / MB) | CStats out (n / MB) |")
        L.append("|---|---:|---:|---:|---:|---:|---:|---:|")
        quiet = [r[0] for r in rows5 if abs(r[3]) < 100_000 and not (r[6] and (r[6]["conv_in"] or r[6]["conv_out"]))]
        for (w, dc, df_, da, dn, dm, cs) in rows5:
            if w in quiet:
                continue
            ci = f"{cs['conv_in']} / {_mb(cs['bytes_in'])}" if cs else "-"
            co = f"{cs['conv_out']} / {_mb(cs['bytes_out'])}" if cs else "-"
            L.append(f"| {w} | {_mb(dc)} | {_mb(df_)} | {_mb(da)} | {_n(dn)} | {_n(dm)} | {ci} | {co} |")
        L.append("")
        if quiet:
            L.append("No conversion (extra alloc under 0.1 MB, no CStats conversions): " + ", ".join(quiet) + ". Those plans run flat "
                     "(sort / group_by / join / unique / describe flatten, and a frame of at most 2^14 rows stays flat): the "
                     "chunked engine adds only a handful of runner allocations there.")
            L.append("")

    # retained vs logical for the result
    rows6 = []
    for w in wids:
        if (w, "reference") not in cells:
            continue
        c = "reference"
        res = (P(w, c, "compute", "live_end") or 0) - (P(w, c, "walk", "live_end") or 0)
        rows_o = cells[(w, c)]["rows"]
        rows6.append((w, rows_o, res))
    if rows6:
        L.append("## 7. Result retained after compute (candidate reference)")
        L.append("")
        L.append("`live after compute` minus `live after parse`: what the result (plus anything the executor leaves behind) retains "
                 "once the cloned inputs have been consumed. Bytes per result row can be compared with the flat bound of the "
                 "result's columns.")
        L.append("")
        L.append("| workload | result rows | retained after compute MB | bytes / result row |")
        L.append("|---|---:|---:|---:|")
        for (w, ro, res) in rows6:
            L.append(f"| {w} | {_n(ro)} | {_mb(res)} | {(f'{res / ro:,.1f}' if ro else '-')} |")
        L.append("")
    return "\n".join(L) + "\n"


def g6_cstats_run(a, ws):
    """CStats (conversion counts / logical bytes of the chunked executor) per workload from bench/m2/cstats.bend (the same
    plans and grain as `BF_ENGINE=chunked`, 1 thread, reading with v02 for speed: the frames are the same): {workload id:
    {"conv_in", "bytes_in", "conv_out", "bytes_out", "walks", "flat_ops"}}. {} if the probe cannot be built."""
    exe = BUILD / "cstats"
    srcs = [HERE / "cstats.bend", HERE / "driver.bend", HERE / "engine.bend", ROOT / "frame.bend"] + sorted((ROOT / "src").glob("*.bend"))
    if not exe.exists() or exe.stat().st_mtime < max(p.stat().st_mtime for p in srcs):
        exe.parent.mkdir(parents=True, exist_ok=True)
        print("building bench/m2/cstats.bend (CStats probe)", flush=True)
        if subprocess.call([BEND, str(HERE / "cstats.bend"), "-o", str(exe)], cwd=ROOT) != 0:
            print("warning: cstats build failed: CStats columns omitted", file=sys.stderr)
            return {}
    out = {}
    for w in ws:
        if w.op in ("q6", "parse", "stages"):
            continue
        aux = "-" if w.aux == "-" else str(ROOT / w.aux)
        argv = [str(exe), "+RTS", "--threads", "1", "-RTS", w.op, str(ROOT / w.file), aux, str(w.param)]
        p = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True, timeout=a.timeout, env=dict(os.environ, BF_ENGINE="v02"))
        j = last_json(p.stdout)
        st = (j or {}).get("stats", "")
        m = re.findall(r"(\w+) (\d+)", st)
        ex = load_expected().get(w.id) or {}
        if p.returncode != 0 or not m:
            print(f"warning: cstats {w.id} gave no stats: {(p.stdout + p.stderr)[-200:]}", file=sys.stderr)
            continue
        out[w.id] = {k: int(v) for k, v in m}
        out[w.id]["chk_ok"] = (j.get("chk") == ex.get("chk")) if ex.get("chk") is not None else None
        print(f"cstats {w.id}: {st}" + ("" if out[w.id]["chk_ok"] in (True, None) else "  RESULT HASH MISMATCH"), flush=True)
    return out


def cmd_g6(a):
    """make m2-g6 LABEL=x: the instrumented matrix, then the table. Baseline x (reference); candidate x (reference, v02,
    v02,chunked); 1 thread; phases mode; one process per cell (counts are deterministic: --procs 2 checks it)."""
    set_instrument(True)
    RESULTS.mkdir(parents=True, exist_ok=True)
    label = a.label[3:] if a.label.startswith("g6-") else a.label
    out = RESULTS / f"g6-{label}.jsonl"
    md = RESULTS / f"g6-{label}.md"
    if not a.no_build:
        for which, extra in (("baseline", []), ("candidate", ["--candidate"])):
            rc = subprocess.call(["bash", str(HERE / "baseline.sh")] + extra + ["--instrument"], cwd=ROOT)
            if rc != 0:
                sys.exit(rc)
    gi = check_binaries(["baseline", "candidate"], a.allow_stale)
    hashes = check_inputs()
    ws = WL.select(a.only or (G6_SMOKE if a.smoke else G6_DEFAULT), None, False)
    if not ws:
        sys.exit("no workload selected")
    cfgs = [("baseline", "v01")] if not a.baseline_engines else [("baseline", e) for e in ("v01", "v02", "v02,chunked")]
    # W8: the candidate's default reader is v0.2: `reference` (no reader token) reads with it, `v01` selects the v0.1
    # reader explicitly (bench/m2/engine.bend)
    cfgs += [("candidate", e) for e in ("v01", "reference", "v02,chunked")]
    if out.exists() and not a.resume:
        sys.exit(f"{out} exists: pick another --label or pass --resume")
    done = set()
    if out.exists():
        for line in open(out):
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            if r.get("type") == "proc":
                done.add((r["workload"], r["binary"], r["engine"], r["rep"]))
    ctx = {"expected": load_expected(), "commit": gi, "bend_version": bend_version(),
           "builds": {b: build_info(b) for b in BIN}, "inputs": {w.id: inputs_of(w, hashes) for w in ws}}
    ma = argparse.Namespace(label=label, provisional=True, note=a.note, engine="v01", timeout=a.timeout,
                            **{k: v for k, v in vars(a).items() if k not in ("label", "note", "timeout", "engine", "provisional")})
    f = open(out, "a")
    if not done:
        f.write(json.dumps(meta_record(ma, gi, ws)) + "\n")
        f.flush()
    total = 0
    for w in ws:
        for rep in range(a.procs):
            for b, eng in cfgs:
                if (w.id, b, eng, rep) in done:
                    continue
                ra = argparse.Namespace(label=label, engine=eng, timeout=a.timeout)
                rec = one(w, "phases", b, 1, rep, ra, ctx)
                f.write(json.dumps(rec) + "\n")
                f.flush()
                os.fsync(f.fileno())
                total += 1
                g = rec.get("g6") or {}
                cp = (g.get("phases") or {}).get("compute") or {}
                flag = "" if rec["valid"] else (" INVALID " + json.dumps(rec["validation"]) if rec["valid"] is False else " (unfrozen)")
                if rec["error"]:
                    flag += " ERROR " + str(rec["error"])[-200:]
                print(f"{w.id:16} {b:9} {eng:12} rep={rep} compute: copy={cp.get('copy_bytes', 0) / 1e6:.2f}MB "
                      f"alloc={cp.get('alloc_bytes', 0) / 1e6:.1f}MB allocs={cp.get('allocs', 0)} wall={rec['wall_s']}s{flag}", flush=True)
    cst = {} if a.no_cstats else g6_cstats_run(a, ws)
    if cst:
        f.write(json.dumps({"type": "cstats", "label": label, "ts": now_iso(), "source": "bench/w5/t53.bend mode 1, 1 thread",
                            "workloads": cst}) + "\n")
    f.close()
    print(f"{total} processes -> {out}")
    g6_report([str(out)], md)


def g6_report(files, outpath=None):
    recs, metas = read_records(files)
    cst = {}
    for m in metas:
        if m.get("type") == "cstats":
            cst.update(m.get("workloads", {}))
    txt = g6_render(recs, metas, cst, note=next((m.get("notes") for m in metas if m.get("type") == "meta" and m.get("notes")), ""))
    if outpath:
        Path(outpath).write_text(txt)
        print(f"-> {outpath}")
    else:
        print(txt)


def cmd_g6report(a):
    g6_report(a.files, a.o)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sp = ap.add_subparsers(dest="cmd", required=True)
    b = sp.add_parser("build")
    b.add_argument("which", nargs="?", default="both", choices=["baseline", "candidate", "both"])
    b.add_argument("--force", action="store_true")
    b.add_argument("--instrument", action="store_true", help="G6: build build/m2/<which>-g6/driver (counters; never timed)")
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
    r.add_argument("--engine", default="reference",
                   help="BF_ENGINE tokens (bench/m2/engine.bend): reference = default reader (v0.2 since W8) + reference "
                        "executor; v01 = the v0.1 reader; v02, chunked, scan")
    r.add_argument("--resume", action="store_true")
    r.add_argument("--require-quiet", type=float, default=None)
    r.add_argument("--wait", type=int, default=0, help="seconds to wait for --require-quiet")
    r.add_argument("--provisional", action="store_true", help="label the run provisional (machine not quiet)")
    r.add_argument("--note", default="")
    r.add_argument("--timeout", type=int, default=3600)
    r.add_argument("--allow-stale", action="store_true")
    r.add_argument("--instrument", action="store_true",
                   help="G6: run the instrumented binaries (build ... --instrument); records are marked, never timed")
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
    g = sp.add_parser("g6", help="G6: instrumented copy / allocation accounting, written to results/g6-LABEL.{jsonl,md}")
    g.add_argument("--label", required=True)
    g.add_argument("--smoke", action="store_true", help="100k-row q1-q6 and str cells instead of the 1M ones")
    g.add_argument("--only", nargs="+", help="workload id globs (default: q?_1m parse_1m str_*)")
    g.add_argument("--procs", type=int, default=1, help="repetitions per cell (counts are deterministic; 2 checks it)")
    g.add_argument("--baseline-engines", action="store_true",
                   help="also run the baseline under v02 and v02,chunked (it ignores BF_ENGINE: identical counts)")
    g.add_argument("--no-build", action="store_true", help="do not (re)build the instrumented binaries first")
    g.add_argument("--no-cstats", action="store_true", help="skip the CStats probe (bench/w5/t53.bend)")
    g.add_argument("--resume", action="store_true")
    g.add_argument("--note", default="")
    g.add_argument("--timeout", type=int, default=3600)
    g.add_argument("--allow-stale", action="store_true")
    g.set_defaults(f=cmd_g6)
    gr = sp.add_parser("g6report", help="render the G6 table of instrumented JSONL files")
    gr.add_argument("files", nargs="+")
    gr.add_argument("-o", help="write the markdown here instead of stdout")
    gr.set_defaults(f=cmd_g6report)
    a = ap.parse_args()
    if getattr(a, "instrument", False) and a.cmd == "run":
        set_instrument(True)
    a.f(a)


if __name__ == "__main__":
    main()
