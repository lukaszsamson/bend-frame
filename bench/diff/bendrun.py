"""Running generated cases through Bend: batching, parsing, crash isolation."""
from __future__ import annotations

import os
import re
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import emit
import model as M

BEND = os.environ.get("BEND", str(Path.home() / ".bend/bin/bend"))
class BendError(RuntimeError):
    pass


HDR = re.compile(r"^-- (d\d+) (eager|raw|opt|full)$", re.M)


def header_for(scratch: Path) -> str:
    rel = os.path.relpath(M.ROOT, scratch)
    return f"import Base\nimport {rel}/frame.bend as DF\nimport {rel}/tests/diff/lib/dx.bend as DX\n"


def batch_text(cases, scratch: Path) -> str:
    emit_hdr = emit.HEADER
    text = emit.program(cases)
    return text.replace(emit_hdr, header_for(scratch), 1)


def parse_output(out: str) -> dict:
    """{case id: {'eager': dump, 'raw': dump, 'opt': dump}} from the printed headers + dumps."""
    res: dict = {}
    pos = [(m.start(), m.end(), m.group(1), m.group(2)) for m in HDR.finditer(out)]
    for i, (s, e, cid, how) in enumerate(pos):
        end = pos[i + 1][0] if i + 1 < len(pos) else len(out)
        body = out[e + 1:end]
        body = body.rstrip("\n") + "\n" if body.strip() else body
        res.setdefault(cid, {})[how] = body
    return res


def run_file(path: Path, mode: str, timeout: float, threads: int | None = None):
    """Run a Bend file; returns (stdout+stderr text, exit code or 'timeout', seconds)."""
    t0 = time.time()
    env = dict(os.environ)
    try:
        if mode == "native":
            exe = path.with_suffix("")
            b = subprocess.run([BEND, str(path), "-o", str(exe)], capture_output=True, text=True, timeout=timeout * 4, env=env)
            if b.returncode != 0:
                return b.stdout + b.stderr, b.returncode, time.time() - t0
            r = subprocess.run([str(exe)], capture_output=True, text=True, timeout=timeout, env=env, stdin=subprocess.DEVNULL)
        else:
            r = subprocess.run([BEND, str(path)], capture_output=True, text=True, timeout=timeout, env=env, stdin=subprocess.DEVNULL)
        return r.stdout + r.stderr, r.returncode, time.time() - t0
    except subprocess.TimeoutExpired as e:
        out = (e.stdout or b"")
        out = out.decode("utf-8", "replace") if isinstance(out, bytes) else out
        return out, "timeout", time.time() - t0


def run_cases(cases, scratch: Path, mode="interp", timeout=300.0, tag="b", depth=0):
    """Run `cases` as one program; on a crash or missing output bisect to isolate the culprit.
    Returns ({id: {how: dump}}, {id: crash text}, stats)."""
    scratch.mkdir(parents=True, exist_ok=True)
    path = scratch / f"{tag}.bend"
    path.write_text(batch_text(cases, scratch))
    out, rc, secs = run_file(path, mode, timeout)
    got = parse_output(out)
    done = {c.id for c in cases if len(got.get(c.id, {})) == 4}
    if rc != 0 and got:
        # a crash: the last printed case may be cut off (stderr text glued to its dump); rerun it
        done.discard(list(got)[-1])
    stats = {"runs": 1, "secs": secs}
    if rc == 0 and len(done) == len(cases):
        return got, {}, stats
    if not got and "stack overflow" not in out and "memory fault" not in out and rc != "timeout":
        # nothing ran at all: the program (or the library under it) does not compile; bisecting
        # would only repeat that error for every case
        raise BendError(f"bend could not run {path}: exit {rc}\n{out[-800:]}")
    missing = [c for c in cases if c.id not in done]
    results = {k: v for k, v in got.items() if k in done}
    crashes = {}
    if len(cases) == 1:
        crashes[cases[0].id] = f"exit {rc}: " + out[-600:]
        return results, crashes, stats
    # re-run the missing ones in two halves (the finished ones are kept)
    mid = len(missing) // 2 or 1
    for k, part in enumerate((missing[:mid], missing[mid:])):
        if not part:
            continue
        r2, c2, s2 = run_cases(part, scratch, mode, timeout, f"{tag}{k}", depth + 1)
        results.update(r2)
        crashes.update(c2)
        stats["runs"] += s2["runs"]
        stats["secs"] += s2["secs"]
    return results, crashes, stats


def run_all(cases, scratch: Path, batch=25, jobs=6, mode="interp", timeout=300.0, progress=None):
    batches = [cases[i:i + batch] for i in range(0, len(cases), batch)]
    results, crashes = {}, {}
    stats = {"runs": 0, "secs": 0.0}

    def one(args):
        k, b = args
        r = run_cases(b, scratch, mode, timeout, f"b{k:03d}")
        if progress:
            progress(k, len(batches))
        return r

    with ThreadPoolExecutor(max_workers=jobs) as ex:
        for r, c, s in ex.map(one, list(enumerate(batches))):
            results.update(r)
            crashes.update(c)
            stats["runs"] += s["runs"]
            stats["secs"] += s["secs"]
    return results, crashes, stats
