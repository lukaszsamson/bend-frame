# bench/w5/scale: the G2 scaling diagnosis (DESIGN.md 16.10, IMPLEMENTING.md "Scaling diagnosis")

Why the chunked walks stopped at ~2x, and the probes that found it. Every number is PROVISIONAL (shared
machine; the 1-minute load is recorded per process in results/*.jsonl).

Files:

- `probe.bend`: one balanced fork tree over an owned tree of U32 leaves (2^24 rows), the per-leaf work per
  mode (fold / fresh output / in place / drops inside / no work / the old list fork `Lst.pmap` / a flat
  helper in the branch argument), `io` or `pure` timing styles, a sequential `gap` before every rep.
  `bend bench/w5/scale/probe.bend -o build/scale/probe; build/scale/probe --threads N MODE DEPTH REPS io GAP`
- `matrix.py`: the interleaved matrix over the probe (`--report` prints the table); `run.py`: one process
  under `/usr/bin/time -l` (CPU time, page reclaims, context switches) as a JSONL row; `sample.py`: macOS
  `sample` of a running probe.
- `instrument.py`: a DIAGNOSTIC build of an emitted C file with scheduler counters (iterations, turns, grow /
  drain / barrier time, ring tasks per thread, grow skips, deferred forks):
  `bend x.bend -o x.c && python3 -I bench/w5/scale/instrument.py x.c x_dbg.c && clang -O2 -w -o x_dbg x_dbg.c -lpthread`
- `fids.py`: the task-table flags (`nofk` = fork-free) of the defs of an emitted C file; `forkaudit.py`: the
  stall shape (`forking def -> non-flat fork-free callee` call tasks) read off an emitted C file. Run it
  on any new fork tree: only leaf-position and join (`*_J*`) callees may remain. `forkaudit.py --forks x.c ...`
  lists the forking defs (defs with a parallel let) with their call tasks; `--check forkaudit.allow x.c ...` is the
  gate (`make fork-audit`): it fails on a call task no allowlist line covers (each line has a one-line reason:
  leaf / root / join) and on a stale line; `--src src/*.bend frame.bend` is the source lint over every parallel
  let (no non-primitive call in a branch argument or before the fork), which also covers the defs no audited
  program reaches (the emitted C holds only reachable defs). `forkaudit.allow`: the reviewed call tasks.
- `t53b.py`: the engine's pre-chunked compute batched above the 1 ms clock (bench/w5/t53.bend mode 3).
- `results/`: matrix.jsonl + matrix_summary.md (the probes), t53_fix.jsonl + t53_fix_summary.md (bench/w5/t53.py
  after the fix), t53b.jsonl + t53b_summary.md (batched), sample_*.txt (the thread samples: old t53x vs the
  probe), smoke.jsonl, fork_audit_*.jsonl (the fork audit's before / after runs of the m2 driver: v0.1 parse, v0.2
  parse, q6; one JSON line per process with the load before it; IMPLEMENTING.md "Fork audit").

The finding, in one line: a forking def that calls a non-flat fork-free helper (`Lst.split`, `CX.cut`,
`Dict.clone`, `List.append`) before its parallel let hands the runtime a task the grow pass does not run; the
drain then runs the helper AND the rest of the def, parallel let included, sequentially, so the subtree
runs on one thread and the tree degenerates to its two root halves. Fix: match, fork, nothing else before
the parallel let; helpers in leaves, joins or a sequential prelude (`Lst.lt`, `CX.ft`).
