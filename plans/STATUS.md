# v0.1 plan status (paused after M1)

Plan: plans/M_01.txt. Contract: DESIGN.md §15. Agent brief: plans/AGENT_BRIEF.md.

## Done
- **M0**: contract frozen (§15, 55-row defect table), `DF.dump` typed oracle,
  typed comparator (bench/check.py), xfail runner, `make ci`, CI workflow
  (not yet run on GitHub), TOOLCHAIN pins, baseline (bench/results/baseline.json,
  measured on a busy machine).
- **M1**: every defect B01–B05 from both reviews has a regression test that
  passes. That covers cardinality, CSV quotedness and scan prefix, numerics
  (strict cast + try_cast, floor_div, shared F32 order, Neumaier sums), sources
  (self-join, validate_bindings), the 2^23 row cap, and the shared expression
  analysis. The default optimizer is now the certified fragment
  (`Optimize.release`); `optimize_full` is opt-in.
  - Defects the differential generator found: NEW-1 (eager static-check
    order), NEW-2 (interpreter stack overflow on large results, dump and CSV),
    and NEW-T23-1/2 (describe min/max). All fixed.
  - Exit criteria: `make test` 117/117 with 0 XFAIL. `make check`, `make proofs`,
    `make verdict`, `make runner-check` and `make bench-check` are green.
    `make diff SEED=1 N=1000` has 0 failing cases (2 inadmissible under the
    §15.9 rule). `make diff-reduce` has no findings.

## Paused, not merged
- **M2** is complete on branch `worktree-agent-a1636193807aae7bf`, based on
  0fef7cc. It needs a merge with master, which has moved since.
  - Proved: 71 laws. R1 (head merge) is proven end to end against
    `Exec.run_pure`. The default optimizer's result equivalence is proven for
    the merge-only fragment. String.eq is proven, P0 well-formedness is
    defined, and gather/compact are proven per step (the full content theorems
    are blocked on a distinct-paths bit-vector lemma). Exec is factored into
    `Exec.run_pure`. The proof files are split.
  - Decisions needed before merging:
    1. Exec error order: scans are now read before any operator runs, so a
       scan error beats an earlier runtime operator error (DESIGN §14 M2
       item 2).
    2. G6 wording until M5: the optimizer theorem covers the head-merge
       fragment; the head sink below certified nodes is tested but not proved.

## Next (per plan §7)
After M2 merges: M3 (minimum API) and M4 (string experiment) in parallel
with M5 (proof closure: P1/P2, R2–R5), then M6 (release candidate). M6
includes a hub publish to a throwaway name, which is permanent and needs
explicit approval.
Not yet measured: the cost of the narrower default optimizer (no predicate
or projection pushdown) on the q1–q6 benchmark.
