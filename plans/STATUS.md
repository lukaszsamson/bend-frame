# v0.1 plan status

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

## M2 (merged 2026-10-09)
- Merged from `worktree-agent-a1636193807aae7bf`. 71 laws; R1 is proven end to end over
  `Exec.run_pure`, the merge-only fragment of the default optimizer is proven, and String.eq
  and P0 are proven. Both decisions are recorded in DESIGN.md: the scan-first error order
  (§15.9 note) and the G6 interim claim (§8).

## Next (per plan §7)
After M2 merges: M3 (minimum API) and M4 (string experiment) in parallel
with M5 (proof closure: P1/P2, R2–R5), then M6 (release candidate). M6
includes a hub publish to a throwaway name, which is permanent and needs
explicit approval.
Not yet measured: the cost of the narrower default optimizer (no predicate
or projection pushdown) on the q1–q6 benchmark.
