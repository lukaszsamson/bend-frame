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

## M5 (proof closure, P1 part; branch `worktree-agent-ae7b89e92babd1684`)
- 90 laws, `make proofs` ~0.6 s, `make verdict` ~2 s, both green. P1 is closed over the
  production kernels: the distinct-paths bit-vector lemma (`paths_distinct`), `Array.set`
  separation (`array_set_other`), `gather_contents`, `compact_contents` (+ `CRoom`
  precondition), `mask_not/and/or_cell`, `iota_cell`, `u32_fold_sum`, `popcount_sum`, and at
  the column level `cell_pure`, `head_cell`, `slice_cell_u32` (DESIGN §8 sections 11, 12 and
  8.1). Four negative fixtures in `tests/proof_negative/`.
- Not done: P2 (analysis / evaluator soundness), P3 R2–R5 and the composition theorem, the
  column-level cell theorems, dictionary lemmas (M4 not merged into the proof branch). The
  G6 claim stays at the merge-only fragment (DESIGN §8, final wording there).

## M3 (merged 2026-10-09)
- M3a: table verbs (drop/rename/slice/tail/unique/concat_vertical/semi/anti). M3b: when/is_in/
  clip/is_between, string predicates, std/var/median. Facade leftovers (DF.column/schema/height/
  collect_show). Examples dedupe, sales_summary, dirty_csv use only the facade.

## M5 part 2 (P2 closed, P3 fallback; branch `worktree-agent-a301b0de831e4ede8`)
- P3 fallback taken: `Optimize.release` = `Opt.hmerge` (adjacent-Head merging only); `release_run`
  / `release_run_obs` proven for EVERY plan and env (no admissibility hypothesis). The certified
  Head sink stays in `optimize_full` (opt-in, tested). Cost on q1-q6: none (no bench plan has a
  Head above a Select/WithColumns; tests/plan_release_bench.bend pins that the plans are unchanged).
- P2 closed: LAWS section 13 (116 laws): reader purity, the WF bridge, `get_cloned_typed`, the ten
  operation typing laws (`eval_un_typed` .. `eval_agg_typed`), `run_typed` (the stack machine, every
  Expr node) and `eval_full_typed` / `eval_expr_typed` over the production `Eval.full` / `Eval.expr`.
  `make proofs` ~1.2 s, `make verdict` ~2.9 s (loaded machine). Seven negative fixtures.
- Final G6 wording in DESIGN section 8. Not done: R3 as a theorem (cell-level commutation), R2/R4/R5,
  cell values and the refs / locality parts of the analysis record, dictionary lemmas (M4 not merged
  into this branch; DESIGN section 14 "M5 part 2" lists what a Dictionary variant needs).

## M5 part 1 (merged 2026-10-09)
- 90 laws: distinct-paths lemma; gather/compact/map/zip/iota/U32 fold/popcount content theorems;
  column cell/head/slice theorems; mutation fixtures for gather and compact.

## In progress
- M4 (string storage): branch `worktree-agent-a7d278e15908e046e`. Raw/Dictionary storage,
  streaming CSV reader, decode-equivalence tests, generator mode, concat merging are done; the
  measurements, the gate decision and the merge are not.


## Decisions
- 2026-10-09 (user): no throwaway hub publish in M6. The clean-consumer check uses a local
  import from a clean clone; the only publish is the proper `bend-frame@0.1.0.0`, done when
  ready and with explicit approval.

## Next (per plan §7)
Finish M4 and M5, then M6 (release candidate; no throwaway publish, see Decisions).
Not yet measured: the cost of the narrower default optimizer (no predicate
or projection pushdown) on the q1–q6 benchmark.
