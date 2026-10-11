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

## M4 (string storage; branch `worktree-agent-a7d278e15908e046e`, ready to merge)
- `CStr.data: ST.Strs` = Raw | Dictionary (src/strs.bend: codes + entries + hash index, entry 0
  `""`); streaming CSV reader (64 MiB pieces; 1 MiB was 3x slower natively); EncRaw / EncDict /
  EncAuto (Dictionary while distinct <= max(16384, rows / 64)); facade `DF.read_csv_enc`,
  `DF.str_raw/str_dict/str_auto`, `DF.encode_strings`, `DF.dict_columns`; decode-equivalence
  tests, generator Dictionary mode (`make diff DIFF_ARGS=--dict`), explicit merging in concat.
- **Gate passed: Auto is the readers' default** (DESIGN §14 "M4 string experiment" item 6,
  bench/README.md "M4 string experiment"). 1M sales auto vs raw: q1 8.3x, q3 8.5-15.6x, q4
  5.1-8.8x, q5 13.9-19.6x; RSS auto <= raw; numeric controls inside 15 % (q2 pooled 0.90x /
  1.02x, the closest); fully distinct controls 0.88-1.24x (median 1.00x). Reader alone (master ->
  raw): 41 MB parse 1.98x / 1.74x faster, -18..-24 % RSS. Target 41 MB parse < 1.5 s NOT met
  (1.98 s at 12 threads).
- Merged with master up to M5 part 2: the P2 typing proofs (116 laws) cover both storages
  (`make proofs` / `make verdict` green; DESIGN §14 M4 item 8 and M5 part 2 item 5).
- Gates on the merged tree (5fd2d1c): `make test` 139/139 (0 XFAIL / XPASS), `make check`,
  `make proofs`, `make verdict`, `make runner-check`, `make bench-check` green; `make diff SEED=1
  N=1000` 0 failing / 0 inadmissible in Raw and in Dictionary mode (`DIFF_ARGS=--dict`);
  `make diff-reduce SEED=1 REDUCE_N=500` no findings.
- Open for the proof agent: the Dictionary decode-preserving lemmas for P1 (DESIGN §14 M4 item 8
  lists exactly which functions: required / only-if-claimed / excluded).

## M5 part 3 (P1 Dictionary lemmas; branch `worktree-agent-aa4a2bf9a7504a99f`)
- 138 laws (section 14: 22). `make proofs` ~1.6 s, `make verdict` ~4.6 s, both green; `make
  check`, `make test` (141 incl. 9 negative fixtures), `make runner-check` green.
- Proven over the production src/strs.bend: the decode model (`decode_cell`), gather / compact /
  clone in both storages, `Str.same`, `Dict.empty`, `Dict.code` with the index (`dict_code_spec`,
  incl. `Keep`: old codes keep their entries), `Strs.encode` (`strs_encode_cells` / `_cell`),
  `Strs.raw` and the column / frame wrappers (`column_encode/decode/recode_cell`,
  `cols_encode_cells`, `frame_encode_cells` = `DF.encode_strings`), `dict_miss_not_code`,
  `dict_merge_spec`, `dict_same_sound`, `dict_find_spec`, `dict_recode_spec`. Two mutation
  fixtures (an encoder reusing code 0; a remap writing the wrong slot).
- Hypotheses not derived (DESIGN section 14 "M5 part 3" item 3): the hash probe's termination
  (`Probe`, per row along the loops), the per-step entry bound in `MergeProbe`, index
  completeness (find / recode are sound, not complete).
- Not done (tested only; DESIGN section 8 lists them): `Strs.append` under `Cat.col` (needs a
  `Kernel.append` / `copy_into` content theorem and `U32.add` lemmas), `Strs.fix` / `Eval.fix.s`
  (`Kernel.mask_data`, in place), `Eval.fill.sd/.sd2` and `Eval.when.sd/.sd2` (`Kernel.choose`,
  in place; their `Dict.merge` half is proven), `WFStrs` for an encoded column.

## M6 release-candidate validation (master after the m6-wip merge; no hub publish, per Decisions)
Machine: M2 Pro, 12 cores; load average 3-25 throughout (other agents running; per-measurement load recorded in the jsonl files).
- **Differential, 22,000 generated cases, 0 failing, 0 crashes, 0 oracle errors.** `--features deep`, Raw: seeds 601-605 x 2000
  (10,000; 6-11 inadmissible-for-T2.1 per seed, ~12 % invalid programs); Dictionary (`--dict`): seeds 611-613 x 2000;
  join-cardinality stress (`--features deep,joinstress`: 20-110 rows per side, keys from a 1-4 value domain + nulls/NaN/-0.0, many-to-many
  inner/left/semi/anti): seeds 621, 622 x 2000, plus seed 631 x 1000 in Dictionary mode; `--backend both` seed 641 x 1000 (interpreter vs native
  compile, 5 + 5 runs, 262 s, jobs 3, timeout 900): 0 failing. `make diff-reduce SEED=1|2 REDUCE_N=2000`: no findings (tightest bound
  use 1.0 of the derived bound, i.e. within it). Summaries `build/m6out/diff_*.json` (not tracked).
- **Scale vs Polars goldens**, `CHECK_MAX=1000000 BENCH_MODE=check scripts/bench.sh`: q1-q6 at 1k, 100k, 1M all pass (16 of 18 byte-identical;
  q6 at 100k 1 and at 1M 2 float cells within rtol 5e-5; q3 vs the f32 reference). Comparator self-test 28/28.
- **High cardinality** (all keys distinct, `bench/hc.py`, `bench/results/m6_hc.jsonl`): group_by / unique / inner join at 100k and 1M,
  results identical to Polars in all 12 (op, n, threads) cells' first runs. Timing: correct but slow. 1 thread, collect ms vs Polars:
  group 997 vs 16 (100k), 17,314 vs 153 (1M); unique 910 vs 5, 17,993 vs 54; join 421 vs 9, 5,132 vs 193 (30-330x). 100k -> 1M costs
  12-20x. RSS 1.1-1.26 GB vs 0.23-0.37 GB at 1M. Not a correctness issue; documented as the weak spot (bench/README.md).
- **Repeated query** (`bench/repeat.py`, 20 iterations in one process, q1-q6 at 100k and 1M): all 20 result hashes equal for every query
  and equal to the one-iteration hash; peak RSS 20 iterations vs 1: -32 .. +39 MB at 1M (<= 3 %, run-to-run variation; q5 1M at 1/20/60
  iterations: 1345.55 / 1345.59 / 1345.67 MB), -0.2 .. +4.7 MB at 100k. No growth. (The harness renders and hashes each result outside the
  timed region: that takes 2.4 min (q1) and 27 min (q2) at 1M rows x 20.)
- **Re-measured table** (540 measurements x 2 runs: `bench/results/m6.jsonl`, `m6b.jsonl`, agree within 1 ms / 10 %; bench/README.md and
  README.md carry m6b). 1M, 1 thread, Bend vs Polars warm: q1 11 vs 1.36 ms (8.1x), q2 15 vs 0.91 (17x), q3 23 vs 11.5 (2.0x), q4 47 vs 13.3
  (3.5x), q5 19 vs 22.2 (0.9x), q6 108 vs 34.5 (3.1x); 12 threads 3-18x (Bend does not scale with threads: 1.0x on q1-q6); peak RSS 1.3 GB
  vs 168 MB. Large gain vs the pre-M4 table (q3 327 -> 23 ms, q4 384 -> 47, q5 399 -> 19). Polars cold first-collect ratios also listed.
- **optimize_full vs default** on q1-q6 (the "not yet measured" item): q3/q4/q6 equal; q1 at 1M 0.6x (7 vs 11 ms), q5 at 1M 0.7-0.8x
  (14-15 vs 19 ms) in both runs; nothing slower beyond noise. The narrower default optimizer costs <= 5 ms on these queries.
- **Clean consumer** (`scripts/consumer_check.sh`, no publish, bend --publish has no dry run): clone of HEAD into /tmp, `--check-only` of
  frame.bend, native build + run of examples/quickstart.bend (output pinned), a separate consumer dir importing the clone by relative and by
  absolute path (`--check-only`, native build, run, output verified; interpreter output equal). All green (about 1 min).
- Gates: `make check` and `make test` (141/141, 0 XFAIL) green on this tree; `make proofs` / `make verdict` not re-run here (no proof file touched).
- Stale prose noticed, not changed (other owners): README.md said "71 laws" and its "Not yet proven" paragraph predated M5.
  (Fixed in the M6 final pass below.)
- Defects found: none (no regression test or fix needed).

## M5 part 4 (merged 2026-10-09, f448ca8)
- 147 laws (LAWS section 15, PROOF_append.bend / PROOF_inplace.bend): `append_cells` (Kernel.append), `strs_append_cells`
  (concat's Str storage, both storages), `mask_data_cell` / `_keeps_mask`, `choose_cell` / `_keeps_mask`, `fix_cell` (Eval.fix,
  every column kind), `fill_str_cell` (fill_null on Str, both storages), `when_str_data` (when's Str storage; validity not stated).
  Merged without DESIGN / STATUS updates and without fixtures; both done in the M6 final pass.

## M6 release candidate (final pass, 2026-10-09; HEAD 6f71462 and later doc commits)
Work: two part-4 mutation fixtures (`tests/proof_negative/append_right_offset.bend`: Kernel.append copying b from na + 1, refused
by `append_cells`; `choose_inverted_mask.bend`: Kernel.choose with the mask test inverted, refused by `choose_cell`; each with a
positive control that checks, `make check` skips both); DESIGN section 8 final (147 laws, file list, timings, row 15, assurance
matrix rows for every part-4 law, the exact numbered "not proven, tested only" list, final G6 text) and section 14 "M5 part 4" /
"M6"; README rewritten (release claim verbatim, Not claimed, laws paragraph, Limits, differences, performance, Development);
CHANGELOG.md (0.1.0); frame.bend: a stale `describe` comment ("a stub") corrected (comment only).

Gates on this tree (machine load average 15-55 during the runs, other processes; timings are therefore upper bounds):
- `make ci` (toolchain-check, check, runner-check, test, proofs, verdict, bench-check): **all gates passed**, 4 min 14 s.
  `make test` 143/143, 0 XFAIL (incl. 11 proof mutation fixtures); `make check` green (skips the 11 fixtures); toolchain pins match;
  bench-check: comparator self-test 28/28, q1-q6 at 1k and 100k identical to the Polars goldens (q6 100k: 1 float cell within
  tolerance).
- `make proofs` ALL PROOFS CHECK in 1.7-2.3 s wall; `make verdict` ALL PROOFS CHECK in 5.1-5.5 s wall (load 22-38).
- `make diff SEED=1 N=1000`: 0 failing, 0 crashes, 0 oracle errors, 0 inadmissible, 113 invalid programs (expected errors).
  `make diff SEED=1 N=1000 DIFF_ARGS=--dict`: the same (0 / 0 / 0 / 0, 113 invalid).
- `make diff-reduce SEED=1` (2000 cases): no findings (tightest bound use 1.0 of the derived bound).
- `scripts/consumer_check.sh` on the clean clone of 6f71462: all ok (check-only, native quickstart, relative and absolute
  imports from a separate directory, interpreter output equal).

### Definition of done (plan section 8), checked against the repo
- [x] **G1 (no known wrong result in the shipped subset)**: was NOT met at 3196845 because of the scan source collision (V01-a: a user
  Source named `#scan0` silently read a CSV scan's frame); met after the fix (2026-10-10, scans in an unnamed Env namespace,
  `tests/regress/V01_a_*`, `V01_b_*`).
- [x] **T6 (public-API coverage matrix)**: absent at 3196845, present now: `scripts/coverage_matrix.py` / `make coverage` (in `make ci`),
  `docs/COVERAGE.md` (774 operation x kind cells: 727 covered, 47 n/a with a stated reason, 0 missing; plus the def-call report), tests in
  `tests/coverage/`, Polars twins in `bench/coverage/`.
- [x] **Every defect from both reviews has a regression test and a disposition.** DESIGN 15.10 lists 54 rows (B01-a .. B05-i).
  Every B01-B04 row except the README row B04-f has a `tests/regress/<ID>_*.bend` (56 files incl. NEW-1 / NEW-2), all passing,
  no `#! xfail` left. The tooling / doc rows: B05-a/b/c by `bench/tests/test_check.py` (28 cases, run by bench-check); B05-d by
  `scripts/bench.sh` check mode (exits 1 on a mismatch or a missing output; the `|| true` left is in the timing loop only, after
  the check); B05-e no "Kahan" left in README, check.py, groupby.bend; B05-f CI workflow exists and `make check` covers the
  facade, examples and bench files; B05-g `B05_g_optimizer_traps.bend` + the T2.1 differential; B05-h
  `tests/proof_negative/mask_not_slots_doubled.bend`; B04-f and B05-i: README rewritten (no "exactly what collect_schema
  refuses", no "byte-identical", law count 147 with the scope).
- [x] **Section 2 API and semantics implemented, eager and lazy, documented.** DESIGN 15.2 (frozen contract); the M3 gap check
  compared all 83 `DF.` names of 15.2 with frame.bend (none missing); tests/facade*.bend, lazy_collect, table_verbs, expr_*;
  README Features lists the surface. Deferred by the plan itself: full join, top-k.
- [x] **Eager / raw-lazy / optimised-lazy agree on the full test matrix.** T2.1 in the differential generator compares eager,
  `collect_raw`, `collect` and `collect_full` (errors and row order included): 22,000 cases in the M6 run (Raw, Dictionary,
  join stress, interpreter vs native) and the two 1000-case runs above, 0 failing. Inadmissible programs (15.9) are counted apart.
- [x] **Correctness failures fail the build; the benchmark cannot hide a mismatch.** (Was NOT fully true at 3196845: `make diff` without
  `--strict` exited 0 on a failure the shrinker labelled with a known-defect rule, and `make ci` ran neither differential suite nor the
  consumer check. Now true, 2026-10-10.) `make ci` stops at the first failing gate (make prerequisites): toolchain-check, check,
  runner-check, diff-driver-check, test, proofs, verdict, mutation-check, bench-check (1k and 100k), diff-smoke (200 strict cases each in Raw
  and Dictionary storage, then the F32 reduction check), consumer-check, coverage. `bench-check` exits 1 on any mismatch, a missing output,
  or when nothing was compared; every differential and reduction failure exits 1, labelled or not (`bench/diff/tests/test_exit.py` is the
  regression). Larger runs are manual. Gap: the GitHub workflow has never run (no remote), so "the build" is `make ci` locally, on macOS arm64 only.
- [~] **Default optimizer theorem passes --verdict, with non-trivial R1-R5 applications tested and witnessed.** `release_run` /
  `release_run_obs` pass `bend` and `--verdict` for every plan and env. R1 is proven and witnessed (theorem + the
  `head_rule_outer_wins` / `head_sink_below_select` fixtures). GAP: by the P3 fallback (M5 part 2) the release optimizer is R1
  only; R2-R5 live in the opt-in `optimize_full`, are TESTED (tests/plan_optimize.bend explains each rewrite firing,
  B05_g traps, T2.1 compares `collect_full` with raw on every generated case) but not theorems, and the generator does not record
  how often each rewrite fired.
- [~] **Production map/zip/gather/compact/head/mask and reduction proofs exist as scoped; the shipped string representation is
  covered.** Proven: gather, compact, map/zip mask combinators, iota, U32 fold sum, popcount, head / slice (U32) / cell, append,
  mask_data, choose, Eval.fix (every kind), and both Str storages through decode / gather / compact / clone / encode / merge /
  recode / find / append / fix / fill_null / when's storage. GAPS (DESIGN 8 "Not proven" list): the plan's grouped scatter
  per-group invariant (count / U32 sum) was not reached; the F32 / String instances of the kernel laws are not stated
  separately (template proofs, used at String / F32 inside the column laws); Dictionary per-entry maps, rank order, comparisons
  and index completeness are tested only; the probe hypothesis is assumed.
- [x] **No theorem relies on an unproved runtime-to-model bridge, an assumed conclusion, or an alternative implementation.** The
  models (`rd`, `rd_at`, `ccell`, `scell`) are tied to the production readers by proven laws (`array_get_pure`, `cell_pure`,
  `decode_cell`); 147 `law`s, 147 `def Laws.*`, no `@unsafe` / axiom / open law. Stated hypotheses (CRoom, CatFits, Probe /
  MergeProbe, WFDict) are premises listed in the assurance matrix, not conclusions.
- [x] **String experiment completed; the default is justified by measurements.** M4 gate passed (bench/README.md "M4 string
  experiment"; Auto default: 5-20x on q1/q3/q4/q5 at 1M, controls within 15 %). The 41 MB parse target (< 1.5 s) was not met
  (1.98 s at 12 threads), stated in README and bench/README.
- [x] **Limits, F32 accuracy, parse behaviour, source ownership and benchmark headlines are truthful in README and
  bench/README.md.** README: release claim verbatim + Not claimed, Limits (row cap, dtypes, memory, no accuracy theorem, the
  out-of-scope list one line each), CSV parse behaviour, sources (several frames per env, a frame read more than once, frames
  handed back as pairs), performance consistent with the bench/README M6 table (shared-machine load, ~1.0x thread scaling,
  1.3 GB vs 168 MB, 30-330x on distinct strings, parse cost). Differences-from-Polars list re-checked against DESIGN 14/15.
- [x] **Clean consumer import, build and examples work on pinned toolchains.** `make toolchain-check` ok; consumer_check green
  on a clean clone; `make check` checks every example; tests/examples_m3.bend runs sales_summary and dirty_csv. Deviation (user
  decision): no throwaway hub publish; the hub upload is first exercised by the real publish.

### The publish (NOT done; the user decides)
From the repo root, after `~/.bend/bin/bend login`:
    ~/.bend/bin/bend frame.bend --publish bend-frame@0.1.0.0
Uploads frame.bend and its transitive `./` imports: the 19 files of src/ (analysis, column, csv, csvparse, dtype, dump, err,
eval, exec, expr, fmt, groupby, join, kernels, plan, schema, sort, strs, table; 577 KB with frame.bend), plus every file named
exactly `LICENSE` beside a published file: the root `LICENSE` (SPDX Apache-2.0 since 2026-10-10, beside frame.bend; verified). `src/LICENSE` (Apache-2.0, added 2026-10-10)
beside the src/ files. No hub dependencies (only Base). LAWS / PROOF*, tests, bench, examples are not uploaded. Public and permanent.

## In progress
- nothing.

## Decisions
- 2026-10-09 (user): no throwaway hub publish in M6. The clean-consumer check uses a local
  import from a clean clone; the only publish is the proper `bend-frame@0.1.0.0`, done when
  ready and with explicit approval.

## Next
- The user decides on the `bend-frame@0.1.0.0` publish (command above). Optional, not v0.1: push to a remote so the CI workflow
  runs once; the gaps in the DoD (R2-R5 as theorems, the grouped scatter invariant, Dictionary completeness / per-entry maps /
  rank order) are v0.2 proof work.

## Decisions (2026-10-10)
- License changed from MIT to Apache-2.0 (user). `LICENSE` and `src/LICENSE` hold
  `SPDX-License-Identifier: Apache-2.0` followed by the unmodified Apache License 2.0 text;
  `NOTICE` names the project and the third-party MIT code (`src/csvparse.bend`, forked from
  `bend-csv-parser@0.1.0.1`, Copyright (c) 2026 nohzafk; its MIT notice stays in the file).
- v0.1 is positioned as an experimental release: R1-only default optimizer and conditional
  Dictionary assurance, with the remaining proof work deferred (both v0.1 reviews recommend this).

## v0.1 review fixes (2026-10-10)

Two independent reviews of the release candidate 3196845: `plans/REVIEW_V01_FABLE.txt` (Fable 5.1: "ready after four small edits") and
`plans/REVIEW_V01_ASTRA.txt` (Astra: "hold publication"). Dispositions: **fixed** (code or gate change, with a test), **documented**
(wording or contract text corrected), **deferred** (named, not for v0.1). Commits: e6c2a92 (Apache-2.0), 8b56d20 / fb1f6fb (scan identity,
149 laws), 062187f (mutation check), dd9c453 / 5fe3c02 / 30651b8 (differential exit status, CI additions), T6 merge 8430fcd, then the
documentation pass (this section's commit).

### Fable review

| finding | disposition |
|---|---|
| H1 `release_run` is about `Exec.run_pure`; the glue (`unscan` commuting with `hmerge`, `validate`, `mat`) is unproven; vacuous on scan plans | **fixed in part**: `Exec.unscan` is gone, `run_pure` runs scan plans through `Env.scans`, `hmerge_keeps_scans` / `release_keeps_scans` proven (149 laws). **documented**: still unproven are `Plan.schema` / `Exec.validate` agreeing for `release(p)` and `p`, and the IO materialisation `Exec.mat` (DESIGN 8, README Laws, CHANGELOG) |
| H2 mutation fixtures mutate a renamed copy; five are name-sensitive | **fixed + documented**: `make mutation-check` (14 production functions mutated in place, all caught, in `make ci`); wording says 11 fixtures, five name-sensitive, plus the in-place check (DESIGN 8, README, CHANGELOG) |
| H3 two typers: LAWS section 2 is about `X.Expr.type` (group_by only), select / with_columns / filter use `A.Expr.analyse` | **documented** (one bullet in DESIGN 8, README, CHANGELOG) |
| H4 "correctness failures fail the build" overstated (`make diff` exit 0 on a classified failure; diff / reduce / consumer not in `make ci`) | **fixed**: every differential / reduction failure exits 1, `diff-driver-check`, `diff-smoke`, `consumer-check`, `mutation-check`, `coverage` in `make ci`; **documented**: larger runs are manual |
| H5 CHANGELOG "goldens at 1k, 100k and 1M (make bench-check)"; q3 golden is the F32 reference; tracked 1k golden regenerated | **documented**: CHANGELOG, README, bench/README (bench-check = 1k and 100k; 1M needs `CHECK_MAX=1000000`; q3 vs the reference) |
| H6 stale comments: LAWS.bend ~1060, `eval_full_typed` ("frame unchanged"), B03_b marker, bench/diff/README speed | **fixed** (comments / docs only): LAWS comments now say the later-writes lemma is proven (section 11) and that the law states nothing about the frame on failure; B03_b marker removed; bench/diff/README speed measured (1000 cases ~5 s wall idle, ~14 s `deep`) and exit status described |
| Note: runner-check timing flake | **fixed**: robust margins (92c5f44) |
| Note: generator mix leans small, no CSV generation | **deferred** (v0.2: wider generator; CSV is covered by regressions, goldens and `V01_b`) |
| Note: 13 stale agent worktrees under `.claude/worktrees` | left to the orchestrator (not touched here) |
| Note: `bench/results` (2.4 MB) tracked | **deferred** (move out of git before v0.2) |
| Note: `ci.yml` mentions a nonexistent `flake.nix` | **documented**: the comment now says what is assumed and untested; the workflow still has never run |
| Note: `consumer_check` depends on the temp path | **documented** in the script (unchanged) |
| Checklist 3: LICENSE in src/ | **fixed**: `src/LICENSE` (Apache-2.0) beside the published src/ files |
| Checklist 4: push to a remote so CI runs, or say CI is untested | **documented** (no remote; README, CHANGELOG, `ci.yml` header say it has never run); **deferred**: first run |
| Not verified by anyone: Linux x86-64, the hub upload, frames near 2^23 rows, CSV through the generator | **documented** (macOS arm64 only); **deferred** |

### Astra review

| finding | disposition |
|---|---|
| P1 scan materialisation silently replaces a user source (`#scan0`) | **fixed**: scans live in `Env.scans`, no name is reserved (DESIGN 14 "v0.1 review: scan source identity", 15.7); regressions `V01_a_*`, `V01_b_*` (raw / default / full; several scans; equal and different schemas) |
| P2 default differential command exits 0 on a classified failure; `make ci` runs no differential or consumer check; "correctness failures fail the build" | **fixed**: see Fable H4; permanent driver regression `bench/diff/tests/test_exit.py` |
| P2 README "every benchmark result identical to Polars except q6"; changelog says bench-check covers 1M | **documented**: README, CHANGELOG, bench/README (q3 exact-rational reference; Polars 96373.4141 vs 96373.4062) |
| 2. API: a bounded subset, not Polars parity | **documented** (unchanged: README Limits and "Not claimed") |
| 2. Strings: Auto threshold, bad distinct-key performance, 0.9x single-thread noise | **documented** (already in README Performance; no change) |
| 2. Tests: 143 counts files, no T6 matrix, no def-call report, no IO-boundary regressions, no per-rewrite firing coverage | **fixed**: `docs/COVERAGE.md` (727 covered, 47 n/a with reasons, 0 missing; def-call report), `V01_b`; wording says "test programs (files)"; **deferred**: per-rewrite firing counts in the generator |
| 2. Optimizer: R1 only, R2-R5 not proven | **documented** as an explicit scope reduction (experimental v0.1); **deferred**: R2-R5 as theorems |
| 3. Proofs: run-vs-run equality is not semantic correctness; scans and native runtime outside | **documented** (scan plans now inside `release_run`; IO / `Exec.mat` and the native runtime remain outside; "Not claimed" list) |
| 3. `EvalTyR` gives no error cause when `total` is False | **documented** (LAWS comments say the law states only `tot == False` on failure) |
| 3. Dictionary: `Probe` / `EncProbe` are premises, index completeness, rank / per-entry maps, grouped scatter invariant missing | **documented** (README / CHANGELOG / DESIGN positioning: conditional assurance); **deferred**: hypotheses, completeness, rank order, grouped scatter invariant |
| 3. Negative fixtures narrower than an automatic fresh-checkout mutation | **fixed**: `make mutation-check`; wording corrected (see H2) |
| 4. runner self-test is load-sensitive | **fixed** (92c5f44) |
| 4. Reported evidence is not independently reproduced here | **documented**: this repository labels its historical pass reports as reported evidence (STATUS M6 sections); the gates were re-run on this tree for this pass (below) |
| 5. LICENSE inclusion; hub-resolved imports untested; hosted CI unverified | **fixed**: `src/LICENSE`; **documented**: no hub dry run exists and CI has never run; the first real publish exercises hub imports |

### Gates on this tree (documentation pass, 2026-10-10, M2 Pro, load average 12-35)

- `make test`: PASS 158 / 158, XFAIL 0 (143 at the first release candidate; the rest are the review regressions and `tests/coverage/`).
- `make check`, `make proofs` (ALL PROOFS CHECK), `make verdict` (ALL PROOFS CHECK): green. Only comments changed in `LAWS.bend` and
  `tests/regress/B03_b_eager_fsum_inf.bend`; no `src/` or test expectation changed.
- `diff/run.py --n 1000 --no-shrink`: seeds 5 (Raw), 7 (`--dict`), 6 (`--features deep`): 0 failing, 0 oracle errors; about 5 s, 3.5 s and 14 s wall.

## Authoritative gate run after the v0.1 review fixes (2026-10-10)
Commit 1ba2954, no agents running (machine load average 11–30 from other processes).
`make ci` exit 0 in 276 s, "ci: all gates passed": toolchain-check, check, runner-check,
diff-driver-check, test (158/158, 0 XFAIL), proofs and verdict (149 laws, ALL PROOFS CHECK),
mutation-check (14/14 rejected, unmutated accepted), bench-check (q1–q6 at 1k/100k), diff-smoke
(Raw and Dictionary: 0 failing; reduction: no findings), consumer-check (clean clone, relative and
absolute imports, interpreter and native), coverage (727 covered, 47 n/a, 0 missing).
Not run: hosted CI (no remote); Linux x86-64; the hub upload (no dry-run mode exists).

## v0.2 performance milestone (plans/M_02.txt; started 2026-10-11)
Brief: plans/AGENT_BRIEF_M2.md (the Bend author's charge turned into review rules:
no row-sized linked structures, no copy without a reason, one balanced fork tree
over owned user-defined chunks ending in flat loops; verify in the emitted C).
Baseline: 3612482 (v0.1 RC). The v0.1 data contract (DESIGN §15) does not change.
- W0 running: measurement harness + provisional baseline (bench/m2/, sonnet);
  engine spikes and DESIGN §16 (chunks, ownership, fusion, reductions, selector; fable);
  strings/reader spikes and DESIGN §17 (coder, ranks, probe ownership, piece reader; opus).
- Measurement policy: agents' numbers are provisional (shared machine); gate numbers
  are taken by the orchestrator with bench/m2/ on a quiet machine.
- 2026-10-11: merged W0 engine spikes + DESIGN §16, W0 strings/reader spikes + DESIGN §17,
  W1a/c (join copies only at splits; describe fused), W1b/e (n_unique radix; when.valid),
  W1d/f (R{v,ok} map_r/zip_r; range-copy slice + range_cell law, 150 laws, 17 mutations).
  Merged master: proofs + verdict ALL PROOFS CHECK, make test 161/161.
  Still running at pause: W0 harness agent (bench/m2/). Open decisions: freeze G2/G3
  thresholds (§16.8, §17.8 propose revisions: q4 >=1.3x, parse >=2x end to end) on a quiet machine.
  Next: W1g (Sort+Head, now T3.4), W2 (§17.7), W3/W4 (§16.7).
- Merged W0 harness (bench/m2/, 41 frozen workloads, expected outputs frozen from 3612482,
  provisional baseline: q1-q6 13/9/24/48/21/111 ms at 1M 1 thread, no thread scaling;
  parse 5.5 s / 2.7 s; RSS 1.3 GB is the reader). Gate runs need load < 2 (the host
  runs other workloads; not yet available).
- Wave 2 running: W2.1+W2.2 (coder, ranks; new modules), T3.1 (liveness/moves + law),
  T3.2+T3.4 (sort pipeline, Sort+Head gather + law), T3.3 (group_by moves),
  W6.1+W6.2 (reader producer + lane; new modules).
- Merged (2026-10-11/12): T3.3 group_by moves; W2.1/W2.2 coder + ranks modules; T3.1 liveness
  moves (+5 laws); W6.1/W6.2 reader producer + lane (41 MB: 0.62 s / 0.34 s at 1 / 12 thr,
  RSS 131 MB, not wired); T3.2/T3.4 sort pipeline + Sort+Head (q4 44 -> 16 ms); W2.4 join on
  the packed flat table (1M distinct join ~0.8-1.3 s); T4.1 fused kernels (+17 laws).
  Master: 176 laws in 18 sections, 45 mutations, 176 tests, verdict green.
- Running: W2.3 coder wiring, W6.3 reader integration, T4.2 eval peepholes (LAWS §19),
  T4.3 Filter+Select shortcut (LAWS §20), T5.1 chunks module (LAWS §21).
- Merged (2026-10-12): W2.3 coder wiring (str group/unique 1M 13.8 s -> 0.18 s), W6.4 CSV fuzz
  (10k cases clean; csv-fuzz-smoke in make ci), W2 pk ranks, T5.1 chunk trees (+11 laws),
  T4.3 Filter+Select step (+5 laws), T5.4 describe column fork (aggregate/gather forks measured and
  removed), T5.2 chunked kernel wrappers (+14 laws; F32 in-order walk anomaly explained and fixed).
  Master 9bfb9a8: 206 laws, 75 mutations, 190 tests, verdict green.
- T4.2 (peepholes, branch worktree-agent-ab4e15f1c2ea65971) conflicts with T4.3's proof; T4.4 is
  integrating them (shared Eval.filter.mask). T5.3 chunked executor running.
