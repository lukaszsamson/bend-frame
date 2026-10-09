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
- Stale prose noticed, not changed (other owners): README.md says "71 laws" and its "Not yet proven" paragraph predates M5; both should
  be refreshed with the final proof counts (see 'M5 part 2': 116 laws) when the proof agent finishes.
- Defects found: none (no regression test or fix needed).

## In progress
- nothing (M5 part 3 stops at the laws above; the remaining Dictionary items are listed under
  M5 part 3 "Not done").

## Decisions
- 2026-10-09 (user): no throwaway hub publish in M6. The clean-consumer check uses a local
  import from a clean clone; the only publish is the proper `bend-frame@0.1.0.0`, done when
  ready and with explicit approval.

## Next (per plan §7)
Merge M5 part 3; then M6 (release candidate; no throwaway publish, see Decisions). Optional before
M6: the in-place kernel content theorems (`Kernel.mask_data`, `Kernel.choose`) and `Kernel.append`,
which would close `Strs.fix`, fill / when over Dictionaries and concat.
Not yet measured: the cost of the narrower default optimizer (no predicate
or projection pushdown) on the q1–q6 benchmark.
