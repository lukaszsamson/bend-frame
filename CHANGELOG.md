# Changelog

## 0.2.0 (performance milestone, 2026-10-11; not published)

The plan is `plans/M_02.txt`; the gate report is `plans/GATES_V02.md`. **The v0.1 data contract (`DESIGN.md` 15) is unchanged**: the same values, validity, names, row order, F32 bits (the existing NaN-payload relaxation aside), errors and error order, for every operation, eager and lazy. No new API surface beyond the engine and reader selectors.

Candidate claim, as far as the gates demonstrate it: "owned chunks and fused kernels reduce copying and improve measured throughput; parallel execution preserves the documented semantics on the supported paths". The load-independent gates are met: correctness (G1), memory on the frozen 1M workload (G4), proofs (G5) and the phase / copy report (G6). **Every timing number below is PROVISIONAL**: the shared machine was never quiet (1-minute load >= 2 before every run), so by M_02 section 5 the timing gates G2 and G3 are recorded as UNEVALUATED, with the provisional observation beside each cell (several are not met even provisionally; `plans/GATES_V02.md` lists every one).

### Changes

- **CSV reader (the default since 0.2.0).** A sequential producer of flat packed bytes in 240 KiB pieces with the record boundaries found in the same walk (`src/csvprod.bend`), ONE balanced fork of typed lanes over the regions (`src/csvlane.bend`: a generated one-def tokenizer, typed loops with cold private records, no per-cell string or list), and a sequential combine in region order that keeps v0.1's error precedence and dictionary codes (`Csv.v2.*` in `src/csv.bend`). The v0.1 reader is kept, selectable (`csv_engine_v01()`, `read_csv_engine`, `collect_engine`), and is the pinned reference of the CSV tests and fuzz.
- **Distinct-key strings.** A flat presized hash coder (`src/hcode.bend`; first-appearance ids, hash hits compared against the strings) and a lexical rank stage by radix refinement (`src/ranks.bend`) replace the Base-Map coder in group_by, unique, Raw n_unique, Raw sort keys and Dictionary ranks; the join probes a packed flat string table sequentially (no table clone per split).
- **Evaluator fusion** (on in the default executor): literal operands as scalars (F1), null-propagating zips with validity in one loop (F2), total casts inside the zip (F3), `fill_null` with the dtype default as a validity change (F4), filter predicate mask and count in one pass (F5), up to four aligned columns compacted per loop (F6), and the Filter + plain Select step at the plan root (F8). Kleene logic and fallible casts are not fused.
- **Fewer copies.** A liveness pass moves single-reference columns and borrows where a kernel hands the buffer back; group_by moves dead inputs and codes its key without a clone; the join copies its table only at a split; describe borrows and fuses its count / sum / min / max; `slice` is one range copy; `Sort + Head` gathers only the kept rows of the exact full argsort; the radix sort reads keys in place with one scan pass, skips sorted words and ping-pongs two buffers; n_unique is a radix sort plus a run count.
- **Chunked engine (opt-in).** Owned chunk trees (`src/chunks.bend`), generated chunked kernel wrappers (`src/ckernels.bend`) and a chunked executor (`src/cexec.bend`) behind `collect_with(engine_chunked(), ..)`: row-wise operators fork over leaves of 2^14 rows; sort, join, group_by, unique and describe run the flat code behind a boundary; a `scan_csv` whose consumer is row-wise is read straight into chunk leaves by the v0.2 reader. Exact against the reference engine on every differential case.
- **Parallel shape.** Every parallel let follows one rule found in this milestone (the Bend 2.0.36 scheduler's fork-shape rule, `DESIGN.md` 16.10): a forking def matches and forks and calls nothing non-flat before its parallel let; `make fork-audit` checks it statically and is part of `make ci`.
- **Tooling.** `bench/m2/` (the frozen workload harness against the pinned baseline 3612482, with an instrumented copy / allocation mode, `make m2-g6`), `make diff-chunked` (G1), `make csv-fuzz` / `csv-fuzz-smoke` (the v0.2 reader against v0.1), `make fork-audit`; `make ci` now also runs `csv-fuzz-smoke` and `fork-audit`, and `diff-smoke` runs every case through the chunked engine too.

### Measured (PROVISIONAL; `plans/GATES_V02.md`, `bench/m2/results/w8-*.jsonl`)

Against the pinned v0.1 baseline (3612482), same driver, Apple M2 Pro, medians of 5 fresh interleaved processes, load 1.4-5.8 (so: PROVISIONAL), 1M rows, 1 thread unless noted:

- CSV parse of the 41 MB sales file: 3,966 -> 632 ms (6.3x); 1,814 -> 334 ms at 12 threads. Peak RSS of the 1M-row q1-q6 runs: 1,315-1,346 MB -> 190-314 MB (G4's 600 MB met).
- Compute (default executor): q1 10 -> 3 ms, q2 7 -> 3, q3 20 -> 12, q4 40 -> 13, q5 17 -> 10, q6 98 -> 49 (16 at 12 threads); end to end (parse + compute) 3.97-4.06 s -> 0.63-0.68 s.
- n_unique over 2^20 distinct U32 1,803 -> 16 ms; group_by / unique over 1M distinct strings 12.5 s -> 0.13 s; the 1M distinct-key join 4.2 s -> 0.36 s.
- Thread scaling (12 vs 1): parse 1.89x; describe 3.1x; with the opt-in chunked engine on already-chunked inputs q1 4.0x, q2 3.8x, a 50% filter 5.9x, q3 / q5 1.4x; sort, join, group_by and unique do not scale.
- Copies: the compute phase of q1-q6 copies no array block (q3 and q5: under 5 kB; v0.1: 8-105 MB per query), exact counts from the instrumented build (`make m2-g6`).
- Regressions: the 1k-row q3 and q5 controls are 1.57x and 1.25x slower than v0.1 (~0.1 ms per query, with either reader); every other cell is equal or faster.

### Verified scope

- 231 laws in `LAWS.bend` (149 in 0.1.0; 82 added: `range_cell`, and sections 16-22: moves, Sort + Head, fused kernels, fusion peepholes, Filter + Select, chunk trees, chunked kernel wrappers), all proven in `PROOF*.bend` over the production functions, checked by `bend PROOF.bend` and `--verdict`. No axiom, no `@unsafe`, no open law; no v0.1 law weakened or dropped; the Dictionary probe hypotheses stay conditional.
- `make mutation-check`: 92 in-place mutations of production functions (14 in 0.1.0), all caught, the unmutated copy accepted.
- New proven facts that matter beyond their kernels: `croom_of_cap` derives v0.1's `CRoom` hypothesis for per-leaf compaction; `sort_head_run` / `collect_obs` relate the physical runner `collect` executes to `Exec.run_pure`; `filter_select_run` proves the Filter + Select step.
- Tested only (`DESIGN.md` 8.2): the chunked executor (no theorem relates it to `Exec.run_pure`), the v0.2 reader, the string coder, the rank stage, the radix sort pipeline, n_unique, describe's fused pass, the balanced list forks, and the native scheduler.

### Testing

- 203 test programs (files) in `make test` (158 in 0.1.0), 0 XFAIL. `docs/COVERAGE.md`: 816 operation x kind cells, 762 covered, 54 n/a with a reason, 0 missing.
- G1 differential counts are in `plans/GATES_V02.md` (generated cases through the reference and the chunked engine at four grains, Raw and Dictionary, deep plans, join stress, interpreter vs native; the CSV fuzz of the v0.2 reader against v0.1 at seven piece sizes).
- `make ci` green on the 0.2.0 tree (time and result in `plans/STATUS.md` "W8").

### Deviations from the plan (each recorded in `DESIGN.md` 14, v0.2 entries)

- G2 parse target revised at W0 from >= 4x to ">= 2x end to end and >= 4x on the fork phase" (`DESIGN.md` 17.8, 17.10 item 1): the File API returns cons lists on the IO thread, so the producer is serial. The G2 / G3 per-query thresholds of 16.8 / 17.8 were proposed at W0 and never frozen on a quiet machine.
- The chunked engine converts lazily (only where an operator needs the other representation), runs group_by flat, and reports data errors by a flat rerun; the reader picks chunks or a flat frame by the scan's consumer. The facade takes no chunk frame (results are flattened once).
- The group_by aggregate fork, the column-gather fork after a sort and a fused group_by scatter were built, measured and removed (no gain on this runtime); describe's column fork is kept.
- Not done: W2.5 (owned-partition coder), W2.6 (Dict index on flat arrays), W7 (flat string storage; deferred per `DESIGN.md` 17.11), a chunked group_by or partitioned parallel sort.
- D7 says the new layout stays opt-in "until G1-G6 pass"; the READER default was flipped on G1 (exact on every CSV test, the 10,000-case fuzz x 7 piece sizes, the adversarial corpus), G4 and provisional parse evidence while G2 / G3 are unevaluated (`DESIGN.md` 14 "W8"). The chunked ENGINE was not flipped. Nothing was removed (removal is a later explicit gate).

### Not claimed

- That every kernel forks, or that thread scaling is general: sort, join, group_by and unique stages do not scale with threads; F32 sums are one sequential pass by contract (`DESIGN.md` 15.5.3); the CSV producer is serial (File API), so the parse scales about 2x end to end.
- That any timing gate passed: no measurement was taken on a quiet machine.
- That hashing or the CSV reader is linear in the worst case (collisions, skew, long records): growth is reported per row and byte at 100k / 300k / 1M, not bounded.
- A verified chunked engine, reader, coder or sort (tested only), Polars compatibility, native runtime correctness; everything 0.1.0 did not claim.

### Known limits

- The machine for every number: Apple M2 Pro (8 P + 4 E cores), shared with other jobs; Bend 2.0.36 native. Linux and hosted CI have never run.
- Peak RSS and times are workload-dependent; small inputs (under 2^14 rows) run the flat loops with no fork.

## 0.1.0 (experimental release candidate, 2026-10-10; not yet published)

The first release, an EXPERIMENTAL one (plans/STATUS.md Decisions, 2026-10-10): the default optimizer is R1 only (adjacent `head` merging), the Dictionary string assurance is conditional (`Probe` / `EncProbe` hypotheses; index completeness is not proven), and the remaining proof work is deferred (R2-R5 as theorems, the grouped scatter invariant for `group_by`, Dictionary completeness and rank order). The release claim: a small Bend-native dataframe library with tested ETL operations, verified core buffer operations and evaluator typing, and a result-preserving default optimizer under documented input and runtime assumptions.

Not claimed: Polars compatibility, a verified engine, verified sort/group/join partitioning, CSV completeness, floating-point accuracy, native runtime correctness.

Toolchain: Bend 2.0.36, Lean 4.34.0 (for `--verdict`), Polars 2.0.0 for the reference side (pins in `TOOLCHAIN`).

### License

Apache-2.0 (`LICENSE`, `NOTICE`). `src/csvparse.bend` is a fork of the MIT-licensed hub package
`bend-csv-parser@0.1.0.1` and keeps its MIT notice.

### What is in it

- Five nullable dtypes (`Bool`, `U32`, `I32`, `F32`, `Str`) with no implicit casts; checked column and frame builders.
- Eager verbs and lazy plans with one data semantics: `select`, `with_columns`, `filter`, `sort` (stable, multi-key), `group_by`, inner / left / semi / anti joins, `head`, `slice`, `tail`, `drop`, `rename`, `unique`, `concat_vertical`, `describe`, `show`, `dump`.
- Expressions: casts (strict `cast`, lenient `try_cast`), arithmetic incl. `floor_div` / `mod` with floor rounding, comparisons, Kleene `and` / `or`, `when`, `is_in`, `clip`, `is_between`, `fill_null`, `abs`, `sqrt`, string predicates and `len_chars`, and the reductions `sum mean min max count len first last n_unique std var median`, in `group_by` and as global reductions.
- Lazy plans: schema and type errors before any row is read (`collect_schema`), binding validation (`validate_bindings`), `explain`, a default optimizer that merges adjacent `head`s, and an opt-in `optimize_full` (filter merge, predicate and projection pushdown, head sink).
- CSV: reading with type inference or explicit schemas, a bounded scan prefix for lazy scans, a streaming reader, writing with quoting and F32 formatting options; the contract is `DESIGN.md` 15.6.
- `Str` columns stored as plain strings or as a Dictionary (codes into distinct entries); the readers choose per column by cardinality, which gave 5-20x on the string-keyed benchmark queries at 1M rows.
- One numeric policy: a shared F32 total order (NaN greatest, `-0.0 == 0.0`), Neumaier-compensated F32 sums with a non-finite guard, wrapping integer arithmetic.
- A 2^23 row cap, checked before allocating.
- `DF.dump`, a typed text form of a result (dtypes, validity, F32 bits, errors), used by the tests and the differential checks.

### Verified scope

- 149 laws in `LAWS.bend`, all proven in `PROOF*.bend` over the production functions, checked by `bend PROOF.bend` and by `bend PROOF.bend --verdict` (BendTT). No axiom, no `@unsafe`, no open law.
- The default optimizer (adjacent `head` merging, R1 only) is proven result-preserving over the production runner `Exec.run_pure` for every plan and environment (frames and errors), scan plans included (scans live in an unnamed `scans` field of the environment; `hmerge_keeps_scans` / `release_keeps_scans` prove the optimized plan reads the same scans in the same order). Not proven: that `Plan.schema` and `Exec.validate` agree for `Optimize.release(p)` and `p` (true by inspection), and the IO materialisation `Exec.mat` itself.
- The evaluator is proven type-sound: an expression the shared analysis (`A.Expr.analyse`, used by `select`, `with_columns` and `filter`) accepts yields the predicted dtype and height, failing only where a strict cast may. The 20 older expression-typing laws (`LAWS.bend` section 2) are about `X.Expr.type`, which production uses only for `group_by`.
- Buffer and column contents: gather, compact (filter), the validity combinators, iota, the U32 sum and popcount folds, head, slice (U32), concatenation's append, the in-place null reset (`Eval.fix`, every column kind) and selection (`fill_null` on strings, `when`'s string storage), and the Dictionary string operations that keep every decoded string (encode, decode, merge, recode, find, gather, compact, append).
- Hypotheses the laws take rather than prove: row counts that fit the buffers (`CRoom`, `CatFits`), and for Dictionaries that each hash probe stops at an empty slot or at the key. `DESIGN.md` section 8 has the assurance matrix and the exact list of what is tested but not proven.
- Mutation evidence: eleven fixtures (`tests/proof_negative/`) mutate a renamed copy of a production function and try the production proof term against it (five are name-sensitive per their headers: an unmutated renamed copy is refused too, so they show a copy is rejected); and `make mutation-check` mutates 14 production functions in place and requires `bend PROOF.bend` to fail each time (all 14 caught).

### Testing

- 158 test programs (files; each holds many cases, so this is not an assertion count) in `make test`, regression tests for every defect of the two pre-release reviews, and `docs/COVERAGE.md`, the operation x case matrix (774 cells: 727 covered, 47 n/a with a stated reason, 0 missing) with a def-call report over `src/`.
- Goldens for six benchmark queries at 1k, 100k and 1M rows: q1, q2, q4, q5 equal Polars' output, q6 is within rtol 5e-5, and q3 is checked against the exact-rational F32 reference (`bench/golden.py`), not Polars (Polars' grouped f32 sum differs by an ulp or two: tiny fixture `inland`, Polars 96373.4141, reference 96373.4062). `make bench-check` covers 1k and 100k; 1M needs `CHECK_MAX=1000000 BENCH_MODE=check scripts/bench.sh`; the tracked 1k golden (`bench/golden/n1000`) is regenerated by each run.
- `make ci` runs: toolchain-check, check, runner-check, diff-driver-check, test, proofs, verdict, mutation-check, bench-check, diff-smoke (200 strict cases each in Raw and Dictionary storage, then the F32 reduction check), consumer-check and coverage. Every differential and reduction failure exits 1. Larger runs (`make diff`, `make diff-reduce`) are manual.
- A differential generator: eager vs raw-lazy vs optimized-lazy, and against a Polars-based oracle, in Raw and Dictionary string storage (22,000 generated cases in the M6 run, 0 failing), plus F32 reductions against an exact reference (`make diff-reduce`).

### Fixed after review

Two independent reviews of the first release candidate (`plans/REVIEW_V01_FABLE.txt`, `plans/REVIEW_V01_ASTRA.txt`) led to these changes before publication; `plans/STATUS.md` lists every finding and its disposition.

- Scan source identity: a CSV scan's frame was bound under the name `#scan<k>` and a user `source("#scan0", ..)` silently read it (`concat([source "#scan0" x=[1], scan x=[2]])` gave `x=[2, 2]`). Scans now live in a separate, unnamed `scans` field of `Env`; no name is reserved. New laws `hmerge_keeps_scans` / `release_keeps_scans`; `release_run` now speaks about scan plans directly. Regressions `tests/regress/V01_a_*` and `V01_b_*` (every lazy verb over `scan_csv` against the eager verb over `read_csv`).
- Differential exit status: `make diff` without `--strict` exited 0 on a failure the shrinker labelled a known defect. Any failure now exits 1 (classification only labels); `bench/diff/tests/test_exit.py` is the permanent driver regression; `reduce.py` has no allowlist.
- CI additions: `diff-driver-check`, `diff-smoke` (bounded strict Raw and Dictionary runs plus the reduction check), `mutation-check`, `consumer-check` and `coverage` are part of `make ci`; the runner self-test's timing margins were made robust under load.
- Mutation check: `scripts/mutation_check.sh` mutates 14 production functions in place (not renamed copies) and requires the proofs to fail.
- Coverage matrix: `scripts/coverage_matrix.py` and `docs/COVERAGE.md` (727 covered, 47 n/a with reasons, 0 missing), with gap-filling tests (`tests/coverage/`) and Polars twins (`bench/coverage/`).
- Documentation: the benchmark equivalence claim (q3), the `bench-check` scope, the exact scope of `release_run`, the mutation-evidence wording, the "failures fail the build" claim, test counting (files, not assertions), CI and platform status, and several stale comments (`LAWS.bend`, `tests/regress/B03_b_*`, `bench/diff/README.md`) were corrected.
- License: Apache-2.0 (noted above).

### Known limits

- Performance at 1M rows on one thread: 0.9-17x Polars' time (2-3.5x on the string-keyed queries); no thread scaling (12 threads ~1.0x of 1); peak RSS about 1.3 GB vs Polars' 168 MB; group_by / unique / join over fully distinct string keys 30-330x slower than Polars. Numbers in `bench/README.md`.
- Not proven, tested only: `optimize_full`, the cell values of most evaluator operations, sort, group_by and join, CSV, every floating-point result, Dictionary lookups that answer "absent".
- Out of scope: F64/I64/U64, dates, lists, structs, maps, window functions, rolling/cumulative, explode/pivot, regex, full/cross/as-of/non-equi joins, Parquet/IPC/SQL, streaming, GPU, automatic parallel scheduling, the Explorer API.
- Deliberate differences from Polars are listed in `README.md` ("Differences from Polars").
- The CI workflow (`.github/workflows/ci.yml`) has never run: the repository has no remote, so the workflow and its Bend archive checksums are untested. `make ci` runs the same gates locally. macOS arm64 is the only platform built and tested; Linux x86-64 has never been run.
