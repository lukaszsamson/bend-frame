# Changelog

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
