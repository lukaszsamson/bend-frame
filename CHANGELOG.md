# Changelog

## 0.1.0 (release candidate, 2026-10-09; not yet published)

The first release: a small Bend-native dataframe library with tested ETL operations, verified core buffer operations and evaluator typing, and a result-preserving default optimizer under documented input and runtime assumptions.

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

- 147 laws in `LAWS.bend`, all proven in `PROOF*.bend` over the production functions, checked by `bend PROOF.bend` and by `bend PROOF.bend --verdict` (BendTT). No axiom, no `@unsafe`, no open law.
- The default optimizer is proven result-preserving over the production runner for every plan and environment (frames and errors).
- The evaluator is proven type-sound: an expression the shared analysis accepts yields the predicted dtype and height, failing only where a strict cast may.
- Buffer and column contents: gather, compact (filter), the validity combinators, iota, the U32 sum and popcount folds, head, slice (U32), concatenation's append, the in-place null reset (`Eval.fix`, every column kind) and selection (`fill_null` on strings, `when`'s string storage), and the Dictionary string operations that keep every decoded string (encode, decode, merge, recode, find, gather, compact, append).
- Hypotheses the laws take rather than prove: row counts that fit the buffers (`CRoom`, `CatFits`), and for Dictionaries that each hash probe stops at an empty slot or at the key. `DESIGN.md` section 8 has the assurance matrix and the exact list of what is tested but not proven.
- Eleven mutation fixtures (`tests/proof_negative/`) check that a one-line change to a proven production function breaks its proof.

### Testing

- 143 test files (`make test`), regression tests for every defect of the two pre-release reviews, goldens against Polars for six benchmark queries at 1k, 100k and 1M rows (`make bench-check`).
- A differential generator: eager vs raw-lazy vs optimized-lazy, and against a Polars-based oracle, in Raw and Dictionary string storage (22,000 generated cases in the M6 run, 0 failing), plus F32 reductions against an exact reference (`make diff-reduce`).

### Known limits

- Performance at 1M rows on one thread: 0.9-17x Polars' time (2-3.5x on the string-keyed queries); no thread scaling (12 threads ~1.0x of 1); peak RSS about 1.3 GB vs Polars' 168 MB; group_by / unique / join over fully distinct string keys 30-330x slower than Polars. Numbers in `bench/README.md`.
- Not proven, tested only: `optimize_full`, the cell values of most evaluator operations, sort, group_by and join, CSV, every floating-point result, Dictionary lookups that answer "absent".
- Out of scope: F64/I64/U64, dates, lists, structs, maps, window functions, rolling/cumulative, explode/pivot, regex, full/cross/as-of/non-equi joins, Parquet/IPC/SQL, streaming, GPU, automatic parallel scheduling, the Explorer API.
- Deliberate differences from Polars are listed in `README.md` ("Differences from Polars").
- The CI workflow (`.github/workflows/ci.yml`) has not run yet: the repository has no remote. `make ci` runs the same gates locally.
