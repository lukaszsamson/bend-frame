# Pending regressions (tests/regress/pending/)

Regressions for DESIGN.md 15.10 rows whose test needs API that does not exist yet. They are
written against the contract's exact signatures (DESIGN.md 15.2) and kept as
`pending/<name>.bend.txt` so `scripts/test.sh` and `make check` skip them.

To activate one: implement the API, then `mv pending/<name>.bend.txt <name>.bend` (the
imports are already written for `tests/regress/`), run it, and add `#! xfail <ID>` on line 1
if the defect is not fixed in the same change. Expected output (`#|` lines) comes from
`bench/contract/regress_expect.py` (`cd bench && uv run python contract/regress_expect.py
--write <name>`), which handles both places.

| file | rows | API it needs (DESIGN.md) | milestone |
|---|---|---|---|
| `B04_c_add_source.bend.txt` | B04-c | `DF.add_source(env, name, f) -> Env & Plan` (15.2.2) | M1 |
| `B04_d_validate_bindings.bend.txt` | B04-d | `DF.validate_bindings(p, env) -> Env & Res(Unit)` (15.2.2, 15.7) | M1 |
| `B04_i_row_cap.bend.txt` | B04-i | `K.Kernel.max_rows()`, `K.Kernel.check_rows(n) -> Maybe<&2, E.Err>` (15.8), `DF.concat_vertical` (M3); the join case needs only the guard | M1 (+M3 concat) |
| `B01_c_zero_column_m3.bend.txt` | B01-c (C22, C24) | `DF.drop / DF.lazy_drop`, `DF.unique / DF.lazy_unique`, `DF.concat_vertical / DF.lazy_concat_vertical` (15.2.3, 15.2.4) | M3 |
| `B05_h_proof_negative.bend.txt` | B05-h | no API: a negative proof fixture (expects `SOME PROOFS FAIL`). It runs and passes under `scripts/test.sh` today, but `make check` runs `bend --check-only` on every `tests/**/*.bend` and fails on it. Activate once `make check` skips fixtures whose expectation is `SOME PROOFS FAIL` (or move it to `tests/proof_negative/` with that exclusion, plan T5). | M0 harness |

Activated in M1 (B03 numerics): `B03_d_floor_div`, `B03_e_try_cast`, `B03_i_checked_i32` (now
`tests/regress/*.bend`, passing).

Assumptions made where the contract names an entry but not its exact form (check them when
implementing): the lazy builders are `DF.lazy_drop(p, names)`, `DF.lazy_unique(p, subset)`,
`DF.lazy_concat_vertical(ps: List<&2, Plan>)` ("`lazy_<verb>` builds the node", 15.2);
`DF.validate_bindings` reports the first error with collect's texts; a join of 2900 x 2900
equal keys reports `too many rows: 8410000 exceeds 8388608`.

Not written (the contract does not fix the entry point): the CSV row-cap test "through a
`Csv.rows` entry taking a record count" and the `from_scalars` test "through a counted-list
entry" (15.8). M1 should add them with the guard.

## Rows with no code regression

Documentation-only rows; behaviour they describe is pinned where possible:

| row | what is tested instead |
|---|---|
| B02-k (README round-trip claim) | `B02_k_inference_roundtrip.bend` pins that "007" comes back as u32 7 |
| B03-g (README: integer mean is f32) | `B03_g_int_mean_f32.bend` pins the f32 dtype |
| B03-j (README: u32 wraps) | `B03_j_u32_wrap.bend` pins the wrap |
| B04-f (README: collect vs collect_schema) | `B04_d_bindings.bend` "missing": collect_schema answers a schema, collect fails |
| B04-g (README: right key dropped) | `B04_g_join_right_key.bend` |
| B04-h (doc + M3 example) | `B04_h_group_agg_shape.bend` (error text and the workaround) |
| B04-k (README: maintain_order=False) | `B04_k_maintain_order_false.bend` |
| B05-a, B05-b, B05-c (comparator) | `bench/tests/test_check.py` (`test_100000_vs_100001_fails`, `test_nan_vs_integer_fails`, `test_csv_module_quoting`) |
| B05-d (bench.sh `\|\| true`) | scripts/bench.sh (harness agent) |
| B05-e (stale Kahan comments) | text only. Already corrected in M0 (DESIGN 14 "M0 T1 / B05"): `bench/check.py` and README no longer mention Kahan; `src/groupby.bend`, `src/kernels.bend` and `bench/README.md` describe today's code accurately (mean / eager sum are Kahan). M1 (B03): the code is now Neumaier (15.5.3) and `src/groupby.bend`, `src/kernels.bend`, `src/fmt.bend`, `bench/README.md`, README say so |
| B05-f (CI, make check) | `.github/workflows/ci.yml`, Makefile |
| B05-g (eager / raw / opt agreement) | every file here prints the three dumps; `B05_g_optimizer_traps.bend` adds Fable's ten traps |
| B05-i (README overclaims) | M6 README |
