# bend-frame

A columnar dataframe library for [Bend](https://bend-lang.com/) 2 (checked against Bend 2.0.36), shaped after the Polars 2.0 eager and lazy APIs, for CSV ETL: load, clean, derive, combine, aggregate, sort and export. Queries are built as a lazy `Plan`, a pure data tree, and the output schema is resolved before any row is read: `DF.collect_schema` returns a strict error such as a filter on a `u32` column, and `DF.collect` refuses the same plan with the same error. Row order is part of the contract: `select`, `with_columns`, `filter` and `head` keep input order, `sort` is stable and multi-key, and `group_by`, `unique` and joins answer in first-appearance and left-row order. Dtypes are `Bool`, `U32`, `I32`, `F32` and `Str`, each nullable through a validity mask, with no implicit casts.

**What v0.1 claims, and only this:** A small Bend-native dataframe library with tested ETL operations, verified core buffer operations and evaluator typing, and a result-preserving default optimizer under documented input and runtime assumptions.

**Not claimed:** Polars compatibility, a verified engine, verified sort/group/join partitioning, CSV completeness, floating-point accuracy, native runtime correctness.

What "verified" covers, exactly, is in [Laws](#laws) below and in `DESIGN.md` section 8; what is tested and not proven is listed there too.

## Quickstart

From a checkout, with the Bend binary at `~/.bend/bin/bend`:

```bend
import ./frame.bend as DF
```

The library is not yet published to the Bend hub. When it is (`bend login`, then `bend frame.bend --publish bend-frame@0.1.0.0`), the import will be by package name. Until then, import from a checkout as above.

This is `examples/quickstart.bend` (comments trimmed). It reads `bench/fixtures/tiny.csv`, adds a revenue column and filters on it. The file sits in `examples/`, so its import path is `./../frame.bend`:

```bend
import ./../frame.bend as DF

# revenue = qty * price * (1 - discount), a missing discount counts as 0
def revenue() -> DF.Expr():
  DF.mul(DF.mul(DF.cast_f32(DF.col("qty")), DF.col("price")),
         DF.sub(DF.lit_f32(1.0), DF.fill_null(DF.col("discount"), DF.lit_f32(0.0))))

# add_revenue and big_ok (in the file) pass an error through and otherwise call
# DF.with_columns and DF.filter

def main() -> IO(Unit):
  do IO<Unit>:
    r : DF.ResT(DF.Frame()) <- DF.read_csv("bench/fixtures/tiny.csv")
    IO.print(DF.show(big_ok(add_revenue(r))))
```

Output (`~/.bend/bin/bend examples/quickstart.bend`, run from the repo root):

```
shape: (4, 8)
+-----+---------+---------+-----+--------+----------+------+-----------+
| id  | region  | product | qty | price  | discount | ok   | revenue   |
| --- | ---     | ---     | --- | ---    | ---      | ---  | ---       |
| u32 | str     | str     | u32 | f32    | f32      | bool | f32       |
+=====+=========+=========+=====+========+==========+======+===========+
| 1   | inland  | prod_61 | 78  | 333.37 |          | true | 26002.86  |
| 10  | coastal | prod_24 | 55  | 197.43 | 0.17     | true | 9012.679  |
| 11  | island  | prod_04 | 55  | 407.87 | 0.28     | true | 16151.652 |
| 18  | coastal | prod_33 | 88  | 190.93 | 0.14     | true | 14449.582 |
+-----+---------+---------+-----+--------+----------+------+-----------+
```

More examples, each importing only the facade: `examples/lazy.bend` (below), `examples/sales_summary.bend` (group_by, global reductions, sort), `examples/dirty_csv.bend` (cleanup with `try_cast`, `when`, `fill_null`, string predicates), `examples/dedupe.bend` (`concat_vertical`, `unique`, semi and anti joins, eager and lazy) and `examples/join.bend`.

## Lazy plans and the strict early error

`examples/lazy.bend` builds a plan over a CSV scan: keep ok sales, then per region the total quantity, mean price and row count, sorted by region.

```bend
def report_plan(p: DF.Plan()) -> DF.Plan():
  DF.lazy_sort(
    DF.lazy_group_by(
      DF.lazy_filter(p, DF.col("ok")),
      [DF.col("region")],
      [DF.alias(DF.sum(DF.col("qty")), "qty_sum"),
       DF.alias(DF.mean(DF.col("price")), "price_mean"),
       DF.alias(DF.len(), "count")]),
    [DF.asc("region")])
```

`DF.explain` before and after `DF.optimize_full` (real output). The full optimizer adds a projection under the filter, so only the columns the plan uses flow on (the CSV itself is still parsed whole). `DF.collect` uses the default optimizer `DF.optimize`, which only merges adjacent `head`s (the one rewrite proven result-preserving); `DF.collect_full` runs `optimize_full` (filter merge, predicate and projection pushdown, a head sink), which is opt-in and tested, not proven:

```
-- plan
SORT BY [col("region")]
  GROUP_BY [col("region")] AGG [col("qty").sum().alias("qty_sum"), col("price").mean().alias("price_mean"), lit(1).len().alias("count")] MAINTAIN_ORDER
    FILTER col("ok")
      SCAN CSV bench/fixtures/tiny.csv [id:u32, region:str, product:str, qty:u32, price:f32, discount:f32, ok:bool]
-- optimized plan (optimize_full)
SORT BY [col("region")]
  GROUP_BY [col("region")] AGG [col("qty").sum().alias("qty_sum"), col("price").mean().alias("price_mean"), lit(1).len().alias("count")] MAINTAIN_ORDER
    FILTER col("ok")
      SELECT [col("region"), col("qty"), col("price"), col("ok")]
        SCAN CSV bench/fixtures/tiny.csv [id:u32, region:str, product:str, qty:u32, price:f32, discount:f32, ok:bool]
```

The schema comes out first, with no data read (`-- schema of the plan (no data read)`): `region:str, qty_sum:u32, price_mean:f32, count:u32`.

A filter on a `u32` column is refused before any row is read. The example builds `DF.lazy_filter(p, DF.col("qty"))` and prints:

```
collect_schema: error: TypeMismatch in filter: expected bool, got u32
collect: error: TypeMismatch in filter: expected bool, got u32
```

`scan_csv` reads only a bounded prefix of the file up front (64 KiB chunks until `infer_rows + 1` line ends outside quotes, default 100 rows) to freeze the schema; no column is built there. `collect` checks the whole plan (`collect_schema`, then the bindings), reads every scanned file once, strictly, with its frozen schema, then runs: a bad value past the prefix is an error at `collect`, not at `scan_csv`, and a scan's error is reported before any error of an operator above it.

## Features

### Operations

- Eager (`Frame -> ResT(Frame)`, an error is a value): `select`, `with_columns`, `filter`, `sort` (multi-key, per-key `asc` / `desc` and nulls placement), `group_by` with `sum mean min max count len first last n_unique std var median`, `inner_join`, `left_join`, `semi_join` and `anti_join` (multi-key), `head`, `slice` (offset and length, clamped), `tail`, `drop`, `rename` (simultaneous `(from, to)` pairs), `unique` (keep first, input order, `[]` = every column), `concat_vertical` (identical names, dtypes and order), `describe`, `show`, `dump` (the typed oracle text: every dtype, name, validity and F32 bit pattern); `then` / `then_io` chain them, passing an error through.
- Lazy (`Plan`): `lazy_select`, `lazy_with_columns`, `lazy_filter`, `lazy_sort`, `lazy_group_by`, `lazy_head`, `lazy_inner_join`, `lazy_left_join`, `lazy_semi_join`, `lazy_anti_join`, `lazy_slice`, `lazy_tail`, `lazy_drop`, `lazy_rename`, `lazy_unique`, `lazy_concat_vertical`, with `source` / `add_source` / `empty_env` for in-memory frames (several named frames in one env; a frame may be read more than once, e.g. a self join) and `scan_csv` for files. Every verb has the same data semantics eagerly and lazily.
- Frames and columns: `column` builds a checked nullable column from a dtype (`t_bool` .. `t_str`) and scalars (`s_null`, `s_bool`, `s_u32`, `s_i32`, `s_f32`, `s_str`), and a first scalar of the wrong dtype is a `TypeMismatch`; `from_columns` with `named` assembles a frame. `schema` and `height` answer the frame's schema and row count and hand the frame back, as a pair.
- Inspect and run: `collect_schema`, `schema_show`, `explain`, `validate_bindings`, `optimize` (the default: adjacent-head merging only), `optimize_full` (opt-in: filter merge, predicate and projection pushdown, head sink), `collect`, `collect_raw` (no optimizer), `collect_full`, and `collect_show` (collect, then the table or the error text). `collect_schema` predicts the static schema and type errors; `validate_bindings` predicts the binding errors (a missing source, a name bound twice, a frame whose schema differs from the plan's); the rest (IO, data-dependent errors such as a failing strict cast or the row cap) shows up only at `collect`.
- CSV: `read_csv` (types inferred per column), `read_csv_opts` / `read_csv_schema` (separator, header or not, inference rows, explicit dtypes), `scan_csv` / `scan_csv_opts` / `scan_csv_schema` (the last one is pure: no IO until `collect`), `write_csv` / `write_csv_opts` (separator, header or not, F32 shortest digits or fixed decimals). A quoted `""` is the empty string and an empty field is null, on read and on write.
- String storage: a `str` column is held either as plain strings (Raw) or as a Dictionary (codes into a table of distinct strings). The readers choose per column (Auto: a Dictionary while the column has at most max(16384, rows / 64) distinct values); `read_csv_enc` with `str_raw` / `str_dict` / `str_auto` forces a choice, `encode_strings` converts a frame, `dict_columns` reports which columns are Dictionaries. Values, dtypes and every result are the same in both storages; only time and memory differ.

### Expressions

- Columns and literals: `col`, `lit_u32`, `lit_i32`, `lit_i32_neg`, `lit_f32`, `lit_str`, `lit_bool`, `lit_null`, `alias`. `lit_i32(v)` with `v >= 2^31` (`lit_i32_neg(v)` with `v > 2^31`) is a cast that fails when evaluated, never a silently negative value; `i32(v)` / `i32_neg(v)` answer a checked `Res(I32)`.
- Casts: `cast`, `cast_f32`, `cast_u32` are strict (the first value that does not convert is an error naming its row); `try_cast` turns those values into nulls.
- Arithmetic: `add sub mul`, `div` (`f32` only), `floor_div` and `mod` (`u32`/`i32`), `neg`, `abs`, `sqrt` (`f32`).
- Comparison: `eq ne lt le gt ge`, `is_between` / `is_between_closed` (expression bounds), `is_in` (a literal list).
- Boolean: `and or not` (Kleene).
- Conditionals and nulls: `when(cond, then, otherwise)` (a null condition picks `otherwise`), `clip`, `is_null`, `is_not_null`, `fill_null`.
- Strings (literal patterns, case-sensitive, code points): `len_chars`, `contains_literal`, `starts_with`, `ends_with`.
- Aggregations: `sum mean min max count len first last n_unique std var median`, as `group_by` aggregations and as global reductions anywhere in `select` / `with_columns` / `filter`, eagerly and lazily. A `select` of only literals and reductions gives one row (also on an empty input); one that mixes them with a column broadcasts them; `with_columns` and `filter` compute reductions over their whole input, then broadcast. A reduction of a reduction is an error. `select([])` gives a `(0, 0)` frame.

### Null semantics

- Every operation ANDs the validity masks of its inputs, so a null operand gives a null result. Null slots hold the dtype default in the data.
- `and` / `or` are Kleene: `false and null` is `false`, `true or null` is `true`. `eq` and the other comparisons are not: a null operand gives null.
- `filter` keeps the rows where the predicate is true. A null predicate drops the row.
- `sum`, `mean`, `min`, `max`, `count`, `std`, `var` and `median` skip nulls. `len` counts rows, `first` and `last` keep a null row, `n_unique` counts null as one value.
- `group_by` and `unique` put all null keys in one group. Join keys: a null key never matches.
- `sort` puts nulls first unless `nulls_last`, the same default as Polars.

### Differences from Polars

The full list, with the Polars 2.0.0 behaviour observed for each, is `DESIGN.md` sections 14 and 15.

- Dtypes are `Bool U32 I32 F32 Str` only. No implicit casts: mixing dtypes in an operator is a `TypeMismatch` error value; a join on a `u32` key against an `i32` key is an error.
- `mean`, `std`, `var` and `median` always answer `F32`, including for integer columns (Polars gives `Float64`); `std` / `var` of `F32` values whose sum overflows f32 are `inf` (Polars, in f64, answers a finite value).
- Every `F32` `sum` and `mean` (eager, lazy, grouped, `describe`) is one compensated (Neumaier) sum in row order that switches to plain IEEE addition once the partial sum is infinite or NaN. Results are checked against the exact sum of the `F32` inputs, not against Polars' bits, which can be an ulp away.
- `F32` comparisons, sort, `group_by`, `unique`, `n_unique`, `is_in` and join keys share one total order: NaN equals NaN and is greater than everything, `-0.0` equals `0.0`. `min`/`max` skip NaN. `median([-0.0, 0.0])` is `0.0` (Polars `-0.0`).
- `u32` and `i32` `add sub mul` and `sum` wrap around (mod 2^32). `div` refuses integers (cast to `f32` first); `floor_div` rounds toward minus infinity and `mod` has the divisor's sign (as Polars), both give null for a zero divisor, and `i32` `MIN // -1` is null (Polars answers `MIN`).
- `cast` is strict and `try_cast` is lenient (Polars' `strict=True` / `False`). `cast` from `str` reads the text as is (no trimming; `"+5"` is not a `u32`); `str` to `bool` accepts exactly `true`, `false`, `True`, `False` (Polars refuses that cast); a number cast to `str` prints `1.0` as `1`, `-0.0` as `-0` and NaN as `nan` (Polars `1.0`, `-0.0`, `NaN`).
- A scalar predicate broadcasts to the input height everywhere: `filter(lit(false))` over a one-row literal `select` gives 0 rows, as eager Polars does (Polars' lazy engine keeps the row). `lit(x).len()` is the input height (Polars answers 1).
- `describe` answers Polars' statistics for numeric columns as `F32` columns; its `25%`, `50%`, `75%` are nearest-rank quantiles (Polars' default `interpolation="nearest"`), so for an even count the `50%` row is the upper middle value while `median` interpolates. For `Bool` and `Str` columns it reports only `count`, `null_count`, `min` and `max`, as text, with nulls elsewhere.
- Join output is always in left-row order, and the matches of one left row come in right-row order. `inner`, `left`, `semi` and `anti` joins exist. `semi` / `anti` answer the left columns only, each left row at most once, in left order; a null key never matches, so `anti` keeps such a row. Join output keeps every left column (keys included), then the right columns minus the right key columns, even when the key names differ; a remaining right name that clashes with a left name gets the `_right` suffix.
- `group_by` answers in first-appearance order; `GroupBy` carries a `maintain_order` flag, but v0.1 always orders by first appearance. `unique` compares rows the way `group_by` groups them and keeps the first row of each key tuple, in input order; on a frame with no columns it keeps one row (if any).
- `concat_vertical` has no diagonal or relaxed mode: every input must have input 0's names, dtypes and column order. A lazy concat is a chain of binary nodes and checks its inputs one by one (an input's own errors, then its schema against input 0's, then the next input), so with two faulty inputs the first in that order is reported.
- Error order: every verb makes all its static checks before it evaluates any data. A lazy `collect` checks the whole plan first, then reads every `scan_csv` in plan order, then runs, so a scan's IO or parse error comes before any operator's data error; an eager program reports errors in the order it runs its verbs, so a multi-verb program with an early data error and a later static error can answer differently eagerly and lazily (`DESIGN.md` 15.9; such programs are excluded from the eager-vs-lazy agreement check).
- `when` evaluates both branches over every row, so a strict `cast` that fails in the branch a row does not choose still fails (Polars too).
- CSV reading (`DESIGN.md` 15.6): a blank line is a null row in a one-column file and is skipped when there are more columns (Polars: an all-null row); a short record is a `ParseError` (Polars fills nulls); an empty file is a `(0, 0)` frame (Polars: error), and writing a `(0, 0)` frame gives `"\n"`, which reads back as one column named `""` with 0 rows; blank lines before the header are skipped (as Polars); a lone CR at the very end of the input is dropped as a line end (elsewhere a lone CR is content); a separator that is `"`, CR or LF is an `InvalidOperation` on read, scan and write; numeric, bool and empty-after-trim fields are trimmed before they are read, so `" 1 "` is the `u32` 1 (Polars infers `str`). Error line numbers are physical lines, counting blank lines and multi-line fields.
- CSV inference is by content: there is no round-trip claim for numeric-looking strings. A `str` column holding `"007"` or `"1.0"` written by `write_csv` is read back by `read_csv` as a number unless an explicit schema (`read_csv_schema`) gives it `str`. With an explicit schema every dtype round-trips (NaN payloads excepted), and so do `""` and null. Text equality with Polars' `write_csv` is not a goal.
- No window functions; see Limits.

## Limits

- At most 2^23 = 8,388,608 rows per frame: a CSV read, a join, `group_by`, `concat_vertical` (the running height sum, saturating instead of wrapping) or a counted column build over the cap is an `InvalidOperation` ("too many rows: <n> exceeds 8388608"), checked before allocating.
- Five dtypes: `Bool`, `U32`, `I32`, `F32`, `Str`, each nullable. Integer arithmetic wraps; floats are f32 only.
- Memory: about 1.3 GB peak RSS for the 1M-row benchmark (Polars: 168 MB). Bend does not use more than one thread today.
- Floating-point results follow the documented algorithms (`DESIGN.md` 15.5) and are checked against an exact reference within a derived bound; no accuracy theorem.

Out of scope for v0.1:

- `F64`, `I64`, `U64`.
- Dates and times.
- Lists.
- Structs.
- Map columns.
- Window functions and `over`.
- Rolling and cumulative operations.
- `explode` and `pivot`.
- Regular expressions.
- Full, cross, as-of and non-equi joins.
- Parquet, IPC and SQL.
- Streaming and out-of-core execution.
- GPU execution.
- Automatic parallel scheduling.
- The Explorer API.

## Laws

`LAWS.bend` states 147 laws over the production code in `src/`, and `PROOF.bend` (one file per area: `PROOF_lib`, `PROOF_schema`, `PROOF_expr`, `PROOF_plan`, `PROOF_kernels`, `PROOF_exec`, `PROOF_bits`, `PROOF_contents`, `PROOF_eval`, `PROOF_evalops`, `PROOF_evalrun`, `PROOF_strs`, `PROOF_append`, `PROOF_inplace`) proves every one with no `@unsafe`, no foreign code, no axiom and no open law: `bend PROOF.bend` prints `ALL PROOFS CHECK`, and `bend PROOF.bend --verdict` confirms it with Bend's independent, Lean-verified BendTT kernel. Every theorem quantifies over the functions that run, not over a model engine. The scope, honestly: the default optimizer, which only merges adjacent `head`s, is proven to give the same result as the unoptimized plan (frames and errors) for every plan and environment, over the production runner `Exec.run_pure` (what `collect` runs after validating the bindings and reading the scans); the evaluator is proven type-sound (an expression the analysis accepts yields a column of the predicted dtype and height, failing only where a strict cast may); the core buffer kernels are proven to move the right cells (gather, compact/filter, the validity-mask combinators, iota, the U32 sum and popcount folds, head, slice, concatenation's append, the in-place null reset and `fill_null` / `when` selection), as are the `Str` storage operations that keep every decoded string (both Raw and Dictionary, including encoding, merging and concatenation), `fill_null` on strings and the null reset of every column kind, under stated hypotheses (row counts that fit the buffers, and for Dictionaries that each hash probe stops at an empty slot or at the key). Not proven, only tested: `optimize_full`, the cell values of arithmetic, comparisons, casts and reductions, sort, group_by and join, CSV reading and writing, every floating-point result, Dictionary lookups that answer "absent", and the native runtime itself. Eleven mutation fixtures (`tests/proof_negative/`) show that a one-line change to a proven production function makes its proof fail. `DESIGN.md` section 8 has the full table, the assurance matrix (theorem, production function, assumptions, checker) and the exact not-proven list.

## Performance

1M-row rows of the M6 re-measurement in [`bench/README.md`](bench/README.md) (Apple M2 Pro, 12 cores; Bend 2.0.36 native with the default string storage and optimizer, Polars 2.0.0; median ms per `collect` of 5 processes, Polars = best of 5 collects in its process; ratio = Bend / Polars). The machine was shared: the load average was 3-20 during these runs, so read differences under ~10 % or ~1 ms as noise.

| query | n | Bend 1t (ms) | Polars 1t (ms) | ratio 1t | Bend 12t (ms) | Polars 12t (ms) | ratio 12t |
|---|---:|---:|---:|---:|---:|---:|---:|
| q1 | 1,000,000 | 11 | 1.36 | 8.1x | 11 | 0.62 | 18x |
| q2 | 1,000,000 | 15 | 0.91 | 17x | 8.7 | 0.54 | 16x |
| q3 | 1,000,000 | 23 | 11.5 | 2.0x | 23 | 3.15 | 7.3x |
| q4 | 1,000,000 | 47 | 13.3 | 3.5x | 46 | 3.33 | 14x |
| q5 | 1,000,000 | 19 | 22.2 | 0.9x | 19 | 6.36 | 3.0x |
| q6 | 1,000,000 | 108 | 34.5 | 3.1x | 104 | 23.7 | 4.4x |

- On one thread, Bend is 0.9x (q5, `join` + `group_by`) to 17x (q2) of Polars at 1M rows, and 2-3.5x on the string-keyed q3 and q4 with the Dictionary string storage. At 1k rows Bend is faster than Polars on five of six queries.
- Bend does not scale with threads: 12 threads vs 1 is about 1.0x on q1-q6, so against all 12 cores of Polars the gap is 3-18x.
- Peak RSS at 1M rows is about 1.3 GB for Bend against 168 MB for Polars.
- The table times `collect` only; the CSV parse is untimed there. Reading the 41 MB, 1M-row sales file takes about 4.4 s on one thread and 2.0 s on 12 (M4 measurement; the 1.5 s target was not met).
- Weak spot: fully distinct string keys. A `group_by`, `unique` or join over 1M distinct strings takes 5-18 s against 0.05-0.2 s for Polars, 30-330x slower (correct, but slow).
- Every result is identical to Polars' (q6 within 5e-5 relative) at 1k, 100k and 1M rows; repeated queries give identical results with flat memory. Full tables, the high-cardinality and repeated-query measurements, `optimize_full` vs the default and the analysis are in [`bench/README.md`](bench/README.md).

## Development

Toolchain pins are in `TOOLCHAIN`: Bend 2.0.36, Lean 4.34.0 (for `--verdict`, via elan), uv 0.12.23, Python 3.14.3, Polars 2.0.0, NumPy 2.5.3 (the Python side lives in the uv project under `bench/`). `make toolchain-check` fails on drift.

```sh
make ci             # every gate below, in CI order: toolchain-check check runner-check test proofs verdict bench-check
make test           # scripts/test.sh: every tests/**/*.bend against its #| expectations (143 files, incl. 11 proof mutation fixtures)
make check          # bend --check-only on every src/, tests/, example and bench file (skips files that expect a failure)
make proofs         # bend PROOF.bend: prints ALL PROOFS CHECK (about 2 s)
make verdict        # bend PROOF.bend --verdict: the same under the BendTT kernel (about 5 s; needs Lean 4.34)
make runner-check   # the test runner itself, over throwaway fixtures
make bench-check    # q1-q6 at 1k and 100k rows against the Polars goldens; fails on any mismatch
make diff SEED=1 N=1000                  # differential generator: eager vs raw-lazy vs optimized-lazy, and vs Polars
make diff SEED=1 N=1000 DIFF_ARGS=--dict # the same with Dictionary string storage
make diff-reduce    # F32 sums, means and describe against an exact reference and the derived error bound
scripts/bench.sh    # the timing benchmark (Polars reference, then Bend; about 10 min)
scripts/consumer_check.sh  # clean clone, imported from another directory, quickstart built and run
```

`.github/workflows/ci.yml` installs the pinned toolchain and runs `make ci`, but it has never run: the repository has no remote yet. `make ci` passes locally. `probes/run_probes.sh` runs the small probe programs the design rests on.

Layout:

- `frame.bend`: the public facade; one import for users (`DF.col`, `DF.filter`, `DF.collect`, ...).
- `src/dtype.bend`: `DType`, the vendored two's-complement `I32`, scalar values.
- `src/err.bend`: the `Err` type and the `Res` / `ResT` result aliases.
- `src/kernels.bend`: flat template kernels over arrays (map, zip, fold, gather, compact, append, choose, the F32 order and sum policy).
- `src/column.bend`: `Column`, validity masks, `Frame`, head, slice, gather.
- `src/strs.bend`: the `Str` storage, Raw or Dictionary (codes, entries, hash index), and its operations.
- `src/schema.bend`: `Field` and `Schema` (project, with_columns).
- `src/expr.bend`: the `Expr` tree and its strict type checker.
- `src/analysis.bend`: the shared expression analysis (dtype, refs, row-wise / scalar / reduction, fallibility) used by the planner and the evaluator.
- `src/eval.bend`: eager expression evaluator (a stack machine over whole columns) and the eager verbs.
- `src/sort.bend`: order-preserving sort words, stable LSD radix argsort, `Sort.frame`.
- `src/groupby.bend`: `group_by`, the key encoders and the aggregations.
- `src/join.bend`: inner, left, semi and anti equi-joins.
- `src/table.bend`: drop, rename, slice, tail, unique, concat_vertical.
- `src/csvparse.bend`: the CSV parser (a fork of the hub package `bend-csv-parser`, MIT, notice kept in the file); cells carry quotedness and records their physical line.
- `src/csv.bend`: CSV reading with type inference and explicit schemas, the scan prefix, the streaming reader, rendering and writing.
- `src/fmt.bend`: table rendering, `describe`, fixed-decimal formatting.
- `src/dump.bend`: `DF.dump`, the typed oracle text.
- `src/plan.bend`: the lazy `Plan`, schema resolution, `explain`, the optimizers.
- `src/exec.bend`: validation, scan materialisation and the pure runner `Exec.run_pure`.
- `LAWS.bend` and `PROOF*.bend`: the laws and their proofs.
- `examples/`, `tests/`, `bench/`, `scripts/`, `probes/`: examples, tests (incl. `tests/regress/` for every review defect and `tests/proof_negative/`), benchmarks and the differential generator, scripts, design probes.

Design and implementation notes: [`DESIGN.md`](DESIGN.md) (goals and the Polars mapping in section 1, laws and the assurance matrix in section 8, deviations in section 14, the v0.1 contract in section 15) and [`IMPLEMENTING.md`](IMPLEMENTING.md) (Bend pitfalls and per-milestone notes). Release notes: [`CHANGELOG.md`](CHANGELOG.md).

## License

Apache License 2.0. Copyright 2026 Lukasz Samson. See [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE). `src/csvparse.bend` is a fork of the MIT-licensed hub package `bend-csv-parser` (Copyright (c) 2026 nohzafk); its MIT notice is kept in the file.
