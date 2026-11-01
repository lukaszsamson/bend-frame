# bend-frame

A columnar dataframe library for [Bend](https://bend-lang.com/) 2 (checked against Bend 2.0.39), shaped after the Polars 2.0 eager and lazy APIs, for CSV ETL: load, clean, derive, combine, aggregate, sort and export. Queries are built as a lazy `Plan`, a pure data tree, and the output schema is resolved before any row is read: `DF.collect_schema` returns a strict error such as a filter on a `u32` column, and `DF.collect` refuses the same plan with the same error. Row order is part of the contract: `select`, `with_columns`, `filter` and `head` keep input order, `sort` is stable and multi-key, and `group_by`, `unique` and joins answer in first-appearance and left-row order. Dtypes are `Bool`, `U32`, `I32`, `F32` and `Str`, each nullable through a validity mask, with no implicit casts.

**What v0.1 claims, and only this:** A small Bend-native dataframe library with tested ETL operations, verified core buffer operations and evaluator typing, and a result-preserving default optimizer under documented input and runtime assumptions.

**Not claimed:** Polars compatibility, a verified engine, verified sort/group/join partitioning, CSV completeness, floating-point accuracy, native runtime correctness.

**This is an experimental v0.1.** The default optimizer is deliberately small: it only merges adjacent `head`s (R1), the one rewrite with a complete proof; the larger optimizer (`optimize_full`: filter merge, predicate and projection pushdown, head sink; R2-R5) is opt-in and tested, not proven. The Dictionary string storage is proven only under stated hypotheses (each hash probe stops at an empty slot or at the key; `Probe` / `EncProbe` in `LAWS.bend`), and index completeness (a lookup that answers "absent") is not proven. Deferred proof work: R2-R5 as theorems, the grouped scatter invariant for `group_by`, Dictionary completeness and rank order. Treat results as tested, not verified, wherever the list below says so.

What "verified" covers, exactly, is in [Laws](#laws) below and in `DESIGN.md` section 8; what is tested and not proven is listed there too.

**v0.3 (unreleased: the stabilisation release, plans/M_03.txt).** No new verbs, dtypes or performance work: on the pinned Bend 2.0.39 every `make ci` gate runs again, with the independent `--verdict` check restored; there are targeted tests and mutation guards for v0.2's three fast paths (selective filters, the join's build side and direct ids, group_by's direct codes), a law for `Kernel.where` (selective filters' row list), a PDS-H check against Polars in ci, and CSV-lane tests run natively. See `CHANGELOG.md` for the list.

**v0.2 (0.2.0, the performance milestone; not published).** The data contract of v0.1 (`DESIGN.md` 15) is unchanged: the same values, validity, names, row order, F32 bits, errors and error order. What v0.2 changes is how fast and in how much memory the same answers come: a flat-buffer CSV reader (the default since 0.2.0), a flat string coder for distinct-key `group_by` / `unique` / joins, fused evaluator kernels, a cheaper sort, fewer copies, and an opt-in chunked engine that runs row-wise pipelines over owned chunks on several threads. The candidate claim of the milestone (plans/M_02.txt) is "owned chunks and fused kernels reduce copying and improve measured throughput; parallel execution preserves the documented semantics on the supported paths"; the numbers behind it are in [Performance](#performance) and `plans/GATES_V02.md`, and the timing numbers are PROVISIONAL: the machine was never quiet, so the timing gates are recorded as unevaluated, not passed (correctness, memory and copy gates are met; the proof gate G5 is PARTIAL, see [Laws](#laws)).

**Release status: experimental; macOS arm64 only (Linux x86-64 and hosted CI have never run); performance numbers PROVISIONAL (no quiet-machine gate run yet); the M_02 thread-scaling goals are INCOMPLETE.** What 0.2.0 delivers, stated as narrowly as the numbers allow: 1.7x to 113x faster on one thread depending on the workload (the 1M-row q1-q5 compute cells 1.7-3.3x, the CSV parse 6.3x, the distinct-string and distinct-key cells 12-113x), about 4-7x less peak memory on the sales workload (190-314 MB against about 1.3 GB), and threads help the CSV parse (1.9x), `describe` (3x) and scan-fed row-wise plans under the opt-in chunked engine (4x); **the default executor does not scale with threads on q1-q5** (12 vs 1 thread: about 1.0x; 0.75-1.09x across two runs). Not a Polars replacement and not "scales on 12 cores". The reader default flipped from v0.1 to v0.2 before the timing gates G2-G4 were evaluated: a recorded deviation from the rollout plan (`DESIGN.md` 14 "W8"), see [Reader and engine selection](#reader-and-engine-selection-v02).

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

### Reader and engine selection (v0.2)

Two selectors, both answering the same frame or the same error (values, validity, names, row order, F32 bits, dictionary codes, error texts and lines):

- The CSV reader. `read_csv*` and the scans of `collect` use the v0.2 reader by default since 0.2.0: a sequential producer of flat byte regions at record boundaries, ONE balanced fork of typed lanes over them, then a sequential combine (dictionary merge in region order, v0.1's error order). `csv_engine_v01()` keeps the v0.1 reader selectable (`read_csv_engine(csv_engine_v01(), path, opts, dtypes, enc)`, `collect_engine(csv_engine_v01(), plan, env)`); it is the pinned reference of the CSV tests and fuzz, and nothing of it was removed. `csv_engine_v02()` / `read_csv_v02` name the v0.2 reader explicitly. `scan_csv`'s plan-time schema inference (the bounded prefix) is the same for both. The reader default flipped to v0.2 at W8 BEFORE the timing gates G2-G4 were evaluated (they are still unevaluated: the machine was never quiet): it rests on exact agreement with v0.1 (G1: every CSV test, the fuzz, the adversarial corpus) and provisional parse and memory evidence, and is a recorded deviation from the rollout plan (`DESIGN.md` 14 "W8", `plans/GATES_V02.md` D7), not a gate pass. The v0.2 reader has no public piece-size knob (the 240 KiB piece size is internal), and the chunked engine cannot be paired with the v0.1 reader from the facade.
- The executor. `collect` / `collect_raw` run the reference executor, which `engine_reference()` names explicitly (`collect_with(engine_reference(), plan, env)` is `collect`, and it is the engine the chunked one is checked against); `collect_with(engine_chunked(), plan, env)` / `collect_raw_with` run the same plan over owned chunk trees (leaves of 2^14 rows; `engine_chunked_at(g)` for 2^g), forking row-wise operators (filter, with_columns, row-wise select) over the leaves. It is opt-in in v0.2 and helps only where its leaves are born at the source: a `scan_csv` plan whose first consumers are row-wise (the v0.2 reader builds the leaves directly) on several threads. **From eager frames it is SLOWER than the default executor**: an eager frame passed as a source pays a conversion into chunks and the result one out, so at one thread (1M rows, PROVISIONAL, `plans/GATES_V02.md` G2 run B) q1 takes 8 ms against 3, q2 18 against 3 and q3 22 against 12, and at 12 threads it is still 1.3-2x slower than the default (q1 4 vs 3 ms, q2 6 vs 3, q3 15 vs 11); an independent run at load 3 gave 8 / 17 / 21 ms against 3 / 3 / 11 at one thread. `sort`, `join`, `group_by`, `unique` and `describe` run the flat code behind that boundary, so q3-q6-shaped plans gain nothing from it. Use it only over `scan_csv` plans with row-wise first consumers, on several threads.

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
- `F32` comparisons, sort, `group_by`, `unique`, `n_unique`, `is_in` and join keys share one total order: NaN equals NaN and is greater than everything, `-0.0` equals `0.0`. `min`/`max` skip NaN. `median([-0.0, 0.0])` is `0.0` (Polars `-0.0`); for an odd count the median of values that tie as zeros is the cell at the middle position of the STABLE order (a zero keeps its own sign), where Polars' unstable selection agreed in every case tried up to 15 values and answered the other sign in about half of random inputs of 21 to 61 values, in both directions (`tests/agg_median_zero_sign.bend`, `DESIGN.md` 15.5.4).
- `u32` and `i32` `add sub mul` and `sum` wrap around (mod 2^32). `div` refuses integers (cast to `f32` first); `floor_div` rounds toward minus infinity and `mod` has the divisor's sign (as Polars), both give null for a zero divisor, and `i32` `MIN // -1` is null (Polars answers `MIN`).
- `cast` is strict and `try_cast` is lenient (Polars' `strict=True` / `False`). `cast` from `str` reads the text as is (no trimming; `"+5"` is not a `u32`); `str` to `bool` accepts exactly `true`, `false`, `True`, `False` (Polars refuses that cast); a number cast to `str` prints `1.0` as `1`, `-0.0` as `-0` and NaN as `nan` (Polars `1.0`, `-0.0`, `NaN`).
- A scalar predicate broadcasts to the input height everywhere: `filter(lit(false))` over a one-row literal `select` gives 0 rows, as eager Polars does (Polars' lazy engine keeps the row). `lit(x).len()` is the input height (Polars answers 1).
- `describe` answers Polars' statistics for numeric columns as `F32` columns; its `25%`, `50%`, `75%` are nearest-rank quantiles (Polars' default `interpolation="nearest"`), so for an even count the `50%` row is the upper middle value while `median` interpolates. For `Bool` and `Str` columns it reports only `count`, `null_count`, `min` and `max`, as text, with nulls elsewhere.
- Join output is always in left-row order, and the matches of one left row come in right-row order. `inner`, `left`, `semi` and `anti` joins exist. `semi` / `anti` answer the left columns only, each left row at most once, in left order; a null key never matches, so `anti` keeps such a row. Join output keeps every left column (keys included), then the right columns minus the right key columns, even when the key names differ; a remaining right name that clashes with a left name gets the `_right` suffix.
- `group_by` answers in first-appearance order; `GroupBy` carries a `maintain_order` flag, but v0.1 always orders by first appearance. `unique` compares rows the way `group_by` groups them and keeps the first row of each key tuple, in input order; on a frame with no columns it keeps one row (if any).
- `concat_vertical` has no diagonal or relaxed mode: every input must have input 0's names, dtypes and column order. A lazy concat is a chain of binary nodes and checks its inputs one by one (an input's own errors, then its schema against input 0's, then the next input), so with two faulty inputs the first in that order is reported.
- Error order: every verb makes all its static checks before it evaluates any data. A lazy `collect` checks the whole plan first, then reads every `scan_csv` in plan order, then runs, so a scan's IO or parse error comes before any operator's data error; an eager program reports errors in the order it runs its verbs, so a multi-verb program with an early data error and a later static error can answer differently eagerly and lazily (`DESIGN.md` 15.9; such programs are excluded from the eager-vs-lazy agreement check).
- `when` evaluates both branches over every row, so a strict `cast` that fails in the branch a row does not choose still fails (Polars too).
- A UTF-8 byte order mark at the start of a CSV file is content, not a marker: both readers and `scan_csv` keep it in the first header name (U+FEFF, then the name), so the column is not named `a` (without a header it stays in the first data cell); Polars strips it (`tests/csv_bom.bend`, `DESIGN.md` 15.6). Strip it before reading, or rename the column.
- CSV reading (`DESIGN.md` 15.6): a blank line is a null row in a one-column file and is skipped when there are more columns (Polars: an all-null row); a short record is a `ParseError` (Polars fills nulls); an empty file is a `(0, 0)` frame (Polars: error), and writing a `(0, 0)` frame gives `"\n"`, which reads back as one column named `""` with 0 rows; blank lines before the header are skipped (as Polars); a lone CR at the very end of the input is dropped as a line end (elsewhere a lone CR is content); a separator that is `"`, CR or LF is an `InvalidOperation` on read, scan and write; numeric, bool and empty-after-trim fields are trimmed before they are read, so `" 1 "` is the `u32` 1 (Polars infers `str`). Error line numbers are physical lines, counting blank lines and multi-line fields.
- CSV inference is by content: there is no round-trip claim for numeric-looking strings. A `str` column holding `"007"` or `"1.0"` written by `write_csv` is read back by `read_csv` as a number unless an explicit schema (`read_csv_schema`) gives it `str`. With an explicit schema every dtype round-trips (NaN payloads excepted), and so do `""` and null. Text equality with Polars' `write_csv` is not a goal.
- No window functions; see Limits.

## Limits

- At most 2^23 = 8,388,608 rows per frame: a CSV read, a join, `group_by`, `concat_vertical` (the running height sum, saturating instead of wrapping) or a counted column build over the cap is an `InvalidOperation` ("too many rows: <n> exceeds 8388608"), checked before allocating.
- Five dtypes: `Bool`, `U32`, `I32`, `F32`, `Str`, each nullable. Integer arithmetic wraps; floats are f32 only.
- Memory: about 190-310 MB peak RSS for the 1M-row q1-q6 runs since 0.2.0 (v0.1: about 1.3 GB, almost all of it the v0.1 reader; Polars: 168 MB). The 600 MB gate covers that sales workload only: a `group_by` or `unique` over 1M distinct strings peaks near 630 MB and a join on 1M distinct string keys near 1 GB. The v0.2 reader allocates about 1.39 GB cumulatively in about 83 million allocations to parse the 41 MB file (allocation traffic, not peak memory; the rest is the File API's per-byte cons cells).
- Execution: everything is in memory (no streaming, no out-of-core); there is no performance guarantee against adversarial hash collisions (the string coder and the hash join compare strings on a hit, so results stay exact, but time is not bounded), huge strings or pathological skew.
- Threads: the CSV reader's lanes (parse 1.9x at 12 vs 1 thread), `describe`'s columns (3x) and, opt-in, the chunked engine's row-wise walks over a `scan_csv` plan (about 4x) run in parallel. The default executor does not scale with threads on q1-q5 (12 vs 1 thread: about 1.0x, 0.75-1.09x across two runs); sort, join, group_by and unique stages do not scale at all; F32 sums are one sequential pass in row order by contract; the CSV producer is serial (the File API), so the parse scales about 2x. Numbers: [Performance](#performance).
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

**In one sentence (v0.3):** proven over the production code are the buffer kernels (gather, compact, map / zip, fold, append, in-place reset and choose, and since v0.3 `Kernel.where`, the row list of a selective filter), both string storages, the chunk trees, the evaluator peepholes against the unfused evaluator, the null-slot producers, the plan-level equivalences (release optimizer = unoptimized, physical runner = pure runner, Filter + Select step) and the v0.1 typing of `Eval.full` / `Eval.run`; tested only are the fused runner `Eval.runz` that filter / select / with_columns execute, the chunked runner, both CSV readers, the string coder and rank stage, the radix sort, sort / group_by / join semantics (including the v0.2 build-side and direct-code paths), floating-point results, Dictionary completeness and native execution; and the independent BendTT check passes on the pinned Bend 2.0.39. `LAWS.bend` states 242 laws over the production code in `src/` (149 in v0.1; v0.3 added `where_contents`; v0.2 added 92: the range copy behind `slice`, the moves of the liveness pass, the Sort + Head bounded gather, the fused kernels and evaluator peepholes, the Filter + Select step, the chunk trees and the chunked kernel wrappers, and the null-slot reset of the B1 fix; `DESIGN.md` 8.2), and `PROOF.bend` (one file per area: `PROOF_lib`, `PROOF_schema`, `PROOF_expr`, `PROOF_plan`, `PROOF_kernels`, `PROOF_exec`, `PROOF_bits`, `PROOF_contents`, `PROOF_eval`, `PROOF_evalops`, `PROOF_evalrun`, `PROOF_strs`, `PROOF_append`, `PROOF_inplace`, and for v0.2 `PROOF_moves`, `PROOF_sorthead`, `PROOF_fused`, `PROOF_peep`, `PROOF_filtsel`, `PROOF_chunks`, `PROOF_ckernels`, and for v0.3 `PROOF_where`) proves every one with no `@unsafe`, no foreign code, no axiom and no open law: `bend PROOF.bend` prints `ALL PROOFS CHECK`, and `bend PROOF.bend --verdict` confirms it with Bend's independent, Lean-verified BendTT kernel (on the pinned Bend 2.0.39 too, since v0.3 wrote one type-level Sigma inline to work around bendlang/bend#1984; `make verdict-probe` checks the translation alone). Every theorem quantifies over production functions, not over a model engine, but NOT over every function that runs: since 0.2.0 the default `select` / `with_columns` / `filter` route runs `Eval.runz(Eval.fuse(Eval.mark(compile)))` (the marked, fused runner), and no theorem relates that runner to `Eval.run` (the three groups below say exactly what is covered). The scope, honestly: the default optimizer, which only merges adjacent `head`s, is proven to give the same result as the unoptimized plan (frames and errors) for every plan and environment, over the production runner `Exec.run_pure`. That runner is what `collect` runs after the static check, the binding validation and the scan reads, and it runs the plan itself, scans included (the scans' frames sit in an unnamed `scans` field of the environment, so `release_run` is not vacuous on scan plans), with `hmerge_keeps_scans` / `release_keeps_scans` proving that the optimized plan reads the same scans in the same order. Still unproven glue: that `Plan.schema` and `Exec.validate` answer alike for `Optimize.release(p)` and for `p` (true by inspection: the pass only merges `head`s), and the IO materialisation `Exec.mat` itself (the CSV reads); the v0.1 evaluator `Eval.full` / `Eval.expr` / `Eval.run` is proven type-sound (an expression the analysis accepts yields a column of the predicted dtype and height, failing only where a strict cast may). The analysis `A.Expr.analyse` is shared by every verb, but the typing THEOREMS (`run_typed`, `eval_full_typed`, `eval_expr_typed`) are stated over `Eval.full` / `Eval.expr` / `Eval.run`, which since 0.2.0 only `group_by`'s computed keys and the sort-by-expression callers execute: `select`, `with_columns` and `filter` run the fused runner `Eval.runz`, whose equivalence to `Eval.run` is NOT proven (tested: `tests/eval_fused`, the differentials). The 20 older expression-typing laws of `LAWS.bend` section 2 are about `X.Expr.type`, which production uses only for `group_by`; the core buffer kernels are proven to move the right cells (gather, compact (the mask compaction of a non-selective filter; a selective filter's row list `Kernel.where` is proven, its gather of every column by that list, `Frame.take_rows`, is tested only), the validity-mask combinators, iota, the U32 sum and popcount folds, head, slice, concatenation's append, the in-place null reset and `fill_null` / `when` selection), as are the `Str` storage operations that keep every decoded string (both Raw and Dictionary, including encoding, merging and concatenation), `fill_null` on strings and the null reset of every column kind, under stated hypotheses (row counts that fit the buffers, and for Dictionaries that each hash probe stops at an empty slot or at the key). Not proven, only tested: `optimize_full`, the cell values of arithmetic, comparisons, casts and reductions, sort, group_by and join, CSV reading and writing, every floating-point result, Dictionary lookups that answer "absent", and the native runtime itself. Mutation evidence has two parts, of different strength: eleven fixtures in `tests/proof_negative/` mutate a renamed disposable copy of a production function and try the production proof term against it (five of them, per their headers, are name-sensitive: an unmutated renamed copy is refused too, so those show only that a copy is rejected), and `make mutation-check` (`scripts/mutation_check.sh`) mutates production functions in place in a temporary copy of the tree and requires `bend PROOF.bend` to fail each time (107 mutations: 14 in v0.1, 90 in v0.2, 3 in v0.3; all caught, the unmutated copy accepted); `make test-mutation-check` does the same for three tested-only fast paths (the join's direct-id probe, group_by's direct code, `Kernel.where`'s cursor), requiring the targeted tests `tests/regress/V03_*` to fail. v0.2 adds no theorem about the chunked executor, the fused runner as a whole, the v0.2 CSV reader, the string coder, the rank stage or the radix sort: those are tested only (the exact list is `DESIGN.md` 8.2), as the v0.1 code they replace was. `DESIGN.md` section 8 has the full table, the assurance matrix (theorem, production function, assumptions, checker) and the exact not-proven list.

**What the proofs cover in 0.2.0, in three groups** (the original gate G5, "every changed proved production path keeps its theorem chain", is recorded as PARTIAL in `plans/GATES_V02.md`):

1. *Preserved theorems about existing functions.* All 149 v0.1 laws are unchanged (none weakened, dropped or turned into a hypothesis; `release_run` still speaks about `Exec.run_pure`). They stay true statements about `Eval.full` / `Eval.expr` / `Eval.run`, `Exec.run_pure`, the buffer kernels and the string storage; but for `select`, `with_columns` and `filter` the evaluator typing theorems no longer describe the code the default path executes (`Eval.runz`).
2. *New local kernel and peephole theorems, each at stated instances and premises.* Of the 82 laws v0.2 added: section 18's fused-kernel laws are each at ONE template instance (for example u32 add, f32 mul), while production instantiates the kernels for u32 / i32 / f32 arithmetic and comparisons; section 19's peephole laws are one instance per peephole, and `peep_f4_cell` (the `fill_null` with the dtype default) was stated at 0.2.0 under the premise that null slots already hold the zero payload; an F32 `neg` breached it (review finding B1, `CHANGELOG.md`), and since the fix F4 resets the slots itself and the law has no slot premise; section 20 (Filter + Select), 16 (moves), 17 (Sort + Head) and 21 (chunk trees) are over the functions named in `DESIGN.md` 8.2; section 22 is 14 laws over 53 generated chunked wrappers, 4 of them (sum, min, max, popcount) on the chunked runner's path.
3. *Unproven integration.* The fused runner `Eval.runz(Eval.fuse(..))` as a whole (stack plumbing, lend / replace; equal to `Eval.run` on the same code only by tests and the differential), the chunked runner's `CX.*` walks and the `Eval.runz` call in each leaf, the Filter + Select step's shared predicate mask, the v0.2 reader, the string coder, the rank stage, the radix sort, and native execution. An experimental release accepts these as tested-only; proving or retiring the fused runner (`runz` = `run`) is v0.3 work.

## Performance

### v0.2 against v0.1 (PROVISIONAL)

The W8 close-out run of the frozen workload harness (`bench/m2/`, `plans/GATES_V02.md`): the pinned v0.1 baseline (commit 3612482) and 0.2.0 built from the same driver, Apple M2 Pro (8 P + 4 E cores), Bend 2.0.36 native, medians of 5 fresh interleaved processes per cell, every result validated against the expected output frozen from the baseline. **PROVISIONAL**: the machine was shared, with a 1-minute load of 1.4-5.8 during the runs (above the protocol's < 2 before the run), so no timing gate is claimed. 1M rows unless noted; `compute` is the plan's `collect` over already parsed inputs (q6: `describe`), with the default (reference) executor.

| workload | v0.1, 1 thread | v0.2, 1 thread | v0.2, 12 threads | v0.1 -> v0.2 (1 thread) |
|---|---:|---:|---:|---:|
| CSV parse, 41 MB (`read_csv` + first walk) | 3,966 ms | 632 ms | 334 ms | 6.3x |
| peak RSS of a 1M-row q1-q6 run | 1,315-1,340 MB | 190-234 MB | 223-314 MB | 5.7-7.0x less |
| q1 compute (filter, select) | 10 ms | 3 ms | 3 ms | 3.3x |
| q2 compute (with_columns) | 7 ms | 3 ms | 3 ms | 2.3x |
| q3 compute (q2 + group_by + sort) | 20 ms | 12 ms | 11 ms | 1.7x |
| q4 compute (3-key sort, head 10) | 40 ms | 13 ms | 13 ms | 3.1x |
| q5 compute (join, group_by, sort) | 17 ms | 10 ms | 10 ms | 1.7x |
| q6 compute (describe of 4 columns) | 98 ms | 49 ms | 16 ms | 2.0x |
| q1-q6 end to end (parse + compute + hash) | 3,973-4,057 ms | 633-682 ms | 338-352 ms | 5.9-6.3x |
| n_unique over 2^20 distinct U32 | 1,803 ms | 16 ms | 15 ms | 113x |
| group_by over 1M distinct strings | 12,458 ms | 125 ms | 127 ms | 100x |
| unique over 1M distinct strings | 12,517 ms | 126 ms | 128 ms | 99x |
| inner join on 1M distinct string keys | 4,186 ms | 356 ms | 354 ms | 12x |

- What scales with threads in v0.2 (all PROVISIONAL): the CSV reader's lanes (the parse goes from 632 to 334 ms, 1.9x; its producer is serial, see below), `describe`'s columns (q6 3.1x) and, with the opt-in chunked engine, the row-wise walks, **but only on inputs born chunked, that is a `scan_csv` plan whose first consumer is row-wise**: there q1 4.0x, q2 3.8x and a 50% filter 5.9x at 12 vs 1 thread (`bench/w5/scale/t53b.py`; plans/GATES_V02.md G2 run F; end to end over the serial parse the same plans gain 1.9x). **The default executor does not scale with threads on q1-q5**: 12 vs 1 thread is about 1.0x (q1-q5 3 / 3 / 12 / 13 / 10 ms at one thread, 3 / 3 / 11 / 13 / 10 at 12). From eager frames the chunked engine does not gain what that sentence suggests: it is 2.7-6x slower than the default at one thread on q1 and q2 and 1.8x slower on q3 (8 / 18 / 22 ms against 3 / 3 / 12), and at 12 threads it is 1.3-2x slower (4 / 6 / 15 ms against 3 / 3 / 11); its 12-vs-1 speedup there is 2.0x, 3.0x and 1.5x (an independent run: 1.6x, 2.8x, 1.5x). `sort`, `join`, `group_by` and `unique` stages do not scale: q3, q4, q5 and the string cells stay at ~1.0x with the reference executor and 1.4x (q3, q5) with the chunked one.
- Small inputs (PROVISIONAL, from one loaded run): the 1k-row controls are within 10% of v0.1 or faster (q3 0.100 vs 0.175 ms, q4 0.050 vs 0.325, q5 0.100 vs 0.200 per query); this rests on a fix made after the W8 measurements and has not been through a quiet-machine gate run. Before the fix, q3 and q5 were 1.57x and 1.25x slower: every radix sort allocated and prefix-summed a 2^17-slot histogram regardless of the input size, and sorting the 8 groups of a 1k-row q3 runs several sorts; small inputs now sort with 8-bit digits (plans/GATES_V02.md G3).
- Memory beyond the sales workloads: the 1M distinct-string `group_by` / `unique` peak at ~630 MB and the 1M distinct-key join at ~1.03 GB (v0.1: 870-890 MB and 1.25 GB); the 600 MB gate covers the frozen sales workload only. The v0.2 reader allocates ~1.39 GB in ~83 M allocations for the 41 MB file (v0.1: 4.0 GB in 352 M), which is allocation traffic, not peak memory.

**The scheduler lesson.** Bend 2.0.36 runs a fork tree in iterations: a grow pass expands it from the frontier by running only tasks whose function can fork, then a drain pass runs the collected pieces to completion on every thread. A call to a fork-free but non-flat helper (a list split, a clone walk, a cut) before a parallel let or in its arguments becomes a task the grow pass does not run; the subtree under it then runs on one thread and the whole tree tops out near 2x however many threads there are. The first chunked walks hit exactly that ceiling. The rule that fixed them: a function with a parallel let does nothing but match and fork; the tree to fork over is built in a sequential prelude, the work is in the leaves, the results join in the continuation. After the fix the walks scale 4-6x on inputs that are already chunked (a `scan_csv` plan read into chunks; from eager frames the conversions dominate and the 12-vs-1 gain is only 1.5-3x on top of a one-thread penalty, see above); `make fork-audit` (in `make ci`) checks every parallel let of `src/` against the rule (`DESIGN.md` 16.10).

Limits of v0.2's parallelism, by design or by platform: F32 sums are one sequential compensated pass in row order (the contract of `DESIGN.md` 15.5.3, kept), so grouped and global F32 reductions do not split; sort, join, group_by and unique run their flat (serial) code even under the chunked engine; the CSV producer is serial because the File API returns cons lists on the IO thread (`DESIGN.md` 17.10), which bounds the parse near 2x end to end.

### v0.1 against Polars (M6, 2026-10-09)

These are the v0.1 numbers, kept as the last comparison with Polars; 0.2.0 was not re-measured against Polars (the v0.2 table above is against v0.1).

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
- Results are checked against goldens at 1k, 100k and 1M rows: q1, q2, q4 and q5 are identical to Polars' output, q6 is within 5e-5 relative (one or two float cells differ in the last digit), and q3 is checked against an exact-rational F32 reference (`bench/golden.py`), not against Polars, whose grouped `f32` sum differs by an ulp or two (for example the tiny fixture's inland sum: Polars 96373.4141, reference and Bend 96373.4062). Repeated queries give identical results with flat memory. Full tables, the high-cardinality and repeated-query measurements, `optimize_full` vs the default and the analysis are in [`bench/README.md`](bench/README.md).

## Development

Toolchain pins are in `TOOLCHAIN`: Bend 2.0.39, Lean 4.34.0 (for `--verdict`, via elan), uv 0.12.23 (informational: `bench/uv.lock` pins the Python side), Python 3.14.3, Polars 2.0.0, NumPy 2.5.3 (the Python side lives in the uv project under `bench/`), and the sha256 of the Bend release archives. `make toolchain-check` fails on drift (it only warns on uv).

```sh
make ci             # the whole gate, in order: toolchain-check check runner-check diff-driver-check test proofs verdict mutation-check test-mutation-check bench-check diff-smoke csv-fuzz-smoke fork-audit radix-check tpch-check consumer-check coverage-check
make test           # scripts/test.sh: every tests/**/*.bend against its #| expectations (212 test programs (files), incl. 11 proof mutation fixtures; a file holds many cases)
make check          # bend --check-only on every src/, tests/, example and bench file (skips files that expect a failure)
make proofs         # bend PROOF.bend: prints ALL PROOFS CHECK (about 2 s)
make verdict        # bend PROOF.bend --verdict: the same under the BendTT kernel (about 30 s on 2.0.39; needs Lean 4.34)
make runner-check   # the test runner itself, over throwaway fixtures
make bench-check    # q1-q6 at 1k and 100k rows against the goldens (Polars; q3 against the F32 reference); fails on any mismatch.
                    # 1M rows: CHECK_MAX=1000000 BENCH_MODE=check scripts/bench.sh (slow). The tracked 1k golden (bench/golden/n1000) is regenerated by each run.
make mutation-check # 107 mutations of production functions in place in a temp copy; `bend PROOF.bend` must fail for each
make coverage       # docs/COVERAGE.md: operation x case matrix, gate and def-call report
make diff-driver-check  # the differential drivers' exit status: every failure exits 1
make diff SEED=1 N=1000                  # differential generator: eager vs raw-lazy vs optimized-lazy, and vs Polars; any failure exits 1
make diff SEED=1 N=1000 DIFF_ARGS=--dict # the same with Dictionary string storage
make diff-reduce    # F32 sums, means and describe against an exact reference and the derived error bound; any finding exits 1
make diff-chunked SEED=1   # G1: the chunked engine against the reference (grains 2^0, 2^2, 2^4, 2^14), Raw, Dictionary, deep plans
make csv-fuzz SEED=1 N=5000 # the v0.2 CSV reader against the v0.1 reader: random files x 7 piece sizes + chunk-mode reads
make fork-audit     # every parallel let of src/ against the scheduler's fork-shape rule (static; DESIGN.md 16.10)
make m2-bench LABEL=x       # the v0.2 measurement harness (bench/m2/README.md): baseline 3612482 vs this checkout, 1/4/12 threads
scripts/bench.sh    # the timing benchmark (Polars reference, then Bend; about 10 min)
scripts/consumer_check.sh  # clean clone, imported from another directory, quickstart built and run
```

What `make ci` runs: `toolchain-check`, `check`, `runner-check`, `diff-driver-check` (the exit-status regression of the differential drivers), `test`, `proofs`, `verdict` (green on the pinned 2.0.39 since v0.3), `mutation-check`, `test-mutation-check` (the tested-only fast paths' mutations must fail the targeted tests), `bench-check` (1k and 100k), `diff-smoke` (fixed seeds, 200 generated cases each in Raw and Dictionary storage with `--strict`, each also run by the chunked engine at four grains, then the F32 reduction check), `csv-fuzz-smoke` (two fixed seeds of 1,500 random CSV files, v0.2 reader against v0.1 at seven piece sizes), `fork-audit` (the static fork-shape check, both halves on 2.0.39), `radix-check` (native: the 8-bit and 16-bit radix paths give the same stable order, on 90 inputs including n = 0 and the dispatch boundary 16383 / 16384 / 16385 / 32768), `tpch-check` (the comparator's self-test, then the nine PDS-H-style queries at sf 0.01 against Polars), `consumer-check` (a clean clone of `HEAD`, so the work must be committed) and `coverage-check` (the operation x case matrix gate; fails when the committed `docs/COVERAGE.md` is stale). Every differential and reduction failure exits 1, classified as a known defect or not, so a regression of a fixed defect fails the build. Larger differential runs (`make diff`, `make diff-reduce`) are manual; the 22,000-case run reported in `plans/STATUS.md` was one.

The test count is 212 test programs (files), not assertions. `docs/COVERAGE.md` (generated by `make coverage`) is the operation x case matrix: 762 cells covered, 54 marked n/a with a stated reason, 0 missing, plus a def-call report over `src/`; the gate checks that each case is accounted for and that its test really calls the operation, not that the case is a good one.

Platform and CI: macOS arm64 (Apple M2 Pro) is the only platform this has been built and tested on; Linux x86-64 and Intel macOS have never been run. `.github/workflows/ci.yml` is written to install the pinned toolchain and run `make ci` on macos-15 and ubuntu-24.04, but it has never run: the repository has no remote. Its Bend 2.0.39 archive checksums (in `TOOLCHAIN`, read by the workflow) and the archive layout it assumes were checked against the GitHub release on 2026-11-01; the workflow itself is untested. `make ci` passes locally on Bend 2.0.39 (the date and duration of the last run are in `plans/STATUS.md`). `probes/run_probes.sh` runs the small probe programs the design rests on.

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
- `src/csv.bend`: CSV reading with type inference and explicit schemas, the scan prefix, the v0.1 streaming reader, the v0.2 reader's header step, inference, combine and chunk build (`Csv.v2.*`, the default since 0.2.0), the reader selector `CsvEngine`, rendering and writing.
- `src/fmt.bend`: table rendering, `describe`, fixed-decimal formatting.
- `src/dump.bend`: `DF.dump`, the typed oracle text.
- `src/plan.bend`: the lazy `Plan`, schema resolution, `explain`, the optimizers.
- `src/exec.bend`: validation, scan materialisation, the pure runner `Exec.run_pure` and the physical runner `Exec.run_phys` (the Sort + Head and Filter + Select steps).
- v0.2: `src/csvprod.bend` (the reader's sequential producer of flat byte regions), `src/csvlane.bend` (the tokenizer and typed loops of one region), `src/hcode.bend` (the flat distinct-key coder), `src/ranks.bend` (lexical ranks of distinct strings), `src/radix.bend` (the radix argsort), `src/chunks.bend` (owned chunk trees), `src/ckernels.bend` (chunked kernel wrappers, generated by `bench/w5/gen_ckernels.py`), `src/cexec.bend` (the chunked executor behind the `Engine` selector).
- `LAWS.bend` and `PROOF*.bend`: the laws and their proofs.
- `examples/`, `tests/`, `bench/`, `scripts/`, `probes/`: examples, tests (incl. `tests/regress/` for every review defect and `tests/proof_negative/`), benchmarks and the differential generator, scripts, design probes.

Design and implementation notes: [`DESIGN.md`](DESIGN.md) (goals and the Polars mapping in section 1, laws and the assurance matrix in section 8, deviations in section 14, the v0.1 contract in section 15) and [`IMPLEMENTING.md`](IMPLEMENTING.md) (Bend pitfalls and per-milestone notes). Release notes: [`CHANGELOG.md`](CHANGELOG.md).

## License

Apache License 2.0. Copyright 2026 Lukasz Samson. See [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE). `src/csvparse.bend` is a fork of the MIT-licensed hub package `bend-csv-parser` (Copyright (c) 2026 nohzafk); its MIT notice is kept in the file.
