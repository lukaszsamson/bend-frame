# bend-frame

A columnar dataframe library for [Bend](https://bend-lang.com/) 2 (checked against Bend 2.0.36), shaped after the Polars 2.0 eager and lazy APIs. Queries are built as a lazy `Plan`, a pure data tree, and the output schema is resolved before any row is read: `DF.collect_schema` returns a strict error such as a filter on a `u32` column, and `DF.collect` refuses the same plan with the same error. Row order is part of the contract: `select`, `with_columns`, `filter` and `head` keep input order, `sort` is stable and multi-key, and `group_by` and joins answer in first-appearance and left-row order. Dtypes are `Bool`, `U32`, `I32`, `F32` and `Str`, each nullable through a validity mask, with no implicit casts. 48 laws over the schema, expression and optimizer code are stated in `LAWS.bend` and machine-checked by `PROOF.bend`: `bend PROOF.bend` prints `ALL PROOFS CHECK`, and `bend PROOF.bend --verdict` confirms it with Bend's independent, Lean-verified BendTT kernel.

## Quickstart

From a checkout, with the Bend binary at `~/.bend/bin/bend`:

```bend
import ./frame.bend as DF
```

The library is not yet published to the Bend hub. Once it is (`bend login`, then `bend frame.bend --publish bend-frame@0.1.0.0`), the import will be by package name. Until then, import from a checkout as above.

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

`DF.explain` before and after `DF.optimize` (real output). The optimizer adds a projection under the filter, so only the columns the plan uses flow on (the CSV itself is still parsed whole, see `bench/README.md`):

```
-- plan
SORT BY [col("region")]
  GROUP_BY [col("region")] AGG [col("qty").sum().alias("qty_sum"), col("price").mean().alias("price_mean"), lit(1).len().alias("count")] MAINTAIN_ORDER
    FILTER col("ok")
      SCAN CSV bench/fixtures/tiny.csv [id:u32, region:str, product:str, qty:u32, price:f32, discount:f32, ok:bool]
-- optimized plan
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

`scan_csv` reads the header and a sample of the file up front; the rows are read at `collect`.

## Features

### Operations

- Eager (`Frame -> ResT(Frame)`, an error is a value): `select`, `with_columns`, `filter`, `sort` (multi-key, per-key `asc` / `desc` and nulls placement), `group_by` with `sum mean min max count len first last n_unique`, `inner_join` and `left_join` (multi-key), `head`, `describe`, `show`.
- Lazy (`Plan`): `lazy_select`, `lazy_with_columns`, `lazy_filter`, `lazy_sort`, `lazy_group_by`, `lazy_head`, `lazy_inner_join`, `lazy_left_join`, with `source` / `empty_env` for in-memory frames and `scan_csv` for files.
- Inspect and run: `collect_schema`, `schema_show`, `explain`, `optimize` (filter merge, predicate and projection pushdown, head merge), `collect`.
- CSV: `read_csv` (types inferred per column), `scan_csv`, `write_csv` (F32 values in shortest form).

### Expressions

- Columns and literals: `col`, `lit_u32`, `lit_i32` (non-negative), `lit_i32_neg`, `lit_f32`, `lit_str`, `lit_bool`, `alias`.
- Casts: `cast`, `cast_f32`, `cast_u32`.
- Arithmetic: `add sub mul div mod`, `neg`.
- Comparison: `eq ne lt le gt ge`.
- Boolean: `and or not`.
- Nulls: `is_null is_not_null fill_null`.
- Aggregations (inside `group_by` only): `sum mean min max count len first last n_unique`.

### Null semantics

- Every operation ANDs the validity masks of its inputs, so a null operand gives a null result. Null slots hold the dtype default in the data.
- `and` / `or` are Kleene: `false and null` is `false`, `true or null` is `true`.
- `filter` keeps the rows where the predicate is true. A null predicate drops the row.
- `sum`, `mean`, `min`, `max` and `count` skip nulls. `len` counts rows, `first` and `last` keep a null row, `n_unique` counts null as one value.
- `group_by` puts all null keys in one group. Join keys: a null key never matches.
- `sort` puts nulls first unless `nulls_last`, the same default as Polars.

### Differences from Polars

- Dtypes are `Bool U32 I32 F32 Str` only. No `F64`, `I64`, `U64`, dates, times, lists, structs or maps.
- No implicit casts: mixing dtypes in an operator is a `TypeMismatch` error value. A join on a `u32` key against an `i32` key is an error.
- `mean` always answers `F32`, including for integer columns (Polars gives `Float64`).
- Join output is always in left-row order, and the matches of one left row come in right-row order. Only `inner` and `left` joins exist; `outer`, `semi` and `anti` are not implemented.
- `group_by` answers in first-appearance order. `GroupBy` carries a `maintain_order` flag, but v1 ignores it and always orders by first appearance.
- `group_by` `sum` over `F32` is a plain sequential add (about 1e-5 relative error against Polars at 1M rows, see `bench/README.md`). `mean` uses a compensated sum.
- `describe` answers Polars' statistics for numeric columns as `F32` columns. For `Bool` and `Str` columns it reports only `count`, `null_count`, `min` and `max`, as text, with nulls elsewhere.
- Strings support equality and ordering only, with no string functions.
- Aggregations are only available inside `group_by`. There are no window functions.

## Laws

`LAWS.bend` states 48 laws over `src/`. `PROOF.bend` proves all of them with no `@unsafe` and no foreign code. The groups:

- Schema: projection has exactly the requested names in order; `with_columns` keeps the width for an existing name and appends a new one.
- Expression typing: comparisons are `bool`; arithmetic keeps a numeric dtype; `&` and `|` over bools; allowed casts have the target dtype; `count`, `len` and `n_unique` are `u32`; `mean` is `f32`; `min`, `max`, `first` and `last` keep the dtype.
- `Plan.schema`: `source`, `head`, `filter`, `sort` and `select` keep or define the schema as stated; a `Select` of plain columns is exactly `Schema.project`.
- Optimizer: head and merge passes keep the schema, merge leaves no `Filter` on a `Filter`, the merge is idempotent and a fixed point, and the head pass leaves no `Head` on a `Head`.
- Columns and kernels: `head(c, n)` has `min(n, len)` rows; the map, zip and iota kernels produce exactly `2^d` slots.
- `I32`: addition commutes, and the bit pattern round-trips.

Not yet proven (recorded in `DESIGN.md` section 8): schema preservation through the predicate and projection pushdowns (blocked on a `String.eq` reflexivity lemma in Base); the height of `with_columns`; `compact` and `gather` bounds; `I32` negation and addition algebra; CSV and number formatting round trips; and the `group_by` and join schema laws.

## Performance

1M-row rows of the table in [`bench/README.md`](bench/README.md) (Apple M2 Pro, 12 cores; Bend 2.0.36 native, Polars 2.0.0; ms per `collect`, ratio = Bend / Polars):

| query | n | Bend 1t (ms) | Polars 1t (ms) | ratio 1t | Bend all (ms) | Polars all (ms) | ratio all | Bend 1t/all |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| q1 | 1,000,000 | 62.00 | 1.30 | 48x | 63.00 | 0.63 | 100x | 1.0x |
| q2 | 1,000,000 | 7.67 | 0.85 | 9.0x | 7.00 | 0.55 | 13x | 1.1x |
| q3 | 1,000,000 | 327 | 10.93 | 30x | 179 | 3.30 | 54x | 1.8x |
| q4 | 1,000,000 | 384 | 12.47 | 31x | 210 | 3.09 | 68x | 1.8x |
| q5 | 1,000,000 | 399 | 20.88 | 19x | 213 | 5.12 | 42x | 1.9x |
| q6 | 1,000,000 | 119 | 32.32 | 3.7x | 119 | 22.12 | 5.4x | 1.0x |

On one thread, Bend is 3.7x (`describe`) to 48x (q1) slower than Polars at 1M rows; the cost is mostly string handling, and no numeric kernel forks yet. Full results, query definitions and analysis are in [`bench/README.md`](bench/README.md).

Top optimization opportunities, from the analysis there:

1. Strings as dictionary codes or flat bytes instead of cons lists. This removes the per-query coding passes and most of the 5 s CSV parse.
2. Sort plus head as top-k, pushing the limit into the sort so only the needed rows are gathered.
3. Real parallelism in the flat numeric kernels and across the expressions of one `with_columns`.

## Development

```sh
make test      # scripts/test.sh: every tests/**/*.bend against its #| expectations (39 files)
make check     # bend --check-only on every src/ and tests/ file
make proofs    # bend PROOF.bend: prints ALL PROOFS CHECK
make verdict   # bend PROOF.bend --verdict: recheck with the BendTT kernel (needs Lean 4.34)
scripts/bench.sh   # Polars reference (needs uv), then Bend; writes results and a table (about 10 min)
```

`bench/` needs [`uv`](https://docs.astral.sh/uv/) and Polars `>=2.0,<3` (see `bench/README.md`). `probes/run_probes.sh` runs the small probe programs that the design rests on.

Layout:

- `frame.bend`: the public façade; one import for users (`DF.col`, `DF.filter`, `DF.collect`, ...).
- `src/dtype.bend`: `DType`, the vendored two's-complement `I32`, scalar values.
- `src/err.bend`: the `Err` type and the `Res` / `ResT` result aliases.
- `src/kernels.bend`: flat template kernels over arrays (map, zip, fold, compact).
- `src/column.bend`: `Column`, validity masks, `Frame`, head.
- `src/schema.bend`: `Field` and `Schema` (project, with_columns).
- `src/expr.bend`: the `Expr` tree and its strict type checker.
- `src/eval.bend`: eager expression evaluator (a stack machine over whole columns) and the eager verbs.
- `src/sort.bend`: order-preserving sort words, stable LSD radix argsort, `Sort.frame`.
- `src/groupby.bend`: dictionary-encoded `group_by` and the aggregations.
- `src/join.bend`: inner and left equi-joins.
- `src/csv.bend`: CSV reading with type inference, scanning and writing.
- `src/fmt.bend`: table rendering, `describe`, fixed-decimal formatting.
- `src/plan.bend`: the lazy `Plan`, schema resolution, `explain`, `optimize`.
- `src/exec.bend`: runs an optimized plan against an `Env`.
- `LAWS.bend` and `PROOF.bend`: the laws and their proofs.
- `examples/`, `tests/`, `bench/`, `scripts/`, `probes/`: examples, tests, benchmarks, scripts and design probes.

Design and implementation notes: [`DESIGN.md`](DESIGN.md) (goals and the Polars mapping in section 1, laws in section 8, deviations from the plan in section 14) and [`IMPLEMENTING.md`](IMPLEMENTING.md) (per-milestone implementer notes).

## License

MIT. Copyright (c) 2026 Lukasz Samson. See [`LICENSE`](LICENSE).
