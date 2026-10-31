# bench/tpch: a PDS-H-style workload

The Polars benchmark suite (PDS-H, the TPC-H queries as dataframe code) adapted to what bend-frame
can express, used to profile the library on a multi-table ETL workload. It is not TPC-H: the data
comes from `gen.py` (seeded, deterministic), not dbgen, and the queries are trimmed to bend-frame's
dtypes and verbs.

| file | what |
|---|---|
| `gen.py` | lineitem, orders, customer, supplier, nation, region as CSV under `bench/data/tpch/sf<scale>/` (gitignored). Same keys, value ranges and selectivities as dbgen; dates are u32 `yyyymmdd`, money is f32; no part / partsupp. sf 0.2: 1.2M lineitem rows (85 MB), 300k orders. |
| `queries.bend` | Q1, Q3, Q4, Q5, Q6, Q10, Q12, Q13, Q18 as lazy plans, public facade only (`frame.bend`). |
| `run.bend` | the driver: reads every table with `DF.read_csv` (each read timed), then runs each query `repeats` times over a fresh clone of the inputs; the timed region is `DF.collect` alone (`TPCH_OPT=full`: `DF.collect_full`). Optionally writes each result as CSV. |
| `run_polars.py` | the same nine queries in Polars: `time` (best-of collect per query) and `check` (compares the driver's CSVs with Polars: exact for keys and integers, 1e-4 relative for floats). |
| `explain.bend` | prints every plan as written and after `DF.optimize_full`. |

What each query exercises: Q1 a 98% filter, a derived column and eight aggregations over two
dictionary-string keys; Q3 two joins, a three-key group_by, a sort and head; Q4 a semi join; Q5 five
joins, the last on two keys; Q6 a 2%-selective four-conjunct filter and a global sum; Q10 three
joins and a four-key group_by including a distinct string; Q12 `is_in`, column-to-column compares
and `when` sums; Q13 a left join, a count of a nullable column and two group_bys; Q18 a group_by
over every order key, then joins back.

```sh
make tpch                                       # gen if missing, build, run at 1 thread, check against Polars
uv run --project bench python bench/tpch/gen.py 0.01 0.2
~/.bend/bin/bend bench/tpch/run.bend -o build/tpch
./build/tpch +RTS --threads 1 -RTS bench/data/tpch/sf0.2 all 5 build/tpch_out   # q1..q18 or all
uv run --project bench python bench/tpch/run_polars.py check bench/data/tpch/sf0.2 build/tpch_out
POLARS_MAX_THREADS=1 uv run --project bench python bench/tpch/run_polars.py time bench/data/tpch/sf0.2 5
```

## Profiling

The native binaries keep one symbol per Bend function (`WL_FID_<module>_<name>`), with the hot loops
as anonymous `spin_N` functions under them, so macOS `sample` gives a usable call graph. Start the
driver with many repeats of one query, wait until the reads are done, then sample:

```sh
./build/tpch +RTS --threads 1 -RTS bench/data/tpch/sf0.2 q1 60 > /dev/null & sleep 5; sample $! 10 1 -file q1.sample
```

`bend bench/tpch/run.bend -o tpch.c` emits the C, where a `spin_N` can be matched to its Bend loop by
its parameter names (`spin_1050`: `_ao_*`, `_mi_*` and `blk_read` of a mask word is
`Kernel.compact_keep.go`).

## Findings (2026-10-31, Apple M2 Pro, Bend 2.0.39, sf 0.2, 1 thread; machine shared, load 15-200)

All results match Polars at sf 0.01 and sf 0.2 (`run_polars.py check`). ms per `collect`, median of
the best-of-5 of 4 interleaved processes per binary (`base` = commit 6893f49, `new` = this tree);
Polars 2.0.0 with `POLARS_MAX_THREADS=1`, best of 5, measured in the same session. The machine was
loaded throughout, so read differences under ~15% as noise.

| query | base | new | new / base | Polars 1t | new / Polars |
|---|---:|---:|---:|---:|---:|
| q1 | 110 | 91 | 0.83 | 30 | 3.1x |
| q3 | 47.5 | 31.5 | 0.66 | 13.5 | 2.3x |
| q4 | 43.5 | 27 | 0.62 | 9.2 | 2.9x |
| q5 | 48.5 | 22 | 0.45 | 12.7 | 1.7x |
| q6 | 18.5 | 13.5 | 0.73 | 2.6 | 5.2x |
| q10 | 37 | 35 | 0.95 | 14.4 | 2.4x |
| q12 | 30.5 | 26 | 0.85 | 23 | 1.1x |
| q13 | 21.5 | 17.5 | 0.81 | 18.2 | 1.0x |
| q18 | 27 | 20 | 0.74 | 38.5 | 0.5x |
| sum | 384 | 283.5 | 0.74 | 162 | 1.8x |

What the profiles showed (`sample`, all nine queries, before the fixes) and what changed:

1. **Joins built their hash table on the right input, whatever its size** (~35% of all query time,
   `Dense.go`). Q5 joins a 45k-row left side to all 1.2M lineitem rows: the pair table had 2^22 slots
   in three arrays and every insert missed the cache. The table is now built over the smaller side and
   probed by the other (`Join.side`; ids only label equal keys, so no match, count or order changes),
   and a first word key whose codes span less than max(2^16, 2 (nl + nr)) gets direct-address ids, one
   read and one write per row, no hashing (`Join.word`). Q5 2.2x, Q4 1.6x, Q3 1.5x.
2. **A selective filter compacted every column over every row** (~20% of query time,
   `Kernel.compact_keep.go`). Q6 keeps 2% of lineitem and compacted all 13 columns over 1.2M rows. When
   at most 1/8 of the rows survive, `Eval.filter.mask` now gathers the kept rows once by their positions
   and hands on an all-ones mask, so the proven compaction that follows walks `kept` rows per column.
   The compaction itself (`Frame.filter_mask`, `Exec.fc`) is unchanged: it is pinned by term-equality
   proofs (PROOF_filtsel, PROOF_contents, PROOF_fused), which hold for every mask result. Q6 1.4x, Q12 1.2x.
3. **group_by ranked a wide integer key with a radix sort** (Q18: ~38% of the query). A key spanning
   1.2M values over 1.2M rows exceeded the fixed 2^20 range of direct coding; the bound is now
   max(2^20, 2n). Q18 1.35x.
4. **Multi-key group_by densified three times** (first key, each combine, then the final pass that
   numbers the groups). Combined codes only need to be injective, so the intermediate densifies are
   gone; a product of ranges over 2^22 densifies both sides before falling back to the pair rank's two
   radix sorts.

Left as they are, with the reason:

- **The CSV read dominates end to end**: lineitem (85 MB) takes 2.0-2.3 s against 0.67-0.76 s for
  Polars at one thread, while all nine queries together take ~0.3 s. The reader's lane parser was the
  subject of the v0.2 milestone; its serial producer and the File API limit are documented in
  DESIGN.md 17.10.
- **Projection pushdown is opt-in.** The default `DF.collect` runs only the proven rewrite (head merge),
  so every filter and join carries all 13 lineitem columns. `TPCH_OPT=full` (`DF.collect_full`) cuts a
  further 25-45% on Q3, Q4, Q6, Q10 and Q13 (Q13 17 -> 9 ms, Q3 31 -> 21 ms). Making it the default is a
  contract decision (README "What v0.1 claims"), not a performance fix.
- **Q1's aggregations** are six separate compensated-sum scatters over 1.2M rows; the sequential
  Neumaier sum in row order is the F32 contract (DESIGN.md 15.5.3), so they are not reassociated.
- **Filters that keep most rows** (Q1 keeps 98%) still compact every column over every row: a cheaper
  compaction loop means re-proving the PROOF_filtsel / PROOF_fused development.
