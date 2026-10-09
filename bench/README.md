# bench: Polars reference + golden outputs

Requires [`uv`](https://docs.astral.sh/uv/); Polars is pinned to `>=2.0,<3` in `pyproject.toml`.

```sh
uv run --project bench python bench/gen.py [n ...]   # default 1_000 100_000 1_000_000 -> bench/data/ (gitignored)
(cd bench && uv run python golden.py)                # regenerate bench/golden/q1..q6.csv from fixtures/tiny.csv
(cd bench && uv run python golden.py --input data/sales_1000.csv --out golden/n1000)   # goldens for another size
scripts/bench.sh                                     # gen if missing; Polars -> results/polars.json; Bend -> results/bend.json; table
```

Data is seeded and deterministic. `fixtures/tiny.csv` (20 rows, includes null discounts) and
`fixtures/products.csv` (64 rows) are tracked; golden floats are written with 4 decimals.
`fixtures/` and `data/` use the same schema, so a Bend implementation can load either.

## Queries (`queries.py`, all signature `qK(sales, products)`; floats are Float32)

| q | what |
|---|------|
| q1 | filter `ok and qty > 50`, select `id, region, price` (file order) |
| q2 | add `revenue = qty * price * (1 - fill_null(discount, 0))` |
| q3 | q2, then group by `region`: sum(revenue), mean(price), count, max(qty), sorted by region |
| q4 | sort by `region` asc, `price` desc (ties broken by `id` asc), first 10 rows |
| q5 | inner join `products` on `product`, group by `category`: sum(qty), sorted by category |
| q6 | `describe()` of `id, qty, price, discount` |

## Timing

`run_polars.py` parses each CSV once (untimed), then times `collect()` per query: best of 5, with
the default engine (streaming in Polars 2.0). It runs twice in subprocesses, once with default
threads and once with `POLARS_MAX_THREADS=1` (must be set before import) for comparison with
single-threaded Bend. Results: `results/polars.json` as `{query, n, seconds, threads}`.
Note q6 includes the `describe()` computation (eager) inside the timed call.

## The release optimizer (M5 part 2)

Since M5 part 2 the default optimizer (`DF.optimize`, `Lazy.collect`) merges adjacent Heads
only (`Optimize.release` = `Opt.hmerge`, proven result-preserving for every plan: LAWS.bend
`release_run`); the analysis-certified Head sink and the other passes are opt-in
(`optimize_full`). Cost on this benchmark: none. No q1-q6 plan has a Head above a
Select/WithColumns (q4's Head sits on a Sort, a barrier for both passes), so the release
optimizer, the previous head pass and the raw plan coincide for q1-q5
(`tests/plan_release_bench.bend` pins the explain texts). Measured on 2026-10-09, q4 at 100k rows,
1 thread, the pre-fallback build (commit 3bd4316^, release = `Opt.head` with the sink) and the
current build interleaved over 4 rounds on a machine with load average 8-14 (another agent
benchmarking at the same time): old 43 / 41 / 39 / 60 ms, new 43 / 41 / 41 / 42 ms; the controls
q1 (old 8, 10; new 10, 8 ms) and q3 (old 36, 38; new 36, 34 ms) scatter the same way. Within the
1 ms clock and the machine noise, no difference.

## Bend side (M7)

`bench/main.bend` is the native driver (`bend bench/main.bend -o build/bench`; `scripts/bench.sh` builds and runs it):

```sh
./build/bench [--threads N] bench/data/sales_1000000.csv q3 [repeats [batch [label [out.csv [consume]]]]]
# -> {"query":"q3","n":1000000,"seconds":0.179,"threads":"default"}
./build/bench bench/data/sales_1000000.csv parse     # CSV parse time (untimed in the benchmark)
```

- `bench/queries.bend` holds the q1..q6 plans (`Q.q1..Q.q5(sales, products)`, `Q.q6(frame)`); main imports it.
- Both CSVs are parsed untimed, then every buffer is walked once (`force`, a fresh parse hands back pending work),
  then `Lazy.collect` (plan optimisation + execution; q6: the eager `describe`) is timed with `IO.now` and the result stays
  alive until after the clock. By default the query runs over a CLONE of the parsed frames and the originals stay referenced, like
  Polars (whose inputs survive `collect`); `consume` runs over the frames themselves, so freeing the 1M-row string columns lands
  inside the timed region (see analysis). `out.csv` writes the first result with `Csv.render(.., Some{4})`.
- `IO.now` has 1 ms resolution: tiny queries run `batch` collects (each over its own freshly parsed inputs) in one window and
  report the mean. Batches distort bigger queries (more live heap: q5 at 100k doubles with batch 3), so `bench.sh` batches only
  where the window would be a few ms (n=1k: 20-500, q2 at 100k: 8, at 1M: 3).
- Parsing again inside one process gets slower (100k rows: ~0.5 s -> ~3 s per parse after a few, 1 thread), and so does everything
  after, so `bench.sh` takes ONE measurement per process, 5 processes (3 at 1M) per cell, best kept. `--threads N` is a
  runtime flag of the native binary (`./file --threads 8`); `IO.args` does not include it, so `bench.sh` passes the label (`1`/`default`).
  Rows below 100 ms at 100k/1M are integer milliseconds (+-1 ms), so read q1/q2 at 100k as rough.
- Correctness (`scripts/bench.sh`, `bench/check.py`): Bend's results (floats at 4 decimals) are diffed against Polars on the same CSV.
  n=1000 goldens are tracked in `golden/n1000/`; n=100k (and 1M with `CHECK_MAX=1000000`) are regenerated into `build/`.
  q1, q2, q4, q5 are byte-identical at 1k, 100k and 1M; q6 at 1k identical, at 100k/1M one float cell differs in the last digit
  (rel 5e-8). **q3 is checked against the f32 reference of DESIGN.md 15.5.3**, not Polars (`bench/golden.py`
  `q3_reference`: the exact sum of each group's f32 values rounded once to f32): Bend's Neumaier group sums are identical to it at
  1k and 100k, while Polars' f32 accumulation is 1-2 ulp away in 5 of 8 groups at 1k. (Before M1, Bend summed groups with a plain
  sequential add: 1M up to 1.3e-5 relative error.)

### Results

Machine: Apple M2 Pro (`sysctl machdep.cpu.brand_string`), 12 cores (8P+4E), 32 GB, macOS 26.7; Bend 2.0.36 native (clang, C lane),
Polars 2.0.0 (`run_polars.py`: best of 5, parsed untimed, default = 12 threads, 1 = `POLARS_MAX_THREADS=1`).
Times are ms per `collect`; ratio = Bend / Polars (above 1x Bend is slower); last column = Bend 1 thread / Bend 12 threads.

| query | n | Bend 1t (ms) | Polars 1t (ms) | ratio 1t | Bend all (ms) | Polars all (ms) | ratio all | Bend 1t/all |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| q1 | 1,000 | 0.07 | 0.09 | 0.8x | 0.07 | 0.13 | 0.6x | 1.0x |
| q2 | 1,000 | 0.05 | 0.09 | 0.6x | 0.05 | 0.13 | 0.4x | 1.1x |
| q3 | 1,000 | 0.45 | 0.26 | 1.8x | 0.55 | 0.90 | 0.6x | 0.8x |
| q4 | 1,000 | 0.57 | 0.17 | 3.4x | 0.62 | 0.60 | 1.0x | 0.9x |
| q5 | 1,000 | 0.55 | 0.27 | 2.0x | 0.62 | 0.91 | 0.7x | 0.9x |
| q6 | 1,000 | 0.50 | 1.48 | 0.3x | 0.55 | 4.44 | 0.1x | 0.9x |
| q1 | 100,000 | 4.00 | 0.18 | 23x | 4.00 | 0.15 | 26x | 1.0x |
| q2 | 100,000 | 0.88 | 0.15 | 6.0x | 0.75 | 0.18 | 4.1x | 1.2x |
| q3 | 100,000 | 30.00 | 1.20 | 25x | 14.00 | 1.27 | 11x | 2.1x |
| q4 | 100,000 | 33.00 | 1.31 | 25x | 17.00 | 1.09 | 16x | 1.9x |
| q5 | 100,000 | 39.00 | 2.10 | 19x | 26.00 | 1.40 | 19x | 1.5x |
| q6 | 100,000 | 11.00 | 8.14 | 1.4x | 11.00 | 6.56 | 1.7x | 1.0x |
| q1 | 1,000,000 | 62.00 | 1.30 | 48x | 63.00 | 0.63 | 100x | 1.0x |
| q2 | 1,000,000 | 7.67 | 0.85 | 9.0x | 7.00 | 0.55 | 13x | 1.1x |
| q3 | 1,000,000 | 327 | 10.93 | 30x | 179 | 3.30 | 54x | 1.8x |
| q4 | 1,000,000 | 384 | 12.47 | 31x | 210 | 3.09 | 68x | 1.8x |
| q5 | 1,000,000 | 399 | 20.88 | 19x | 213 | 5.12 | 42x | 1.9x |
| q6 | 1,000,000 | 119 | 32.32 | 3.7x | 119 | 22.12 | 5.4x | 1.0x |

### Analysis

**Where Bend's time goes (1M rows, 12 threads; probes of the same engine, not part of the table).**
- *Strings.* Every string cell is a cons list. Numeric-only variants of the queries are 1.5-3x cheaper than their string
  counterparts: filter + select of numeric columns 43 ms vs q1 63 ms (the extra `region` gather); group_by on a numeric key
  (100 groups, q3's aggregates) 60 ms vs q3's 179 ms with `region`; group_by region sum(qty) alone 172 ms (almost all of it is coding the 1M
  strings once); sort (price desc, id) + head 130 ms vs sort by `region` + head 196 ms vs q4 210 ms; the join alone is 104 ms
  (hashing every `product` string, ~70 ms) and q5 is 213 ms because the joined `category` strings are gathered and coded again for the group_by.
  Numeric kernels are cheap: q2 (qty*price*(1-fill_null(discount)), 1M rows, 6 passes) is 7-8 ms, 9-13x Polars.
- *CSV.* The parse is untimed but is the biggest single cost in the process: the 41 MB `sales_1000000.csv` takes 5.0 s to read at
  12 threads (5.9 s at 1 thread, i.e. barely parallel), plus 0.44 s for the first walk of the result (the pending work);
  100k rows: 0.35 s / 0.48 s. ~120 ns per input byte: every field is a cons list of `Char`s, then a column of such lists.
- *Freeing inputs.* Bend frames are linear: a query that consumes the parsed 1M-row frames pays to free their string cells inside the
  timed region. With `consume` (inputs not kept) q1 takes 311 ms instead of 63 ms, q3 412 vs 179, q5 513 vs 213 (12 threads);
  the ~250-300 ms difference is the freeing of the unused string cells. The table uses the "inputs stay alive" mode, like Polars.
- *Fixed engine costs* are small: at 1k rows Bend's q1/q2 take 50-70 us, q3-q6 0.45-0.6 ms (Polars default threads: 0.13-4.4 ms,
  its thread-pool overhead dominates there; at 1 thread Polars is 1.8-3.4x faster than Bend on q3-q5 and Bend wins q6 and q1/q2).

**What parallelism bought.** Only operators that fork explicitly scale: q3, q4, q5 run 1.8-2.1x faster on 12 threads (q3 at 100k 2.1x:
string coding in 8 parallel blocks, the join probe forked over 16 blocks, group_by scatter), q1, q2 and q6 gain nothing (1.0-1.2x),
and at 1k rows threads cost 10-20 % (0.8-0.9x). No kernel is forked: `Kernel.fork_depth` is a constant 0 that nothing reads, and there
is no `Eval.parallel_exprs`, so a 12-core machine is mostly idle in the timed region. Polars gains 3.3-4.1x
on q3/q4/q5 at 1M (e.g. q5 21 ms -> 5.1 ms) from the same 12 cores. Bend's 1-thread numbers are therefore the fairer engine comparison:
9-48x slower than 1-thread Polars at 1M (3.7x for q6), 19-25x at 100k (q1, q3-q5); with all threads the gap widens to 13-100x because Polars
keeps scaling and Bend does not.

**Top 3 optimisation opportunities.**
1. *Strings as dictionary codes (or bytes) instead of cons lists*: dictionary-encode low-cardinality string columns at parse time
   (U32 codes + a small dictionary), or hold string columns as flat byte buffers. It removes the per-query coding passes (~120-150 ms
   of q3, q4, q5 at 1M, the 70 ms join hash walk), makes the sort ranks and group keys free, shrinks the gathers, and attacks the 5 s CSV parse and
   the ~300 ms of freeing strings.
2. *Sort + head as top-k, and gather only what is needed*: `Head{10, Sort}` still sorts and gathers all 7 columns of 1M rows (q4 =
   210 ms, most of the difference to the key coding being the gather); an optimiser rule that pushes the limit into `Sort.frame` (argsort, then gather 10 rows)
   or a single-pass top-k would make q4 mostly the key coding. Likewise q5 gathers/codes the joined `category` column for 1M rows when a
   group_by over the 64-row dimension's codes (aggregate by `product` first, then join) would touch 64 groups.
3. *Real parallelism in the numeric kernels and across expressions*: fork the flat kernels (`Kernel.map/zip/fold/compact`) over `ANode`
   halves (the `fork_depth` knob exists but is unused; intra-column speedup was measured at <=1.8x in the probes, so go for fewer, fatter
   blocks) and evaluate independent expressions of a `with_columns`/`select` in parallel; q1, q2 and q6 are flat today and a 12-core
   machine could take them from 8-120 ms towards Polars' range. Smaller items: sum f32 in `group_by` with compensation or pairwise
   (error 1e-5 vs Polars 1e-7 at 1M), and `Plan.optimize` pushing the projection into `Csv.read_with` (the CSV is still parsed whole).

Decision for DESIGN M7: `Kernel.fork_depth` stays 0 and `Eval.parallel_exprs` is not added: there is nothing to tune until kernels
actually fork (item 3), and the numbers do not justify it before the string work (item 1), which is the dominant cost.
