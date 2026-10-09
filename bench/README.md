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


## M4 string experiment: Raw / Dictionary storage (plans/M_01.txt section 5)

**Decision: the readers' default str storage is Auto** (`Csv.enc_default() = EncAuto`): a column
read from CSV is a Dictionary (U32 codes + each distinct string once) while it has at most
`max(16384, rows / 64)` distinct values, else Raw (one string per row). `DF.read_csv_enc` with
`DF.str_raw()` / `DF.str_dict()` / `DF.str_auto()` chooses explicitly, `DF.encode_strings`
converts; values, dumps and errors are identical in every storage (DESIGN.md section 14 "M4 string
experiment"). The gate passed; the 41 MB parse target did not (below).

### How it was measured

```sh
uv run --project bench python bench/gen_str.py        # bench/data/str/: <shape>_<distinct>_<rows>.csv + dim_*.csv
MASTER=/tmp/m bash bench/m4.sh                        # build/bench, build/strbench, build/scanbench_{raw,dict,auto}
                                                      # (+ _master binaries from a pre-M4 tree, see the script)
mkdir -p build/m4bin && cp build/bench* build/strbench build/scanbench_* build/m4bin/   # frozen copies
R="uv run --project bench python bench/strbench.py"; B="--bin build/m4bin --threads 1 default --reps 5"
$R q    $B --sizes 1000 100000 1000000 --queries parse q1 q2 q3 q4 q5 q6 --encs master raw auto dict --out ..
$R scan $B --sizes 1000 100000 1000000 --queries q1 q3 q4 q5 --encs master raw auto dict --out ..
$R ops  $B --files short_8_100000 ... --ops parse eq lt gather sort group join render --encs raw dict auto --out ..
$R table --wide <file.jsonl>      # storages side by side;   $R pivot --enc auto <ops.jsonl>   # data x op
```

- Native binaries (Bend 2.0.36, C lane), Apple M2 Pro 12 cores (8P+4E), 32 GB, macOS 26.7. `1` =
  `--threads 1`, `12` = the runtime default. **One measurement per process, 5 processes per cell**,
  the storages of a cell run back to back in each repetition with the order rotated (A/B/C
  interleaving), medians with [min-max]; peak RSS from `/usr/bin/time -l`; the 1-minute load average
  before each run is recorded in the JSON lines and its median is in the wide tables (`load`). The
  machine was shared (other agents' builds and proof checks); during part of the 1k / 100k query runs
  my own `make test` / `make diff` ran too (load 15-30). Ratios between interleaved storages held;
  absolute times are 0-30 % above a quiet machine (e.g. the pre-M4 q1 at 1M, 62 ms in the Results
  table above, measured 101 ms here for the same master binary).
- **Baselines.** `master`: bench/main.bend built from the pre-M4 tree (whole-file reader, Raw
  strings). `raw`: this branch with `EncRaw` (the streaming reader, Raw strings). `auto` / `dict`:
  `EncAuto` / `EncDict`. So `master -> raw` is the **reader's effect** and `raw -> auto/dict` the
  **dictionary's effect**; the tables give both.
- Queries (`build/bench`): parse untimed except the `parse` row (`read_ms + first_walk_ms` of the
  sales file), inputs cloned untimed, the collect timed (1 ms clock: at n = 1000 each value is the
  mean of 40 collects). Operations (`build/strbench`, bench/strbench.bend): one op per process on
  column `s` of a generated file (`id u32, s str, v u32, x f32`; 5 % nulls, 2 % `""`), shapes short
  (3-8 letters), long (60-80 chars of words), prefix (31-char shared prefix + 6 digits), unicode
  (CJK / Polish / Greek / Cyrillic / emoji), with 8, 64, 1,000 or N (all) distinct values; `join` is
  against `dim_*.csv`, every distinct value once in another order, so **equal values carry different
  codes on the two sides**. A ratio is raw / storage (above 1x the storage is faster); when the
  storage's op took 0-1 ms (the clock), the ratio is a lower bound and a 0 ms cell shows `(raw/0 ms)`.

### Sales queries and the parse (100k, 1M rows; 1k in bench/results/m4/final_queries.jsonl)

| data | op | thr | master ms | raw ms | auto ms | dict ms | auto x | dict x | raw vs master | peak RSS MB master/raw/auto/dict | load |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| sales_100000 | parse | 1 | 731 [726-855] | 426 [414-476] | 419 [406-443] | 426 [408-433] | 1.02x | 1.00x | 1.72x | 167/135/133/133 | 20.5 |
| sales_100000 | parse | 12 | 381 [373-388] | 239 [235-258] | 194 [191-200] | 191 [188-311] | 1.23x | 1.25x | 1.59x | 178/136/134/134 | 18.3 |
| sales_100000 | q1 | 1 | 11 [9-11] | 10 [9-11] | 2.0 [1.0-2.0] | 1.0 [1.0-2.0] | 5.00x | 10.00x | 1.10x | 176/139/137/137 | 17.2 |
| sales_100000 | q1 | 12 | 12 [10-13] | 15 [9-16] | 2.0 [1.0-2.0] | 2.0 [1.0-2.0] | 7.50x | 7.50x | 0.80x | 187/141/138/138 | 16.4 |
| sales_100000 | q2 | 1 | 1.0 [1.0-1.0] | 1.0 [1.0-4.0] | 1.0 [1.0-1.0] | 1.0 [1.0-3.0] | 1.00x | 1.00x | 1.00x | 175/138/136/136 | 15.8 |
| sales_100000 | q2 | 12 | 1.0 [0.0-2.0] | 1.0 [1.0-2.0] | 1.0 [1.0-1.0] | 1.0 [1.0-2.0] | 1.00x | 1.00x | 1.00x | 185/140/137/137 | 14.9 |
| sales_100000 | q3 | 1 | 41 [37-48] | 37 [34-41] | 3.0 [3.0-4.0] | 3.0 [3.0-5.0] | 12.33x | 12.33x | 1.11x | 175/140/136/136 | 14.3 |
| sales_100000 | q3 | 12 | 21 [20-23] | 20 [18-22] | 3.0 [2.0-4.0] | 4.0 [3.0-6.0] | 6.67x | 5.00x | 1.05x | 190/145/138/138 | 13.5 |
| sales_100000 | q4 | 1 | 40 [39-80] | 39 [39-42] | 4.0 [4.0-4.0] | 5.0 [4.0-24.0] | 9.75x | 7.80x | 1.03x | 178/140/136/136 | 13.3 |
| sales_100000 | q4 | 12 | 23 [21-47] | 22 [20-29] | 5.0 [4.0-6.0] | 4.0 [3.0-5.0] | 4.40x | 5.50x | 1.05x | 192/145/137/137 | 12.0 |
| sales_100000 | q5 | 1 | 44 [42-44] | 45 [43-57] | 2.0 [2.0-2.0] | 2.0 [2.0-3.0] | 22.50x | 22.50x | 0.98x | 179/141/137/137 | 11.6 |
| sales_100000 | q5 | 12 | 29 [28-32] | 30 [28-32] | 3.0 [2.0-3.0] | 3.0 [2.0-3.0] | 10.00x | 10.00x | 0.97x | 193/148/139/139 | 11.1 |
| sales_100000 | q6 | 1 | 16 [15-18] | 16 [15-25] | 11 [11-13] | 11 [11-15] | 1.45x | 1.45x | 1.00x | 175/138/134/134 | 10.4 |
| sales_100000 | q6 | 12 | 16 [15-17] | 16 [14-18] | 11 [11-13] | 11 [10-16] | 1.45x | 1.45x | 1.00x | 186/140/136/136 | 11.0 |
| sales_1000000 | parse | 1 | 8951 [8667-9925] | 4526 [4489-4700] | 4382 [4263-5623] | 4379 [4261-4385] | 1.03x | 1.03x | 1.98x | 1627/1331/1283/1305 | 22.3 |
| sales_1000000 | parse | 12 | 4277 [4094-4501] | 2456 [2385-2628] | 1977 [1948-3177] | 2085 [1927-2470] | 1.24x | 1.18x | 1.74x | 1732/1332/1315/1306 | 12.5 |
| sales_1000000 | q1 | 1 | 101 [97-102] | 100 [97-104] | 12 [10-13] | 12 [11-22] | 8.33x | 8.33x | 1.01x | 1654/1317/1298/1298 | 10.6 |
| sales_1000000 | q1 | 12 | 104 [99-105] | 101 [98-109] | 12 [11-14] | 12 [12-13] | 8.42x | 8.42x | 1.03x | 1780/1372/1345/1345 | 8.0 |
| sales_1000000 | q2 | 1 | 12 [9-19] | 7.0 [7.0-11.0] | 8.0 [8.0-12.0] | 9.0 [9.0-13.0] | 0.88x | 0.78x | 1.71x | 1647/1314/1305/1301 | 9.3 |
| sales_1000000 | q2 | 12 | 12 [9-17] | 8.0 [7.0-9.0] | 9.0 [7.0-12.0] | 9.0 [8.0-10.0] | 0.89x | 0.89x | 1.50x | 1782/1362/1337/1337 | 14.6 |
| sales_1000000 | q3 | 1 | 372 [356-396] | 343 [339-386] | 22 [21-30] | 25 [23-29] | 15.59x | 13.72x | 1.08x | 1680/1368/1305/1294 | 9.1 |
| sales_1000000 | q3 | 12 | 172 [161-196] | 195 [178-206] | 23 [21-30] | 24 [23-24] | 8.48x | 8.12x | 0.88x | 1814/1398/1341/1306 | 9.0 |
| sales_1000000 | q4 | 1 | 448 [431-508] | 422 [410-445] | 48 [45-64] | 45 [44-52] | 8.79x | 9.38x | 1.06x | 1678/1331/1290/1290 | 12.4 |
| sales_1000000 | q4 | 12 | 265 [235-274] | 248 [228-289] | 49 [45-63] | 48 [46-60] | 5.06x | 5.17x | 1.07x | 1832/1390/1333/1337 | 8.0 |
| sales_1000000 | q5 | 1 | 448 [425-472] | 451 [434-594] | 23 [20-24] | 20 [19-22] | 19.61x | 22.55x | 0.99x | 1676/1335/1298/1298 | 9.4 |
| sales_1000000 | q5 | 12 | 260 [243-271] | 278 [247-300] | 20 [18-101] | 22 [20-24] | 13.90x | 12.64x | 0.94x | 1844/1424/1345/1316 | 9.5 |
| sales_1000000 | q6 | 1 | 166 [147-186] | 149 [143-176] | 109 [106-110] | 107 [106-144] | 1.37x | 1.39x | 1.11x | 1649/1339/1281/1283 | 14.2 |
| sales_1000000 | q6 | 12 | 156 [148-202] | 158 [148-160] | 104 [103-199] | 106 [103-108] | 1.52x | 1.49x | 0.99x | 1765/1362/1328/1328 | 8.8 |

At 1k rows (40-collect means): q3 0.70-0.80 ms raw -> 0.20 ms auto (3.5-3.8x), q4 2.6-2.9x, q5
3.1-4.1x, q1 2x, q2 1.0-1.5x, q6 1.0-1.1x; peak RSS 20-32 MB raw vs 9-21 MB auto.

### scan_csv + collect end to end (1M; 1k, 100k in bench/results/m4/final_scan.jsonl)

| data | op | thr | master ms | raw ms | auto ms | dict ms | auto x | dict x | raw vs master | peak RSS MB master/raw/auto/dict | load |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| sales_1000000 | scan+q1 | 1 | 10671 [10206-13259] | 5131 [4442-7233] | 5446 [4479-9377] | 5194 [4279-7704] | 0.94x | 0.99x | 2.08x | 1591/1299/1281/1282 | 7.5 |
| sales_1000000 | scan+q1 | 12 | 4619 [4443-5652] | 2935 [2725-3002] | 2106 [1958-3424] | 2276 [2036-2740] | 1.39x | 1.29x | 1.57x | 1729/1315/1307/1306 | 12.1 |
| sales_1000000 | scan+q3 | 1 | 10117 [9539-16026] | 5046 [4784-5928] | 4504 [4411-5006] | 4803 [4489-5947] | 1.12x | 1.05x | 2.00x | 1599/1306/1289/1273 | 17.7 |
| sales_1000000 | scan+q3 | 12 | 4243 [3866-4675] | 2543 [2326-2939] | 2203 [1890-2331] | 1927 [1863-3118] | 1.15x | 1.32x | 1.67x | 1792/1371/1307/1316 | 10.9 |
| sales_1000000 | scan+q4 | 1 | 8371 [7970-8695] | 4410 [4273-4430] | 4224 [4135-5149] | 4185 [4175-4640] | 1.04x | 1.05x | 1.90x | 1660/1343/1315/1315 | 5.5 |
| sales_1000000 | scan+q4 | 12 | 3849 [3753-3990] | 2184 [2134-2580] | 1937 [1885-2010] | 1983 [1905-2214] | 1.13x | 1.10x | 1.76x | 1791/1373/1316/1316 | 4.5 |
| sales_1000000 | scan+q5 | 1 | 8787 [8528-12989] | 4767 [4590-5055] | 4219 [4119-4700] | 4280 [4151-5965] | 1.13x | 1.11x | 1.84x | 1669/1342/1315/1283 | 7.3 |
| sales_1000000 | scan+q5 | 12 | 4633 [4452-6688] | 2583 [2443-2827] | 2090 [1965-2707] | 2127 [1983-3674] | 1.24x | 1.21x | 1.79x | 1808/1385/1316/1316 | 17.6 |

The 1-thread scan+q1 cell above was the noisiest (spread 4.4-9.4 s); rerun on its own
(bench/results/m4/final_scan_q1_rerun.jsonl, 5 processes, interleaved):

| data | op | thr | master ms | raw ms | auto ms | dict ms | auto x | dict x | raw vs master | peak RSS MB master/raw/auto/dict | load |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| sales_1000000 | scan+q1 | 1 | 8235 [8127-8346] | 4382 [4226-4651] | 4159 [4057-4356] | 4176 [4110-4222] | 1.05x | 1.05x | 1.88x | 1651/1342/1323/1323 | 12.5 |

At 100k: raw vs master 1.55-1.77x; auto vs raw 1.02-1.27x. End to end is the parse plus the query,
so the dictionary's gain here is the parse at 12 threads (2.46 s -> 1.98 s) plus the query.

### Isolated operations, 1M rows, `short` strings (auto vs raw; 5 processes, 1 and 12 threads)

This first set is bench/results/m4/ops_1m.jsonl, measured in an earlier session of the same branch with
the same `src/` (no source change between that run and the frozen binaries; quieter machine, load 2-8).

| data | thr | parse | sort | group | join | eq | gather |
|---|---|---:|---:|---:|---:|---:|---:|
| short_1000_1000000 | 1 | 0.90x (2175) | 34.76x (730) | 90.67x (816) | 32.50x (390) | 30.00x (240) | 199.00x (597) |
| short_1000_1000000 | 12 | 1.00x (1359) | 10.90x (218) | 32.11x (289) | 15.83x (190) | 30.50x (244) | 206.67x (620) |
| short_64_1000000 | 1 | 0.95x (2118) | 23.10x (462) | 59.56x (536) | 18.73x (206) | 29.25x (234) | 186.00x (558) |
| short_64_1000000 | 12 | 1.05x (1296) | 9.30x (186) | 28.33x (255) | 11.00x (121) | 29.50x (236) | 195.00x (585) |
| short_8_1000000 | 1 | 1.00x (2270) | 18.17x (327) | 39.00x (390) | 14.18x (156) | 30.50x (244) | 163.00x (489) |
| short_8_1000000 | 12 | 1.06x (1354) | 7.79x (148) | 22.00x (220) | 8.92x (107) | 31.50x (252) | 164.33x (493) |
| short_N_1000000 | 1 | 1.00x (2460) | 0.99x (13093) | 0.99x (12915) | 1.00x (6262) | 1.01x (301) | 1.01x (717) |
| short_N_1000000 | 12 | 0.99x (1553) | 0.98x (7811) | 1.02x (7867) | 0.99x (5428) | 1.00x (294) | 0.98x (712) |

Forced Dictionary on the fully distinct column (what Auto avoids by falling back to Raw):

| data | thr | parse | sort | group | join | eq | gather |
|---|---|---:|---:|---:|---:|---:|---:|
| short_N_1000000 | 1 | 0.72x (2460) | 2.77x (13093) | 141.92x (12915) | 0.87x (6262) | 3.50x (301) | 0.88x (717) |
| short_N_1000000 | 12 | 0.66x (1553) | 1.64x (7811) | 81.10x (7867) | 0.84x (5428) | 3.46x (294) | 0.91x (712) |

More 1M operations (encode = `C.Frame.encode` of a Raw frame, decode = back to Raw, drop = freeing the
read frame inside the timed region (input destruction), lt = `s < lit`, pred = `starts_with` +
`len_chars`, render = `Csv.render`, groupv = group by the u32 `v` with `max(s)`, sortx = sort by the f32
`x` (numeric keys; `s` is gathered), group5 = five group_bys each over its own clone (repeated-query
memory: compare its peak RSS with `group`):

| data | thr | encode | decode | drop | lt | pred | render | groupv | sortx | group5 |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| short_1000_1000000 | 1 | (438/0 ms) | (0/4 ms) | (223/0 ms) | 14.93x (224) | 52.00x (156) | 1.11x (3720) | 2.91x (276) | 3.19x (51) | 76.32x (4274) |
| short_1000_1000000 | 12 | (397/0 ms) | (0/4 ms) | 186.00x (186) | 15.00x (180) | 41.00x (164) | 1.28x (3038) | 2.99x (266) | 3.29x (56) | 24.07x (1348) |
| short_64_1000000 | 1 | (281/0 ms) | (0/4 ms) | (125/0 ms) | 16.73x (184) | 51.00x (153) | 1.21x (3176) | 2.93x (258) | 3.33x (50) | 45.77x (2426) |
| short_64_1000000 | 12 | (274/0 ms) | (0/3 ms) | (119/0 ms) | 15.55x (171) | 50.67x (152) | 1.34x (2816) | 2.89x (254) | 3.36x (47) | 17.73x (975) |
| short_8_1000000 | 1 | (214/0 ms) | (0/4 ms) | (101/0 ms) | 20.91x (230) | 50.00x (150) | 1.26x (3260) | 2.31x (261) | 3.21x (45) | 30.96x (1672) |
| short_8_1000000 | 12 | (217/0 ms) | (0/3 ms) | (98/0 ms) | 20.91x (230) | 53.00x (159) | 1.37x (2908) | 2.29x (268) | 3.21x (45) | 12.91x (736) |
| short_N_1000000 | 1 | 1.09x (1503) | (0/0 ms) | 0.98x (195) | 0.93x (154) | 1.09x (202) | 1.04x (4056) | 1.01x (330) | 1.00x (53) | 1.08x (114283) |
| short_N_1000000 | 12 | 0.99x (1604) | (0/0 ms) | 1.03x (204) | 1.04x (152) | 0.99x (180) | 1.13x (4157) | 1.10x (352) | 0.98x (54) | 1.05x (56018) |

| data | op | thr | raw ms | auto ms | dict ms | auto x | dict x | peak RSS MB raw/auto/dict | load |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|
| short_1000_1000000 | group | 1 | 816 [797-843] | 9.0 [8.0-10.0] | 9.0 [8.0-9.0] | 90.67x | 90.67x | 882/854/854 | 4.2 |
| short_1000_1000000 | group | 12 | 289 [283-331] | 9.0 [8.0-10.0] | 9.0 [9.0-10.0] | 32.11x | 32.11x | 910/859/859 | 4.0 |
| short_1000_1000000 | group5 | 1 | 4274 [4125-8282] | 56 [52-75] | 55 [54-78] | 76.32x | 77.71x | 895/871/871 | 15.8 |
| short_1000_1000000 | group5 | 12 | 1348 [1220-1609] | 56 [51-66] | 55 [53-61] | 24.07x | 24.51x | 971/876/876 | 25.5 |
| short_64_1000000 | group | 1 | 536 [526-561] | 9.0 [9.0-9.0] | 9.0 [9.0-10.0] | 59.56x | 59.56x | 856/828/828 | 2.4 |
| short_64_1000000 | group | 12 | 255 [209-275] | 9.0 [8.0-10.0] | 9.0 [9.0-10.0] | 28.33x | 28.33x | 880/833/833 | 2.0 |
| short_64_1000000 | group5 | 1 | 2426 [2323-5428] | 53 [52-69] | 53 [51-55] | 45.77x | 45.77x | 865/832/845 | 13.5 |
| short_64_1000000 | group5 | 12 | 975 [877-1291] | 55 [52-63] | 53 [52-74] | 17.73x | 18.40x | 948/850/850 | 13.8 |
| short_8_1000000 | group | 1 | 390 [383-394] | 10 [10-11] | 10 [10-11] | 39.00x | 39.00x | 827/799/799 | 6.6 |
| short_8_1000000 | group | 12 | 220 [198-283] | 10 [9-11] | 10 [10-10] | 22.00x | 22.00x | 853/804/804 | 6.3 |
| short_8_1000000 | group5 | 1 | 1672 [1644-1687] | 54 [54-57] | 54 [53-57] | 30.96x | 30.96x | 839/815/815 | 8.5 |
| short_8_1000000 | group5 | 12 | 736 [730-817] | 57 [55-62] | 56 [53-57] | 12.91x | 13.14x | 909/820/820 | 8.1 |
| short_N_1000000 | group | 1 | 12915 [12844-13550] | 13016 [12886-13359] | 91 [90-97] | 0.99x | 141.92x | 972/970/1079 | 3.8 |
| short_N_1000000 | group | 12 | 7867 [7614-8191] | 7723 [7700-7781] | 97 [90-111] | 1.02x | 81.10x | 1018/1025/1088 | 3.2 |
| short_N_1000000 | group5 | 1 | 114283 [89653-124202] | 106121 [95210-113558] | 785 [764-834] | 1.08x | 145.58x | 987/987/1299 | 18.4 |
| short_N_1000000 | group5 | 12 | 56018 [46693-66120] | 53106 [48194-57114] | 826 [690-1122] | 1.05x | 67.82x | 1033/1031/1305 | 11.4 |

Forced Dictionary on the fully distinct column, the same operations:

| data | thr | encode | decode | drop | lt | pred | render | groupv | sortx | group5 |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| short_N_1000000 | 1 | (1503/0 ms) | (0/95 ms) | 0.22x (195) | 0.02x (154) | 0.55x (202) | 0.88x (4056) | 0.30x (330) | 3.31x (53) | 145.58x (114283) |
| short_N_1000000 | 12 | (1604/0 ms) | (0/77 ms) | 0.25x (204) | 0.02x (152) | 0.48x (180) | 0.86x (4157) | 0.31x (352) | 3.38x (54) | 67.82x (56018) |

### Shapes at 100k rows (auto vs raw; 5 processes, 1 and 12 threads)

| data | thr | parse | eq | lt | gather | sort | group | join | render |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| long_1000_100000 | 1 | 0.75x (703) | 134.00x (134) | 16.60x (83) | 89.00x (178) | 131.71x (922) | 961.00x (961) | 10.17x (722) | 1.41x (898) |
| long_1000_100000 | 12 | 0.70x (485) | 131.00x (131) | 16.20x (81) | 87.50x (175) | 48.60x (243) | 288.00x (288) | 37.00x (370) | 1.57x (802) |
| long_64_100000 | 1 | 0.72x (690) | 135.00x (135) | 37.00x (37) | (187/0 ms) | 185.00x (370) | 457.00x (457) | 95.00x (285) | 1.48x (923) |
| long_64_100000 | 12 | 0.73x (449) | 130.00x (130) | 18.50x (37) | 169.00x (169) | 39.67x (119) | 228.00x (228) | 53.00x (106) | 1.75x (786) |
| long_8_100000 | 1 | 0.94x (689) | 142.00x (142) | 55.00x (110) | (163/0 ms) | 121.00x (242) | 318.00x (318) | 124.00x (124) | 1.54x (872) |
| long_8_100000 | 12 | 0.75x (435) | 142.00x (142) | 112.00x (112) | (158/0 ms) | 41.00x (82) | 159.00x (159) | 37.00x (74) | 1.79x (789) |
| long_N_100000 | 1 | 0.89x (641) | 1.05x (137) | 0.97x (57) | 1.02x (178) | 1.00x (3203) | 0.91x (3244) | 0.90x (1637) | 0.91x (793) |
| long_N_100000 | 12 | 0.93x (468) | 1.24x (162) | 0.98x (56) | 1.01x (182) | 0.93x (1955) | 1.08x (2082) | 0.93x (1375) | 1.08x (768) |
| prefix_1000_100000 | 1 | 0.78x (403) | 209.00x (209) | 16.64x (183) | 94.00x (94) | 53.86x (754) | 648.00x (648) | 11.33x (204) | 1.53x (574) |
| prefix_1000_100000 | 12 | 0.78x (258) | 213.00x (213) | 21.56x (194) | 97.00x (97) | 12.00x (120) | 165.00x (165) | 21.20x (106) | 1.62x (523) |
| prefix_64_100000 | 1 | 0.83x (379) | 211.00x (211) | 178.00x (178) | (112/0 ms) | 104.00x (312) | 350.00x (350) | 89.00x (89) | 1.52x (570) |
| prefix_64_100000 | 12 | 0.81x (266) | 214.00x (214) | 177.00x (177) | (113/0 ms) | 24.33x (73) | 117.00x (117) | 25.00x (50) | 1.70x (521) |
| prefix_8_100000 | 1 | 0.89x (383) | 213.00x (213) | 89.00x (178) | (110/0 ms) | 93.00x (186) | 241.00x (241) | 52.00x (52) | 1.41x (523) |
| prefix_8_100000 | 12 | 0.84x (261) | 208.00x (208) | 185.00x (185) | 119.00x (119) | 34.00x (68) | 111.00x (111) | 36.00x (36) | 1.65x (476) |
| prefix_N_100000 | 1 | 0.96x (409) | 1.02x (208) | 0.98x (197) | 1.03x (119) | 0.98x (5104) | 1.01x (5247) | 1.06x (999) | 1.08x (617) |
| prefix_N_100000 | 12 | 0.96x (274) | 1.00x (204) | 0.99x (198) | 0.97x (112) | 0.97x (2632) | 1.09x (2844) | 1.01x (863) | 1.03x (508) |
| short_1000_100000 | 1 | 0.90x (215) | 25.00x (25) | 9.00x (18) | 61.00x (61) | 38.00x (114) | 124.00x (124) | 36.00x (108) | 1.21x (316) |
| short_1000_100000 | 12 | 0.97x (140) | 25.00x (25) | 10.00x (20) | 59.00x (59) | 9.00x (27) | 39.00x (39) | 10.00x (30) | 1.20x (280) |
| short_64_100000 | 1 | 0.92x (201) | 24.00x (24) | 23.00x (23) | 63.00x (63) | 16.33x (49) | 58.00x (58) | 25.00x (25) | 1.05x (316) |
| short_64_100000 | 12 | 1.10x (141) | 23.00x (23) | 24.00x (24) | (73/0 ms) | 6.67x (20) | 31.00x (31) | 8.00x (16) | 1.34x (284) |
| short_8_100000 | 1 | 0.99x (206) | 24.00x (24) | 24.00x (24) | 49.00x (49) | 17.00x (34) | 41.00x (41) | 16.00x (16) | 1.40x (331) |
| short_8_100000 | 12 | 1.11x (135) | 28.00x (28) | 25.00x (25) | (52/0 ms) | 9.00x (18) | 28.00x (28) | 12.00x (12) | 1.27x (251) |
| short_N_100000 | 1 | 0.93x (222) | 1.00x (30) | 1.05x (23) | 1.13x (77) | 1.05x (904) | 1.10x (1078) | 1.04x (595) | 1.03x (372) |
| short_N_100000 | 12 | 0.96x (157) | 0.94x (29) | 0.88x (22) | 0.89x (74) | 0.96x (509) | 0.93x (497) | 0.96x (467) | 0.96x (306) |
| unicode_1000_100000 | 1 | 0.90x (254) | 35.00x (35) | 5.00x (25) | 58.00x (58) | 28.83x (173) | 196.00x (196) | 31.00x (93) | 1.20x (317) |
| unicode_1000_100000 | 12 | 0.89x (161) | 35.00x (35) | 7.50x (30) | 63.00x (63) | 11.00x (44) | 61.00x (61) | 13.33x (40) | 1.21x (263) |
| unicode_64_100000 | 1 | 0.88x (227) | 31.00x (31) | 9.50x (19) | (55/0 ms) | 39.00x (78) | 96.00x (96) | 35.00x (35) | 1.31x (307) |
| unicode_64_100000 | 12 | 0.97x (166) | 32.00x (32) | 17.00x (17) | 69.00x (69) | 14.00x (28) | 49.00x (49) | 11.00x (22) | 1.34x (268) |
| unicode_8_100000 | 1 | 0.89x (208) | 36.00x (36) | 28.00x (28) | 50.00x (50) | 24.00x (48) | 66.00x (66) | 23.00x (23) | 1.26x (298) |
| unicode_8_100000 | 12 | 1.03x (146) | 34.00x (34) | 29.00x (29) | (67/0 ms) | 11.50x (23) | 40.00x (40) | 18.00x (18) | 1.38x (287) |
| unicode_N_100000 | 1 | 0.95x (246) | 1.03x (40) | 1.04x (26) | 0.88x (65) | 1.14x (2104) | 1.05x (1888) | 1.03x (641) | 1.03x (333) |
| unicode_N_100000 | 12 | 0.99x (175) | 1.00x (38) | 1.00x (26) | 1.01x (75) | 0.99x (1054) | 0.99x (1113) | 0.95x (552) | 1.11x (318) |

Forced Dictionary on the fully distinct columns:

| data | thr | parse | eq | lt | gather | sort | group | join | render |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| long_N_100000 | 1 | 0.66x (641) | 19.57x (137) | 0.05x (57) | 0.94x (178) | 2.84x (3203) | 405.50x (3244) | 0.96x (1637) | 0.90x (793) |
| long_N_100000 | 12 | 0.63x (468) | 23.14x (162) | 0.05x (56) | 0.99x (182) | 1.65x (1955) | 173.50x (2082) | 0.98x (1375) | 0.99x (768) |
| prefix_N_100000 | 1 | 0.74x (409) | 41.60x (208) | 0.12x (197) | 1.04x (119) | 3.21x (5104) | 1049.40x (5247) | 0.96x (999) | 0.94x (617) |
| prefix_N_100000 | 12 | 0.64x (274) | 40.80x (204) | 0.13x (198) | 0.89x (112) | 1.79x (2632) | 474.00x (2844) | 0.93x (863) | 0.98x (508) |
| short_N_100000 | 1 | 0.72x (222) | 4.29x (30) | 0.07x (23) | 1.01x (77) | 2.49x (904) | 154.00x (1078) | 0.77x (595) | 0.90x (372) |
| short_N_100000 | 12 | 0.67x (157) | 5.80x (29) | 0.07x (22) | 0.94x (74) | 1.49x (509) | 62.12x (497) | 0.85x (467) | 0.88x (306) |
| unicode_N_100000 | 1 | 0.75x (246) | 8.00x (40) | 0.04x (26) | 0.90x (65) | 3.14x (2104) | 377.60x (1888) | 0.79x (641) | 0.90x (333) |
| unicode_N_100000 | 12 | 0.68x (175) | 9.50x (38) | 0.04x (26) | 0.99x (75) | 1.75x (1054) | 222.60x (1113) | 0.80x (552) | 0.93x (318) |

### Cardinality sweep at 1M (`short`; 10k, 100k, 500k distinct; `prefix` with 1000; 3 processes, 12 threads, earlier session)

dict vs raw:

| data | thr | parse | sort | group | join | eq |
|---|---|---:|---:|---:|---:|---:|
| prefix_1000_1000000 | 12 | 0.79x (2712) | 28.44x (768) | 134.22x (1208) | 36.67x (550) | 302.57x (2118) |
| short_100000_1000000 | 12 | 0.76x (1497) | 10.30x (2502) | 189.29x (2650) | 3.41x (1604) | 26.36x (290) |
| short_10000_1000000 | 12 | 1.01x (1450) | 13.23x (410) | 54.67x (492) | 13.54x (379) | 39.14x (274) |
| short_500000_1000000 | 12 | 0.68x (1583) | 3.63x (5851) | 121.61x (5959) | 1.22x (3163) | 6.89x (303) |

auto vs raw (10k stays a Dictionary; 100k and 500k fall back to Raw):

| data | thr | parse | sort | group | join | eq |
|---|---|---:|---:|---:|---:|---:|
| prefix_1000_1000000 | 12 | 0.79x (2712) | 25.60x (768) | 134.22x (1208) | 39.29x (550) | 302.57x (2118) |
| short_100000_1000000 | 12 | 1.01x (1497) | 0.99x (2502) | 1.02x (2650) | 1.02x (1604) | 1.00x (290) |
| short_10000_1000000 | 12 | 0.99x (1450) | 12.81x (410) | 54.67x (492) | 14.04x (379) | 34.25x (274) |
| short_500000_1000000 | 12 | 1.03x (1583) | 0.99x (5851) | 1.00x (5959) | 1.01x (3163) | 1.00x (303) |

### The gate (plan section 5) and the decision

| criterion | result |
|---|---|
| >= 1.5x median on representative low-cardinality workloads | **pass**: sales q1 / q3 / q4 / q5 (8, 64, 8 and 64 distinct keys) auto vs raw at 1M: q1 8.3-8.4x, q3 8.5-15.6x, q4 5.1-8.8x, q5 13.9-19.6x; at 100k 4.4-22.5x; at 1k 2-4x. Isolated low-cardinality ops at 1M: eq 29-31x, gather 160-200x, sort 7.8-35x, group 22-91x, join 8.9-33x |
| no material memory regression | **pass**: peak RSS auto <= raw in every sales cell (1M: 1281-1345 MB vs 1314-1424 MB raw, 1627-1844 MB master); low-cardinality ops -2..-6 %; high-cardinality auto = raw +0-4 % (forced Dictionary +7-32 %, which Auto avoids); repeated queries (group5) grow the peak RSS by +1-2 % over one group_by in auto (short_1000 at 1M: 854 -> 871 MB at 1 thread, 859 -> 876 MB at 12) against +1-7 % in raw (882 -> 895, 910 -> 971 MB); fully distinct: auto 970 -> 987 MB = raw 972 -> 987 MB (forced Dictionary 1079 -> 1299 MB) |
| no > 15 % median slowdown on numeric controls | **pass**: q2 (numeric with_columns) 0.81-1.23x over three sets of 5 processes (a 7-12 ms query whose single runs range 7-35 ms on this machine): at 1M the batch-1 set (final_queries) reads 0.88x / 0.89x (1 / 12 threads, 7 vs 8 and 8 vs 9 ms at the 1 ms clock) and the batch-3 set (final_q2_1m_batch) 0.81x / 1.23x, pooled medians 0.90x (raw 8.7, auto 9.7 ms) / 1.02x; at 100k (batch 20, final_q26_batch) 1.00x / 0.86x, forced Dictionary 0.70x / 1.10x. The closest control to the 15 % line, inside it on every pooled median; its timed region touches no string, so the residue is the noise floor rather than a storage cost; q6 (describe of 4 numeric columns) 1.37-1.52x faster (the timed region drops the unused str columns, cheaper as codes); sortx (numeric sort keys) 3.2-3.4x faster on 8 / 64 / 1,000 distinct (the gathered `s` is codes), 0.98-1.00x on the fully distinct column; groupv (numeric key, `max(s)`) 2.3-3.0x faster on 8 / 64 / 1,000 distinct, 1.01-1.10x on the fully distinct column |
| no > 15 % median slowdown on high-cardinality controls | **pass** (Auto falls back to Raw): every fully distinct cell at 100k and 1M is within 0.88x-1.24x of raw (median of the cells 1.00x; the worst, 0.88x, are 22 vs 25 ms and 65 vs 74 ms cells whose other thread count reads 1.05x / 1.03x); the 100k / 500k-distinct 1M files 0.99-1.03x |
| target 3x on q1 / q3 / q5 | **met** at 100k and 1M (above) |
| target 41 MB parse < 1.5 s | **not met**: 1.98 s auto at 12 threads [1.95-3.18], 4.38 s at 1 thread (raw 2.46 / 4.53 s; master 4.28 / 8.95 s) |

**Costs that remain (reported, not gated):**
- *Parsing low-cardinality long strings*: coding a cell walks it twice more than keeping it (hash,
  then compare with the entry) and frees it: long (60-80 chars) 0.70-0.94x of raw's parse at 100k,
  prefix (37 chars) 0.78-0.89x, prefix_1000 at 1M 0.79x; short strings 0.90-1.11x; the sales file
  (short keys, 7 columns) is faster to read (1.24x at 12 threads, 1.03x at 1). Any string operation
  after the read repays it many times over; read + render only roughly breaks even (render
  1.2-1.8x faster). A forward hash computed while the parser accumulates the field would remove one
  walk (not done).
- *Auto's fall-back*: a fully distinct column is coded for its first ~16k rows, then decoded (the one
  rescan); at 100k that is visible as 0.89-0.96x on the parse of N-distinct files, at 1M 0.99-1.00x.
- *Raw high-cardinality group / sort stay slow* (fully distinct 1M short strings: group 7.9-12.9 s,
  sort 7.8-13.1 s; forced Dictionary 91 ms / 4.7 s) because Auto keeps them Raw; the Raw group_by
  should code keys through the same hash index (`ST.Dict`) instead of its current path (future work).
- *The transient whole-file string*: a file under 64 MiB is read as one Bend `String` (one piece,
  DESIGN.md section 14 M4 item 5), which dominates the peak RSS of a 41 MB read (~1.3 GB in every
  storage; master 1.6-1.8 GB). 1 MiB pieces would cap that (measured at the change: 464 MB Raw /
  155 MB Dictionary) but were ~3x slower natively.

**Reader effect vs dictionary effect (1M sales).** The streaming reader alone (master -> raw): parse
1.98x faster at 1 thread, 1.74x at 12; peak RSS -18..-24 %; the queries unchanged (0.88-1.11x: they
run over the same Raw columns; q2 at 1M read 1.5-1.7x in the batch-1 runs, 0.97-1.03x batched at 100k). The dictionary (raw -> auto): parse 1.03x / 1.24x, queries 5-20x,
RSS -2..-6 %. End to end (scan + collect, 1M): master -> raw 1.57-2.08x, raw -> auto 1.04-1.39x
(scan+q1 at 1 thread read 0.94x with a 4.5-9.4 s spread; rerun alone: 1.05x).

**Result files** (bench/results/m4/, JSON lines, one run per line with its load and peak RSS):
final_queries.jsonl (q1-q6 and the parse, 1k / 100k / 1M, master / raw / auto / dict), final_scan.jsonl
and final_scan_q1_rerun.jsonl (scan_csv + collect), final_q26_batch.jsonl and final_q2_1m_batch.jsonl
(q2 above the clock), final_ops_1k.jsonl, final_ops_100k.jsonl, final_ops_1m_more.jsonl and
ops_1m.jsonl (isolated operations; ops_1m from an earlier session, same `src/`), ops_sweep.jsonl (the
cardinality sweep). queries.jsonl, scan.jsonl, ops_100k.jsonl and ops_1m_more.jsonl are earlier
partial runs of the same matrix (pre-final binaries), kept for reference and superseded by the final_ files.
