# bench/m2: the W0 measurement harness (v0.2 performance milestone)

Everything the v0.2 work packages and the orchestrator need to take gate measurements (plans/M_02.txt
sections 0 and 5: G2 scaling, G3 targets, G4 RSS, G6 phases) with the SAME procedure, against the pinned
baseline (commit 3612482) built side by side with the candidate checkout.

```sh
make m2-baseline                  # build/m2/baseline-src (git archive of 3612482) + build/m2/baseline/driver
make m2-candidate                 # build/m2/candidate/driver from this checkout (run.py refuses a stale one)
make m2-data                      # bench/data/** (gitignored) and a check of its frozen sha256
make m2-smoke                     # 1 process per cell, 1k/100k rows, 1 and 12 threads, both binaries: a sanity check
make m2-bench LABEL=x             # the full gate run (needs load < 2 at the start; see "Acceptance rules")
make m2-bench LABEL=x M2_ARGS=--provisional   # the same on a shared machine, labelled provisional
make m2-summary LABEL=x           # medians, ranges, raw samples, ratios, scaling, RSS, stage table
make m2-micro LABEL=x             # the preserved review probes (bench/micro)
make m2-freeze                    # re-freeze expected outputs from the BASELINE (a deliberate act)
```

Everything is `python3 bench/m2/run.py <cmd>` (standard library only; `uv run --project bench python` works
too). `run.py list --md` prints the workload table, `run.py list --inputs` the input hashes.

## Files

| file | what |
|---|---|
| `driver.bend` | the ONE native driver, built unchanged at baseline and candidate: modes `phases`, `e2e`, `e2ecsv`, `stages`, `selfcheck` |
| `baseline.sh` | materialises 3612482 (`git archive` into `build/m2/baseline-src`, no `.git`), copies the driver in, builds both binaries, writes `BUILD.json` (commit, src hash, driver hash, bend version) |
| `workloads.py` | the FROZEN workload list (ids, ops, inputs, batches, modes) |
| `gen.py` | input generation for the m2-only inputs and the check of every input's sha256 (`inputs.json`) |
| `run.py` | build / freeze / run / summary / micro / list |
| `expected.json` | the expected outputs, frozen from the BASELINE binary (content hash, dump hash for small results, row count, CSV sha256) |
| `inputs.json` | sha256 of every input file |
| `results/*.jsonl` | one JSON record per process (+ a `meta` record per run); `provisional-baseline.jsonl` is the W0 provisional run |
| `../micro/` | the perf-review probes `ops.bend`, `maps.bend` (see its README) |

## Baseline and candidate

`bench/m2/baseline.sh` does `git archive 3612482 | tar -x -C build/m2/baseline-src`, copies
`bench/m2/driver.bend` into it and builds `build/m2/baseline/driver`; `--candidate` builds
`build/m2/candidate/driver` from the checkout. Both drivers are the same file; the baseline's
`bench/main.bend` and `bench/queries.bend` are NOT used, so `bench/main.bend` (and `scripts/bench.sh`,
`make bench-check`) are untouched. The driver reaches the library through the public facade
(`import ./../../frame.bend as DF`: read_csv, clone, collect, source/add_source, the lazy verbs, the eager
verbs, describe, write_csv, dump) and touches `src/` only in the clearly marked shim at the top of the
file: the walk that forces every cell (`Fw.*`, the same code as `bench/main.bend` `force`), the content
hash (`Hc.*`) and the plan constructor `P.GroupBy` (the facade's `lazy_group_by` sets
`maintain_order = True`, the baseline q3/hc runs use `False`). The facade at HEAD is identical to the baseline's
(`frame.bend` is part of the source hash; the same driver compiles at both ends and `BUILD.json` records
`facade_changed_lines_vs_baseline`). If a later work package changes the column representation, only `Fw.*`
and `Hc.*` need adapting; `Hc` hashes the LOGICAL content, so the frozen expectations stay valid.

`run.py` records for each binary its `BUILD.json` and refuses a candidate whose source hash
(`frame.bend` + `src/**/*.bend`) or driver hash differs from the checkout (`--allow-stale` to override):
never measure a stale binary. Rebuild with `make m2-candidate`.

### Engine selector

A string, `v01` for the current (baseline) executor. The runner passes it to every process as the
environment variable `BF_ENGINE` and records it in every JSONL record (`--engine NAME`). W5 (D7) registers
new names (`chunked`, ...) and decides how Bend code reads the variable (`IO.get_env("BF_ENGINE")`, as
`bench/main.bend` does for `BF_STR`/`BF_OPT`). The thread count is the native runtime flag `--threads N`
(not visible in `IO.args`).

W6.3: `BF_ENGINE=v02` selects the v0.2 CSV reader for every input the driver reads (`--engine v02`).
The driver reads CSV through `bench/m2/engine.bend` (`Eng.read_csv`: `DF.read_csv_v02` for `v02`, else
`DF.read_csv`). The pinned baseline facade has no v0.2 reader, so `baseline.sh` copies
`bench/m2/engine_v01.bend` in as the baseline's `engine.bend` (v0.1 whatever `BF_ENGINE` says): a run
with `--engine v02` therefore compares the v0.2 reader (candidate) against the v0.1 reader (baseline).
The driver hash in `BUILD.json` (and `run.py`'s staleness check) covers `driver.bend` followed by
`engine.bend`. `selfcheck` reads with v0.1 only.

## Workloads (frozen)

Paths are under `bench/data/` (gitignored). Changing a workload invalidates `expected.json` and every
number taken with it: add new ids instead, and re-freeze deliberately.

| id | group | op | input | aux | rows | batch | param | modes | smoke | what |
|---|---|---|---|---|---:|---:|---:|---|---|---|
| q1_1m | q1m | q1 | `sales_1000000.csv` | `products.csv` | 1,000,000 | 1 | - | phases, e2e |  | filter ok & qty>50, select id,region,price (1M rows) |
| q2_1m | q1m | q2 | `sales_1000000.csv` | `products.csv` | 1,000,000 | 1 | - | phases, e2e |  | with_columns revenue = qty*price*(1-fill_null(discount,0)) (1M rows) |
| q3_1m | q1m | q3 | `sales_1000000.csv` | `products.csv` | 1,000,000 | 1 | - | phases, e2e |  | q2, group_by region (sum revenue, mean price, count, max qty), sort region (1M rows) |
| q4_1m | q1m | q4 | `sales_1000000.csv` | `products.csv` | 1,000,000 | 1 | - | phases, e2e |  | sort region asc, price desc, id asc; head 10 (1M rows) |
| q5_1m | q1m | q5 | `sales_1000000.csv` | `products.csv` | 1,000,000 | 1 | - | phases, e2e |  | inner join products, group_by category sum qty, sort (1M rows) |
| q6_1m | q1m | q6 | `sales_1000000.csv` | `products.csv` | 1,000,000 | 1 | - | phases, e2e |  | describe of id, qty, price, discount (1M rows) |
| parse_1m | parse | parse | `sales_1000000.csv` | - | 1,000,000 | 1 | - | phases, e2e |  | CSV parse of bench/data/sales_1000000.csv (41 MB) |
| filter_sel0_1m | filter | filter | `sales_1000000.csv` | - | 1,000,000 | 1 | 100 | phases |  | filter qty > 100: about 0% of 1M rows kept (all 7 columns compacted) |
| filter_sel1_1m | filter | filter | `sales_1000000.csv` | - | 1,000,000 | 1 | 99 | phases |  | filter qty > 99: about 1% of 1M rows kept (all 7 columns compacted) |
| filter_sel50_1m | filter | filter | `sales_1000000.csv` | - | 1,000,000 | 1 | 50 | phases |  | filter qty > 50: about 50% of 1M rows kept (all 7 columns compacted) |
| filter_sel100_1m | filter | filter | `sales_1000000.csv` | - | 1,000,000 | 1 | - | phases |  | filter qty > 0: about 100% of 1M rows kept (all 7 columns compacted) |
| stages_1m | stages | stages | `sales_1000000.csv` | `products.csv` | 1,000,000 | 1 | - | stages |  | each eager stage of q1..q6 timed alone, 1M rows |
| nunique_1m | nunique | nunique | `m2/nunique_1048576.csv` | - | 1,048,576 | 1 | - | phases |  | select n_unique(x) over 2^20 distinct shuffled U32 |
| str_group_100k | str | group | `hc/t_100000.csv` | - | 100,000 | 1 | - | phases | yes | group_by k: sum v, len (k all distinct), 100,000 rows |
| str_unique_100k | str | unique | `hc/t_100000.csv` | - | 100,000 | 1 | - | phases | yes | select k, unique(k) (k all distinct), 100,000 rows |
| str_join_100k | str | join | `hc/t_100000.csv` | `hc/dim_100000.csv` | 100,000 | 1 | - | phases | yes | inner join dim on k (90% match), 100,000 rows |
| str_group_300k | str | group | `hc/t_300000.csv` | - | 300,000 | 1 | - | phases |  | group_by k: sum v, len (k all distinct), 300,000 rows |
| str_unique_300k | str | unique | `hc/t_300000.csv` | - | 300,000 | 1 | - | phases |  | select k, unique(k) (k all distinct), 300,000 rows |
| str_join_300k | str | join | `hc/t_300000.csv` | `hc/dim_300000.csv` | 300,000 | 1 | - | phases |  | inner join dim on k (90% match), 300,000 rows |
| str_group_1m | str | group | `hc/t_1000000.csv` | - | 1,000,000 | 1 | - | phases |  | group_by k: sum v, len (k all distinct), 1,000,000 rows |
| str_unique_1m | str | unique | `hc/t_1000000.csv` | - | 1,000,000 | 1 | - | phases |  | select k, unique(k) (k all distinct), 1,000,000 rows |
| str_join_1m | str | join | `hc/t_1000000.csv` | `hc/dim_1000000.csv` | 1,000,000 | 1 | - | phases |  | inner join dim on k (90% match), 1,000,000 rows |
| lp_group_100k | lp | group | `m2/lp_t_100000.csv` | - | 100,000 | 1 | - | phases |  | group_by k over 45-char keys sharing a 39-char prefix, 100,000 rows |
| lp_unique_100k | lp | unique | `m2/lp_t_100000.csv` | - | 100,000 | 1 | - | phases |  | select k, unique(k) over 45-char keys sharing a 39-char prefix, 100,000 rows |
| lp_join_100k | lp | join | `m2/lp_t_100000.csv` | `m2/lp_dim_100000.csv` | 100,000 | 1 | - | phases | yes | inner join dim on k over 45-char keys sharing a 39-char prefix, 100,000 rows |
| lp_group_300k | lp | group | `m2/lp_t_300000.csv` | - | 300,000 | 1 | - | phases |  | group_by k over 45-char keys sharing a 39-char prefix, 300,000 rows |
| lp_unique_300k | lp | unique | `m2/lp_t_300000.csv` | - | 300,000 | 1 | - | phases |  | select k, unique(k) over 45-char keys sharing a 39-char prefix, 300,000 rows |
| lp_join_300k | lp | join | `m2/lp_t_300000.csv` | `m2/lp_dim_300000.csv` | 300,000 | 1 | - | phases |  | inner join dim on k over 45-char keys sharing a 39-char prefix, 300,000 rows |
| q1_100k | q100k | q1 | `sales_100000.csv` | `products.csv` | 100,000 | 1 | - | phases | yes | filter ok & qty>50, select id,region,price (100k rows) |
| q2_100k | q100k | q2 | `sales_100000.csv` | `products.csv` | 100,000 | 8 | - | phases |  | with_columns revenue = qty*price*(1-fill_null(discount,0)) (100k rows) |
| q3_100k | q100k | q3 | `sales_100000.csv` | `products.csv` | 100,000 | 1 | - | phases | yes | q2, group_by region (sum revenue, mean price, count, max qty), sort region (100k rows) |
| q4_100k | q100k | q4 | `sales_100000.csv` | `products.csv` | 100,000 | 1 | - | phases | yes | sort region asc, price desc, id asc; head 10 (100k rows) |
| q5_100k | q100k | q5 | `sales_100000.csv` | `products.csv` | 100,000 | 1 | - | phases | yes | inner join products, group_by category sum qty, sort (100k rows) |
| q6_100k | q100k | q6 | `sales_100000.csv` | `products.csv` | 100,000 | 1 | - | phases | yes | describe of id, qty, price, discount (100k rows) |
| ctl_q1_1k | ctl | q1 | `sales_1000.csv` | `products.csv` | 1,000 | 500 | - | phases | yes | filter ok & qty>50, select id,region,price (1k rows control, batched) |
| ctl_q2_1k | ctl | q2 | `sales_1000.csv` | `products.csv` | 1,000 | 500 | - | phases | yes | with_columns revenue = qty*price*(1-fill_null(discount,0)) (1k rows control, batched) |
| ctl_q3_1k | ctl | q3 | `sales_1000.csv` | `products.csv` | 1,000 | 40 | - | phases | yes | q2, group_by region (sum revenue, mean price, count, max qty), sort region (1k rows control, batched) |
| ctl_q4_1k | ctl | q4 | `sales_1000.csv` | `products.csv` | 1,000 | 40 | - | phases | yes | sort region asc, price desc, id asc; head 10 (1k rows control, batched) |
| ctl_q5_1k | ctl | q5 | `sales_1000.csv` | `products.csv` | 1,000 | 40 | - | phases | yes | inner join products, group_by category sum qty, sort (1k rows control, batched) |
| ctl_q6_1k | ctl | q6 | `sales_1000.csv` | `products.csv` | 1,000 | 40 | - | phases | yes | describe of id, qty, price, discount (1k rows control, batched) |
| stages_100k | stages | stages | `sales_100000.csv` | `products.csv` | 100,000 | 1 | - | stages | yes | each eager stage of q1..q6 timed alone, 100k rows |

`phases` and `e2e` are the driver modes below; `stages` is the per-stage breakdown. `e2ecsv` (end to end
including a `write_csv` with floats at 4 decimals; validated by the sha256 of the file) is frozen for the
workloads with small or fixed-precision output (q1-q6) and is opt-in in `run` (`--modes e2ecsv`).
The 1k controls run `batch` inputs per timed window (each input parsed on its own, the batch rule of
`scripts/bench.sh`: q1, q2 500; q3-q6 40; 100k: q2 8) and report window/batch: IO.now has 1 ms resolution.
All 1M-row cells run one input per process (batching would inflate RSS).

### Input generation and hashes

```sh
uv run --project bench python bench/m2/gen.py            # generate what is missing, then check sha256
uv run --project bench python bench/m2/gen.py --check    # only check
```

| source | what |
|---|---|
| `bench/gen.py` (seed 42) | `sales_{1000,100000,1000000}.csv`, `products.csv` (q1-q6, parse, filter) |
| `bench/hc.py gen N` | `hc/t_N.csv`, `hc/dim_N.csv` for N in 100000, 300000, 1000000: key = 8..14 random lowercase letters + base-36 row id, every key distinct, so the key-length distribution (12..18 chars) is the same at every size from 46,656 rows up; dim = 90% of t's keys shuffled + N/10 absent keys |
| `gen.py` | `m2/nunique_1048576.csv`: `x = perm(2^20) * 4093 + 7`, 2^20 distinct shuffled U32 below 2^32; `m2/lp_{t,dim}_{100000,300000}.csv`: keys `customer_segment_internal_account_code_` (39 chars) + a 6-digit id, fixed length 45, every key distinct, the dim as for hc |

| file (under bench/data/) | bytes | sha256 |
|---|---:|---|
| `hc/dim_100000.csv` | 2,134,336 | `93bf9aaf9ace71702bd49cd818ca3c9144569d98a158771999025c726531418e` |
| `hc/dim_1000000.csv` | 21,794,460 | `13a888454a714a9d03a79896aed407cf6a44420d8164d50c060342fd4838279e` |
| `hc/dim_300000.csv` | 6,492,090 | `661f7a288307b6b3deef1d09a07f1e2856da07b403fdb4d506e746c5bfc842b7` |
| `hc/t_100000.csv` | 2,550,875 | `aeac994f872f726bca49754daf5226477ae644a8d36a4fd5a5bfbd4718f97ed3` |
| `hc/t_1000000.csv` | 25,938,843 | `5b6345645c84c1af941edbef52a8abce4afa4d3a84fb28d0d5f1f6e68a269b8b` |
| `hc/t_300000.csv` | 7,748,616 | `5a4242568cd1a1788d8698baaf73c072508b44b17c1142e9669d8f22fe22aebf` |
| `m2/lp_dim_100000.csv` | 5,188,897 | `1aadcffb8dbf7ce852fa58c2a5a8797b92ac7254c539f0b6b41a3316575f6c1c` |
| `m2/lp_dim_300000.csv` | 15,566,683 | `b4c869cd8affe849ebc98b25c6be4f2fb01098a838365b8953faf99d8bc150ff` |
| `m2/lp_t_100000.csv` | 5,598,820 | `bbbd060ad15e055db76e6db434b7f4e06554e2e9eb5555348d667b67e6c4077c` |
| `m2/lp_t_300000.csv` | 16,796,724 | `9bbee7fa45db21f00e833475c80486353eaf859bcaa1d077180bf79fdc9865e2` |
| `m2/nunique_1048576.csv` | 11,262,866 | `498cf388b8957cd8d72246760590cd46f13f53b7be7776945479aaec9895c7df` |
| `products.csv` | 1,290 | `b0222ca6acf5a069171574286e9a327373a5c58ea5808dd68e0fb3fe603be54c` |
| `sales_1000.csv` | 38,386 | `bad9d048a89a7bf729acff95e3f4ebde9e8ddfc74e2b0f9ab0d24c7f8d87cae8` |
| `sales_100000.csv` | 4,019,437 | `1446e10c64f12d765409a026e75cf96ce34e7dcfca49a6f21c5fbf3a328bc04e` |
| `sales_1000000.csv` | 41,193,278 | `85cc7d7c5b5a9ae832e45e54ebea83e0d6d410b01c5ffd169d223e3fe8ab74c8` |

The runner checks every file against `inputs.json` before it runs (a mismatch aborts), and records the
sha256 of each workload's inputs in every record.

## What the driver times (timing boundaries)

One process = one mode = one workload, ONE measurement (parsing again in one process gets slower, so no
repeats inside a process; no warmup: every number is a cold, fresh-process number). `IO.now` has 1 ms
resolution.

`phases` (G6; the input-preservation mode of `bench/main.bend`):

| field | boundary |
|---|---|
| `read_ms` | `DF.read_csv` of the primary (and aux) file, as returned |
| `walk_ms` | the first full walk of every buffer (the read's last work is still pending when it returns); `parse_ms = read_ms + walk_ms` |
| `prep_ms` | the input-preservation clone (`DF.clone` of every input: the run is over the clone, the originals stay referenced until after the clock, like Polars whose inputs survive `collect`) |
| `compute_ms` | `DF.collect` of the plan (optimisation + execution) over the cloned Source frames; q6: the eager `describe`; `parse`: nothing; the result stays alive |
| `check_ms` | the output/validation phase: the content hash of the first result (consuming it, so freeing the result and the kept inputs is billed here). Parallel work still pending when `compute` returned is billed here too: compute+check is the safe figure |

`e2e` (G6 end to end): ONE timed region = read + compute + check (hash), with `consume` semantics: no
walk, no preservation clone, the inputs are freed inside the region. `e2e_ms`. `e2ecsv`: read + compute +
`write_csv` in one region; the hash and the file's sha256 are checked after the clock.

`stages` (G2 feasibility): one parse, then the eager stages of q1-q6 each timed ALONE over fresh clones (or
the previous stage's output): `filter_q1`, `select_q1`, `withcols_q2`, `groupby_q3`, `sort_q3`, `sort_q4`,
`head_q4`, `join_q5`, `groupby_q5`, `sort_q5`, `describe_q6`. These are eager verbs without the optimizer's
pushdown or fusion, so they show where the time goes, not an exact decomposition of the lazy q-times.
Clones and the per-stage hash are outside each stage's clock.

Instrument overhead (G6) is separate by construction: `IO.now` pairs (microseconds), the clone
(`prep_ms`) and the hash (`check_ms`) are reported fields, never inside `compute_ms`. Allocation and copy
bytes: the native runtime offers no allocation counters (only `--threads` and `--gpu`), so W0 records
peak RSS, macOS `peak memory footprint`, `page reclaims` (pages touched: a proxy for allocated bytes, 16 KiB
each), `instructions retired` and `cycles elapsed` per process from `/usr/bin/time -l`; exact per-workload
copy-byte counters (W1.h) need counters in `src/` (not part of W0).

## Result validation

Every result is validated AFTER the clock against `expected.json`, which `run.py freeze` took from the
BASELINE binary at 1 and 12 threads (they must agree) and in every mode the workload is scheduled in:

- `chk`: a content hash of the result frame (`Hc.frame` in the driver): order-sensitive FNV-1a over
  the column names, a dtype tag, the length, the validity (an all-ones mask hashes like `AllValid`), the
  payload with null slots reset (garbage under nulls does not count), F32 as bits with every NaN canonical
  (the documented NaN-payload relaxation), strings by text (a Dictionary column hashes like the Raw one:
  `driver selfcheck <file>` shows Raw, Dictionary, Auto and a clone all give the same value). It is a
  function of the LOGICAL content, so a candidate that keeps v0.1's values, validity, names, row order and
  F32 bits passes. It consumes the frame (a streaming fold: no text is built, so it does not disturb RSS).
- `dump`: for results of at most 2,000 rows also the hash of `DF.dump_frame` (the typed oracle text, no
  `src/` internals): an independent second witness.
- `rows`; `csv_sha256` for `e2ecsv`; per-stage `rows`/`chk` for `stages`.

A record with a wrong result has `valid: false` and the reason; the summary lists those and excludes them
from medians. A workload without an expected entry has `valid: null`. Row order of `group_by` is
unspecified in DESIGN.md (first appearance in v0.1); G1 requires the v0.1 order, and the hash is
order-sensitive: if a later engine changes the order of an unordered result on purpose, that is a decision
to take (re-freeze), not something to absorb silently.

## Record format (`results/<label>.jsonl`)

The first line is a `meta` record (machine, bend version, toolchain, commit, builds, load, top CPU
consumers, `pmset -g therm`, the arguments, `provisional`). Then one `proc` record per process: `command`,
`env`, `commit` {head, dirty, dirty_src, src_hash, driver_hash}, `build` (the binary's BUILD.json),
`bend_version`, `binary`, `engine`, `workload`, `mode`, `threads`, `rep`, `batch`, `rows_in`,
`input_sha256`, `driver` (the process's own JSON line: phase timings, `chk`, `dump`, `rows`),
`rss_bytes` + `rss_method` (`usr_bin_time_l`; `wait4_rusage` if `/usr/bin/time -l` is refused; the micro
runner and every record state the method), `usr_s`, `sys_s`, `real_s`, `instructions`, `cycles`,
`peak_footprint`, `page_reclaims`, `load_before`/`load_after` (`os.getloadavg`: 1, 5, 15 min),
`valid` + `validation`, `rc`, `error`, `wall_s`, `ts`.

## Measurement protocol and acceptance rules (predeclared)

- Cells are (binary, workload, mode, threads); every cell is run `--procs` (default 5) times, each in a
  FRESH process. The runs are INTERLEAVED: within a workload and mode, repetition by repetition, the
  (binary, thread count) combinations are visited round-robin and the starting point rotates every
  repetition; baseline and candidate are never blocked, 1/4/12 threads are never blocked.
- Thread scaling compares the SAME workload at 1, 4 and 12 threads for the same binary (serial work
  included): `S12 = median(1 thread) / median(12 threads)`.
- Gate samples are accepted only from a quiet PRE-RUN machine: 1-minute load < 2 and no known competing
  jobs at the start (`--require-quiet 2`; `make m2-bench` does this and aborts otherwise; `--wait S` waits).
  A 12-thread run itself raises the load; the in-run load is recorded but never used to reject a sample.
  Retry rule: a gate run that started quiet is used as is; if the machine was not quiet at the start the
  whole run is repeated, never individual samples. Every sample is kept, medians AND min/max AND raw values
  are reported. A run on a shared machine is `--provisional` (recorded in the meta record and the file
  name) and no gate is evaluated from it.
- Invalid results (wrong hash) are reported and excluded from medians; a failed process (rc != 0) too.
- `summary --max-load X` filters by the load before each process: a diagnostic after the fact, not an
  acceptance rule.
- The toolchain is pinned (`TOOLCHAIN`): one bend binary builds both drivers; the record stores
  `bend version`; the binaries' sha256 is in `BUILD.json`.

## Reading the summary

`run.py summary <files> [--raw] [--max-load X]` prints: timings per cell (median [min..max] n) with the
ratio candidate/baseline; the phase table; thread scaling with the Amdahl serial fraction
`s = (1/S12 - 1/12) / (1 - 1/12)` (and `1/s`, the ceiling for infinite parallelism at that fraction);
the stage table (share of the 1-thread sum and S12 per stage); load statistics; with `--raw` every sample.

## Provisional baseline (W0 harness validation; NOT a gate run)

`results/provisional-baseline.jsonl` (1,440 processes, every one validated against `expected.json`: 0 invalid;
`results/provisional-baseline.md` is its full `summary --raw`). Taken on a SHARED machine (other agents
building and benchmarking; 1-minute load before each process: min 9, median 19, max 264, the meta record
lists the top consumers), `--provisional`: **no gate is evaluated from these numbers**; absolute times are
inflated by contention and by the 12-thread runs competing with it. What it is good for:

1. It validates the harness: baseline (3612482) and candidate (this checkout, `src/` and `frame.bend`
   byte-identical to the baseline, the binaries are even bit-identical) were interleaved, so the ratio must
   be ~1.0. ratio candidate/baseline over 84 cells with baseline median >= 20 ms: min 0.86, median 1.000, max 1.14. Cells below ~20 ms are dominated by the 1 ms clock and by load spikes.
2. It is the first look at the baseline's shape (below): who forks today, which phase dominates, memory.

Medians of 5 fresh interleaved processes per cell (ms; `S4`/`S12` = median(1 thread)/median(N threads) of the
baseline; `cand/base` = candidate over baseline median; RSS in MB from `/usr/bin/time -l`, 1 thread; the
batched 1k controls are ms per input). Raw samples and min/max are in the `.md`/`.jsonl`.

| workload | metric | base 1t | base 4t | base 12t | S4 | S12 | cand/base 1t | 4t | 12t | RSS MB (phases, 1t) | RSS MB (e2e, 1t) |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| q1_1m | compute_ms | 13.0 | 12.0 | 13.0 | 1.08 | 1.00 | 0.85 | 1.00 | 1.00 | 1298 | - |
| q1_1m | e2e_ms | 5,464 | 3,221 | 2,510 | 1.70 | 2.18 | 1.02 | 0.99 | 1.01 | - | 1294 |
| q2_1m | compute_ms | 9.00 | 8.00 | 9.00 | 1.12 | 1.00 | 1.00 | 1.12 | 1.00 | 1290 | - |
| q2_1m | e2e_ms | 5,715 | 3,124 | 2,782 | 1.83 | 2.05 | 0.99 | 1.06 | 1.01 | - | 1272 |
| q3_1m | compute_ms | 24.0 | 24.0 | 23.0 | 1.00 | 1.04 | 1.00 | 1.00 | 1.00 | 1310 | - |
| q3_1m | e2e_ms | 5,472 | 3,052 | 2,868 | 1.79 | 1.91 | 1.01 | 1.02 | 0.93 | - | 1273 |
| q4_1m | compute_ms | 48.0 | 44.0 | 46.0 | 1.09 | 1.04 | 0.94 | 1.07 | 1.02 | 1290 | - |
| q4_1m | e2e_ms | 5,600 | 3,420 | 2,552 | 1.64 | 2.19 | 1.03 | 0.88 | 1.07 | - | 1284 |
| q5_1m | compute_ms | 21.0 | 20.0 | 22.0 | 1.05 | 0.95 | 1.00 | 1.00 | 0.91 | 1298 | - |
| q5_1m | e2e_ms | 5,736 | 3,128 | 2,788 | 1.83 | 2.06 | 0.96 | 1.00 | 0.99 | - | 1273 |
| q6_1m | compute_ms | 111 | 109 | 111 | 1.02 | 1.00 | 1.02 | 1.01 | 1.00 | 1281 | - |
| q6_1m | e2e_ms | 6,228 | 4,197 | 3,485 | 1.48 | 1.79 | 1.09 | 0.93 | 0.94 | - | 1272 |
| parse_1m | parse_ms | 5,511 | 3,046 | 2,672 | 1.81 | 2.06 | 1.01 | 1.14 | 1.05 | 1314 | - |
| parse_1m | e2e_ms | 5,391 | 3,030 | 2,619 | 1.78 | 2.06 | 1.03 | 0.97 | 0.99 | - | 1314 |
| filter_sel0_1m | compute_ms | 9.00 | 8.00 | 8.00 | 1.12 | 1.12 | 0.89 | 1.00 | 1.00 | 1286 | - |
| filter_sel1_1m | compute_ms | 8.00 | 8.00 | 8.00 | 1.00 | 1.00 | 1.12 | 1.25 | 1.12 | 1286 | - |
| filter_sel50_1m | compute_ms | 11.0 | 12.0 | 11.0 | 0.92 | 1.00 | 1.09 | 1.08 | 1.09 | 1302 | - |
| filter_sel100_1m | compute_ms | 11.0 | 13.0 | 12.0 | 0.85 | 0.92 | 1.27 | 1.00 | 1.00 | 1327 | - |
| nunique_1m | compute_ms | 4,448 | 1,831 | 1,608 | 2.43 | 2.77 | 0.94 | 0.86 | 1.10 | 394 | - |
| str_group_100k | compute_ms | 1,062 | 645 | 690 | 1.65 | 1.54 | 0.96 | 1.07 | 0.94 | 93 | - |
| str_unique_100k | compute_ms | 990 | 711 | 648 | 1.39 | 1.53 | 1.00 | 0.97 | 0.96 | 90 | - |
| str_join_100k | compute_ms | 623 | 577 | 544 | 1.08 | 1.15 | 1.06 | 1.01 | 1.05 | 129 | - |
| str_group_300k | compute_ms | 3,723 | 2,463 | 2,460 | 1.51 | 1.51 | 0.99 | 1.02 | 0.96 | 274 | - |
| str_unique_300k | compute_ms | 3,167 | 2,168 | 2,093 | 1.46 | 1.51 | 1.03 | 0.97 | 1.01 | 274 | - |
| str_join_300k | compute_ms | 1,733 | 1,569 | 1,563 | 1.10 | 1.11 | 0.98 | 1.02 | 0.99 | 409 | - |
| str_group_1m | compute_ms | 16,465 | 9,889 | 9,345 | 1.66 | 1.76 | 1.03 | 1.00 | 1.01 | 859 | - |
| str_unique_1m | compute_ms | 16,900 | 10,154 | 9,523 | 1.66 | 1.77 | 0.99 | 1.00 | 1.04 | 830 | - |
| str_join_1m | compute_ms | 6,958 | 6,368 | 6,166 | 1.09 | 1.13 | 0.95 | 0.93 | 1.01 | 1206 | - |
| lp_group_100k | compute_ms | 6,372 | 3,366 | 3,250 | 1.89 | 1.96 | 1.02 | 1.01 | 0.99 | 274 | - |
| lp_unique_100k | compute_ms | 6,479 | 3,376 | 3,302 | 1.92 | 1.96 | 1.00 | 1.01 | 0.98 | 270 | - |
| lp_join_100k | compute_ms | 902 | 796 | 790 | 1.13 | 1.14 | 0.98 | 1.01 | 1.00 | 352 | - |
| lp_group_300k | compute_ms | 20,254 | 11,286 | 10,925 | 1.79 | 1.85 | 0.99 | 0.97 | 1.01 | 802 | - |
| lp_unique_300k | compute_ms | 19,690 | 11,044 | 11,077 | 1.78 | 1.78 | 1.00 | 1.00 | 1.00 | 796 | - |
| lp_join_300k | compute_ms | 2,724 | 2,440 | 2,450 | 1.12 | 1.11 | 0.97 | 1.03 | 1.02 | 1054 | - |
| q1_100k | compute_ms | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | 137 | - |
| q2_100k | compute_ms | 1.12 | 0.875 | 0.750 | 1.29 | 1.50 | 1.00 | 1.00 | 1.00 | 198 | - |
| q3_100k | compute_ms | 2.00 | 3.00 | 3.00 | 0.67 | 0.67 | 1.50 | 1.00 | 1.00 | 137 | - |
| q4_100k | compute_ms | 4.00 | 4.00 | 4.00 | 1.00 | 1.00 | 1.00 | 1.00 | 1.25 | 136 | - |
| q5_100k | compute_ms | 2.00 | 3.00 | 2.00 | 0.67 | 1.00 | 1.50 | 0.67 | 1.00 | 137 | - |
| q6_100k | compute_ms | 11.0 | 10.0 | 11.0 | 1.10 | 1.00 | 0.91 | 1.00 | 1.00 | 135 | - |
| ctl_q1_1k | compute_ms | 0.054 | 0.052 | 0.058 | 1.04 | 0.93 | 1.04 | 0.92 | 0.93 | 63 | - |
| ctl_q2_1k | compute_ms | 0.052 | 0.052 | 0.052 | 1.00 | 1.00 | 0.92 | 1.00 | 1.00 | 63 | - |
| ctl_q3_1k | compute_ms | 0.175 | 0.175 | 0.250 | 1.00 | 0.70 | 1.00 | 1.14 | 0.80 | 9 | - |
| ctl_q4_1k | compute_ms | 0.325 | 0.325 | 0.325 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | 9 | - |
| ctl_q5_1k | compute_ms | 0.200 | 0.225 | 0.275 | 0.89 | 0.73 | 1.00 | 1.11 | 0.91 | 9 | - |
| ctl_q6_1k | compute_ms | 0.575 | 0.550 | 0.575 | 1.05 | 1.00 | 1.04 | 1.05 | 1.00 | 9 | - |

### Baseline serial fractions (G2 feasibility; baseline medians, 1 / 4 / 12 threads)

Amdahl serial fraction `s = (1/S12 - 1/12) / (1 - 1/12)`; `1/s` is the ceiling at that fraction. G2 needs
S12 >= 3 on q1-q6 compute (s <= 1/3) and >= 4 on parse (s <= 0.18).

| workload | T1 | T4 | T12 | S12 | s | confirmed |
|---|---:|---:|---:|---:|---:|---|
| q1 compute | 13 | 12 | 13 | 1.00 | 1.00 | nothing forks |
| q2 compute | 9 | 8 | 9 | 1.00 | 1.00 | nothing forks |
| q3 compute | 24 | 24 | 23 | 1.04 | 0.95 | nothing forks |
| q4 compute | 48 | 44 | 46 | 1.04 | 0.95 | nothing forks |
| q5 compute | 21 | 20 | 22 | 0.95 | 1.05 | nothing forks |
| q6 compute | 111 | 109 | 111 | 1.00 | 1.00 | nothing forks |
| parse 1M (read + walk) | 5,511 | 3,046 | 2,672 | 2.06 | 0.44 | forks per column only (1.8x at 4 threads, 2.1x at 12) |

So the compute of q1-q6 is exactly as the plan says (no fork; 12 threads = 1 thread within noise). Parse is
NOT serial today: `Csv.cols` forks the column parsers, which gives 2.1x and saturates at 4 threads
(7 columns, uneven cost); G2's 4x needs s <= 0.18, i.e. piece-level parsing, not more column forks. Other
paths that already fork (so "nothing forks" is true for q1-q6 only): n_unique over distinct U32 (S12 2.8),
distinct-string group_by / unique (S12 1.5-1.9; presumably the coder's `pcodes`/`pmerge`, not investigated), the joins (S12 1.1).

### Where the time goes (per-stage table, `stages_1m`, baseline, ms; S12 ~ 1.0 for every stage)

The eager stages timed alone over one parse (`stages` mode; they are not the optimizer's fused plan, but
they sum to within ~20% of the lazy q-times):

| stage | 1t | 4t | 12t | share of the 1t sum |
|---|---:|---:|---:|---:|
| filter_q1 (ok and qty > 50) | 13 | 11 | 11 | 6% |
| select_q1 | 0 | 0 | 0 | 0% |
| withcols_q2 (revenue) | 7 | 6 | 7 | 3% |
| groupby_q3 (8 groups, F32 sum/mean, U32 max, len) | 15 | 14 | 14 | 7% |
| sort_q3 (8 rows) | 1 | 0 | 0 | 0% |
| sort_q4 (3 keys, 1M rows) | 46 | 46 | 43 | 22% |
| head_q4 | 0 | 0 | 0 | 0% |
| join_q5 (64-row dim) | 9 | 8 | 8 | 4% |
| groupby_q5 | 8 | 8 | 8 | 4% |
| sort_q5 | 0 | 0 | 0 | 0% |
| describe_q6 (4 columns) | 110 | 105 | 112 | 53% |
| sum of stages | 209 | 198 | 203 | |
| parse (read + walk) | 5,665 | 3,007 | 2,571 | (27x the sum of all stages) |

By query: q1 = the filter's compaction; q2 = one fused-able map; q3 = withcols + one group_by (F32
sums are sequential by contract D4: only the 8 independent groups / aggregates can fork); q4 = ONE sort
(radix scatter: the stage G2 text says may scale less); q5 = a tiny-dim join + group_by; q6 = describe, 4
independent columns (each with serial F32 work and the quantile sorts), so a column fork bounds it at
4x before the serial parts. These are readings of the table, not measurements of the future design.

### G6 phases at the baseline (1 thread, medians, ms)

| workload | parse | prep (clone) | compute | check (hash) | e2e (one region) |
|---|---:|---:|---:|---:|---:|
| q1 | 5,615 | 2 | 13 | 1 | 5,464 |
| q2 | 5,425 | 2 | 9 | 14 | 5,715 |
| q3 | 5,836 | 2 | 24 | 0 | 5,472 |
| q4 | 5,990 | 3 | 48 | 3 | 5,600 |
| q5 | 5,685 | 2 | 21 | 1 | 5,736 |
| q6 | 6,960 | 3 | 111 | 0 | 6,228 |

Parse is over 99% of an end-to-end q1-q6 run at 1M rows; the input-preservation clone costs 2-3 ms and a
fraction of the RSS: peak RSS with the clone (phases, 1,281-1,310 MB) and without it (e2e, 1,272-1,294 MB)
differ by ~30 MB, so the 1.3 GB is the READER's high-water mark (parse alone: 1,314 MB), not the engine's.
Walk is 5 ms (the read's pending work is small at 1M rows).

### Baseline against the G3/G4 numbers (baseline medians; to be re-taken on a quiet machine)

| gate item | target | provisional baseline | gap |
|---|---|---:|---:|
| q1 compute, 1 thread | <= 3 ms | 13 ms | 4.3x |
| q2 | <= 3 ms | 9 ms | 3x |
| q3 | <= 12 ms | 24 ms | 2x |
| q4 | <= 20 ms | 48 ms | 2.4x |
| q5 | no > 10% regression | 21 ms | - |
| q6 | <= 60 ms | 111 ms | 1.9x |
| n_unique over 2^20 distinct U32, CSV-parsed, shuffled | <= 30 ms | 4,448 ms (1.4 s on the sorted file) | 148x |
| distinct-string group_by / unique / join at 1M | <= 2 s each | 16.5 s / 16.9 s / 7.0 s | 8.2x / 8.4x / 3.5x |
| 41 MB parse, 1 thread / 12 threads | <= 2 s / <= 0.6 s | 5.5 s / 2.7 s | 2.8x / 4.5x |
| peak RSS, 1M-row q1-q6 | <= 600 MB | 1,270-1,310 MB | 2.2x |
| 1k controls | within 10% | q1 0.054, q2 0.052, q3 0.175, q4 0.325, q5 0.2, q6 0.575 ms/input | baseline reference |

### Surprises and caveats

- n_unique: the review's 202 ms (and the G3 premise "~12x off") is for a 2^20 already-sorted iota column built in
  memory (`bench/micro` `ops nunique` still gives ~216 ms here). Through the facade on a CSV-parsed column the
  same distinct count takes 1.4 s when the file is sorted and 4.4 s when it is shuffled (this workload): the gap
  to the 30 ms target is ~150x, not 12x. Cause not investigated (W1.b); the workload is the frozen one.
- Distinct-string workloads: the RSS of the 1M group/unique is 830-860 MB (join 1.2 GB), above G4's 600 MB too.
- q2 at 1M: `check_ms` 14 ms is the content hash of 1M x 8 cells (it is not pending compute: q2's compute
  is 9 ms in both modes and e2e is not larger by that amount); the hash of a parsed 1M frame also costs 14 ms.
- The 1 ms clock: q1_100k/q3_100k/q5_100k at 1-3 ms show ratios 0.67-1.5 that are pure resolution noise.
- Load: median 19, spikes of 100-260 (12-thread runs by other agents). The `usr_s`/`sys_s`, `instructions` and
  `cycles` fields recorded for every process are the load-insensitive cross-check for the orchestrator.
- Not covered by W0 (needs work in `src/` or a quiet machine): exact allocation/copy bytes (G6 `W1.h`),
  the gate evaluation of G2-G4, the review's disposable spikes (aligned chunk zip/filter, probe ownership,
  cold-parser conversion, lexical ranks, quote-boundary scanner): those belong to the design agents; the
  runner, the frozen workloads and the validation are what they use.

### Proposed thresholds to freeze (orchestrator to confirm on a quiet machine)

G2 (S12 on the compute of the same candidate, includes its serial work): q1 >= 3x, q2 >= 3x (measure with
batching: at the G3 target of 3 ms single-threaded, 3x is 1 ms, the clock resolution), q3 >= 3x only with a
group-level fork (8 groups; F32 sums stay sequential per group) else 2x, q4 >= 2x (one sort: radix scatter /
bandwidth-bound; G2 text allows less), q5 >= 2x (tiny-dim join + 8-group aggregate), q6 >= 2.5x (4 columns:
a column fork is bounded at 4x before the serial parts), parse >= 4x (s <= 0.18). Distinct-string and join
cells: report only (S12 today 1.1-1.9). These are proposals from the stage table; none is evaluated here.

