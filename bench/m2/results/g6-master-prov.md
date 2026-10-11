# G6 instrumentation: copy and allocation accounting (master-prov)

**Counts, never timings.** Instrumented binaries (`bench/m2/instrument.py`: the emitted C patched with relaxed atomic counters, a `BF_G6` line per `IO.now`) at 1 thread; every number below is exact and deterministic (see the determinism line). Their wall times, RSS and driver `*_ms` fields are not valid and are not used anywhere. Counts do not depend on machine load. Reproduce with `make m2-g6 LABEL=x` (it builds the instrumented binaries first).

- run `master-prov`: 2026-10-11T15:13:15+00:00, candidate commit `76ca92a795` dirty=False src `7efb8fd008`, bend bend 2.0.36
- baseline: commit `36124822c9`, src `0bf1c69670`, instrument.py `4bd2d5a072`, binary `ebda1bfdbc`
- candidate: commit `76ca92a795`, src `7efb8fd008`, instrument.py `4bd2d5a072`, binary `0aa9893520`
- 128 instrumented processes, 64 cells, 2 repetition(s) per cell; counters identical across repetitions in every phase of every cell (read, walk, prep, compute, check); the exit tail (JSON print + process exit, after the last snapshot) differs by at most 6 allocations / 72 bytes in 7 cells, so whole-process totals are exact to that
- every result validated against `expected.json`: all valid; configs: `baseline` = the pinned 3612482 binary (it ignores `BF_ENGINE`: its three engine combinations are one run), `reference` / `v02` / `v02,chunked` = the candidate with `BF_ENGINE` unset / `v02` / `v02,chunked`

Counters (bytes are exact, MB = 10^6 bytes): **copy** = `blk_copy` (`Array.clone`, `Column.clone`, `DF.clone`: a full O(n) copy of one array block); **fork copy** = `blk_node` + `blk_half` (an array rebuilt out of, or matched into, its halves: each copies the data it moves); **alloc** = every heap allocation (array blocks AND constructor / task nodes), `allocs` their number; **live** = allocated minus freed at the end of the phase (the retained heap); **minflt** = `getrusage` soft page faults in the phase (a 16 KiB page each on this machine). Phases are the driver's `IO.now` windows: read, walk (first walk of every buffer), prep (the input-preservation clone), compute (`DF.collect` / describe), check (the content hash, which consumes the result and frees the kept inputs).

## 1. Compute phase

The engine's own work (optimizer + executor, or the eager describe for q6), over the cloned inputs. `copy MB` is what the plan copies that a move or a borrow could in principle avoid; `alloc MB` is all fresh storage, including the outputs.

| workload | config | copy MB | fork copy MB | alloc MB | allocs | minflt | live after MB | result rows |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| q1_1m | baseline 3612482 | 8.39 | 0 | 29.41 | 2,977 | 1,556 | 36.74 | 249,356 |
| q1_1m | candidate reference | 0 | 0 | 7.39 | 3,070 | 483 | 36.74 | 249,356 |
| q1_1m | candidate v02 reader | 0 | 0 | 7.39 | 3,070 | 492 | 36.74 | 249,356 |
| q1_1m | candidate v02,chunked | 0 | 0 | 33.32 | 56,085 | 1,809 | 36.74 | 249,356 |
| q2_1m | baseline 3612482 | 16.78 | 0 | 41.99 | 3,224 | 1,046 | 71.35 | 1,000,000 |
| q2_1m | candidate reference | 0 | 0 | 12.64 | 3,627 | 818 | 71.35 | 1,000,000 |
| q2_1m | candidate v02 reader | 0 | 0 | 12.64 | 3,627 | 818 | 71.35 | 1,000,000 |
| q2_1m | candidate v02,chunked | 0 | 0 | 84.41 | 93,860 | 2,559 | 71.35 | 1,000,000 |
| q3_1m | baseline 3612482 | 37.75 | 0 | 96.87 | 8,905 | 1,328 | 33.59 | 8 |
| q3_1m | candidate reference | 4.19 | 0 | 32.10 | 8,330 | 1,117 | 33.59 | 8 |
| q3_1m | candidate v02 reader | 4.19 | 0 | 32.10 | 8,330 | 1,119 | 33.59 | 8 |
| q3_1m | candidate v02,chunked | 4.19 | 0 | 82.93 | 100,508 | 2,347 | 33.59 | 8 |
| q4_1m | baseline 3612482 | 12.58 | 0 | 123.0 | 2,866 | 1,061 | 67.15 | 10 |
| q4_1m | candidate reference | 0 | 0 | 37.26 | 2,422 | 1,084 | 33.60 | 10 |
| q4_1m | candidate v02 reader | 0 | 0 | 37.26 | 2,422 | 1,090 | 33.60 | 10 |
| q4_1m | candidate v02,chunked | 0 | 0 | 37.26 | 2,491 | 1,088 | 33.60 | 10 |
| q5_1m | baseline 3612482 | 16.78 | 0.00 | 88.49 | 8,765 | 1,586 | 33.59 | 6 |
| q5_1m | candidate reference | 4.20 | 0 | 53.07 | 7,433 | 1,357 | 33.59 | 6 |
| q5_1m | candidate v02 reader | 4.20 | 0 | 53.07 | 7,433 | 1,360 | 33.59 | 6 |
| q5_1m | candidate v02,chunked | 4.20 | 0 | 53.09 | 8,412 | 1,362 | 33.59 | 6 |
| q6_1m | baseline 3612482 | 104.9 | 0 | 245.1 | 1,391 | 538 | 33.59 | 9 |
| q6_1m | candidate reference | 0 | 0 | 94.40 | 1,367 | 560 | 33.59 | 9 |
| q6_1m | candidate v02 reader | 0 | 0 | 94.40 | 1,367 | 565 | 33.59 | 9 |
| q6_1m | candidate v02,chunked | 0 | 0 | 94.40 | 1,367 | 565 | 33.59 | 9 |
| parse_1m | baseline 3612482 | 0 | 0 | 0.00 | 81 | 1 | 67.14 | 1,000,000 |
| parse_1m | candidate reference | 0 | 0 | 0.00 | 81 | 2 | 67.14 | 1,000,000 |
| parse_1m | candidate v02 reader | 0 | 0 | 0.00 | 81 | 2 | 67.14 | 1,000,000 |
| parse_1m | candidate v02,chunked | 0 | 0 | 0.00 | 81 | 2 | 67.14 | 1,000,000 |
| str_group_100k | baseline 3612482 | 1.57 | 7.86 | 1,592 | 90,499,992 | 473 | 39.05 | 100,000 |
| str_group_100k | candidate reference | 0 | 0 | 20.48 | 2,264 | 1,001 | 39.05 | 100,000 |
| str_group_100k | candidate v02 reader | 0 | 0 | 20.48 | 2,264 | 1,068 | 39.05 | 100,000 |
| str_group_100k | candidate v02,chunked | 0 | 0 | 20.49 | 3,020 | 1,070 | 39.05 | 100,000 |
| str_unique_100k | baseline 3612482 | 1.05 | 7.86 | 1,590 | 90,498,511 | 340 | 38.00 | 100,000 |
| str_unique_100k | candidate reference | 0 | 0 | 22.03 | 920 | 932 | 38.00 | 100,000 |
| str_unique_100k | candidate v02 reader | 0 | 0 | 22.03 | 920 | 1,000 | 38.00 | 100,000 |
| str_unique_100k | candidate v02,chunked | 0 | 0 | 22.04 | 1,060 | 1,001 | 38.00 | 100,000 |
| str_join_100k | baseline 3612482 | 1.05 | 2.10 | 57.51 | 2,792,754 | 1,231 | 75.83 | 90,000 |
| str_join_100k | candidate reference | 1.05 | 0 | 26.77 | 1,905 | 1,184 | 75.83 | 90,000 |
| str_join_100k | candidate v02 reader | 1.05 | 0 | 26.77 | 1,905 | 1,184 | 75.83 | 90,000 |
| str_join_100k | candidate v02,chunked | 1.05 | 0 | 26.77 | 1,974 | 1,183 | 75.83 | 90,000 |
| str_group_300k | baseline 3612482 | 6.29 | 31.46 | 5,085 | 291,026,833 | 1,576 | 123.6 | 300,000 |
| str_group_300k | candidate reference | 0 | 0 | 81.82 | 2,264 | 3,882 | 123.6 | 300,000 |
| str_group_300k | candidate v02 reader | 0 | 0 | 81.82 | 2,264 | 4,140 | 123.6 | 300,000 |
| str_group_300k | candidate v02,chunked | 0 | 0 | 81.83 | 3,020 | 4,142 | 123.6 | 300,000 |
| str_unique_300k | baseline 3612482 | 4.19 | 31.46 | 5,077 | 291,025,352 | 1,058 | 119.4 | 300,000 |
| str_unique_300k | candidate reference | 0 | 0 | 88.09 | 920 | 3,621 | 119.4 | 300,000 |
| str_unique_300k | candidate v02 reader | 0 | 0 | 88.09 | 920 | 3,880 | 119.4 | 300,000 |
| str_unique_300k | candidate v02,chunked | 0 | 0 | 88.10 | 1,060 | 3,881 | 119.4 | 300,000 |
| str_join_300k | baseline 3612482 | 4.19 | 8.39 | 198.2 | 8,552,694 | 4,519 | 238.2 | 270,000 |
| str_join_300k | candidate reference | 4.19 | 0 | 107.0 | 1,909 | 4,646 | 238.2 | 270,000 |
| str_join_300k | candidate v02 reader | 4.19 | 0 | 107.0 | 1,909 | 4,640 | 238.2 | 270,000 |
| str_join_300k | candidate v02,chunked | 4.19 | 0 | 107.0 | 1,978 | 4,639 | 238.2 | 270,000 |
| str_group_1m | baseline 3612482 | 12.58 | 62.91 | 22,802 | 1,325,635,237 | 12,282 | 392.3 | 1,000,000 |
| str_group_1m | candidate reference | 0 | 0 | 163.6 | 2,268 | 7,770 | 392.3 | 1,000,000 |
| str_group_1m | candidate v02 reader | 0 | 0 | 163.6 | 2,268 | 8,236 | 392.3 | 1,000,000 |
| str_group_1m | candidate v02,chunked | 0 | 0 | 163.6 | 3,024 | 8,235 | 392.3 | 1,000,000 |
| str_unique_1m | baseline 3612482 | 8.39 | 62.91 | 22,785 | 1,325,633,752 | 20,067 | 384.0 | 1,000,000 |
| str_unique_1m | candidate reference | 0 | 0 | 176.2 | 920 | 7,169 | 384.0 | 1,000,000 |
| str_unique_1m | candidate v02 reader | 0 | 0 | 176.2 | 920 | 7,720 | 384.0 | 1,000,000 |
| str_unique_1m | candidate v02,chunked | 0 | 0 | 176.2 | 1,060 | 7,718 | 384.0 | 1,000,000 |
| str_join_1m | baseline 3612482 | 8.39 | 16.78 | 538.5 | 28,812,932 | 11,375 | 766.9 | 900,000 |
| str_join_1m | candidate reference | 8.39 | 0 | 213.9 | 1,909 | 9,230 | 766.9 | 900,000 |
| str_join_1m | candidate v02 reader | 8.39 | 0 | 213.9 | 1,909 | 9,248 | 766.9 | 900,000 |
| str_join_1m | candidate v02,chunked | 8.39 | 0 | 213.9 | 1,978 | 9,246 | 766.9 | 900,000 |

## 2. Preparation and output phases

prep is the input-preservation clone (`DF.clone` of every input: the copy Polars does not make because its inputs are shared); check is the content hash (a streaming fold: it should copy nothing). Both are harness phases, outside `compute`.

| workload | config | prep copy MB | prep alloc MB | check alloc MB | check copy MB | check allocs |
|---|---|---:|---:|---:|---:|---:|
| q1_1m | baseline 3612482 | 33.57 | 33.57 | 1.05 | 0 | 12 |
| q1_1m | candidate reference | 33.57 | 33.57 | 1.05 | 0 | 12 |
| q1_1m | candidate v02 reader | 33.57 | 33.57 | 1.05 | 0 | 12 |
| q1_1m | candidate v02,chunked | 33.57 | 33.57 | 1.05 | 0 | 12 |
| q2_1m | baseline 3612482 | 33.57 | 33.57 | 8.39 | 0 | 14 |
| q2_1m | candidate reference | 33.57 | 33.57 | 8.39 | 0 | 14 |
| q2_1m | candidate v02 reader | 33.57 | 33.57 | 8.39 | 0 | 14 |
| q2_1m | candidate v02,chunked | 33.57 | 33.57 | 8.39 | 0 | 14 |
| q3_1m | baseline 3612482 | 33.57 | 33.57 | 0.06 | 0.00 | 4,616 |
| q3_1m | candidate reference | 33.57 | 33.57 | 0.06 | 0.00 | 4,616 |
| q3_1m | candidate v02 reader | 33.57 | 33.57 | 0.06 | 0.00 | 4,616 |
| q3_1m | candidate v02,chunked | 33.57 | 33.57 | 0.06 | 0.00 | 4,616 |
| q4_1m | baseline 3612482 | 33.57 | 33.57 | 42.04 | 33.56 | 7,107 |
| q4_1m | candidate reference | 33.57 | 33.57 | 0.10 | 0.01 | 7,107 |
| q4_1m | candidate v02 reader | 33.57 | 33.57 | 0.10 | 0.01 | 7,107 |
| q4_1m | candidate v02,chunked | 33.57 | 33.57 | 0.10 | 0.01 | 7,107 |
| q5_1m | baseline 3612482 | 33.57 | 33.57 | 0.02 | 0.00 | 1,324 |
| q5_1m | candidate reference | 33.57 | 33.57 | 0.02 | 0.00 | 1,324 |
| q5_1m | candidate v02 reader | 33.57 | 33.57 | 0.02 | 0.00 | 1,324 |
| q5_1m | candidate v02,chunked | 33.57 | 33.57 | 0.02 | 0.00 | 1,324 |
| q6_1m | baseline 3612482 | 33.57 | 33.57 | 0.08 | 0.00 | 6,527 |
| q6_1m | candidate reference | 33.57 | 33.57 | 0.08 | 0.00 | 6,527 |
| q6_1m | candidate v02 reader | 33.57 | 33.57 | 0.08 | 0.00 | 6,527 |
| q6_1m | candidate v02,chunked | 33.57 | 33.57 | 0.08 | 0.00 | 6,527 |
| parse_1m | baseline 3612482 | 33.56 | 33.56 | 8.39 | 0 | 14 |
| parse_1m | candidate reference | 33.56 | 33.56 | 8.39 | 0 | 14 |
| parse_1m | candidate v02 reader | 33.56 | 33.56 | 8.39 | 0 | 14 |
| parse_1m | candidate v02,chunked | 33.56 | 33.56 | 8.39 | 0 | 14 |
| str_group_100k | baseline 3612482 | 2.10 | 2.10 | 0.00 | 0 | 10 |
| str_group_100k | candidate reference | 2.10 | 2.10 | 0.00 | 0 | 10 |
| str_group_100k | candidate v02 reader | 2.10 | 2.10 | 0.00 | 0 | 10 |
| str_group_100k | candidate v02,chunked | 2.10 | 2.10 | 0.00 | 0 | 10 |
| str_unique_100k | baseline 3612482 | 2.10 | 2.10 | 0.00 | 0 | 10 |
| str_unique_100k | candidate reference | 2.10 | 2.10 | 0.00 | 0 | 10 |
| str_unique_100k | candidate v02 reader | 2.10 | 2.10 | 0.00 | 0 | 10 |
| str_unique_100k | candidate v02,chunked | 2.10 | 2.10 | 0.00 | 0 | 10 |
| str_join_100k | baseline 3612482 | 3.67 | 3.67 | 0.00 | 0 | 10 |
| str_join_100k | candidate reference | 3.67 | 3.67 | 0.00 | 0 | 10 |
| str_join_100k | candidate v02 reader | 3.67 | 3.67 | 0.00 | 0 | 10 |
| str_join_100k | candidate v02,chunked | 3.67 | 3.67 | 0.00 | 0 | 10 |
| str_group_300k | baseline 3612482 | 8.39 | 8.39 | 0.00 | 0 | 10 |
| str_group_300k | candidate reference | 8.39 | 8.39 | 0.00 | 0 | 10 |
| str_group_300k | candidate v02 reader | 8.39 | 8.39 | 0.00 | 0 | 10 |
| str_group_300k | candidate v02,chunked | 8.39 | 8.39 | 0.00 | 0 | 10 |
| str_unique_300k | baseline 3612482 | 8.39 | 8.39 | 0.00 | 0 | 10 |
| str_unique_300k | candidate reference | 8.39 | 8.39 | 0.00 | 0 | 10 |
| str_unique_300k | candidate v02 reader | 8.39 | 8.39 | 0.00 | 0 | 10 |
| str_unique_300k | candidate v02,chunked | 8.39 | 8.39 | 0.00 | 0 | 10 |
| str_join_300k | baseline 3612482 | 14.68 | 14.68 | 0.00 | 0 | 10 |
| str_join_300k | candidate reference | 14.68 | 14.68 | 0.00 | 0 | 10 |
| str_join_300k | candidate v02 reader | 14.68 | 14.68 | 0.00 | 0 | 10 |
| str_join_300k | candidate v02,chunked | 14.68 | 14.68 | 0.00 | 0 | 10 |
| str_group_1m | baseline 3612482 | 16.78 | 16.78 | 0.00 | 0 | 10 |
| str_group_1m | candidate reference | 16.78 | 16.78 | 0.00 | 0 | 10 |
| str_group_1m | candidate v02 reader | 16.78 | 16.78 | 0.00 | 0 | 10 |
| str_group_1m | candidate v02,chunked | 16.78 | 16.78 | 0.00 | 0 | 10 |
| str_unique_1m | baseline 3612482 | 16.78 | 16.78 | 0.00 | 0 | 10 |
| str_unique_1m | candidate reference | 16.78 | 16.78 | 0.00 | 0 | 10 |
| str_unique_1m | candidate v02 reader | 16.78 | 16.78 | 0.00 | 0 | 10 |
| str_unique_1m | candidate v02,chunked | 16.78 | 16.78 | 0.00 | 0 | 10 |
| str_join_1m | baseline 3612482 | 29.36 | 29.36 | 0.00 | 0 | 10 |
| str_join_1m | candidate reference | 29.36 | 29.36 | 0.00 | 0 | 10 |
| str_join_1m | candidate v02 reader | 29.36 | 29.36 | 0.00 | 0 | 10 |
| str_join_1m | candidate v02,chunked | 29.36 | 29.36 | 0.00 | 0 | 10 |

## 3. Parse (read + walk)

`retained after parse` is the live heap once the input frames exist (primary + aux, before the preservation clone). The `flat lower bound` is 4 bytes x columns x rows of the CSV files: one U32 / F32 / dictionary code per cell, string payload NOT included, so string workloads exceed 1.0 legitimately; array blocks are power-of-two sized (1M rows occupy 2^20 slots, +4.9%), which is most of the 1.20 of the sales file (its dictionary column adds the rest). `alloc MB` of the v0.1 reader counts every cons cell of the intermediate character lists; the v0.2 reader (`v02` rows) shows what removing them saves.

| workload | config | copy MB | fork copy MB | alloc MB | allocs | minflt | retained after parse MB | flat lower bound MB | retained / bound |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| q1_1m | baseline 3612482 | 0 | 0.00 | 5,009 | 413,074,558 | 80,116 | 33.59 | 28.00 | 1.20 |
| q1_1m | candidate reference | 0 | 0.00 | 4,036 | 352,278,390 | 80,114 | 33.59 | 28.00 | 1.20 |
| q1_1m | candidate v02 reader | 0 | 0.00 | 1,392 | 83,110,547 | 11,322 | 33.59 | 28.00 | 1.20 |
| q1_1m | candidate v02,chunked | 0 | 0.00 | 1,392 | 83,110,621 | 11,321 | 33.59 | 28.00 | 1.20 |
| q2_1m | baseline 3612482 | 0 | 0.00 | 5,009 | 413,074,558 | 114,100 | 33.59 | 28.00 | 1.20 |
| q2_1m | candidate reference | 0 | 0.00 | 4,036 | 352,278,390 | 80,318 | 33.59 | 28.00 | 1.20 |
| q2_1m | candidate v02 reader | 0 | 0.00 | 1,392 | 83,110,547 | 11,321 | 33.59 | 28.00 | 1.20 |
| q2_1m | candidate v02,chunked | 0 | 0.00 | 1,392 | 83,110,621 | 11,321 | 33.59 | 28.00 | 1.20 |
| q3_1m | baseline 3612482 | 0 | 0.00 | 5,009 | 413,074,558 | 86,955 | 33.59 | 28.00 | 1.20 |
| q3_1m | candidate reference | 0 | 0.00 | 4,036 | 352,278,390 | 80,114 | 33.59 | 28.00 | 1.20 |
| q3_1m | candidate v02 reader | 0 | 0.00 | 1,392 | 83,110,547 | 11,320 | 33.59 | 28.00 | 1.20 |
| q3_1m | candidate v02,chunked | 0 | 0.00 | 1,392 | 83,110,621 | 11,321 | 33.59 | 28.00 | 1.20 |
| q4_1m | baseline 3612482 | 0 | 0.00 | 5,009 | 413,074,558 | 118,930 | 33.59 | 28.00 | 1.20 |
| q4_1m | candidate reference | 0 | 0.00 | 4,036 | 352,278,390 | 82,133 | 33.59 | 28.00 | 1.20 |
| q4_1m | candidate v02 reader | 0 | 0.00 | 1,392 | 83,110,547 | 11,322 | 33.59 | 28.00 | 1.20 |
| q4_1m | candidate v02,chunked | 0 | 0.00 | 1,392 | 83,110,621 | 11,321 | 33.59 | 28.00 | 1.20 |
| q5_1m | baseline 3612482 | 0 | 0.00 | 5,009 | 413,074,558 | 115,243 | 33.59 | 28.00 | 1.20 |
| q5_1m | candidate reference | 0 | 0.00 | 4,036 | 352,278,390 | 80,115 | 33.59 | 28.00 | 1.20 |
| q5_1m | candidate v02 reader | 0 | 0.00 | 1,392 | 83,110,547 | 11,312 | 33.59 | 28.00 | 1.20 |
| q5_1m | candidate v02,chunked | 0 | 0.00 | 1,392 | 83,110,621 | 11,304 | 33.59 | 28.00 | 1.20 |
| q6_1m | baseline 3612482 | 0 | 0.00 | 5,009 | 413,074,558 | 109,808 | 33.59 | 28.00 | 1.20 |
| q6_1m | candidate reference | 0 | 0.00 | 4,036 | 352,278,390 | 80,114 | 33.59 | 28.00 | 1.20 |
| q6_1m | candidate v02 reader | 0 | 0.00 | 1,392 | 83,110,547 | 11,304 | 33.59 | 28.00 | 1.20 |
| q6_1m | candidate v02,chunked | 0 | 0.00 | 1,392 | 83,110,621 | 11,312 | 33.59 | 28.00 | 1.20 |
| parse_1m | baseline 3612482 | 0 | 0.00 | 5,009 | 413,057,644 | 85,564 | 33.57 | 28.00 | 1.20 |
| parse_1m | candidate reference | 0 | 0.00 | 4,036 | 352,264,616 | 80,126 | 33.57 | 28.00 | 1.20 |
| parse_1m | candidate v02 reader | 0 | 0.00 | 1,391 | 83,101,296 | 11,313 | 33.57 | 28.00 | 1.20 |
| parse_1m | candidate v02,chunked | 0 | 0.00 | 1,391 | 83,101,333 | 11,313 | 33.57 | 28.00 | 1.20 |
| str_group_100k | baseline 3612482 | 1.31 | 0.52 | 239.8 | 19,462,056 | 5,084 | 36.95 | 1.20 | 30.79 |
| str_group_100k | candidate reference | 1.31 | 0.52 | 187.8 | 16,208,768 | 5,083 | 36.95 | 1.20 | 30.79 |
| str_group_100k | candidate v02 reader | 0 | 0.52 | 137.7 | 9,882,326 | 3,048 | 36.95 | 1.20 | 30.79 |
| str_group_100k | candidate v02,chunked | 0 | 0.52 | 137.7 | 9,882,363 | 3,049 | 36.95 | 1.20 | 30.79 |
| str_unique_100k | baseline 3612482 | 1.31 | 0.52 | 239.8 | 19,462,056 | 5,084 | 36.95 | 1.20 | 30.79 |
| str_unique_100k | candidate reference | 1.31 | 0.52 | 187.8 | 16,208,768 | 5,083 | 36.95 | 1.20 | 30.79 |
| str_unique_100k | candidate v02 reader | 0 | 0.52 | 137.7 | 9,882,326 | 3,048 | 36.95 | 1.20 | 30.79 |
| str_unique_100k | candidate v02,chunked | 0 | 0.52 | 137.7 | 9,882,363 | 3,056 | 36.95 | 1.20 | 30.79 |
| str_join_100k | baseline 3612482 | 2.62 | 1.05 | 428.1 | 34,800,610 | 6,522 | 73.21 | 2.00 | 36.61 |
| str_join_100k | candidate reference | 2.62 | 1.05 | 335.6 | 29,020,940 | 6,520 | 73.21 | 2.00 | 36.61 |
| str_join_100k | candidate v02 reader | 0 | 1.05 | 260.8 | 18,996,728 | 5,300 | 73.21 | 2.00 | 36.61 |
| str_join_100k | candidate v02,chunked | 0 | 1.05 | 260.8 | 18,996,802 | 5,300 | 73.21 | 2.00 | 36.61 |
| str_group_300k | baseline 3612482 | 1.31 | 0.52 | 724.0 | 58,842,569 | 15,598 | 115.2 | 3.60 | 32.01 |
| str_group_300k | candidate reference | 1.31 | 0.52 | 566.4 | 48,993,588 | 15,598 | 115.2 | 3.60 | 32.01 |
| str_group_300k | candidate v02 reader | 0 | 0.52 | 405.6 | 29,080,720 | 9,202 | 115.2 | 3.60 | 32.01 |
| str_group_300k | candidate v02,chunked | 0 | 0.52 | 405.6 | 29,080,757 | 9,210 | 115.2 | 3.60 | 32.01 |
| str_unique_300k | baseline 3612482 | 1.31 | 0.52 | 724.0 | 58,842,569 | 15,600 | 115.2 | 3.60 | 32.01 |
| str_unique_300k | candidate reference | 1.31 | 0.52 | 566.4 | 48,993,588 | 15,598 | 115.2 | 3.60 | 32.01 |
| str_unique_300k | candidate v02 reader | 0 | 0.52 | 405.6 | 29,080,720 | 9,200 | 115.2 | 3.60 | 32.01 |
| str_unique_300k | candidate v02,chunked | 0 | 0.52 | 405.6 | 29,080,757 | 9,202 | 115.2 | 3.60 | 32.01 |
| str_join_300k | baseline 3612482 | 2.62 | 1.05 | 1,291 | 105,280,865 | 20,098 | 227.7 | 6.00 | 37.96 |
| str_join_300k | candidate reference | 2.62 | 1.05 | 1,011 | 87,770,005 | 20,097 | 227.7 | 6.00 | 37.96 |
| str_join_300k | candidate v02 reader | 0 | 1.05 | 764.8 | 55,655,617 | 16,068 | 227.7 | 6.00 | 37.96 |
| str_join_300k | candidate v02,chunked | 0 | 1.05 | 764.8 | 55,655,691 | 16,078 | 227.7 | 6.00 | 37.96 |
| str_group_1m | baseline 3612482 | 1.31 | 0.52 | 2,367 | 196,663,040 | 49,766 | 375.6 | 12.00 | 31.30 |
| str_group_1m | candidate reference | 1.31 | 0.52 | 1,840 | 163,731,499 | 49,722 | 375.6 | 12.00 | 31.30 |
| str_group_1m | candidate v02 reader | 0 | 0.52 | 1,316 | 96,265,114 | 29,359 | 375.6 | 12.00 | 31.30 |
| str_group_1m | candidate v02,chunked | 0 | 0.52 | 1,316 | 96,265,151 | 29,368 | 375.6 | 12.00 | 31.30 |
| str_unique_1m | baseline 3612482 | 1.31 | 0.52 | 2,367 | 196,663,040 | 53,402 | 375.6 | 12.00 | 31.30 |
| str_unique_1m | candidate reference | 1.31 | 0.52 | 1,840 | 163,731,499 | 49,709 | 375.6 | 12.00 | 31.30 |
| str_unique_1m | candidate v02 reader | 0 | 0.52 | 1,316 | 96,265,114 | 29,357 | 375.6 | 12.00 | 31.30 |
| str_unique_1m | candidate v02,chunked | 0 | 0.52 | 1,316 | 96,265,151 | 29,376 | 375.6 | 12.00 | 31.30 |
| str_join_1m | baseline 3612482 | 2.62 | 1.05 | 4,225 | 352,202,338 | 89,560 | 745.9 | 20.00 | 37.29 |
| str_join_1m | candidate reference | 2.62 | 1.05 | 3,287 | 293,584,261 | 64,593 | 745.9 | 20.00 | 37.29 |
| str_join_1m | candidate v02 reader | 0 | 1.05 | 2,482 | 184,193,323 | 51,970 | 745.9 | 20.00 | 37.29 |
| str_join_1m | candidate v02,chunked | 0 | 1.05 | 2,482 | 184,193,397 | 51,978 | 745.9 | 20.00 | 37.29 |

## 4. Whole process

Totals at process exit (all phases; the exit line is printed from an `atexit` handler: live at exit is 0 when every allocation was freed, which is how the accounting is self-checked). `peak live` is the high-water mark of the retained heap (the G4 quantity; the arena can be larger).

| workload | config | alloc MB | allocs | copy MB | fork copy MB | peak live MB | minflt | live at exit MB |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| q1_1m | baseline 3612482 | 5,073 | 413,079,599 | 41.96 | 0.00 | 1,203 | 81,957 | 0 |
| q1_1m | candidate reference | 4,079 | 352,283,522 | 33.57 | 0.00 | 1,203 | 80,882 | 0 |
| q1_1m | candidate v02 reader | 1,434 | 83,115,679 | 33.57 | 0.00 | 98.31 | 13,891 | 0 |
| q1_1m | candidate v02,chunked | 1,460 | 83,168,774 | 33.57 | 0.00 | 98.31 | 15,208 | 0 |
| q2_1m | baseline 3612482 | 5,093 | 413,079,862 | 50.34 | 0.00 | 1,203 | 115,430 | 0 |
| q2_1m | candidate reference | 4,091 | 352,284,095 | 33.57 | 0.00 | 1,203 | 81,444 | 0 |
| q2_1m | candidate v02 reader | 1,446 | 83,116,252 | 33.57 | 0.00 | 98.31 | 14,214 | 0 |
| q2_1m | candidate v02,chunked | 1,518 | 83,206,565 | 33.57 | 0.00 | 98.31 | 15,958 | 0 |
| q3_1m | baseline 3612482 | 5,140 | 413,090,153 | 71.32 | 0.00 | 1,203 | 88,638 | 0 |
| q3_1m | candidate reference | 4,102 | 352,293,414 | 37.76 | 0.00 | 1,203 | 81,518 | 0 |
| q3_1m | candidate v02 reader | 1,457 | 83,125,571 | 37.76 | 0.00 | 98.31 | 14,518 | 0 |
| q3_1m | candidate v02,chunked | 1,508 | 83,217,823 | 37.76 | 0.00 | 98.31 | 15,748 | 0 |
| q4_1m | baseline 3612482 | 5,208 | 413,086,605 | 79.71 | 0.00 | 1,203 | 120,280 | 0 |
| q4_1m | candidate reference | 4,107 | 352,289,997 | 33.57 | 0.00 | 1,203 | 83,504 | 0 |
| q4_1m | candidate v02 reader | 1,463 | 83,122,154 | 33.57 | 0.00 | 98.31 | 14,493 | 0 |
| q4_1m | candidate v02,chunked | 1,463 | 83,122,297 | 33.57 | 0.00 | 98.31 | 14,490 | 0 |
| q5_1m | baseline 3612482 | 5,131 | 413,086,721 | 50.35 | 0.01 | 1,203 | 117,120 | 0 |
| q5_1m | candidate reference | 4,123 | 352,289,225 | 37.76 | 0.00 | 1,203 | 81,757 | 0 |
| q5_1m | candidate v02 reader | 1,478 | 83,121,382 | 37.76 | 0.00 | 98.31 | 14,752 | 0 |
| q5_1m | candidate v02,chunked | 1,478 | 83,122,435 | 37.76 | 0.00 | 98.31 | 14,746 | 0 |
| q6_1m | baseline 3612482 | 5,288 | 413,084,556 | 138.4 | 0.00 | 1,203 | 110,733 | 0 |
| q6_1m | candidate reference | 4,165 | 352,288,362 | 33.57 | 0.00 | 1,203 | 80,960 | 0 |
| q6_1m | candidate v02 reader | 1,520 | 83,120,519 | 33.57 | 0.00 | 98.31 | 13,939 | 0 |
| q6_1m | candidate v02,chunked | 1,520 | 83,120,593 | 33.57 | 0.00 | 98.31 | 13,957 | 0 |
| parse_1m | baseline 3612482 | 5,051 | 413,059,582 | 33.56 | 0.00 | 1,203 | 85,858 | 0 |
| parse_1m | candidate reference | 4,078 | 352,266,558 | 33.56 | 0.00 | 1,203 | 80,412 | 0 |
| parse_1m | candidate v02 reader | 1,433 | 83,103,238 | 33.56 | 0.00 | 98.31 | 13,392 | 0 |
| parse_1m | candidate v02,chunked | 1,433 | 83,103,275 | 33.56 | 0.00 | 98.31 | 13,391 | 0 |
| str_group_100k | baseline 3612482 | 1,834 | 109,963,870 | 4.98 | 8.39 | 73.71 | 5,841 | 0 |
| str_group_100k | candidate reference | 210.4 | 16,212,846 | 3.41 | 0.52 | 73.71 | 6,368 | 0 |
| str_group_100k | candidate v02 reader | 160.3 | 9,886,404 | 2.10 | 0.52 | 55.30 | 4,497 | 0 |
| str_group_100k | candidate v02,chunked | 160.3 | 9,887,197 | 2.10 | 0.52 | 55.30 | 4,499 | 0 |
| str_unique_100k | baseline 3612482 | 1,832 | 109,962,399 | 4.46 | 8.39 | 73.71 | 5,708 | 0 |
| str_unique_100k | candidate reference | 211.9 | 16,211,512 | 3.41 | 0.52 | 73.71 | 6,300 | 0 |
| str_unique_100k | candidate v02 reader | 161.9 | 9,885,070 | 2.10 | 0.52 | 54.77 | 4,428 | 0 |
| str_unique_100k | candidate v02,chunked | 161.9 | 9,885,247 | 2.10 | 0.52 | 54.77 | 4,438 | 0 |
| str_join_100k | baseline 3612482 | 489.3 | 37,595,416 | 7.34 | 3.15 | 121.3 | 8,102 | 0 |
| str_join_100k | candidate reference | 366.1 | 29,024,895 | 7.34 | 1.05 | 98.26 | 8,052 | 0 |
| str_join_100k | candidate v02 reader | 291.3 | 19,000,683 | 4.72 | 1.05 | 94.18 | 6,929 | 0 |
| str_join_100k | candidate v02,chunked | 291.3 | 19,000,826 | 4.72 | 1.05 | 94.18 | 6,928 | 0 |
| str_group_300k | baseline 3612482 | 5,818 | 349,871,234 | 15.99 | 31.98 | 222.6 | 17,459 | 0 |
| str_group_300k | candidate reference | 656.6 | 48,997,676 | 9.70 | 0.52 | 222.6 | 19,764 | 0 |
| str_group_300k | candidate v02 reader | 495.8 | 29,084,808 | 8.39 | 0.52 | 188.6 | 14,006 | 0 |
| str_group_300k | candidate v02,chunked | 495.8 | 29,085,604 | 8.39 | 0.52 | 188.6 | 14,019 | 0 |
| str_unique_300k | baseline 3612482 | 5,809 | 349,869,763 | 13.89 | 31.98 | 222.6 | 16,942 | 0 |
| str_unique_300k | candidate reference | 662.9 | 48,996,345 | 9.70 | 0.52 | 222.6 | 19,499 | 0 |
| str_unique_300k | candidate v02 reader | 502.1 | 29,083,474 | 8.39 | 0.52 | 186.5 | 13,749 | 0 |
| str_unique_300k | candidate v02,chunked | 502.1 | 29,083,651 | 8.39 | 0.52 | 186.5 | 13,750 | 0 |
| str_join_300k | baseline 3612482 | 1,504 | 113,835,641 | 21.50 | 9.44 | 388.2 | 25,160 | 0 |
| str_join_300k | candidate reference | 1,132 | 87,773,988 | 21.50 | 1.05 | 311.6 | 25,285 | 0 |
| str_join_300k | candidate v02 reader | 886.5 | 55,659,588 | 18.87 | 1.05 | 311.6 | 21,760 | 0 |
| str_join_300k | candidate v02,chunked | 886.5 | 55,659,731 | 18.87 | 1.05 | 311.6 | 21,769 | 0 |
| str_group_1m | baseline 3612482 | 25,186 | 1,522,300,140 | 30.67 | 63.44 | 742.5 | 62,333 | 0 |
| str_group_1m | candidate reference | 2,021 | 163,735,616 | 18.09 | 0.52 | 742.5 | 58,022 | 0 |
| str_group_1m | candidate v02 reader | 1,496 | 96,269,225 | 16.78 | 0.52 | 522.4 | 38,648 | 0 |
| str_group_1m | candidate v02,chunked | 1,496 | 96,270,018 | 16.78 | 0.52 | 522.4 | 38,654 | 0 |
| str_unique_1m | baseline 3612482 | 25,169 | 1,522,298,665 | 26.48 | 63.44 | 742.5 | 76,646 | 0 |
| str_unique_1m | candidate reference | 2,033 | 163,734,275 | 18.09 | 0.52 | 742.5 | 57,146 | 0 |
| str_unique_1m | candidate v02 reader | 1,509 | 96,267,890 | 16.78 | 0.52 | 518.2 | 38,130 | 0 |
| str_unique_1m | candidate v02,chunked | 1,509 | 96,268,073 | 16.78 | 0.52 | 518.2 | 38,150 | 0 |
| str_join_1m | baseline 3612482 | 4,793 | 381,017,358 | 40.37 | 17.83 | 1,209 | 104,674 | 0 |
| str_join_1m | candidate reference | 3,530 | 293,588,256 | 40.37 | 1.05 | 994.6 | 74,602 | 0 |
| str_join_1m | candidate v02 reader | 2,726 | 184,197,312 | 37.75 | 1.05 | 913.7 | 63,038 | 0 |
| str_join_1m | candidate v02,chunked | 2,726 | 184,197,455 | 37.75 | 1.05 | 913.7 | 63,044 | 0 |

## 5. Copy sources (call sites of `blk_copy` / `blk_node` / `blk_half`, at least 0.1 MB)

Each row is one C call site (`bench/m2/instrument.py` wraps the three runtime entries with `__LINE__`), resolved to the enclosing Bend function: `FID` names are `module path + Bend def`, `spin_N <- FID` is a flat loop traced up the static call graph to the nearest Bend function(s) that contain it (a spin shared by several callers lists up to three). `copy` = `Array.clone` and friends, `node` / `half` = array rebuilt from / matched into halves. The prep phase (the harness's input-preservation `DF.clone`) is omitted, and so are the rows of a `v02` / `chunked` / `v02,chunked` config whose phase is identical to the candidate reference's (a phase with no row has no site of 0.1 MB or more).

| workload | config | phase | kind | MB | calls | where |
|---|---|---|---|---:|---:|---|
| q1_1m | baseline 3612482 | compute | copy | 8.39 | 2 | `spin_795 <- SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST, SRC_FMT_FMT_D_COL_K3839` |
| q2_1m | baseline 3612482 | compute | copy | 12.58 | 3 | `spin_795 <- SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST, SRC_FMT_FMT_D_COL_K3839` |
| q2_1m | baseline 3612482 | compute | copy | 4.19 | 1 | `spin_642 <- SRC_JOIN_KEY_ENC, SRC_JOIN_KEY_ENC_K1667, SRC_JOIN_KEY_ENC_K1669` |
| q3_1m | baseline 3612482 | compute | copy | 25.17 | 6 | `spin_795 <- SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST, SRC_FMT_FMT_D_COL_K3839` |
| q3_1m | baseline 3612482 | compute | copy | 4.19 | 2 | `spin_798 <- SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST, SRC_FMT_FMT_D_COL_K3839` |
| q3_1m | baseline 3612482 | compute | copy | 4.19 | 1 | `SRC_GROUPBY_GRP_ENCODE_KEEP` |
| q3_1m | baseline 3612482 | compute | copy | 4.19 | 1 | `spin_642 <- SRC_JOIN_KEY_ENC, SRC_JOIN_KEY_ENC_K1667, SRC_JOIN_KEY_ENC_K1669` |
| q3_1m | candidate reference | compute | copy | 4.19 | 1 | `spin_1650 <- SRC_GROUPBY_GROUPBY_RUN_K6932` |
| q4_1m | baseline 3612482 | compute | copy | 8.39 | 2 | `spin_795 <- SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST, SRC_FMT_FMT_D_COL_K3839` |
| q4_1m | baseline 3612482 | compute | copy | 4.19 | 1 | `spin_798 <- SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST, SRC_FMT_FMT_D_COL_K3839` |
| q5_1m | baseline 3612482 | compute | copy | 4.19 | 2 | `SRC_JOIN_KEY_ENC_K1670` |
| q5_1m | baseline 3612482 | compute | copy | 4.19 | 2 | `spin_798 <- SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST, SRC_FMT_FMT_D_COL_K3839` |
| q5_1m | baseline 3612482 | compute | copy | 4.19 | 1 | `spin_795 <- SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST, SRC_FMT_FMT_D_COL_K3839` |
| q5_1m | baseline 3612482 | compute | copy | 4.19 | 1 | `SRC_GROUPBY_GRP_ENCODE_KEEP` |
| q5_1m | candidate reference | compute | copy | 4.19 | 1 | `spin_1650 <- SRC_GROUPBY_GROUPBY_RUN_K6932` |
| q6_1m | baseline 3612482 | compute | copy | 100.7 | 24 | `spin_795 <- SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST, SRC_FMT_FMT_D_COL_K3839` |
| q6_1m | baseline 3612482 | compute | copy | 4.19 | 1 | `spin_642 <- SRC_JOIN_KEY_ENC, SRC_JOIN_KEY_ENC_K1667, SRC_JOIN_KEY_ENC_K1669` |
| str_group_100k | baseline 3612482 | compute | node | 4.72 | 14 | `spin_656 <- SRC_SORT_SORT_PCODES_K1517` |
| str_group_100k | baseline 3612482 | compute | half | 3.15 | 14 | `SRC_SORT_SORT_PCODES` |
| str_group_100k | baseline 3612482 | compute | copy | 1.05 | 1 | `spin_798 <- SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST, SRC_FMT_FMT_D_COL_K3839` |
| str_group_100k | baseline 3612482 | compute | copy | 0.52 | 1 | `spin_795 <- SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST, SRC_FMT_FMT_D_COL_K3839` |
| str_group_100k | baseline 3612482 | read | copy | 1.31 | 2 | `spin_523 <- SRC_CSV_CB_FEED_K1918, SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST` |
| str_group_100k | baseline 3612482 | read | node | 0.52 | 15 | `spin_527 <- SRC_STRS_DICT_ADD` |
| str_group_100k | candidate reference | read | copy | 1.31 | 2 | `spin_1559 <- SRC_CEXEC_CX_CCLONE_K3176, SRC_CEXEC_CX_DCLONE_K2827` |
| str_group_100k | candidate reference | read | node | 0.52 | 15 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_group_100k | candidate v02 reader | read | node | 0.52 | 15 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_group_100k | candidate v02,chunked | read | node | 0.52 | 15 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_unique_100k | baseline 3612482 | compute | node | 4.72 | 14 | `spin_656 <- SRC_SORT_SORT_PCODES_K1517` |
| str_unique_100k | baseline 3612482 | compute | half | 3.15 | 14 | `SRC_SORT_SORT_PCODES` |
| str_unique_100k | baseline 3612482 | compute | copy | 1.05 | 1 | `spin_798 <- SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST, SRC_FMT_FMT_D_COL_K3839` |
| str_unique_100k | baseline 3612482 | read | copy | 1.31 | 2 | `spin_523 <- SRC_CSV_CB_FEED_K1918, SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST` |
| str_unique_100k | baseline 3612482 | read | node | 0.52 | 15 | `spin_527 <- SRC_STRS_DICT_ADD` |
| str_unique_100k | candidate reference | read | copy | 1.31 | 2 | `spin_1559 <- SRC_CEXEC_CX_CCLONE_K3176, SRC_CEXEC_CX_DCLONE_K2827` |
| str_unique_100k | candidate reference | read | node | 0.52 | 15 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_unique_100k | candidate v02 reader | read | node | 0.52 | 15 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_unique_100k | candidate v02,chunked | read | node | 0.52 | 15 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_join_100k | baseline 3612482 | compute | node | 1.05 | 1 | `SRC_JOIN_PROBE_FORK` |
| str_join_100k | baseline 3612482 | compute | half | 1.05 | 2 | `SRC_JOIN_PROBE_FORK` |
| str_join_100k | baseline 3612482 | compute | copy | 0.52 | 1 | `spin_889 <- SRC_JOIN_JOIN_RUN_K3635` |
| str_join_100k | baseline 3612482 | compute | copy | 0.52 | 1 | `spin_1012 <- SRC_JOIN_JOIN_RUN_K3635` |
| str_join_100k | baseline 3612482 | read | copy | 2.62 | 4 | `spin_523 <- SRC_CSV_CB_FEED_K1918, SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST` |
| str_join_100k | baseline 3612482 | read | node | 1.05 | 30 | `spin_527 <- SRC_STRS_DICT_ADD` |
| str_join_100k | candidate reference | compute | copy | 0.52 | 1 | `spin_2311 <- SRC_JOIN_JOIN_RUN_K6908` |
| str_join_100k | candidate reference | compute | copy | 0.52 | 1 | `spin_2474 <- SRC_JOIN_JOIN_RUN_K6908` |
| str_join_100k | candidate reference | read | copy | 2.62 | 4 | `spin_1559 <- SRC_CEXEC_CX_CCLONE_K3176, SRC_CEXEC_CX_DCLONE_K2827` |
| str_join_100k | candidate reference | read | node | 1.05 | 30 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_join_100k | candidate v02 reader | read | node | 1.05 | 30 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_join_100k | candidate v02,chunked | read | node | 1.05 | 30 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_group_300k | baseline 3612482 | compute | node | 18.87 | 14 | `spin_656 <- SRC_SORT_SORT_PCODES_K1517` |
| str_group_300k | baseline 3612482 | compute | half | 12.58 | 14 | `SRC_SORT_SORT_PCODES` |
| str_group_300k | baseline 3612482 | compute | copy | 4.19 | 1 | `spin_798 <- SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST, SRC_FMT_FMT_D_COL_K3839` |
| str_group_300k | baseline 3612482 | compute | copy | 2.10 | 1 | `spin_795 <- SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST, SRC_FMT_FMT_D_COL_K3839` |
| str_group_300k | baseline 3612482 | read | copy | 1.31 | 2 | `spin_523 <- SRC_CSV_CB_FEED_K1918, SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST` |
| str_group_300k | baseline 3612482 | read | node | 0.52 | 15 | `spin_527 <- SRC_STRS_DICT_ADD` |
| str_group_300k | candidate reference | read | copy | 1.31 | 2 | `spin_1559 <- SRC_CEXEC_CX_CCLONE_K3176, SRC_CEXEC_CX_DCLONE_K2827` |
| str_group_300k | candidate reference | read | node | 0.52 | 15 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_group_300k | candidate v02 reader | read | node | 0.52 | 15 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_group_300k | candidate v02,chunked | read | node | 0.52 | 15 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_unique_300k | baseline 3612482 | compute | node | 18.87 | 14 | `spin_656 <- SRC_SORT_SORT_PCODES_K1517` |
| str_unique_300k | baseline 3612482 | compute | half | 12.58 | 14 | `SRC_SORT_SORT_PCODES` |
| str_unique_300k | baseline 3612482 | compute | copy | 4.19 | 1 | `spin_798 <- SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST, SRC_FMT_FMT_D_COL_K3839` |
| str_unique_300k | baseline 3612482 | read | copy | 1.31 | 2 | `spin_523 <- SRC_CSV_CB_FEED_K1918, SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST` |
| str_unique_300k | baseline 3612482 | read | node | 0.52 | 15 | `spin_527 <- SRC_STRS_DICT_ADD` |
| str_unique_300k | candidate reference | read | copy | 1.31 | 2 | `spin_1559 <- SRC_CEXEC_CX_CCLONE_K3176, SRC_CEXEC_CX_DCLONE_K2827` |
| str_unique_300k | candidate reference | read | node | 0.52 | 15 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_unique_300k | candidate v02 reader | read | node | 0.52 | 15 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_unique_300k | candidate v02,chunked | read | node | 0.52 | 15 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_join_300k | baseline 3612482 | compute | node | 4.19 | 1 | `SRC_JOIN_PROBE_FORK` |
| str_join_300k | baseline 3612482 | compute | half | 4.19 | 2 | `SRC_JOIN_PROBE_FORK` |
| str_join_300k | baseline 3612482 | compute | copy | 2.10 | 1 | `spin_889 <- SRC_JOIN_JOIN_RUN_K3635` |
| str_join_300k | baseline 3612482 | compute | copy | 2.10 | 1 | `spin_1012 <- SRC_JOIN_JOIN_RUN_K3635` |
| str_join_300k | baseline 3612482 | read | copy | 2.62 | 4 | `spin_523 <- SRC_CSV_CB_FEED_K1918, SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST` |
| str_join_300k | baseline 3612482 | read | node | 1.05 | 30 | `spin_527 <- SRC_STRS_DICT_ADD` |
| str_join_300k | candidate reference | compute | copy | 2.10 | 1 | `spin_2311 <- SRC_JOIN_JOIN_RUN_K6908` |
| str_join_300k | candidate reference | compute | copy | 2.10 | 1 | `spin_2474 <- SRC_JOIN_JOIN_RUN_K6908` |
| str_join_300k | candidate reference | read | copy | 2.62 | 4 | `spin_1559 <- SRC_CEXEC_CX_CCLONE_K3176, SRC_CEXEC_CX_DCLONE_K2827` |
| str_join_300k | candidate reference | read | node | 1.05 | 30 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_join_300k | candidate v02 reader | read | node | 1.05 | 30 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_join_300k | candidate v02,chunked | read | node | 1.05 | 30 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_group_1m | baseline 3612482 | compute | node | 37.75 | 14 | `spin_656 <- SRC_SORT_SORT_PCODES_K1517` |
| str_group_1m | baseline 3612482 | compute | half | 25.17 | 14 | `SRC_SORT_SORT_PCODES` |
| str_group_1m | baseline 3612482 | compute | copy | 8.39 | 1 | `spin_798 <- SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST, SRC_FMT_FMT_D_COL_K3839` |
| str_group_1m | baseline 3612482 | compute | copy | 4.19 | 1 | `spin_795 <- SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST, SRC_FMT_FMT_D_COL_K3839` |
| str_group_1m | baseline 3612482 | read | copy | 1.31 | 2 | `spin_523 <- SRC_CSV_CB_FEED_K1918, SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST` |
| str_group_1m | baseline 3612482 | read | node | 0.52 | 15 | `spin_527 <- SRC_STRS_DICT_ADD` |
| str_group_1m | candidate reference | read | copy | 1.31 | 2 | `spin_1559 <- SRC_CEXEC_CX_CCLONE_K3176, SRC_CEXEC_CX_DCLONE_K2827` |
| str_group_1m | candidate reference | read | node | 0.52 | 15 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_group_1m | candidate v02 reader | read | node | 0.52 | 15 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_group_1m | candidate v02,chunked | read | node | 0.52 | 15 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_unique_1m | baseline 3612482 | compute | node | 37.75 | 14 | `spin_656 <- SRC_SORT_SORT_PCODES_K1517` |
| str_unique_1m | baseline 3612482 | compute | half | 25.17 | 14 | `SRC_SORT_SORT_PCODES` |
| str_unique_1m | baseline 3612482 | compute | copy | 8.39 | 1 | `spin_798 <- SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST, SRC_FMT_FMT_D_COL_K3839` |
| str_unique_1m | baseline 3612482 | read | copy | 1.31 | 2 | `spin_523 <- SRC_CSV_CB_FEED_K1918, SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST` |
| str_unique_1m | baseline 3612482 | read | node | 0.52 | 15 | `spin_527 <- SRC_STRS_DICT_ADD` |
| str_unique_1m | candidate reference | read | copy | 1.31 | 2 | `spin_1559 <- SRC_CEXEC_CX_CCLONE_K3176, SRC_CEXEC_CX_DCLONE_K2827` |
| str_unique_1m | candidate reference | read | node | 0.52 | 15 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_unique_1m | candidate v02 reader | read | node | 0.52 | 15 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_unique_1m | candidate v02,chunked | read | node | 0.52 | 15 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_join_1m | baseline 3612482 | compute | node | 8.39 | 1 | `SRC_JOIN_PROBE_FORK` |
| str_join_1m | baseline 3612482 | compute | half | 8.39 | 2 | `SRC_JOIN_PROBE_FORK` |
| str_join_1m | baseline 3612482 | compute | copy | 4.19 | 1 | `spin_889 <- SRC_JOIN_JOIN_RUN_K3635` |
| str_join_1m | baseline 3612482 | compute | copy | 4.19 | 1 | `spin_1012 <- SRC_JOIN_JOIN_RUN_K3635` |
| str_join_1m | baseline 3612482 | read | copy | 2.62 | 4 | `spin_523 <- SRC_CSV_CB_FEED_K1918, SRC_COLUMN_COLS_CLONE_K4297, SRC_EVAL_EVAL_CAST` |
| str_join_1m | baseline 3612482 | read | node | 1.05 | 30 | `spin_527 <- SRC_STRS_DICT_ADD` |
| str_join_1m | candidate reference | compute | copy | 4.19 | 1 | `spin_2311 <- SRC_JOIN_JOIN_RUN_K6908` |
| str_join_1m | candidate reference | compute | copy | 4.19 | 1 | `spin_2474 <- SRC_JOIN_JOIN_RUN_K6908` |
| str_join_1m | candidate reference | read | copy | 2.62 | 4 | `spin_1559 <- SRC_CEXEC_CX_CCLONE_K3176, SRC_CEXEC_CX_DCLONE_K2827` |
| str_join_1m | candidate reference | read | node | 1.05 | 30 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_join_1m | candidate v02 reader | read | node | 1.05 | 30 | `spin_1771 <- SRC_STRS_DICT_ADD` |
| str_join_1m | candidate v02,chunked | read | node | 1.05 | 30 | `spin_1771 <- SRC_STRS_DICT_ADD` |

## 6. Chunk conversions (`BF_ENGINE=chunked`)

The chunked executor converts flat env frames to chunk trees (`of_frame`) and back (`to_frame`) inside the compute window. The facade does not expose `CStats` (`collect_with` drops it), so the conversion cost is read off the counters: the compute phase of `v02,chunked` minus the compute phase of `v02` (same reader, same frames; the reference executor). The conversions do not use `blk_copy` / `blk_node` / `blk_half` (cuts and joins are fresh blocks), so they show as extra **alloc** bytes and allocations, not as copy bytes; the extra also contains whatever the chunked leaves allocate beyond the reference's operators. The `CStats` columns are the runner's own counters of conversions (count / LOGICAL bytes = 4 x rows x columns converted) from `bench/m2/cstats.bend`, the same plan at the same grain (`-` = no CStats record; q4 and the string ops run flat, 0 conversions). q6 and parse do not collect.

| workload | extra copy MB | extra fork copy MB | extra alloc MB | extra allocs | extra minflt | CStats in (n / MB) | CStats out (n / MB) |
|---|---:|---:|---:|---:|---:|---:|---:|
| q1_1m | 0 | 0 | 25.93 | 53,015 | 1,317 | 1 / 20.00 | 1 / 2.99 |
| q2_1m | 0 | 0 | 71.77 | 90,233 | 1,741 | 1 / 32.00 | 1 / 36.00 |
| q3_1m | 0.00 | 0 | 50.83 | 92,178 | 1,228 | 1 / 32.00 | 1 / 16.00 |

No conversion (extra alloc under 0.1 MB, no CStats conversions): q4_1m, q5_1m, q6_1m, parse_1m, str_group_100k, str_unique_100k, str_join_100k, str_group_300k, str_unique_300k, str_join_300k, str_group_1m, str_unique_1m, str_join_1m. Those plans run flat (sort / group_by / join / unique / describe flatten, and a frame of at most 2^14 rows stays flat): the chunked engine adds only a handful of runner allocations there.

## 7. Result retained after compute (candidate reference)

`live after compute` minus `live after parse`: what the result (plus anything the executor leaves behind) retains once the cloned inputs have been consumed. Bytes per result row can be compared with the flat bound of the result's columns.

| workload | result rows | retained after compute MB | bytes / result row |
|---|---:|---:|---:|
| q1_1m | 249,356 | 3.15 | 12.6 |
| q2_1m | 1,000,000 | 37.76 | 37.8 |
| q3_1m | 8 | 0.00 | 217.0 |
| q4_1m | 10 | 0.01 | 748.8 |
| q5_1m | 6 | 0.00 | 136.0 |
| q6_1m | 9 | 0.00 | 154.7 |
| parse_1m | 1,000,000 | 33.56 | 33.6 |
| str_group_100k | 100,000 | 2.10 | 21.0 |
| str_unique_100k | 100,000 | 1.05 | 10.5 |
| str_join_100k | 90,000 | 2.62 | 29.1 |
| str_group_300k | 300,000 | 8.39 | 28.0 |
| str_unique_300k | 300,000 | 4.19 | 14.0 |
| str_join_300k | 270,000 | 10.49 | 38.8 |
| str_group_1m | 1,000,000 | 16.78 | 16.8 |
| str_unique_1m | 1,000,000 | 8.39 | 8.4 |
| str_join_1m | 900,000 | 20.97 | 23.3 |

