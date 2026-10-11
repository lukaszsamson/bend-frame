# W0 summary: t54-final

- run `t54-final`: 2026-10-11T07:46:56+00:00, commit 20eacdec14 dirty=True src 16153790df, bend bend 2.0.36, load at start [45.05, 21.38, 23.79], provisional=True
- load (1 min) before/after every process: min 8.3 median 11.0 max 45.0
- 150 valid processes, 0 invalid/failed

## Timings (ms; median [min..max] n) and candidate/baseline ratio

key metric per row: compute_ms (queries), parse_ms (parse), e2e_ms (e2e); ms per input for batched controls

| workload | mode | metric | thr | baseline | candidate | ratio c/b | load max |
|---|---|---|---:|---|---|---:|---:|
| q3_1m | phases | compute_ms | 1 | 22.0 [18.0..39.0] n=5 | 21.0 [19.0..22.0] n=5 | 0.95 | 45 |
| q3_1m | phases | compute_ms | 4 | 21.0 [17.0..22.0] n=5 | 19.0 [17.0..21.0] n=5 | 0.90 | 45 |
| q3_1m | phases | compute_ms | 12 | 20.0 [19.0..23.0] n=5 | 18.0 [17.0..28.0] n=5 | 0.90 | 42 |
| q4_1m | phases | compute_ms | 1 | 17.0 [16.0..25.0] n=5 | 18.0 [16.0..24.0] n=5 | 1.06 | 19 |
| q4_1m | phases | compute_ms | 4 | 17.0 [16.0..17.0] n=5 | 17.0 [16.0..18.0] n=5 | 1.00 | 18 |
| q4_1m | phases | compute_ms | 12 | 15.0 [14.0..17.0] n=5 | 16.0 [15.0..24.0] n=5 | 1.07 | 18 |
| q5_1m | phases | compute_ms | 1 | 14.0 [14.0..15.0] n=5 | 18.0 [13.0..21.0] n=5 | 1.29 | 14 |
| q5_1m | phases | compute_ms | 4 | 15.0 [14.0..18.0] n=5 | 15.0 [14.0..20.0] n=5 | 1.00 | 13 |
| q5_1m | phases | compute_ms | 12 | 14.0 [13.0..17.0] n=5 | 15.0 [13.0..18.0] n=5 | 1.07 | 13 |
| q6_1m | phases | compute_ms | 1 | 55.0 [53.0..75.0] n=5 | 54.0 [51.0..80.0] n=5 | 0.98 | 10 |
| q6_1m | phases | compute_ms | 4 | 55.0 [54.0..59.0] n=5 | 33.0 [31.0..37.0] n=5 | 0.60 | 10 |
| q6_1m | phases | compute_ms | 12 | 56.0 [53.0..58.0] n=5 | 32.0 [30.0..36.0] n=5 | 0.57 | 10 |

## Phases (G6): medians in ms per input (parse = read + walk; prep = input-preservation clone; compute; check = output/validation hash)

| workload | binary | thr | read | walk | parse | prep | compute | check | compute+check | e2e (e2e mode) | rss MB (phases) | rss MB (e2e) |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| q3_1m | baseline | 1 | 4,751 | 5.00 | 4,759 | 3.00 | 22.0 | 1.00 | 23.0 | - | 1,307 | - |
| q3_1m | baseline | 4 | 2,962 | 5.00 | 2,968 | 2.00 | 21.0 | 0.000 | 21.0 | - | 1,295 | - |
| q3_1m | baseline | 12 | 2,316 | 5.00 | 2,321 | 2.00 | 20.0 | 0.000 | 20.0 | - | 1,306 | - |
| q3_1m | candidate | 1 | 4,749 | 5.00 | 4,754 | 2.00 | 21.0 | 0.000 | 21.0 | - | 1,290 | - |
| q3_1m | candidate | 4 | 2,501 | 5.00 | 2,506 | 2.00 | 19.0 | 0.000 | 19.0 | - | 1,326 | - |
| q3_1m | candidate | 12 | 2,119 | 5.00 | 2,124 | 2.00 | 18.0 | 0.000 | 19.0 | - | 1,338 | - |
| q4_1m | baseline | 1 | 4,569 | 5.00 | 4,574 | 2.00 | 17.0 | 0.000 | 17.0 | - | 1,305 | - |
| q4_1m | baseline | 4 | 2,671 | 5.00 | 2,676 | 2.00 | 17.0 | 0.000 | 17.0 | - | 1,295 | - |
| q4_1m | baseline | 12 | 2,278 | 5.00 | 2,283 | 2.00 | 15.0 | 0.000 | 15.0 | - | 1,306 | - |
| q4_1m | candidate | 1 | 4,776 | 5.00 | 4,781 | 2.00 | 18.0 | 0.000 | 18.0 | - | 1,290 | - |
| q4_1m | candidate | 4 | 2,522 | 5.00 | 2,527 | 2.00 | 17.0 | 0.000 | 17.0 | - | 1,337 | - |
| q4_1m | candidate | 12 | 2,126 | 5.00 | 2,131 | 2.00 | 16.0 | 0.000 | 17.0 | - | 1,337 | - |
| q5_1m | baseline | 1 | 4,592 | 5.00 | 4,597 | 2.00 | 14.0 | 0.000 | 14.0 | - | 1,320 | - |
| q5_1m | baseline | 4 | 2,582 | 5.00 | 2,587 | 2.00 | 15.0 | 0.000 | 15.0 | - | 1,322 | - |
| q5_1m | baseline | 12 | 2,099 | 5.00 | 2,104 | 2.00 | 14.0 | 0.000 | 14.0 | - | 1,337 | - |
| q5_1m | candidate | 1 | 4,558 | 5.00 | 4,564 | 2.00 | 18.0 | 0.000 | 18.0 | - | 1,312 | - |
| q5_1m | candidate | 4 | 2,620 | 5.00 | 2,625 | 2.00 | 15.0 | 0.000 | 15.0 | - | 1,306 | - |
| q5_1m | candidate | 12 | 2,142 | 6.00 | 2,147 | 2.00 | 15.0 | 0.000 | 15.0 | - | 1,342 | - |
| q6_1m | baseline | 1 | 4,434 | 5.00 | 4,439 | 2.00 | 55.0 | 1.00 | 55.0 | - | 1,306 | - |
| q6_1m | baseline | 4 | 2,599 | 5.00 | 2,604 | 2.00 | 55.0 | 0.000 | 56.0 | - | 1,306 | - |
| q6_1m | baseline | 12 | 2,160 | 5.00 | 2,165 | 2.00 | 56.0 | 0.000 | 56.0 | - | 1,329 | - |
| q6_1m | candidate | 1 | 4,500 | 5.00 | 4,505 | 1.00 | 54.0 | 0.000 | 54.0 | - | 1,323 | - |
| q6_1m | candidate | 4 | 2,506 | 5.00 | 2,510 | 2.00 | 33.0 | 0.000 | 33.0 | - | 1,337 | - |
| q6_1m | candidate | 12 | 2,146 | 5.00 | 2,151 | 2.00 | 32.0 | 0.000 | 32.0 | - | 1,342 | - |

## Thread scaling (G2): speedup = median(1 thread) / median(N threads); serial fraction s from Amdahl with N = 12

s = (1/S - 1/12) / (1 - 1/12) from the 12-thread speedup S; 1/s is the speedup even infinite parallelism would give at that serial fraction. Today nothing forks, so S ~ 1 (s ~ 1) is expected at the baseline; G2 needs S >= 3 (q1-q6 compute) and >= 4 (parse), i.e. s <= 1/3 (parse: 1/4 is not enough: needs s <= ~0.2).

| workload | mode | binary | metric | T1 | T4 | T12 | S4 | S12 | s | 1/s |
|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|
| q3_1m | phases | baseline | compute_ms | 22.0 | 21.0 | 20.0 | 1.05 | 1.10 | 0.90 | 1.1 |
| q3_1m | phases | candidate | compute_ms | 21.0 | 19.0 | 18.0 | 1.11 | 1.17 | 0.84 | 1.2 |
| q4_1m | phases | baseline | compute_ms | 17.0 | 17.0 | 15.0 | 1.00 | 1.13 | 0.87 | 1.1 |
| q4_1m | phases | candidate | compute_ms | 18.0 | 17.0 | 16.0 | 1.06 | 1.12 | 0.88 | 1.1 |
| q5_1m | phases | baseline | compute_ms | 14.0 | 15.0 | 14.0 | 0.93 | 1.00 | 1.00 | 1.0 |
| q5_1m | phases | candidate | compute_ms | 18.0 | 15.0 | 15.0 | 1.20 | 1.20 | 0.82 | 1.2 |
| q6_1m | phases | baseline | compute_ms | 55.0 | 55.0 | 56.0 | 1.00 | 0.98 | 1.02 | 1.0 |
| q6_1m | phases | candidate | compute_ms | 54.0 | 33.0 | 32.0 | 1.64 | 1.69 | 0.56 | 1.8 |

## Stage breakdown of q1-q6 (eager stages, each alone; medians in ms)

### stages_1m, baseline

| stage | 1t ms | 4t ms | 12t ms | share of 1t sum | S12 |
|---|---:|---:|---:|---:|---:|
| filter_q1 | 14.0 | 12.0 | 11.0 | 11% | 1.27 |
| select_q1 | 1.00 | 0.000 | 0.000 | 1% | - |
| withcols_q2 | 7.00 | 6.00 | 6.00 | 6% | 1.17 |
| groupby_q3 | 10.0 | 9.00 | 10.0 | 8% | 1.00 |
| sort_q3 | 0.000 | 0.000 | 0.000 | 0% | - |
| sort_q4 | 30.0 | 23.0 | 24.0 | 24% | 1.25 |
| head_q4 | 0.000 | 0.000 | 0.000 | 0% | - |
| join_q5 | 6.00 | 6.00 | 6.00 | 5% | 1.00 |
| groupby_q5 | 5.00 | 4.00 | 4.00 | 4% | 1.25 |
| sort_q5 | 0.000 | 0.000 | 1.00 | 0% | - |
| describe_q6 | 54.0 | 52.0 | 52.0 | 43% | 1.04 |
| (sum of stages) | 127 | 112 | 114 | | |

parse (read + walk) ms: 1t 4,440, 4t 2,383, 12t 2,044

### stages_1m, candidate

| stage | 1t ms | 4t ms | 12t ms | share of 1t sum | S12 |
|---|---:|---:|---:|---:|---:|
| filter_q1 | 13.0 | 12.0 | 13.0 | 11% | 1.00 |
| select_q1 | 0.000 | 0.000 | 0.000 | 0% | - |
| withcols_q2 | 6.00 | 6.00 | 6.00 | 5% | 1.00 |
| groupby_q3 | 9.00 | 9.00 | 9.00 | 8% | 1.00 |
| sort_q3 | 0.000 | 0.000 | 1.00 | 0% | - |
| sort_q4 | 24.0 | 25.0 | 24.0 | 21% | 1.00 |
| head_q4 | 0.000 | 0.000 | 0.000 | 0% | - |
| join_q5 | 6.00 | 6.00 | 6.00 | 5% | 1.00 |
| groupby_q5 | 4.00 | 4.00 | 5.00 | 3% | 0.80 |
| sort_q5 | 0.000 | 0.000 | 0.000 | 0% | - |
| describe_q6 | 53.0 | 28.0 | 28.0 | 46% | 1.89 |
| (sum of stages) | 115 | 90.0 | 92.0 | | |

parse (read + walk) ms: 1t 4,514, 4t 2,466, 12t 2,039

## Raw samples (ms per input; one value per process, in rep order)

- q3_1m phases baseline t=1 compute_ms: [25.0, 22.0, 18.0, 39.0, 18.0]  load1 [45.05, 30.54, 24.32, 20.71, 18.56]
- q3_1m phases candidate t=1 compute_ms: [21.0, 19.0, 22.0, 19.0, 21.0]  load1 [42.18, 34.91, 26.85, 23.18, 19.32]
- q3_1m phases baseline t=4 compute_ms: [22.0, 21.0, 17.0, 20.0, 22.0]  load1 [44.72, 37.17, 23.18, 20.41, 19.0]
- q3_1m phases candidate t=4 compute_ms: [19.0, 19.0, 17.0, 19.0, 21.0]  load1 [39.45, 32.68, 25.74, 21.64, 19.66]
- q3_1m phases baseline t=12 compute_ms: [23.0, 19.0, 20.0, 20.0, 23.0]  load1 [42.18, 34.91, 28.49, 19.66, 19.32]
- q3_1m phases candidate t=12 compute_ms: [18.0, 18.0, 17.0, 18.0, 28.0]  load1 [37.17, 30.54, 25.74, 20.71, 18.56]
- q4_1m phases baseline t=1 compute_ms: [16.0, 16.0, 17.0, 25.0, 17.0]  load1 [18.65, 14.81, 13.94, 13.4, 12.41]
- q4_1m phases candidate t=1 compute_ms: [16.0, 24.0, 17.0, 24.0, 18.0]  load1 [17.29, 15.41, 14.34, 12.96, 12.38]
- q4_1m phases baseline t=4 compute_ms: [17.0, 17.0, 17.0, 17.0, 16.0]  load1 [18.36, 15.79, 13.22, 13.05, 11.89]
- q4_1m phases candidate t=4 compute_ms: [17.0, 16.0, 18.0, 16.0, 18.0]  load1 [16.38, 15.06, 13.76, 13.52, 12.97]
- q4_1m phases baseline t=12 compute_ms: [14.0, 15.0, 17.0, 15.0, 15.0]  load1 [18.36, 15.79, 14.34, 13.05, 11.89]
- q4_1m phases candidate t=12 compute_ms: [16.0, 16.0, 24.0, 24.0, 15.0]  load1 [16.38, 15.06, 13.94, 13.52, 12.97]
- q5_1m phases baseline t=1 compute_ms: [15.0, 14.0, 14.0, 15.0, 14.0]  load1 [13.31, 11.91, 10.38, 9.19, 10.16]
- q5_1m phases candidate t=1 compute_ms: [13.0, 21.0, 14.0, 18.0, 19.0]  load1 [13.81, 12.18, 11.28, 9.95, 9.92]
- q5_1m phases baseline t=4 compute_ms: [14.0, 15.0, 16.0, 18.0, 14.0]  load1 [13.45, 12.37, 9.95, 9.25, 9.82]
- q5_1m phases candidate t=4 compute_ms: [20.0, 15.0, 15.0, 14.0, 15.0]  load1 [13.19, 12.17, 10.94, 9.55, 10.43]
- q5_1m phases baseline t=12 compute_ms: [14.0, 14.0, 17.0, 15.0, 13.0]  load1 [13.45, 12.37, 11.28, 10.43, 9.82]
- q5_1m phases candidate t=12 compute_ms: [15.0, 15.0, 13.0, 18.0, 13.0]  load1 [13.19, 12.17, 10.94, 9.19, 10.16]
- q6_1m phases baseline t=1 compute_ms: [55.0, 75.0, 55.0, 53.0, 53.0]  load1 [9.52, 9.98, 9.35, 9.74, 9.23]
- q6_1m phases candidate t=1 compute_ms: [53.0, 80.0, 54.0, 51.0, 54.0]  load1 [9.54, 9.47, 10.14, 9.96, 9.85]
- q6_1m phases baseline t=4 compute_ms: [59.0, 55.0, 54.0, 54.0, 56.0]  load1 [9.32, 9.16, 9.08, 9.6, 9.14]
- q6_1m phases candidate t=4 compute_ms: [37.0, 36.0, 33.0, 32.0, 31.0]  load1 [9.17, 10.15, 9.65, 9.72, 9.6]
- q6_1m phases baseline t=12 compute_ms: [56.0, 58.0, 56.0, 53.0, 54.0]  load1 [9.32, 9.16, 10.14, 9.6, 9.85]
- q6_1m phases candidate t=12 compute_ms: [36.0, 32.0, 34.0, 30.0, 32.0]  load1 [9.17, 10.15, 9.35, 9.72, 9.23]

