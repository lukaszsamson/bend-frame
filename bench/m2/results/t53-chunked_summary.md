# W0 summary: t53-chunked

- run `t53-chunked`: 2026-10-11T10:26:33+00:00, commit 4f5b93754a dirty=True src e6905ccb47, bend bend 2.0.36, load at start [6.61, 8.19, 13.12], provisional=True
- load (1 min) before/after every process: min 6.6 median 7.9 max 12.6
- 90 valid processes, 0 invalid/failed

## Timings (ms; median [min..max] n) and candidate/baseline ratio

key metric per row: compute_ms (queries), parse_ms (parse), e2e_ms (e2e); ms per input for batched controls

| workload | mode | metric | thr | baseline | candidate | ratio c/b | load max |
|---|---|---|---:|---|---|---:|---:|
| q1_1m | phases | compute_ms | 1 | - | 14.0 [12.0..15.0] n=5 | - | 9 |
| q1_1m | phases | compute_ms | 4 | - | 9.00 [7.00..11.0] n=5 | - | 9 |
| q1_1m | phases | compute_ms | 12 | - | 9.00 [9.00..16.0] n=5 | - | 9 |
| q2_1m | phases | compute_ms | 1 | - | 25.0 [23.0..26.0] n=5 | - | 9 |
| q2_1m | phases | compute_ms | 4 | - | 15.0 [14.0..18.0] n=5 | - | 9 |
| q2_1m | phases | compute_ms | 12 | - | 16.0 [14.0..17.0] n=5 | - | 9 |
| q3_1m | phases | compute_ms | 1 | - | 28.0 [27.0..30.0] n=5 | - | 9 |
| q3_1m | phases | compute_ms | 4 | - | 22.0 [22.0..46.0] n=5 | - | 9 |
| q3_1m | phases | compute_ms | 12 | - | 22.0 [20.0..24.0] n=5 | - | 9 |
| q4_1m | phases | compute_ms | 1 | - | 17.0 [16.0..19.0] n=5 | - | 10 |
| q4_1m | phases | compute_ms | 4 | - | 18.0 [14.0..24.0] n=5 | - | 10 |
| q4_1m | phases | compute_ms | 12 | - | 17.0 [14.0..18.0] n=5 | - | 10 |
| q5_1m | phases | compute_ms | 1 | - | 13.0 [12.0..14.0] n=5 | - | 10 |
| q5_1m | phases | compute_ms | 4 | - | 13.0 [12.0..13.0] n=5 | - | 10 |
| q5_1m | phases | compute_ms | 12 | - | 13.0 [12.0..15.0] n=5 | - | 10 |
| q6_1m | phases | compute_ms | 1 | - | 55.0 [53.0..56.0] n=5 | - | 13 |
| q6_1m | phases | compute_ms | 4 | - | 32.0 [29.0..36.0] n=5 | - | 10 |
| q6_1m | phases | compute_ms | 12 | - | 31.0 [29.0..34.0] n=5 | - | 13 |

## Phases (G6): medians in ms per input (parse = read + walk; prep = input-preservation clone; compute; check = output/validation hash)

| workload | binary | thr | read | walk | parse | prep | compute | check | compute+check | e2e (e2e mode) | rss MB (phases) | rss MB (e2e) |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| q1_1m | candidate | 1 | 4,488 | 5.00 | 4,493 | 2.00 | 14.0 | 1.00 | 15.0 | - | 1,347 | - |
| q1_1m | candidate | 4 | 2,596 | 5.00 | 2,601 | 2.00 | 9.00 | 1.00 | 11.0 | - | 1,352 | - |
| q1_1m | candidate | 12 | 2,089 | 5.00 | 2,094 | 1.00 | 9.00 | 1.00 | 11.0 | - | 1,353 | - |
| q2_1m | candidate | 1 | 4,441 | 5.00 | 4,446 | 1.00 | 25.0 | 14.0 | 39.0 | - | 1,356 | - |
| q2_1m | candidate | 4 | 2,488 | 5.00 | 2,493 | 2.00 | 15.0 | 15.0 | 30.0 | - | 1,361 | - |
| q2_1m | candidate | 12 | 2,030 | 5.00 | 2,034 | 2.00 | 16.0 | 15.0 | 31.0 | - | 1,366 | - |
| q3_1m | candidate | 1 | 4,468 | 5.00 | 4,473 | 2.00 | 28.0 | 0.000 | 28.0 | - | 1,353 | - |
| q3_1m | candidate | 4 | 2,526 | 5.00 | 2,530 | 1.00 | 22.0 | 0.000 | 22.0 | - | 1,353 | - |
| q3_1m | candidate | 12 | 2,059 | 5.00 | 2,064 | 2.00 | 22.0 | 0.000 | 22.0 | - | 1,358 | - |
| q4_1m | candidate | 1 | 4,491 | 5.00 | 4,496 | 2.00 | 17.0 | 0.000 | 17.0 | - | 1,332 | - |
| q4_1m | candidate | 4 | 2,454 | 5.00 | 2,459 | 2.00 | 18.0 | 0.000 | 18.0 | - | 1,337 | - |
| q4_1m | candidate | 12 | 2,129 | 5.00 | 2,133 | 2.00 | 17.0 | 0.000 | 17.0 | - | 1,337 | - |
| q5_1m | candidate | 1 | 4,554 | 5.00 | 4,559 | 2.00 | 13.0 | 0.000 | 13.0 | - | 1,336 | - |
| q5_1m | candidate | 4 | 2,438 | 4.00 | 2,442 | 2.00 | 13.0 | 0.000 | 13.0 | - | 1,341 | - |
| q5_1m | candidate | 12 | 2,099 | 5.00 | 2,104 | 1.00 | 13.0 | 0.000 | 13.0 | - | 1,338 | - |
| q6_1m | candidate | 1 | 4,359 | 5.00 | 4,364 | 1.00 | 55.0 | 0.000 | 55.0 | - | 1,323 | - |
| q6_1m | candidate | 4 | 2,505 | 5.00 | 2,509 | 2.00 | 32.0 | 0.000 | 32.0 | - | 1,341 | - |
| q6_1m | candidate | 12 | 2,010 | 5.00 | 2,015 | 2.00 | 31.0 | 0.000 | 31.0 | - | 1,342 | - |

## Thread scaling (G2): speedup = median(1 thread) / median(N threads); serial fraction s from Amdahl with N = 12

s = (1/S - 1/12) / (1 - 1/12) from the 12-thread speedup S; 1/s is the speedup even infinite parallelism would give at that serial fraction. Today nothing forks, so S ~ 1 (s ~ 1) is expected at the baseline; G2 needs S >= 3 (q1-q6 compute) and >= 4 (parse), i.e. s <= 1/3 (parse: 1/4 is not enough: needs s <= ~0.2).

| workload | mode | binary | metric | T1 | T4 | T12 | S4 | S12 | s | 1/s |
|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|
| q1_1m | phases | candidate | compute_ms | 14.0 | 9.00 | 9.00 | 1.56 | 1.56 | 0.61 | 1.6 |
| q2_1m | phases | candidate | compute_ms | 25.0 | 15.0 | 16.0 | 1.67 | 1.56 | 0.61 | 1.6 |
| q3_1m | phases | candidate | compute_ms | 28.0 | 22.0 | 22.0 | 1.27 | 1.27 | 0.77 | 1.3 |
| q4_1m | phases | candidate | compute_ms | 17.0 | 18.0 | 17.0 | 0.94 | 1.00 | 1.00 | 1.0 |
| q5_1m | phases | candidate | compute_ms | 13.0 | 13.0 | 13.0 | 1.00 | 1.00 | 1.00 | 1.0 |
| q6_1m | phases | candidate | compute_ms | 55.0 | 32.0 | 31.0 | 1.72 | 1.77 | 0.52 | 1.9 |

## Raw samples (ms per input; one value per process, in rep order)

- q1_1m phases candidate t=1 compute_ms: [14.0, 12.0, 12.0, 15.0, 14.0]  load1 [6.61, 7.83, 8.73, 8.54, 7.56]
- q1_1m phases candidate t=4 compute_ms: [8.0, 11.0, 7.0, 9.0, 10.0]  load1 [7.52, 8.08, 8.99, 8.01, 8.13]
- q1_1m phases candidate t=12 compute_ms: [9.0, 9.0, 16.0, 12.0, 9.0]  load1 [7.56, 8.08, 8.73, 7.93, 7.56]
- q2_1m phases candidate t=1 compute_ms: [23.0, 23.0, 25.0, 26.0, 26.0]  load1 [7.56, 8.03, 9.07, 7.93, 7.47]
- q2_1m phases candidate t=4 compute_ms: [14.0, 15.0, 16.0, 15.0, 18.0]  load1 [7.51, 7.69, 8.75, 8.02, 7.6]
- q2_1m phases candidate t=12 compute_ms: [15.0, 16.0, 16.0, 14.0, 17.0]  load1 [7.23, 7.69, 9.07, 8.02, 7.47]
- q3_1m phases candidate t=1 compute_ms: [27.0, 28.0, 28.0, 30.0, 28.0]  load1 [7.23, 7.63, 8.61, 7.62, 7.7]
- q3_1m phases candidate t=4 compute_ms: [22.0, 22.0, 22.0, 46.0, 23.0]  load1 [7.21, 7.95, 9.36, 7.65, 7.59]
- q3_1m phases candidate t=12 compute_ms: [24.0, 20.0, 21.0, 22.0, 22.0]  load1 [7.12, 7.95, 8.61, 7.65, 7.7]
- q4_1m phases candidate t=1 compute_ms: [18.0, 17.0, 16.0, 19.0, 17.0]  load1 [7.12, 7.58, 8.77, 9.76, 7.43]
- q4_1m phases candidate t=4 compute_ms: [19.0, 18.0, 18.0, 24.0, 14.0]  load1 [7.19, 7.63, 8.63, 10.02, 7.73]
- q4_1m phases candidate t=12 compute_ms: [16.0, 18.0, 14.0, 17.0, 17.0]  load1 [7.19, 7.58, 9.36, 10.02, 7.43]
- q5_1m phases candidate t=1 compute_ms: [13.0, 14.0, 13.0, 12.0, 13.0]  load1 [8.05, 7.83, 8.74, 10.01, 7.6]
- q5_1m phases candidate t=4 compute_ms: [12.0, 12.0, 13.0, 13.0, 13.0]  load1 [7.81, 7.3, 8.2, 10.09, 7.47]
- q5_1m phases candidate t=12 compute_ms: [12.0, 12.0, 13.0, 15.0, 14.0]  load1 [7.81, 7.83, 8.63, 10.09, 7.47]
- q6_1m phases candidate t=1 compute_ms: [55.0, 56.0, 53.0, 55.0, 54.0]  load1 [8.14, 12.6, 8.2, 10.33, 7.14]
- q6_1m phases candidate t=4 compute_ms: [32.0, 36.0, 29.0, 33.0, 31.0]  load1 [7.89, 7.69, 8.1, 10.06, 7.15]
- q6_1m phases candidate t=12 compute_ms: [34.0, 32.0, 29.0, 31.0, 30.0]  load1 [7.89, 12.6, 8.2, 10.06, 7.15]

