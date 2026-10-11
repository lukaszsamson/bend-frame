# W0 summary: t53-v01

- run `t53-v01`: 2026-10-11T10:25:39+00:00, commit 4f5b93754a dirty=True src e6905ccb47, bend bend 2.0.36, load at start [7.45, 8.62, 13.57], provisional=True
- load (1 min) before/after every process: min 6.3 median 8.2 max 12.4
- 90 valid processes, 0 invalid/failed

## Timings (ms; median [min..max] n) and candidate/baseline ratio

key metric per row: compute_ms (queries), parse_ms (parse), e2e_ms (e2e); ms per input for batched controls

| workload | mode | metric | thr | baseline | candidate | ratio c/b | load max |
|---|---|---|---:|---|---|---:|---:|
| q1_1m | phases | compute_ms | 1 | - | 7.00 [6.00..7.00] n=5 | - | 12 |
| q1_1m | phases | compute_ms | 4 | - | 7.00 [6.00..7.00] n=5 | - | 12 |
| q1_1m | phases | compute_ms | 12 | - | 7.00 [6.00..8.00] n=5 | - | 12 |
| q2_1m | phases | compute_ms | 1 | - | 8.00 [7.00..10.0] n=5 | - | 12 |
| q2_1m | phases | compute_ms | 4 | - | 8.00 [7.00..62.0] n=5 | - | 12 |
| q2_1m | phases | compute_ms | 12 | - | 8.00 [7.00..9.00] n=5 | - | 12 |
| q3_1m | phases | compute_ms | 1 | - | 17.0 [17.0..23.0] n=5 | - | 11 |
| q3_1m | phases | compute_ms | 4 | - | 17.0 [16.0..17.0] n=5 | - | 10 |
| q3_1m | phases | compute_ms | 12 | - | 18.0 [17.0..20.0] n=5 | - | 11 |
| q4_1m | phases | compute_ms | 1 | - | 18.0 [15.0..20.0] n=5 | - | 10 |
| q4_1m | phases | compute_ms | 4 | - | 15.0 [15.0..18.0] n=5 | - | 10 |
| q4_1m | phases | compute_ms | 12 | - | 18.0 [15.0..21.0] n=5 | - | 10 |
| q5_1m | phases | compute_ms | 1 | - | 13.0 [13.0..16.0] n=5 | - | 10 |
| q5_1m | phases | compute_ms | 4 | - | 13.0 [12.0..14.0] n=5 | - | 10 |
| q5_1m | phases | compute_ms | 12 | - | 13.0 [12.0..20.0] n=5 | - | 10 |
| q6_1m | phases | compute_ms | 1 | - | 55.0 [54.0..89.0] n=5 | - | 9 |
| q6_1m | phases | compute_ms | 4 | - | 30.0 [29.0..31.0] n=5 | - | 9 |
| q6_1m | phases | compute_ms | 12 | - | 31.0 [30.0..35.0] n=5 | - | 10 |

## Phases (G6): medians in ms per input (parse = read + walk; prep = input-preservation clone; compute; check = output/validation hash)

| workload | binary | thr | read | walk | parse | prep | compute | check | compute+check | e2e (e2e mode) | rss MB (phases) | rss MB (e2e) |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| q1_1m | candidate | 1 | 4,237 | 5.00 | 4,242 | 1.00 | 7.00 | 1.00 | 8.00 | - | 1,335 | - |
| q1_1m | candidate | 4 | 2,369 | 5.00 | 2,374 | 2.00 | 7.00 | 2.00 | 8.00 | - | 1,340 | - |
| q1_1m | candidate | 12 | 2,028 | 5.00 | 2,032 | 2.00 | 7.00 | 1.00 | 8.00 | - | 1,340 | - |
| q2_1m | candidate | 1 | 4,373 | 5.00 | 4,379 | 1.00 | 8.00 | 14.0 | 22.0 | - | 1,332 | - |
| q2_1m | candidate | 4 | 2,562 | 5.00 | 2,567 | 2.00 | 8.00 | 14.0 | 22.0 | - | 1,332 | - |
| q2_1m | candidate | 12 | 2,011 | 5.00 | 2,016 | 2.00 | 8.00 | 15.0 | 23.0 | - | 1,337 | - |
| q3_1m | candidate | 1 | 4,333 | 5.00 | 4,338 | 2.00 | 17.0 | 0.000 | 18.0 | - | 1,332 | - |
| q3_1m | candidate | 4 | 2,404 | 5.00 | 2,409 | 2.00 | 17.0 | 0.000 | 17.0 | - | 1,337 | - |
| q3_1m | candidate | 12 | 2,030 | 5.00 | 2,035 | 2.00 | 18.0 | 0.000 | 18.0 | - | 1,338 | - |
| q4_1m | candidate | 1 | 4,534 | 5.00 | 4,539 | 1.00 | 18.0 | 0.000 | 18.0 | - | 1,332 | - |
| q4_1m | candidate | 4 | 2,411 | 5.00 | 2,416 | 2.00 | 15.0 | 0.000 | 16.0 | - | 1,337 | - |
| q4_1m | candidate | 12 | 2,104 | 5.00 | 2,109 | 2.00 | 18.0 | 0.000 | 19.0 | - | 1,333 | - |
| q5_1m | candidate | 1 | 4,436 | 5.00 | 4,442 | 2.00 | 13.0 | 0.000 | 13.0 | - | 1,336 | - |
| q5_1m | candidate | 4 | 2,448 | 5.00 | 2,453 | 2.00 | 13.0 | 0.000 | 13.0 | - | 1,341 | - |
| q5_1m | candidate | 12 | 2,093 | 5.00 | 2,098 | 2.00 | 13.0 | 0.000 | 13.0 | - | 1,342 | - |
| q6_1m | candidate | 1 | 4,587 | 5.00 | 4,592 | 2.00 | 55.0 | 0.000 | 55.0 | - | 1,323 | - |
| q6_1m | candidate | 4 | 2,423 | 5.00 | 2,428 | 1.00 | 30.0 | 0.000 | 31.0 | - | 1,337 | - |
| q6_1m | candidate | 12 | 2,044 | 5.00 | 2,050 | 2.00 | 31.0 | 0.000 | 31.0 | - | 1,342 | - |

## Thread scaling (G2): speedup = median(1 thread) / median(N threads); serial fraction s from Amdahl with N = 12

s = (1/S - 1/12) / (1 - 1/12) from the 12-thread speedup S; 1/s is the speedup even infinite parallelism would give at that serial fraction. Today nothing forks, so S ~ 1 (s ~ 1) is expected at the baseline; G2 needs S >= 3 (q1-q6 compute) and >= 4 (parse), i.e. s <= 1/3 (parse: 1/4 is not enough: needs s <= ~0.2).

| workload | mode | binary | metric | T1 | T4 | T12 | S4 | S12 | s | 1/s |
|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|
| q1_1m | phases | candidate | compute_ms | 7.00 | 7.00 | 7.00 | 1.00 | 1.00 | 1.00 | 1.0 |
| q2_1m | phases | candidate | compute_ms | 8.00 | 8.00 | 8.00 | 1.00 | 1.00 | 1.00 | 1.0 |
| q3_1m | phases | candidate | compute_ms | 17.0 | 17.0 | 18.0 | 1.00 | 0.94 | 1.06 | 0.9 |
| q4_1m | phases | candidate | compute_ms | 18.0 | 15.0 | 18.0 | 1.20 | 1.00 | 1.00 | 1.0 |
| q5_1m | phases | candidate | compute_ms | 13.0 | 13.0 | 13.0 | 1.00 | 1.00 | 1.00 | 1.0 |
| q6_1m | phases | candidate | compute_ms | 55.0 | 30.0 | 31.0 | 1.83 | 1.77 | 0.52 | 1.9 |

## Raw samples (ms per input; one value per process, in rep order)

- q1_1m phases candidate t=1 compute_ms: [7.0, 7.0, 6.0, 7.0, 7.0]  load1 [7.45, 7.74, 11.96, 8.01, 9.46]
- q1_1m phases candidate t=4 compute_ms: [6.0, 7.0, 6.0, 7.0, 7.0]  load1 [7.09, 7.74, 11.8, 8.17, 9.41]
- q1_1m phases candidate t=12 compute_ms: [6.0, 7.0, 7.0, 8.0, 7.0]  load1 [7.09, 7.74, 12.39, 8.17, 9.41]
- q2_1m phases candidate t=1 compute_ms: [8.0, 8.0, 7.0, 10.0, 8.0]  load1 [7.09, 7.63, 11.65, 7.76, 9.57]
- q2_1m phases candidate t=4 compute_ms: [7.0, 8.0, 8.0, 9.0, 62.0]  load1 [7.49, 7.6, 11.65, 7.76, 9.18]
- q2_1m phases candidate t=12 compute_ms: [7.0, 8.0, 7.0, 9.0, 9.0]  load1 [7.05, 7.63, 11.8, 8.5, 9.18]
- q3_1m phases candidate t=1 compute_ms: [18.0, 17.0, 17.0, 17.0, 23.0]  load1 [7.05, 6.93, 11.04, 8.5, 10.26]
- q3_1m phases candidate t=4 compute_ms: [17.0, 17.0, 16.0, 17.0, 17.0]  load1 [6.64, 7.18, 10.4, 7.9, 9.76]
- q3_1m phases candidate t=12 compute_ms: [18.0, 17.0, 17.0, 19.0, 20.0]  load1 [6.59, 6.93, 11.04, 8.14, 9.76]
- q4_1m phases candidate t=1 compute_ms: [17.0, 20.0, 15.0, 19.0, 18.0]  load1 [6.59, 6.99, 10.12, 8.14, 9.46]
- q4_1m phases candidate t=4 compute_ms: [17.0, 15.0, 15.0, 18.0, 15.0]  load1 [6.62, 7.25, 9.71, 8.05, 9.76]
- q4_1m phases candidate t=12 compute_ms: [19.0, 16.0, 15.0, 18.0, 21.0]  load1 [6.62, 7.25, 10.12, 8.21, 9.76]
- q5_1m phases candidate t=1 compute_ms: [13.0, 14.0, 13.0, 13.0, 16.0]  load1 [6.41, 7.05, 9.9, 8.21, 8.94]
- q5_1m phases candidate t=4 compute_ms: [14.0, 13.0, 13.0, 13.0, 12.0]  load1 [6.3, 7.31, 9.5, 8.43, 8.94]
- q5_1m phases candidate t=12 compute_ms: [20.0, 13.0, 13.0, 15.0, 12.0]  load1 [6.3, 7.31, 9.71, 8.43, 8.94]
- q6_1m phases candidate t=1 compute_ms: [54.0, 57.0, 54.0, 89.0, 55.0]  load1 [6.84, 8.0, 9.14, 8.56, 8.5]
- q6_1m phases candidate t=4 compute_ms: [29.0, 30.0, 31.0, 30.0, 31.0]  load1 [6.61, 8.0, 9.14, 8.67, 8.63]
- q6_1m phases candidate t=12 compute_ms: [31.0, 33.0, 30.0, 30.0, 35.0]  load1 [6.61, 8.0, 9.5, 8.54, 8.5]

