# W0 summary: w8-v01parse-prov

- run `w8-v01parse-prov`: 2026-10-11T19:36:16+00:00, commit 4cf2e52058 dirty=True src 16e2fecde1, bend bend 2.0.36, load at start [2.4, 2.63, 2.69], provisional=True
- load (1 min) before/after every process: min 2.1 median 2.4 max 2.7
- 30 valid processes, 0 invalid/failed

## Timings (ms; median [min..max] n) and candidate/baseline ratio

key metric per row: compute_ms (queries), parse_ms (parse), e2e_ms (e2e); ms per input for batched controls

| workload | mode | metric | thr | baseline | candidate | ratio c/b | load max |
|---|---|---|---:|---|---|---:|---:|
| parse_1m | e2e | e2e_ms | 1 | - | 3,913 [3,907..3,937] n=5 | - | 2 |
| parse_1m | e2e | e2e_ms | 4 | - | 2,166 [2,145..2,168] n=5 | - | 3 |
| parse_1m | e2e | e2e_ms | 12 | - | 1,819 [1,811..1,820] n=5 | - | 3 |
| parse_1m | phases | parse_ms | 1 | - | 3,911 [3,896..3,934] n=5 | - | 3 |
| parse_1m | phases | parse_ms | 4 | - | 2,160 [2,148..2,186] n=5 | - | 3 |
| parse_1m | phases | parse_ms | 12 | - | 1,818 [1,808..1,825] n=5 | - | 3 |

## Phases (G6): medians in ms per input (parse = read + walk; prep = input-preservation clone; compute; check = output/validation hash)

| workload | binary | thr | read | walk | parse | prep | compute | check | compute+check | e2e (e2e mode) | rss MB (phases) | rss MB (e2e) |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| parse_1m | candidate | 1 | 3,906 | 5.00 | 3,911 | 1.00 | 0.000 | 12.0 | 12.0 | 3,913 | 1,314 | 1,314 |
| parse_1m | candidate | 4 | 2,156 | 5.00 | 2,160 | 1.00 | 0.000 | 12.0 | 12.0 | 2,166 | 1,315 | 1,315 |
| parse_1m | candidate | 12 | 1,813 | 4.00 | 1,818 | 2.00 | 0.000 | 12.0 | 12.0 | 1,819 | 1,320 | 1,315 |

## Thread scaling (G2): speedup = median(1 thread) / median(N threads); serial fraction s from Amdahl with N = 12

s = (1/S - 1/12) / (1 - 1/12) from the 12-thread speedup S; 1/s is the speedup even infinite parallelism would give at that serial fraction. Today nothing forks, so S ~ 1 (s ~ 1) is expected at the baseline; G2 needs S >= 3 (q1-q6 compute) and >= 4 (parse), i.e. s <= 1/3 (parse: 1/4 is not enough: needs s <= ~0.2).

| workload | mode | binary | metric | T1 | T4 | T12 | S4 | S12 | s | 1/s |
|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|
| parse_1m | e2e | candidate | e2e_ms | 3,913 | 2,166 | 1,819 | 1.81 | 2.15 | 0.42 | 2.4 |
| parse_1m | phases | candidate | parse_ms | 3,911 | 2,160 | 1,818 | 1.81 | 2.15 | 0.42 | 2.4 |

## Raw samples (ms per input; one value per process, in rep order)

- parse_1m e2e candidate t=1 e2e_ms: [3913.0, 3912.0, 3916.0, 3937.0, 3907.0]  load1 [2.41, 2.44, 2.32, 2.21, 2.46]
- parse_1m e2e candidate t=4 e2e_ms: [2154.0, 2168.0, 2166.0, 2166.0, 2145.0]  load1 [2.41, 2.3, 2.21, 2.12, 2.59]
- parse_1m e2e candidate t=12 e2e_ms: [1820.0, 1819.0, 1814.0, 1811.0, 1820.0]  load1 [2.3, 2.44, 2.32, 2.59, 2.59]
- parse_1m phases candidate t=1 parse_ms: [3903.0, 3911.0, 3934.0, 3919.0, 3896.0]  load1 [2.4, 2.66, 2.53, 2.37, 2.54]
- parse_1m phases candidate t=4 parse_ms: [2186.0, 2160.0, 2148.0, 2149.0, 2177.0]  load1 [2.28, 2.28, 2.41, 2.37, 2.58]
- parse_1m phases candidate t=12 parse_ms: [1818.0, 1818.0, 1808.0, 1825.0, 1816.0]  load1 [2.28, 2.66, 2.53, 2.58, 2.54]

