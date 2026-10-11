# W0 summary: w8-ctl-v01-prov

- run `w8-ctl-v01-prov`: 2026-10-11T19:32:15+00:00, commit 4cf2e52058 dirty=True src 16e2fecde1, bend bend 2.0.36, load at start [3.29, 2.92, 2.8], provisional=True
- load (1 min) before/after every process: min 3.3 median 3.3 max 3.3
- 20 valid processes, 0 invalid/failed

## Timings (ms; median [min..max] n) and candidate/baseline ratio

key metric per row: compute_ms (queries), parse_ms (parse), e2e_ms (e2e); ms per input for batched controls

| workload | mode | metric | thr | baseline | candidate | ratio c/b | load max |
|---|---|---|---:|---|---|---:|---:|
| ctl_q3_1k | phases | compute_ms | 1 | 0.175 [0.175..0.250] n=5 | 0.300 [0.275..0.300] n=5 | 1.71 | 3 |
| ctl_q5_1k | phases | compute_ms | 1 | 0.200 [0.200..0.225] n=5 | 0.275 [0.250..0.275] n=5 | 1.38 | 3 |

## Phases (G6): medians in ms per input (parse = read + walk; prep = input-preservation clone; compute; check = output/validation hash)

| workload | binary | thr | read | walk | parse | prep | compute | check | compute+check | e2e (e2e mode) | rss MB (phases) | rss MB (e2e) |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| ctl_q3_1k | baseline | 1 | 3.88 | 0.000 | 3.88 | 0.000 | 0.175 | 0.025 | 0.200 | - | 9.40 | - |
| ctl_q3_1k | candidate | 1 | 3.85 | 0.000 | 3.88 | 0.000 | 0.300 | 0.025 | 0.325 | - | 10.2 | - |
| ctl_q5_1k | baseline | 1 | 3.92 | 0.000 | 3.92 | 0.000 | 0.200 | 0.025 | 0.225 | - | 9.49 | - |
| ctl_q5_1k | candidate | 1 | 3.88 | 0.000 | 3.88 | 0.000 | 0.275 | 0.025 | 0.300 | - | 10.1 | - |

## Thread scaling (G2): speedup = median(1 thread) / median(N threads); serial fraction s from Amdahl with N = 12

s = (1/S - 1/12) / (1 - 1/12) from the 12-thread speedup S; 1/s is the speedup even infinite parallelism would give at that serial fraction. Today nothing forks, so S ~ 1 (s ~ 1) is expected at the baseline; G2 needs S >= 3 (q1-q6 compute) and >= 4 (parse), i.e. s <= 1/3 (parse: 1/4 is not enough: needs s <= ~0.2).

| workload | mode | binary | metric | T1 | T4 | T12 | S4 | S12 | s | 1/s |
|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|

## Raw samples (ms per input; one value per process, in rep order)

- ctl_q3_1k phases baseline t=1 compute_ms: [0.25, 0.2, 0.17, 0.17, 0.17]  load1 [3.29, 3.29, 3.29, 3.29, 3.29]
- ctl_q3_1k phases candidate t=1 compute_ms: [0.3, 0.3, 0.28, 0.28, 0.3]  load1 [3.29, 3.29, 3.29, 3.29, 3.29]
- ctl_q5_1k phases baseline t=1 compute_ms: [0.23, 0.2, 0.2, 0.2, 0.2]  load1 [3.29, 3.29, 3.29, 3.29, 3.29]
- ctl_q5_1k phases candidate t=1 compute_ms: [0.28, 0.25, 0.28, 0.28, 0.28]  load1 [3.29, 3.29, 3.29, 3.29, 3.29]

