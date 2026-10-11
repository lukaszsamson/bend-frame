# W0 summary: w8-refscan-prov

- run `w8-refscan-prov`: 2026-10-11T19:35:42+00:00, commit 4cf2e52058 dirty=True src 16e2fecde1, bend bend 2.0.36, load at start [2.62, 2.69, 2.72], provisional=True
- load (1 min) before/after every process: min 2.4 median 2.5 max 2.7
- 75 valid processes, 0 invalid/failed

## Timings (ms; median [min..max] n) and candidate/baseline ratio

key metric per row: compute_ms (queries), parse_ms (parse), e2e_ms (e2e); ms per input for batched controls

| workload | mode | metric | thr | baseline | candidate | ratio c/b | load max |
|---|---|---|---:|---|---|---:|---:|
| q1_1m | e2e | e2e_ms | 1 | - | 620 [616..634] n=5 | - | 3 |
| q1_1m | e2e | e2e_ms | 4 | - | 376 [367..378] n=5 | - | 3 |
| q1_1m | e2e | e2e_ms | 12 | - | 331 [328..333] n=5 | - | 3 |
| q2_1m | e2e | e2e_ms | 1 | - | 640 [636..665] n=5 | - | 3 |
| q2_1m | e2e | e2e_ms | 4 | - | 387 [383..391] n=5 | - | 3 |
| q2_1m | e2e | e2e_ms | 12 | - | 346 [335..347] n=5 | - | 3 |
| q3_1m | e2e | e2e_ms | 1 | - | 634 [632..635] n=5 | - | 3 |
| q3_1m | e2e | e2e_ms | 4 | - | 377 [376..382] n=5 | - | 3 |
| q3_1m | e2e | e2e_ms | 12 | - | 330 [327..332] n=5 | - | 3 |
| q4_1m | e2e | e2e_ms | 1 | - | 637 [635..648] n=5 | - | 2 |
| q4_1m | e2e | e2e_ms | 4 | - | 379 [378..380] n=5 | - | 2 |
| q4_1m | e2e | e2e_ms | 12 | - | 332 [332..334] n=5 | - | 2 |
| q5_1m | e2e | e2e_ms | 1 | - | 630 [629..633] n=5 | - | 3 |
| q5_1m | e2e | e2e_ms | 4 | - | 375 [371..377] n=5 | - | 3 |
| q5_1m | e2e | e2e_ms | 12 | - | 329 [325..332] n=5 | - | 3 |

## Phases (G6): medians in ms per input (parse = read + walk; prep = input-preservation clone; compute; check = output/validation hash)

| workload | binary | thr | read | walk | parse | prep | compute | check | compute+check | e2e (e2e mode) | rss MB (phases) | rss MB (e2e) |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|

## Thread scaling (G2): speedup = median(1 thread) / median(N threads); serial fraction s from Amdahl with N = 12

s = (1/S - 1/12) / (1 - 1/12) from the 12-thread speedup S; 1/s is the speedup even infinite parallelism would give at that serial fraction. Today nothing forks, so S ~ 1 (s ~ 1) is expected at the baseline; G2 needs S >= 3 (q1-q6 compute) and >= 4 (parse), i.e. s <= 1/3 (parse: 1/4 is not enough: needs s <= ~0.2).

| workload | mode | binary | metric | T1 | T4 | T12 | S4 | S12 | s | 1/s |
|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|
| q1_1m | e2e | candidate | e2e_ms | 620 | 376 | 331 | 1.65 | 1.87 | 0.49 | 2.0 |
| q2_1m | e2e | candidate | e2e_ms | 640 | 387 | 346 | 1.65 | 1.85 | 0.50 | 2.0 |
| q3_1m | e2e | candidate | e2e_ms | 634 | 377 | 330 | 1.68 | 1.92 | 0.48 | 2.1 |
| q4_1m | e2e | candidate | e2e_ms | 637 | 379 | 332 | 1.68 | 1.92 | 0.48 | 2.1 |
| q5_1m | e2e | candidate | e2e_ms | 630 | 375 | 329 | 1.68 | 1.91 | 0.48 | 2.1 |

## Raw samples (ms per input; one value per process, in rep order)

- q1_1m e2e candidate t=1 e2e_ms: [630.0, 634.0, 618.0, 616.0, 620.0]  load1 [2.62, 2.62, 2.62, 2.65, 2.65]
- q1_1m e2e candidate t=4 e2e_ms: [367.0, 376.0, 376.0, 369.0, 378.0]  load1 [2.62, 2.62, 2.65, 2.65, 2.65]
- q1_1m e2e candidate t=12 e2e_ms: [331.0, 331.0, 333.0, 331.0, 328.0]  load1 [2.62, 2.62, 2.62, 2.65, 2.65]
- q2_1m e2e candidate t=1 e2e_ms: [636.0, 653.0, 665.0, 640.0, 638.0]  load1 [2.65, 2.68, 2.68, 2.68, 2.68]
- q2_1m e2e candidate t=4 e2e_ms: [388.0, 387.0, 391.0, 383.0, 384.0]  load1 [2.65, 2.65, 2.68, 2.68, 2.68]
- q2_1m e2e candidate t=12 e2e_ms: [347.0, 346.0, 347.0, 335.0, 336.0]  load1 [2.65, 2.68, 2.68, 2.68, 2.68]
- q3_1m e2e candidate t=1 e2e_ms: [634.0, 632.0, 633.0, 635.0, 634.0]  load1 [2.55, 2.55, 2.55, 2.55, 2.42]
- q3_1m e2e candidate t=4 e2e_ms: [377.0, 376.0, 382.0, 376.0, 379.0]  load1 [2.55, 2.55, 2.55, 2.42, 2.42]
- q3_1m e2e candidate t=12 e2e_ms: [330.0, 331.0, 332.0, 329.0, 327.0]  load1 [2.55, 2.55, 2.55, 2.42, 2.42]
- q4_1m e2e candidate t=1 e2e_ms: [641.0, 636.0, 637.0, 635.0, 648.0]  load1 [2.42, 2.42, 2.39, 2.39, 2.39]
- q4_1m e2e candidate t=4 e2e_ms: [379.0, 380.0, 378.0, 379.0, 379.0]  load1 [2.42, 2.42, 2.39, 2.39, 2.39]
- q4_1m e2e candidate t=12 e2e_ms: [334.0, 333.0, 332.0, 332.0, 332.0]  load1 [2.42, 2.42, 2.42, 2.39, 2.39]
- q5_1m e2e candidate t=1 e2e_ms: [632.0, 630.0, 630.0, 629.0, 633.0]  load1 [2.39, 2.52, 2.52, 2.52, 2.4]
- q5_1m e2e candidate t=4 e2e_ms: [371.0, 376.0, 375.0, 374.0, 377.0]  load1 [2.39, 2.52, 2.52, 2.52, 2.52]
- q5_1m e2e candidate t=12 e2e_ms: [325.0, 329.0, 329.0, 332.0, 331.0]  load1 [2.52, 2.52, 2.52, 2.52, 2.52]

