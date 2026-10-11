# W0 summary: w8-scan-prov

- run `w8-scan-prov`: 2026-10-11T19:31:43+00:00, commit 4cf2e52058 dirty=True src 16e2fecde1, bend bend 2.0.36, load at start [3.44, 2.88, 2.78], provisional=True
- load (1 min) before/after every process: min 1.9 median 2.7 max 3.7
- 150 valid processes, 0 invalid/failed

## Timings (ms; median [min..max] n) and candidate/baseline ratio

key metric per row: compute_ms (queries), parse_ms (parse), e2e_ms (e2e); ms per input for batched controls

| workload | mode | metric | thr | baseline | candidate | ratio c/b | load max |
|---|---|---|---:|---|---|---:|---:|
| q1_1m | e2e | e2e_ms | 1 | 3,999 [3,973..4,078] n=5 | 616 [609..638] n=5 | 0.15 | 4 |
| q1_1m | e2e | e2e_ms | 4 | 2,220 [2,206..2,256] n=5 | 371 [363..386] n=5 | 0.17 | 4 |
| q1_1m | e2e | e2e_ms | 12 | 1,862 [1,814..1,907] n=5 | 316 [313..328] n=5 | 0.17 | 4 |
| q2_1m | e2e | e2e_ms | 1 | 3,992 [3,982..4,008] n=5 | 644 [641..647] n=5 | 0.16 | 3 |
| q2_1m | e2e | e2e_ms | 4 | 2,230 [2,222..2,270] n=5 | 383 [381..386] n=5 | 0.17 | 3 |
| q2_1m | e2e | e2e_ms | 12 | 1,828 [1,821..1,837] n=5 | 335 [332..338] n=5 | 0.18 | 3 |
| q3_1m | e2e | e2e_ms | 1 | 3,994 [3,990..4,026] n=5 | 626 [625..631] n=5 | 0.16 | 3 |
| q3_1m | e2e | e2e_ms | 4 | 2,225 [2,217..2,246] n=5 | 376 [375..380] n=5 | 0.17 | 3 |
| q3_1m | e2e | e2e_ms | 12 | 1,826 [1,821..1,836] n=5 | 328 [324..333] n=5 | 0.18 | 3 |
| q4_1m | e2e | e2e_ms | 1 | 4,028 [4,012..4,041] n=5 | 633 [631..636] n=5 | 0.16 | 3 |
| q4_1m | e2e | e2e_ms | 4 | 2,259 [2,241..2,269] n=5 | 382 [379..385] n=5 | 0.17 | 3 |
| q4_1m | e2e | e2e_ms | 12 | 1,853 [1,851..1,857] n=5 | 335 [329..354] n=5 | 0.18 | 3 |
| q5_1m | e2e | e2e_ms | 1 | 3,982 [3,974..4,089] n=5 | 636 [633..639] n=5 | 0.16 | 3 |
| q5_1m | e2e | e2e_ms | 4 | 2,217 [2,211..2,265] n=5 | 373 [371..375] n=5 | 0.17 | 2 |
| q5_1m | e2e | e2e_ms | 12 | 1,822 [1,817..1,828] n=5 | 327 [323..335] n=5 | 0.18 | 2 |

## Phases (G6): medians in ms per input (parse = read + walk; prep = input-preservation clone; compute; check = output/validation hash)

| workload | binary | thr | read | walk | parse | prep | compute | check | compute+check | e2e (e2e mode) | rss MB (phases) | rss MB (e2e) |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|

## Thread scaling (G2): speedup = median(1 thread) / median(N threads); serial fraction s from Amdahl with N = 12

s = (1/S - 1/12) / (1 - 1/12) from the 12-thread speedup S; 1/s is the speedup even infinite parallelism would give at that serial fraction. Today nothing forks, so S ~ 1 (s ~ 1) is expected at the baseline; G2 needs S >= 3 (q1-q6 compute) and >= 4 (parse), i.e. s <= 1/3 (parse: 1/4 is not enough: needs s <= ~0.2).

| workload | mode | binary | metric | T1 | T4 | T12 | S4 | S12 | s | 1/s |
|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|
| q1_1m | e2e | baseline | e2e_ms | 3,999 | 2,220 | 1,862 | 1.80 | 2.15 | 0.42 | 2.4 |
| q1_1m | e2e | candidate | e2e_ms | 616 | 371 | 316 | 1.66 | 1.95 | 0.47 | 2.1 |
| q2_1m | e2e | baseline | e2e_ms | 3,992 | 2,230 | 1,828 | 1.79 | 2.18 | 0.41 | 2.4 |
| q2_1m | e2e | candidate | e2e_ms | 644 | 383 | 335 | 1.68 | 1.92 | 0.48 | 2.1 |
| q3_1m | e2e | baseline | e2e_ms | 3,994 | 2,225 | 1,826 | 1.80 | 2.19 | 0.41 | 2.5 |
| q3_1m | e2e | candidate | e2e_ms | 626 | 376 | 328 | 1.66 | 1.91 | 0.48 | 2.1 |
| q4_1m | e2e | baseline | e2e_ms | 4,028 | 2,259 | 1,853 | 1.78 | 2.17 | 0.41 | 2.4 |
| q4_1m | e2e | candidate | e2e_ms | 633 | 382 | 335 | 1.66 | 1.89 | 0.49 | 2.1 |
| q5_1m | e2e | baseline | e2e_ms | 3,982 | 2,217 | 1,822 | 1.80 | 2.19 | 0.41 | 2.4 |
| q5_1m | e2e | candidate | e2e_ms | 636 | 373 | 327 | 1.71 | 1.94 | 0.47 | 2.1 |

## Raw samples (ms per input; one value per process, in rep order)

- q1_1m e2e baseline t=1 e2e_ms: [4078.0, 3986.0, 3973.0, 4060.0, 3999.0]  load1 [3.44, 3.71, 3.52, 3.32, 3.11]
- q1_1m e2e candidate t=1 e2e_ms: [638.0, 625.0, 609.0, 611.0, 616.0]  load1 [3.6, 3.71, 3.52, 3.32, 2.78]
- q1_1m e2e baseline t=4 e2e_ms: [2220.0, 2225.0, 2206.0, 2256.0, 2207.0]  load1 [3.56, 3.6, 3.32, 3.29, 2.94]
- q1_1m e2e candidate t=4 e2e_ms: [377.0, 386.0, 363.0, 364.0, 371.0]  load1 [3.6, 3.71, 3.52, 3.32, 3.11]
- q1_1m e2e baseline t=12 e2e_ms: [1862.0, 1814.0, 1862.0, 1907.0, 1843.0]  load1 [3.6, 3.71, 3.65, 3.11, 2.94]
- q1_1m e2e candidate t=12 e2e_ms: [317.0, 328.0, 316.0, 313.0, 315.0]  load1 [3.6, 3.71, 3.52, 3.32, 3.11]
- q2_1m e2e baseline t=1 e2e_ms: [4005.0, 3992.0, 3982.0, 4008.0, 3990.0]  load1 [2.78, 2.68, 2.62, 2.37, 2.16]
- q2_1m e2e candidate t=1 e2e_ms: [644.0, 644.0, 641.0, 647.0, 641.0]  load1 [2.8, 2.68, 2.62, 2.37, 2.95]
- q2_1m e2e baseline t=4 e2e_ms: [2229.0, 2245.0, 2230.0, 2222.0, 2270.0]  load1 [2.8, 2.74, 2.49, 2.26, 2.16]
- q2_1m e2e candidate t=4 e2e_ms: [382.0, 381.0, 386.0, 384.0, 383.0]  load1 [2.74, 2.68, 2.62, 2.37, 2.26]
- q2_1m e2e baseline t=12 e2e_ms: [1837.0, 1821.0, 1828.0, 1825.0, 1828.0]  load1 [2.8, 2.74, 2.62, 2.26, 2.95]
- q2_1m e2e candidate t=12 e2e_ms: [335.0, 337.0, 338.0, 332.0, 333.0]  load1 [2.74, 2.68, 2.62, 2.37, 2.16]
- q3_1m e2e baseline t=1 e2e_ms: [4026.0, 4010.0, 3990.0, 3993.0, 3994.0]  load1 [2.95, 2.68, 2.86, 2.71, 2.82]
- q3_1m e2e candidate t=1 e2e_ms: [627.0, 625.0, 626.0, 626.0, 631.0]  load1 [2.65, 2.68, 3.02, 2.71, 3.24]
- q3_1m e2e baseline t=4 e2e_ms: [2226.0, 2225.0, 2246.0, 2222.0, 2217.0]  load1 [2.79, 2.65, 2.71, 2.89, 2.92]
- q3_1m e2e candidate t=4 e2e_ms: [376.0, 380.0, 376.0, 375.0, 378.0]  load1 [2.65, 2.68, 2.86, 2.71, 2.82]
- q3_1m e2e baseline t=12 e2e_ms: [1821.0, 1836.0, 1822.0, 1826.0, 1826.0]  load1 [2.65, 2.68, 3.02, 2.82, 2.92]
- q3_1m e2e candidate t=12 e2e_ms: [328.0, 324.0, 327.0, 333.0, 333.0]  load1 [2.65, 2.68, 2.86, 2.71, 2.82]
- q4_1m e2e baseline t=1 e2e_ms: [4041.0, 4028.0, 4017.0, 4037.0, 4012.0]  load1 [3.24, 2.75, 2.61, 2.92, 2.62]
- q4_1m e2e candidate t=1 e2e_ms: [634.0, 631.0, 633.0, 632.0, 636.0]  load1 [3.06, 2.75, 2.61, 2.48, 2.57]
- q4_1m e2e baseline t=4 e2e_ms: [2260.0, 2246.0, 2259.0, 2269.0, 2241.0]  load1 [3.06, 2.9, 2.48, 2.76, 2.62]
- q4_1m e2e candidate t=4 e2e_ms: [385.0, 383.0, 380.0, 379.0, 382.0]  load1 [2.9, 2.75, 2.61, 2.92, 2.76]
- q4_1m e2e baseline t=12 e2e_ms: [1852.0, 1853.0, 1857.0, 1851.0, 1854.0]  load1 [3.06, 2.9, 2.61, 2.76, 2.57]
- q4_1m e2e candidate t=12 e2e_ms: [329.0, 354.0, 335.0, 329.0, 339.0]  load1 [2.9, 2.75, 2.61, 2.92, 2.76]
- q5_1m e2e baseline t=1 e2e_ms: [3974.0, 3994.0, 3982.0, 3974.0, 4089.0]  load1 [2.57, 2.38, 2.25, 2.15, 1.97]
- q5_1m e2e candidate t=1 e2e_ms: [635.0, 637.0, 636.0, 633.0, 639.0]  load1 [2.33, 2.38, 2.27, 2.15, 2.62]
- q5_1m e2e baseline t=4 e2e_ms: [2217.0, 2211.0, 2265.0, 2239.0, 2212.0]  load1 [2.45, 2.33, 2.15, 2.06, 1.9]
- q5_1m e2e candidate t=4 e2e_ms: [371.0, 375.0, 372.0, 373.0, 373.0]  load1 [2.33, 2.38, 2.25, 2.15, 1.97]
- q5_1m e2e baseline t=12 e2e_ms: [1821.0, 1828.0, 1822.0, 1817.0, 1826.0]  load1 [2.33, 2.38, 2.27, 2.06, 1.9]
- q5_1m e2e candidate t=12 e2e_ms: [327.0, 323.0, 335.0, 327.0, 325.0]  load1 [2.33, 2.38, 2.25, 2.15, 1.97]

