# W0 summary: w8-chunked-prov

- run `w8-chunked-prov`: 2026-10-11T19:26:33+00:00, commit 4cf2e52058 dirty=True src 16e2fecde1, bend bend 2.0.36, load at start [3.67, 2.9, 2.79], provisional=True
- load (1 min) before/after every process: min 1.9 median 3.0 max 4.2
- 720 valid processes, 0 invalid/failed

## Timings (ms; median [min..max] n) and candidate/baseline ratio

key metric per row: compute_ms (queries), parse_ms (parse), e2e_ms (e2e); ms per input for batched controls

| workload | mode | metric | thr | baseline | candidate | ratio c/b | load max |
|---|---|---|---:|---|---|---:|---:|
| q1_1m | e2e | e2e_ms | 1 | - | 640 [638..645] n=5 | - | 3 |
| q1_1m | e2e | e2e_ms | 4 | - | 386 [383..402] n=5 | - | 3 |
| q1_1m | e2e | e2e_ms | 12 | - | 341 [339..343] n=5 | - | 3 |
| q1_1m | phases | compute_ms | 1 | - | 8.00 [8.00..12.0] n=5 | - | 4 |
| q1_1m | phases | compute_ms | 4 | - | 5.00 [4.00..5.00] n=5 | - | 4 |
| q1_1m | phases | compute_ms | 12 | - | 4.00 [4.00..5.00] n=5 | - | 4 |
| q2_1m | e2e | e2e_ms | 1 | - | 661 [660..666] n=5 | - | 3 |
| q2_1m | e2e | e2e_ms | 4 | - | 400 [398..404] n=5 | - | 3 |
| q2_1m | e2e | e2e_ms | 12 | - | 353 [350..356] n=5 | - | 3 |
| q2_1m | phases | compute_ms | 1 | - | 18.0 [17.0..19.0] n=5 | - | 3 |
| q2_1m | phases | compute_ms | 4 | - | 8.00 [7.00..8.00] n=5 | - | 3 |
| q2_1m | phases | compute_ms | 12 | - | 6.00 [6.00..7.00] n=5 | - | 3 |
| q3_1m | e2e | e2e_ms | 1 | - | 652 [652..655] n=5 | - | 3 |
| q3_1m | e2e | e2e_ms | 4 | - | 397 [391..437] n=5 | - | 3 |
| q3_1m | e2e | e2e_ms | 12 | - | 350 [346..371] n=5 | - | 3 |
| q3_1m | phases | compute_ms | 1 | - | 22.0 [21.0..22.0] n=5 | - | 3 |
| q3_1m | phases | compute_ms | 4 | - | 14.0 [13.0..14.0] n=5 | - | 3 |
| q3_1m | phases | compute_ms | 12 | - | 15.0 [14.0..15.0] n=5 | - | 3 |
| q4_1m | e2e | e2e_ms | 1 | - | 645 [643..671] n=5 | - | 4 |
| q4_1m | e2e | e2e_ms | 4 | - | 394 [393..397] n=5 | - | 4 |
| q4_1m | e2e | e2e_ms | 12 | - | 350 [348..353] n=5 | - | 4 |
| q4_1m | phases | compute_ms | 1 | - | 13.0 [13.0..14.0] n=5 | - | 4 |
| q4_1m | phases | compute_ms | 4 | - | 14.0 [13.0..14.0] n=5 | - | 4 |
| q4_1m | phases | compute_ms | 12 | - | 14.0 [13.0..15.0] n=5 | - | 4 |
| q5_1m | e2e | e2e_ms | 1 | - | 647 [643..671] n=5 | - | 3 |
| q5_1m | e2e | e2e_ms | 4 | - | 394 [391..402] n=5 | - | 3 |
| q5_1m | e2e | e2e_ms | 12 | - | 348 [344..349] n=5 | - | 3 |
| q5_1m | phases | compute_ms | 1 | - | 10.0 [10.0..11.0] n=5 | - | 4 |
| q5_1m | phases | compute_ms | 4 | - | 10.0 [10.0..11.0] n=5 | - | 4 |
| q5_1m | phases | compute_ms | 12 | - | 10.0 [10.0..12.0] n=5 | - | 4 |
| q6_1m | e2e | e2e_ms | 1 | - | 682 [680..687] n=5 | - | 3 |
| q6_1m | e2e | e2e_ms | 4 | - | 397 [396..400] n=5 | - | 3 |
| q6_1m | e2e | e2e_ms | 12 | - | 353 [350..356] n=5 | - | 3 |
| q6_1m | phases | compute_ms | 1 | - | 50.0 [50.0..52.0] n=5 | - | 3 |
| q6_1m | phases | compute_ms | 4 | - | 16.0 [16.0..17.0] n=5 | - | 3 |
| q6_1m | phases | compute_ms | 12 | - | 16.0 [16.0..16.0] n=5 | - | 3 |
| parse_1m | e2e | e2e_ms | 1 | - | 644 [642..676] n=5 | - | 3 |
| parse_1m | e2e | e2e_ms | 4 | - | 390 [388..397] n=5 | - | 3 |
| parse_1m | e2e | e2e_ms | 12 | - | 344 [341..348] n=5 | - | 3 |
| parse_1m | phases | parse_ms | 1 | - | 634 [630..710] n=5 | - | 3 |
| parse_1m | phases | parse_ms | 4 | - | 382 [379..409] n=5 | - | 3 |
| parse_1m | phases | parse_ms | 12 | - | 339 [335..347] n=5 | - | 3 |
| filter_sel0_1m | phases | compute_ms | 1 | - | 13.0 [13.0..16.0] n=5 | - | 3 |
| filter_sel0_1m | phases | compute_ms | 4 | - | 6.00 [5.00..6.00] n=5 | - | 3 |
| filter_sel0_1m | phases | compute_ms | 12 | - | 5.00 [5.00..6.00] n=5 | - | 3 |
| filter_sel1_1m | phases | compute_ms | 1 | - | 13.0 [12.0..13.0] n=5 | - | 3 |
| filter_sel1_1m | phases | compute_ms | 4 | - | 5.00 [5.00..6.00] n=5 | - | 3 |
| filter_sel1_1m | phases | compute_ms | 12 | - | 5.00 [4.00..6.00] n=5 | - | 3 |
| filter_sel50_1m | phases | compute_ms | 1 | - | 19.0 [18.0..19.0] n=5 | - | 2 |
| filter_sel50_1m | phases | compute_ms | 4 | - | 7.00 [7.00..7.00] n=5 | - | 2 |
| filter_sel50_1m | phases | compute_ms | 12 | - | 7.00 [6.00..7.00] n=5 | - | 2 |
| filter_sel100_1m | phases | compute_ms | 1 | - | 30.0 [29.0..35.0] n=5 | - | 2 |
| filter_sel100_1m | phases | compute_ms | 4 | - | 11.0 [11.0..11.0] n=5 | - | 2 |
| filter_sel100_1m | phases | compute_ms | 12 | - | 13.0 [12.0..13.0] n=5 | - | 2 |
| nunique_1m | phases | compute_ms | 1 | - | 16.0 [16.0..16.0] n=5 | - | 2 |
| nunique_1m | phases | compute_ms | 4 | - | 16.0 [15.0..17.0] n=5 | - | 2 |
| nunique_1m | phases | compute_ms | 12 | - | 16.0 [16.0..16.0] n=5 | - | 2 |
| str_group_100k | phases | compute_ms | 1 | - | 12.0 [12.0..13.0] n=5 | - | 2 |
| str_group_100k | phases | compute_ms | 4 | - | 12.0 [12.0..13.0] n=5 | - | 2 |
| str_group_100k | phases | compute_ms | 12 | - | 12.0 [12.0..13.0] n=5 | - | 2 |
| str_unique_100k | phases | compute_ms | 1 | - | 12.0 [12.0..13.0] n=5 | - | 2 |
| str_unique_100k | phases | compute_ms | 4 | - | 12.0 [12.0..13.0] n=5 | - | 2 |
| str_unique_100k | phases | compute_ms | 12 | - | 12.0 [12.0..13.0] n=5 | - | 2 |
| str_join_100k | phases | compute_ms | 1 | - | 24.0 [24.0..24.0] n=5 | - | 2 |
| str_join_100k | phases | compute_ms | 4 | - | 24.0 [24.0..27.0] n=5 | - | 2 |
| str_join_100k | phases | compute_ms | 12 | - | 24.0 [24.0..25.0] n=5 | - | 2 |
| str_group_300k | phases | compute_ms | 1 | - | 42.0 [42.0..43.0] n=5 | - | 2 |
| str_group_300k | phases | compute_ms | 4 | - | 42.0 [42.0..44.0] n=5 | - | 2 |
| str_group_300k | phases | compute_ms | 12 | - | 43.0 [42.0..44.0] n=5 | - | 2 |
| str_unique_300k | phases | compute_ms | 1 | - | 42.0 [42.0..44.0] n=5 | - | 2 |
| str_unique_300k | phases | compute_ms | 4 | - | 42.0 [42.0..48.0] n=5 | - | 2 |
| str_unique_300k | phases | compute_ms | 12 | - | 43.0 [42.0..43.0] n=5 | - | 2 |
| str_join_300k | phases | compute_ms | 1 | - | 91.0 [90.0..92.0] n=5 | - | 2 |
| str_join_300k | phases | compute_ms | 4 | - | 91.0 [90.0..96.0] n=5 | - | 2 |
| str_join_300k | phases | compute_ms | 12 | - | 91.0 [90.0..93.0] n=5 | - | 2 |
| str_group_1m | phases | compute_ms | 1 | - | 127 [126..132] n=5 | - | 2 |
| str_group_1m | phases | compute_ms | 4 | - | 127 [126..154] n=5 | - | 2 |
| str_group_1m | phases | compute_ms | 12 | - | 130 [128..131] n=5 | - | 2 |
| str_unique_1m | phases | compute_ms | 1 | - | 127 [126..127] n=5 | - | 2 |
| str_unique_1m | phases | compute_ms | 4 | - | 131 [127..152] n=5 | - | 2 |
| str_unique_1m | phases | compute_ms | 12 | - | 129 [127..182] n=5 | - | 2 |
| str_join_1m | phases | compute_ms | 1 | - | 360 [354..362] n=5 | - | 3 |
| str_join_1m | phases | compute_ms | 4 | - | 359 [355..366] n=5 | - | 3 |
| str_join_1m | phases | compute_ms | 12 | - | 362 [360..389] n=5 | - | 3 |
| lp_group_100k | phases | compute_ms | 1 | - | 31.0 [30.0..31.0] n=5 | - | 3 |
| lp_group_100k | phases | compute_ms | 4 | - | 31.0 [30.0..31.0] n=5 | - | 3 |
| lp_group_100k | phases | compute_ms | 12 | - | 31.0 [31.0..32.0] n=5 | - | 3 |
| lp_unique_100k | phases | compute_ms | 1 | - | 31.0 [30.0..32.0] n=5 | - | 3 |
| lp_unique_100k | phases | compute_ms | 4 | - | 31.0 [30.0..33.0] n=5 | - | 3 |
| lp_unique_100k | phases | compute_ms | 12 | - | 31.0 [30.0..31.0] n=5 | - | 3 |
| lp_join_100k | phases | compute_ms | 1 | - | 61.0 [59.0..62.0] n=5 | - | 3 |
| lp_join_100k | phases | compute_ms | 4 | - | 62.0 [60.0..67.0] n=5 | - | 3 |
| lp_join_100k | phases | compute_ms | 12 | - | 61.0 [60.0..61.0] n=5 | - | 3 |
| lp_group_300k | phases | compute_ms | 1 | - | 86.0 [83.0..90.0] n=5 | - | 3 |
| lp_group_300k | phases | compute_ms | 4 | - | 84.0 [82.0..88.0] n=5 | - | 3 |
| lp_group_300k | phases | compute_ms | 12 | - | 83.0 [83.0..85.0] n=5 | - | 3 |
| lp_unique_300k | phases | compute_ms | 1 | - | 83.0 [81.0..85.0] n=5 | - | 3 |
| lp_unique_300k | phases | compute_ms | 4 | - | 83.0 [82.0..84.0] n=5 | - | 3 |
| lp_unique_300k | phases | compute_ms | 12 | - | 84.0 [82.0..89.0] n=5 | - | 3 |
| lp_join_300k | phases | compute_ms | 1 | - | 185 [180..189] n=5 | - | 3 |
| lp_join_300k | phases | compute_ms | 4 | - | 186 [183..197] n=5 | - | 3 |
| lp_join_300k | phases | compute_ms | 12 | - | 183 [182..189] n=5 | - | 3 |
| q1_100k | phases | compute_ms | 1 | - | 1.00 [1.00..1.00] n=5 | - | 3 |
| q1_100k | phases | compute_ms | 4 | - | 1.00 [0.000..1.00] n=5 | - | 3 |
| q1_100k | phases | compute_ms | 12 | - | 1.00 [0.000..1.00] n=5 | - | 3 |
| q2_100k | phases | compute_ms | 1 | - | 1.62 [1.50..1.62] n=5 | - | 3 |
| q2_100k | phases | compute_ms | 4 | - | 0.625 [0.625..0.750] n=5 | - | 3 |
| q2_100k | phases | compute_ms | 12 | - | 0.750 [0.750..0.875] n=5 | - | 3 |
| q3_100k | phases | compute_ms | 1 | - | 2.00 [2.00..3.00] n=5 | - | 3 |
| q3_100k | phases | compute_ms | 4 | - | 2.00 [2.00..2.00] n=5 | - | 3 |
| q3_100k | phases | compute_ms | 12 | - | 2.00 [2.00..2.00] n=5 | - | 3 |
| q4_100k | phases | compute_ms | 1 | - | 2.00 [1.00..2.00] n=5 | - | 3 |
| q4_100k | phases | compute_ms | 4 | - | 2.00 [1.00..2.00] n=5 | - | 3 |
| q4_100k | phases | compute_ms | 12 | - | 2.00 [1.00..2.00] n=5 | - | 3 |
| q5_100k | phases | compute_ms | 1 | - | 1.00 [1.00..2.00] n=5 | - | 3 |
| q5_100k | phases | compute_ms | 4 | - | 1.00 [1.00..2.00] n=5 | - | 3 |
| q5_100k | phases | compute_ms | 12 | - | 2.00 [1.00..2.00] n=5 | - | 3 |
| q6_100k | phases | compute_ms | 1 | - | 5.00 [5.00..6.00] n=5 | - | 3 |
| q6_100k | phases | compute_ms | 4 | - | 2.00 [2.00..2.00] n=5 | - | 3 |
| q6_100k | phases | compute_ms | 12 | - | 2.00 [2.00..2.00] n=5 | - | 3 |
| ctl_q1_1k | phases | compute_ms | 1 | - | 0.046 [0.044..0.046] n=5 | - | 3 |
| ctl_q1_1k | phases | compute_ms | 4 | - | 0.046 [0.046..0.048] n=5 | - | 3 |
| ctl_q1_1k | phases | compute_ms | 12 | - | 0.048 [0.048..0.050] n=5 | - | 3 |
| ctl_q2_1k | phases | compute_ms | 1 | - | 0.054 [0.054..0.058] n=5 | - | 3 |
| ctl_q2_1k | phases | compute_ms | 4 | - | 0.056 [0.054..0.058] n=5 | - | 3 |
| ctl_q2_1k | phases | compute_ms | 12 | - | 0.056 [0.056..0.058] n=5 | - | 3 |
| ctl_q3_1k | phases | compute_ms | 1 | - | 0.325 [0.300..0.325] n=5 | - | 3 |
| ctl_q3_1k | phases | compute_ms | 4 | - | 0.300 [0.300..0.325] n=5 | - | 3 |
| ctl_q3_1k | phases | compute_ms | 12 | - | 0.325 [0.300..0.325] n=5 | - | 3 |
| ctl_q4_1k | phases | compute_ms | 1 | - | 0.300 [0.275..0.300] n=5 | - | 3 |
| ctl_q4_1k | phases | compute_ms | 4 | - | 0.275 [0.275..0.300] n=5 | - | 3 |
| ctl_q4_1k | phases | compute_ms | 12 | - | 0.300 [0.275..0.300] n=5 | - | 3 |
| ctl_q5_1k | phases | compute_ms | 1 | - | 0.250 [0.250..0.275] n=5 | - | 3 |
| ctl_q5_1k | phases | compute_ms | 4 | - | 0.275 [0.250..0.275] n=5 | - | 3 |
| ctl_q5_1k | phases | compute_ms | 12 | - | 0.275 [0.250..0.275] n=5 | - | 3 |
| ctl_q6_1k | phases | compute_ms | 1 | - | 0.200 [0.200..0.225] n=5 | - | 3 |
| ctl_q6_1k | phases | compute_ms | 4 | - | 0.225 [0.225..0.225] n=5 | - | 3 |
| ctl_q6_1k | phases | compute_ms | 12 | - | 0.225 [0.225..0.225] n=5 | - | 3 |

## Phases (G6): medians in ms per input (parse = read + walk; prep = input-preservation clone; compute; check = output/validation hash)

| workload | binary | thr | read | walk | parse | prep | compute | check | compute+check | e2e (e2e mode) | rss MB (phases) | rss MB (e2e) |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| q1_1m | candidate | 1 | 629 | 4.00 | 633 | 4.00 | 8.00 | 1.00 | 9.00 | 640 | 242 | 212 |
| q1_1m | candidate | 4 | 381 | 4.00 | 386 | 3.00 | 5.00 | 1.00 | 6.00 | 386 | 253 | 224 |
| q1_1m | candidate | 12 | 335 | 5.00 | 340 | 3.00 | 4.00 | 1.00 | 5.00 | 341 | 275 | 245 |
| q2_1m | candidate | 1 | 630 | 4.00 | 635 | 3.00 | 18.0 | 13.0 | 31.0 | 661 | 258 | 224 |
| q2_1m | candidate | 4 | 380 | 5.00 | 384 | 3.00 | 8.00 | 13.0 | 21.0 | 400 | 265 | 235 |
| q2_1m | candidate | 12 | 333 | 5.00 | 338 | 3.00 | 6.00 | 13.0 | 20.0 | 353 | 286 | 257 |
| q3_1m | candidate | 1 | 631 | 5.00 | 636 | 3.00 | 22.0 | 0.000 | 22.0 | 652 | 254 | 225 |
| q3_1m | candidate | 4 | 382 | 5.00 | 386 | 4.00 | 14.0 | 1.00 | 14.0 | 397 | 265 | 236 |
| q3_1m | candidate | 12 | 337 | 5.00 | 342 | 3.00 | 15.0 | 0.000 | 15.0 | 350 | 287 | 258 |
| q4_1m | candidate | 1 | 634 | 5.00 | 639 | 3.00 | 13.0 | 0.000 | 14.0 | 645 | 234 | 200 |
| q4_1m | candidate | 4 | 383 | 5.00 | 388 | 3.00 | 14.0 | 0.000 | 14.0 | 394 | 245 | 212 |
| q4_1m | candidate | 12 | 339 | 5.00 | 344 | 3.00 | 14.0 | 0.000 | 14.0 | 350 | 267 | 233 |
| q5_1m | candidate | 1 | 634 | 4.00 | 638 | 3.00 | 10.0 | 0.000 | 10.0 | 647 | 234 | 201 |
| q5_1m | candidate | 4 | 382 | 5.00 | 387 | 3.00 | 10.0 | 0.000 | 10.0 | 394 | 245 | 212 |
| q5_1m | candidate | 12 | 336 | 5.00 | 341 | 3.00 | 10.0 | 0.000 | 10.0 | 348 | 267 | 233 |
| q6_1m | candidate | 1 | 639 | 5.00 | 644 | 3.00 | 50.0 | 0.000 | 50.0 | 682 | 226 | 192 |
| q6_1m | candidate | 4 | 389 | 5.00 | 394 | 4.00 | 16.0 | 0.000 | 16.0 | 397 | 284 | 251 |
| q6_1m | candidate | 12 | 337 | 4.00 | 341 | 4.00 | 16.0 | 0.000 | 16.0 | 353 | 306 | 272 |
| parse_1m | candidate | 1 | 630 | 5.00 | 634 | 4.00 | 0.000 | 12.0 | 12.0 | 644 | 216 | 187 |
| parse_1m | candidate | 4 | 377 | 4.00 | 382 | 4.00 | 0.000 | 13.0 | 13.0 | 390 | 227 | 198 |
| parse_1m | candidate | 12 | 334 | 5.00 | 339 | 4.00 | 0.000 | 12.0 | 12.0 | 344 | 249 | 219 |
| filter_sel0_1m | candidate | 1 | 632 | 5.00 | 637 | 3.00 | 13.0 | 0.000 | 13.0 | - | 250 | - |
| filter_sel0_1m | candidate | 4 | 380 | 5.00 | 385 | 3.00 | 6.00 | 0.000 | 6.00 | - | 260 | - |
| filter_sel0_1m | candidate | 12 | 333 | 4.00 | 337 | 4.00 | 5.00 | 0.000 | 5.00 | - | 282 | - |
| filter_sel1_1m | candidate | 1 | 629 | 5.00 | 634 | 3.00 | 13.0 | 0.000 | 13.0 | - | 250 | - |
| filter_sel1_1m | candidate | 4 | 379 | 4.00 | 383 | 4.00 | 5.00 | 0.000 | 5.00 | - | 261 | - |
| filter_sel1_1m | candidate | 12 | 333 | 4.00 | 337 | 4.00 | 5.00 | 0.000 | 6.00 | - | 283 | - |
| filter_sel50_1m | candidate | 1 | 630 | 5.00 | 634 | 3.00 | 19.0 | 6.00 | 25.0 | - | 267 | - |
| filter_sel50_1m | candidate | 4 | 378 | 5.00 | 383 | 3.00 | 7.00 | 7.00 | 14.0 | - | 278 | - |
| filter_sel50_1m | candidate | 12 | 332 | 5.00 | 337 | 3.00 | 7.00 | 7.00 | 14.0 | - | 300 | - |
| filter_sel100_1m | candidate | 1 | 627 | 5.00 | 632 | 4.00 | 30.0 | 12.0 | 43.0 | - | 313 | - |
| filter_sel100_1m | candidate | 4 | 379 | 5.00 | 383 | 3.00 | 11.0 | 12.0 | 23.0 | - | 324 | - |
| filter_sel100_1m | candidate | 12 | 331 | 5.00 | 336 | 3.00 | 13.0 | 13.0 | 26.0 | - | 346 | - |
| nunique_1m | candidate | 1 | 132 | 1.00 | 133 | 0.000 | 16.0 | 0.000 | 16.0 | - | 61.9 | - |
| nunique_1m | candidate | 4 | 99.0 | 0.000 | 99.0 | 0.000 | 16.0 | 0.000 | 16.0 | - | 67.6 | - |
| nunique_1m | candidate | 12 | 94.0 | 1.00 | 94.0 | 0.000 | 16.0 | 0.000 | 16.0 | - | 71.0 | - |
| str_group_100k | candidate | 1 | 68.0 | 7.00 | 75.0 | 0.000 | 12.0 | 27.0 | 39.0 | - | 70.5 | - |
| str_group_100k | candidate | 4 | 46.0 | 7.00 | 53.0 | 0.000 | 12.0 | 27.0 | 39.0 | - | 74.2 | - |
| str_group_100k | candidate | 12 | 45.0 | 6.00 | 51.0 | 1.00 | 12.0 | 27.0 | 39.0 | - | 77.5 | - |
| str_unique_100k | candidate | 1 | 68.0 | 6.00 | 75.0 | 1.00 | 12.0 | 27.0 | 39.0 | - | 69.5 | - |
| str_unique_100k | candidate | 4 | 47.0 | 6.00 | 53.0 | 0.000 | 12.0 | 27.0 | 39.0 | - | 73.1 | - |
| str_unique_100k | candidate | 12 | 44.0 | 7.00 | 51.0 | 0.000 | 12.0 | 27.0 | 39.0 | - | 76.3 | - |
| str_join_100k | candidate | 1 | 130 | 13.0 | 143 | 1.00 | 24.0 | 48.0 | 72.0 | - | 110 | - |
| str_join_100k | candidate | 4 | 92.0 | 13.0 | 105 | 1.00 | 24.0 | 48.0 | 72.0 | - | 115 | - |
| str_join_100k | candidate | 12 | 86.0 | 13.0 | 99.0 | 1.00 | 24.0 | 49.0 | 73.0 | - | 120 | - |
| str_group_300k | candidate | 1 | 182 | 21.0 | 203 | 1.00 | 42.0 | 84.0 | 126 | - | 226 | - |
| str_group_300k | candidate | 4 | 106 | 21.0 | 127 | 2.00 | 42.0 | 84.0 | 126 | - | 233 | - |
| str_group_300k | candidate | 12 | 95.0 | 21.0 | 116 | 2.00 | 43.0 | 84.0 | 127 | - | 238 | - |
| str_unique_300k | candidate | 1 | 182 | 21.0 | 203 | 1.00 | 42.0 | 83.0 | 125 | - | 222 | - |
| str_unique_300k | candidate | 4 | 106 | 21.0 | 127 | 1.00 | 42.0 | 83.0 | 125 | - | 229 | - |
| str_unique_300k | candidate | 12 | 94.0 | 21.0 | 115 | 1.00 | 43.0 | 83.0 | 126 | - | 234 | - |
| str_join_300k | candidate | 1 | 342 | 41.0 | 383 | 3.00 | 91.0 | 149 | 240 | - | 353 | - |
| str_join_300k | candidate | 4 | 200 | 42.0 | 242 | 3.00 | 91.0 | 149 | 240 | - | 362 | - |
| str_join_300k | candidate | 12 | 179 | 43.0 | 223 | 3.00 | 91.0 | 150 | 242 | - | 371 | - |
| str_group_1m | candidate | 1 | 577 | 72.0 | 647 | 4.00 | 127 | 279 | 406 | - | 630 | - |
| str_group_1m | candidate | 4 | 312 | 72.0 | 384 | 4.00 | 127 | 278 | 405 | - | 641 | - |
| str_group_1m | candidate | 12 | 264 | 72.0 | 336 | 4.00 | 130 | 278 | 408 | - | 647 | - |
| str_unique_1m | candidate | 1 | 579 | 71.0 | 649 | 4.00 | 127 | 276 | 402 | - | 622 | - |
| str_unique_1m | candidate | 4 | 311 | 72.0 | 383 | 3.00 | 131 | 276 | 406 | - | 633 | - |
| str_unique_1m | candidate | 12 | 263 | 72.0 | 335 | 3.00 | 129 | 277 | 406 | - | 638 | - |
| str_join_1m | candidate | 1 | 1,075 | 144 | 1,220 | 7.00 | 360 | 498 | 857 | - | 1,030 | - |
| str_join_1m | candidate | 4 | 574 | 140 | 714 | 6.00 | 359 | 497 | 855 | - | 1,046 | - |
| str_join_1m | candidate | 12 | 479 | 141 | 620 | 7.00 | 362 | 496 | 859 | - | 1,052 | - |
| lp_group_100k | candidate | 1 | 144 | 8.00 | 152 | 1.00 | 31.0 | 67.0 | 98.0 | - | 198 | - |
| lp_group_100k | candidate | 4 | 91.0 | 8.00 | 99.0 | 0.000 | 31.0 | 67.0 | 97.0 | - | 200 | - |
| lp_group_100k | candidate | 12 | 85.0 | 8.00 | 93.0 | 1.00 | 31.0 | 68.0 | 99.0 | - | 204 | - |
| lp_unique_100k | candidate | 1 | 143 | 7.00 | 150 | 1.00 | 31.0 | 67.0 | 98.0 | - | 196 | - |
| lp_unique_100k | candidate | 4 | 91.0 | 7.00 | 98.0 | 1.00 | 31.0 | 67.0 | 98.0 | - | 199 | - |
| lp_unique_100k | candidate | 12 | 84.0 | 8.00 | 94.0 | 1.00 | 31.0 | 67.0 | 97.0 | - | 203 | - |
| lp_join_100k | candidate | 1 | 282 | 16.0 | 298 | 1.00 | 61.0 | 138 | 199 | - | 311 | - |
| lp_join_100k | candidate | 4 | 178 | 16.0 | 198 | 1.00 | 62.0 | 137 | 197 | - | 314 | - |
| lp_join_100k | candidate | 12 | 163 | 19.0 | 183 | 1.00 | 61.0 | 137 | 198 | - | 321 | - |
| lp_group_300k | candidate | 1 | 388 | 24.0 | 411 | 2.00 | 86.0 | 202 | 287 | - | 522 | - |
| lp_group_300k | candidate | 4 | 214 | 24.0 | 237 | 2.00 | 84.0 | 201 | 284 | - | 528 | - |
| lp_group_300k | candidate | 12 | 186 | 27.0 | 212 | 1.00 | 83.0 | 202 | 285 | - | 531 | - |
| lp_unique_300k | candidate | 1 | 388 | 25.0 | 413 | 1.00 | 83.0 | 202 | 284 | - | 518 | - |
| lp_unique_300k | candidate | 4 | 215 | 25.0 | 240 | 2.00 | 83.0 | 200 | 283 | - | 523 | - |
| lp_unique_300k | candidate | 12 | 185 | 27.0 | 211 | 2.00 | 84.0 | 201 | 284 | - | 527 | - |
| lp_join_300k | candidate | 1 | 751 | 51.0 | 802 | 3.00 | 185 | 405 | 594 | - | 867 | - |
| lp_join_300k | candidate | 4 | 408 | 49.0 | 457 | 3.00 | 186 | 403 | 591 | - | 875 | - |
| lp_join_300k | candidate | 12 | 357 | 52.0 | 409 | 3.00 | 183 | 406 | 591 | - | 882 | - |
| q1_100k | candidate | 1 | 67.0 | 1.00 | 68.0 | 0.000 | 1.00 | 0.000 | 1.00 | - | 36.7 | - |
| q1_100k | candidate | 4 | 45.0 | 1.00 | 46.0 | 0.000 | 1.00 | 0.000 | 1.00 | - | 40.6 | - |
| q1_100k | candidate | 12 | 43.0 | 0.000 | 43.0 | 1.00 | 1.00 | 0.000 | 1.00 | - | 51.4 | - |
| q2_100k | candidate | 1 | 64.6 | 0.500 | 65.2 | 0.375 | 1.62 | 0.125 | 1.75 | - | 101 | - |
| q2_100k | candidate | 4 | 43.8 | 0.500 | 44.2 | 0.500 | 0.625 | 0.250 | 0.875 | - | 108 | - |
| q2_100k | candidate | 12 | 39.8 | 0.500 | 40.2 | 0.500 | 0.750 | 0.250 | 1.00 | - | 124 | - |
| q3_100k | candidate | 1 | 67.0 | 0.000 | 67.0 | 1.00 | 2.00 | 0.000 | 2.00 | - | 38.4 | - |
| q3_100k | candidate | 4 | 45.0 | 1.00 | 46.0 | 0.000 | 2.00 | 0.000 | 2.00 | - | 42.5 | - |
| q3_100k | candidate | 12 | 43.0 | 0.000 | 43.0 | 1.00 | 2.00 | 0.000 | 2.00 | - | 52.7 | - |
| q4_100k | candidate | 1 | 67.0 | 0.000 | 68.0 | 0.000 | 2.00 | 0.000 | 2.00 | - | 36.2 | - |
| q4_100k | candidate | 4 | 45.0 | 1.00 | 46.0 | 0.000 | 2.00 | 0.000 | 2.00 | - | 40.4 | - |
| q4_100k | candidate | 12 | 43.0 | 1.00 | 43.0 | 0.000 | 2.00 | 0.000 | 2.00 | - | 51.1 | - |
| q5_100k | candidate | 1 | 67.0 | 0.000 | 67.0 | 1.00 | 1.00 | 0.000 | 1.00 | - | 35.9 | - |
| q5_100k | candidate | 4 | 46.0 | 1.00 | 46.0 | 0.000 | 1.00 | 0.000 | 1.00 | - | 40.0 | - |
| q5_100k | candidate | 12 | 42.0 | 1.00 | 43.0 | 0.000 | 2.00 | 0.000 | 2.00 | - | 50.7 | - |
| q6_100k | candidate | 1 | 68.0 | 0.000 | 68.0 | 0.000 | 5.00 | 0.000 | 5.00 | - | 34.9 | - |
| q6_100k | candidate | 4 | 46.0 | 0.000 | 46.0 | 1.00 | 2.00 | 0.000 | 2.00 | - | 45.9 | - |
| q6_100k | candidate | 12 | 43.0 | 0.000 | 43.0 | 0.000 | 2.00 | 0.000 | 2.00 | - | 56.8 | - |
| ctl_q1_1k | candidate | 1 | 1.61 | 0.008 | 1.62 | 0.008 | 0.046 | 0.024 | 0.070 | - | 64.2 | - |
| ctl_q1_1k | candidate | 4 | 1.64 | 0.008 | 1.65 | 0.008 | 0.046 | 0.024 | 0.070 | - | 67.8 | - |
| ctl_q1_1k | candidate | 12 | 1.84 | 0.008 | 1.84 | 0.010 | 0.048 | 0.026 | 0.074 | - | 74.0 | - |
| ctl_q2_1k | candidate | 1 | 1.61 | 0.006 | 1.62 | 0.008 | 0.054 | 0.034 | 0.088 | - | 63.9 | - |
| ctl_q2_1k | candidate | 4 | 1.65 | 0.008 | 1.66 | 0.008 | 0.056 | 0.036 | 0.090 | - | 67.6 | - |
| ctl_q2_1k | candidate | 12 | 1.83 | 0.008 | 1.84 | 0.010 | 0.056 | 0.036 | 0.092 | - | 73.9 | - |
| ctl_q3_1k | candidate | 1 | 1.60 | 0.000 | 1.60 | 0.000 | 0.325 | 0.025 | 0.325 | - | 10.6 | - |
| ctl_q3_1k | candidate | 4 | 1.62 | 0.000 | 1.62 | 0.000 | 0.300 | 0.025 | 0.325 | - | 12.7 | - |
| ctl_q3_1k | candidate | 12 | 1.80 | 0.000 | 1.80 | 0.000 | 0.325 | 0.025 | 0.350 | - | 16.1 | - |
| ctl_q4_1k | candidate | 1 | 1.60 | 0.000 | 1.60 | 0.000 | 0.300 | 0.025 | 0.325 | - | 10.1 | - |
| ctl_q4_1k | candidate | 4 | 1.62 | 0.000 | 1.62 | 0.000 | 0.275 | 0.025 | 0.300 | - | 12.3 | - |
| ctl_q4_1k | candidate | 12 | 1.82 | 0.000 | 1.82 | 0.000 | 0.300 | 0.025 | 0.325 | - | 15.3 | - |
| ctl_q5_1k | candidate | 1 | 1.57 | 0.000 | 1.60 | 0.000 | 0.250 | 0.025 | 0.275 | - | 10.3 | - |
| ctl_q5_1k | candidate | 4 | 1.62 | 0.000 | 1.62 | 0.000 | 0.275 | 0.025 | 0.275 | - | 12.5 | - |
| ctl_q5_1k | candidate | 12 | 1.82 | 0.000 | 1.82 | 0.000 | 0.275 | 0.025 | 0.300 | - | 15.5 | - |
| ctl_q6_1k | candidate | 1 | 1.60 | 0.000 | 1.62 | 0.000 | 0.200 | 0.025 | 0.225 | - | 9.83 | - |
| ctl_q6_1k | candidate | 4 | 1.62 | 0.000 | 1.62 | 0.000 | 0.225 | 0.000 | 0.225 | - | 12.0 | - |
| ctl_q6_1k | candidate | 12 | 1.82 | 0.000 | 1.85 | 0.000 | 0.225 | 0.025 | 0.250 | - | 15.3 | - |

## Thread scaling (G2): speedup = median(1 thread) / median(N threads); serial fraction s from Amdahl with N = 12

s = (1/S - 1/12) / (1 - 1/12) from the 12-thread speedup S; 1/s is the speedup even infinite parallelism would give at that serial fraction. Today nothing forks, so S ~ 1 (s ~ 1) is expected at the baseline; G2 needs S >= 3 (q1-q6 compute) and >= 4 (parse), i.e. s <= 1/3 (parse: 1/4 is not enough: needs s <= ~0.2).

| workload | mode | binary | metric | T1 | T4 | T12 | S4 | S12 | s | 1/s |
|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|
| q1_1m | e2e | candidate | e2e_ms | 640 | 386 | 341 | 1.66 | 1.88 | 0.49 | 2.0 |
| q1_1m | phases | candidate | compute_ms | 8.00 | 5.00 | 4.00 | 1.60 | 2.00 | 0.45 | 2.2 |
| q2_1m | e2e | candidate | e2e_ms | 661 | 400 | 353 | 1.65 | 1.87 | 0.49 | 2.0 |
| q2_1m | phases | candidate | compute_ms | 18.0 | 8.00 | 6.00 | 2.25 | 3.00 | 0.27 | 3.7 |
| q3_1m | e2e | candidate | e2e_ms | 652 | 397 | 350 | 1.64 | 1.86 | 0.49 | 2.0 |
| q3_1m | phases | candidate | compute_ms | 22.0 | 14.0 | 15.0 | 1.57 | 1.47 | 0.65 | 1.5 |
| q4_1m | e2e | candidate | e2e_ms | 645 | 394 | 350 | 1.64 | 1.84 | 0.50 | 2.0 |
| q4_1m | phases | candidate | compute_ms | 13.0 | 14.0 | 14.0 | 0.93 | 0.93 | 1.08 | 0.9 |
| q5_1m | e2e | candidate | e2e_ms | 647 | 394 | 348 | 1.64 | 1.86 | 0.50 | 2.0 |
| q5_1m | phases | candidate | compute_ms | 10.0 | 10.0 | 10.0 | 1.00 | 1.00 | 1.00 | 1.0 |
| q6_1m | e2e | candidate | e2e_ms | 682 | 397 | 353 | 1.72 | 1.93 | 0.47 | 2.1 |
| q6_1m | phases | candidate | compute_ms | 50.0 | 16.0 | 16.0 | 3.12 | 3.12 | 0.26 | 3.9 |
| parse_1m | e2e | candidate | e2e_ms | 644 | 390 | 344 | 1.65 | 1.87 | 0.49 | 2.0 |
| parse_1m | phases | candidate | parse_ms | 634 | 382 | 339 | 1.66 | 1.87 | 0.49 | 2.0 |
| filter_sel0_1m | phases | candidate | compute_ms | 13.0 | 6.00 | 5.00 | 2.17 | 2.60 | 0.33 | 3.0 |
| filter_sel1_1m | phases | candidate | compute_ms | 13.0 | 5.00 | 5.00 | 2.60 | 2.60 | 0.33 | 3.0 |
| filter_sel50_1m | phases | candidate | compute_ms | 19.0 | 7.00 | 7.00 | 2.71 | 2.71 | 0.31 | 3.2 |
| filter_sel100_1m | phases | candidate | compute_ms | 30.0 | 11.0 | 13.0 | 2.73 | 2.31 | 0.38 | 2.6 |
| nunique_1m | phases | candidate | compute_ms | 16.0 | 16.0 | 16.0 | 1.00 | 1.00 | 1.00 | 1.0 |
| str_group_100k | phases | candidate | compute_ms | 12.0 | 12.0 | 12.0 | 1.00 | 1.00 | 1.00 | 1.0 |
| str_unique_100k | phases | candidate | compute_ms | 12.0 | 12.0 | 12.0 | 1.00 | 1.00 | 1.00 | 1.0 |
| str_join_100k | phases | candidate | compute_ms | 24.0 | 24.0 | 24.0 | 1.00 | 1.00 | 1.00 | 1.0 |
| str_group_300k | phases | candidate | compute_ms | 42.0 | 42.0 | 43.0 | 1.00 | 0.98 | 1.03 | 1.0 |
| str_unique_300k | phases | candidate | compute_ms | 42.0 | 42.0 | 43.0 | 1.00 | 0.98 | 1.03 | 1.0 |
| str_join_300k | phases | candidate | compute_ms | 91.0 | 91.0 | 91.0 | 1.00 | 1.00 | 1.00 | 1.0 |
| str_group_1m | phases | candidate | compute_ms | 127 | 127 | 130 | 1.00 | 0.98 | 1.03 | 1.0 |
| str_unique_1m | phases | candidate | compute_ms | 127 | 131 | 129 | 0.97 | 0.98 | 1.02 | 1.0 |
| str_join_1m | phases | candidate | compute_ms | 360 | 359 | 362 | 1.00 | 0.99 | 1.01 | 1.0 |
| lp_group_100k | phases | candidate | compute_ms | 31.0 | 31.0 | 31.0 | 1.00 | 1.00 | 1.00 | 1.0 |
| lp_unique_100k | phases | candidate | compute_ms | 31.0 | 31.0 | 31.0 | 1.00 | 1.00 | 1.00 | 1.0 |
| lp_join_100k | phases | candidate | compute_ms | 61.0 | 62.0 | 61.0 | 0.98 | 1.00 | 1.00 | 1.0 |
| lp_group_300k | phases | candidate | compute_ms | 86.0 | 84.0 | 83.0 | 1.02 | 1.04 | 0.96 | 1.0 |
| lp_unique_300k | phases | candidate | compute_ms | 83.0 | 83.0 | 84.0 | 1.00 | 0.99 | 1.01 | 1.0 |
| lp_join_300k | phases | candidate | compute_ms | 185 | 186 | 183 | 0.99 | 1.01 | 0.99 | 1.0 |
| q1_100k | phases | candidate | compute_ms | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | 1.0 |
| q2_100k | phases | candidate | compute_ms | 1.62 | 0.625 | 0.750 | 2.60 | 2.17 | 0.41 | 2.4 |
| q3_100k | phases | candidate | compute_ms | 2.00 | 2.00 | 2.00 | 1.00 | 1.00 | 1.00 | 1.0 |
| q4_100k | phases | candidate | compute_ms | 2.00 | 2.00 | 2.00 | 1.00 | 1.00 | 1.00 | 1.0 |
| q5_100k | phases | candidate | compute_ms | 1.00 | 1.00 | 2.00 | 1.00 | 0.50 | 2.09 | 0.5 |
| q6_100k | phases | candidate | compute_ms | 5.00 | 2.00 | 2.00 | 2.50 | 2.50 | 0.35 | 2.9 |
| ctl_q1_1k | phases | candidate | compute_ms | 0.046 | 0.046 | 0.048 | 1.00 | 0.96 | 1.05 | 1.0 |
| ctl_q2_1k | phases | candidate | compute_ms | 0.054 | 0.056 | 0.056 | 0.96 | 0.96 | 1.04 | 1.0 |
| ctl_q3_1k | phases | candidate | compute_ms | 0.325 | 0.300 | 0.325 | 1.08 | 1.00 | 1.00 | 1.0 |
| ctl_q4_1k | phases | candidate | compute_ms | 0.300 | 0.275 | 0.300 | 1.09 | 1.00 | 1.00 | 1.0 |
| ctl_q5_1k | phases | candidate | compute_ms | 0.250 | 0.275 | 0.275 | 0.91 | 0.91 | 1.11 | 0.9 |
| ctl_q6_1k | phases | candidate | compute_ms | 0.200 | 0.225 | 0.225 | 0.89 | 0.89 | 1.14 | 0.9 |

## Stage breakdown of q1-q6 (eager stages, each alone; medians in ms)

### stages_1m, candidate

| stage | 1t ms | 4t ms | 12t ms | share of 1t sum | S12 |
|---|---:|---:|---:|---:|---:|
| filter_q1 | 7.00 | 7.00 | 7.00 | 7% | 1.00 |
| select_q1 | 0.000 | 0.000 | 0.000 | 0% | - |
| withcols_q2 | 3.00 | 3.00 | 3.00 | 3% | 1.00 |
| groupby_q3 | 8.00 | 8.00 | 8.00 | 8% | 1.00 |
| sort_q3 | 0.000 | 0.000 | 0.000 | 0% | - |
| sort_q4 | 22.0 | 22.0 | 21.0 | 23% | 1.05 |
| head_q4 | 0.000 | 0.000 | 0.000 | 0% | - |
| join_q5 | 5.00 | 6.00 | 5.00 | 5% | 1.00 |
| groupby_q5 | 3.00 | 3.00 | 3.00 | 3% | 1.00 |
| sort_q5 | 0.000 | 0.000 | 0.000 | 0% | - |
| describe_q6 | 49.0 | 15.0 | 14.0 | 51% | 3.50 |
| (sum of stages) | 97.0 | 64.0 | 61.0 | | |

parse (read + walk) ms: 1t 644, 4t 386, 12t 340

### stages_100k, candidate

| stage | 1t ms | 4t ms | 12t ms | share of 1t sum | S12 |
|---|---:|---:|---:|---:|---:|
| filter_q1 | 1.00 | 0.000 | 1.00 | 10% | 1.00 |
| select_q1 | 0.000 | 0.000 | 0.000 | 0% | - |
| withcols_q2 | 0.000 | 1.00 | 0.000 | 0% | - |
| groupby_q3 | 1.00 | 1.00 | 1.00 | 10% | 1.00 |
| sort_q3 | 0.000 | 0.000 | 0.000 | 0% | - |
| sort_q4 | 2.00 | 2.00 | 2.00 | 20% | 1.00 |
| head_q4 | 0.000 | 0.000 | 0.000 | 0% | - |
| join_q5 | 1.00 | 1.00 | 1.00 | 10% | 1.00 |
| groupby_q5 | 0.000 | 0.000 | 1.00 | 0% | - |
| sort_q5 | 0.000 | 0.000 | 0.000 | 0% | - |
| describe_q6 | 5.00 | 1.00 | 2.00 | 50% | 2.50 |
| (sum of stages) | 10.0 | 6.00 | 8.00 | | |

parse (read + walk) ms: 1t 68.0, 4t 46.0, 12t 43.0

## Raw samples (ms per input; one value per process, in rep order)

- q1_1m e2e candidate t=1 e2e_ms: [645.0, 640.0, 638.0, 638.0, 642.0]  load1 [3.45, 3.45, 3.34, 3.34, 3.34]
- q1_1m e2e candidate t=4 e2e_ms: [400.0, 402.0, 386.0, 383.0, 386.0]  load1 [3.45, 3.45, 3.34, 3.34, 3.34]
- q1_1m e2e candidate t=12 e2e_ms: [341.0, 343.0, 340.0, 341.0, 339.0]  load1 [3.45, 3.45, 3.34, 3.34, 3.34]
- q1_1m phases candidate t=1 compute_ms: [12.0, 9.0, 8.0, 8.0, 8.0]  load1 [3.67, 3.67, 3.67, 3.67, 3.45]
- q1_1m phases candidate t=4 compute_ms: [5.0, 5.0, 4.0, 4.0, 5.0]  load1 [3.67, 3.67, 3.67, 3.45, 3.45]
- q1_1m phases candidate t=12 compute_ms: [4.0, 5.0, 4.0, 4.0, 4.0]  load1 [3.67, 3.67, 3.67, 3.45, 3.45]
- q2_1m e2e candidate t=1 e2e_ms: [663.0, 660.0, 661.0, 666.0, 660.0]  load1 [3.3, 3.3, 3.19, 3.19, 3.19]
- q2_1m e2e candidate t=4 e2e_ms: [400.0, 400.0, 401.0, 404.0, 398.0]  load1 [3.3, 3.3, 3.19, 3.19, 3.19]
- q2_1m e2e candidate t=12 e2e_ms: [353.0, 356.0, 353.0, 355.0, 350.0]  load1 [3.3, 3.3, 3.3, 3.19, 3.19]
- q2_1m phases candidate t=1 compute_ms: [19.0, 18.0, 18.0, 17.0, 18.0]  load1 [3.34, 3.15, 3.15, 3.15, 3.3]
- q2_1m phases candidate t=4 compute_ms: [7.0, 8.0, 8.0, 8.0, 7.0]  load1 [3.15, 3.15, 3.15, 3.15, 3.3]
- q2_1m phases candidate t=12 compute_ms: [7.0, 6.0, 6.0, 6.0, 7.0]  load1 [3.15, 3.15, 3.15, 3.3, 3.3]
- q3_1m e2e candidate t=1 e2e_ms: [653.0, 655.0, 652.0, 652.0, 652.0]  load1 [3.41, 3.41, 3.41, 3.22, 3.22]
- q3_1m e2e candidate t=4 e2e_ms: [437.0, 401.0, 391.0, 395.0, 397.0]  load1 [3.41, 3.41, 3.22, 3.22, 3.22]
- q3_1m e2e candidate t=12 e2e_ms: [371.0, 349.0, 346.0, 353.0, 350.0]  load1 [3.41, 3.41, 3.41, 3.22, 3.22]
- q3_1m phases candidate t=1 compute_ms: [22.0, 22.0, 22.0, 22.0, 21.0]  load1 [3.19, 3.1, 3.1, 3.1, 3.41]
- q3_1m phases candidate t=4 compute_ms: [14.0, 14.0, 14.0, 14.0, 13.0]  load1 [3.19, 3.1, 3.1, 3.1, 3.1]
- q3_1m phases candidate t=12 compute_ms: [14.0, 14.0, 15.0, 15.0, 15.0]  load1 [3.1, 3.1, 3.1, 3.1, 3.41]
- q4_1m e2e candidate t=1 e2e_ms: [671.0, 645.0, 643.0, 649.0, 645.0]  load1 [3.91, 3.91, 3.91, 3.67, 3.67]
- q4_1m e2e candidate t=4 e2e_ms: [397.0, 393.0, 394.0, 397.0, 394.0]  load1 [3.91, 3.91, 3.91, 3.67, 3.67]
- q4_1m e2e candidate t=12 e2e_ms: [350.0, 350.0, 353.0, 351.0, 348.0]  load1 [3.91, 3.91, 3.91, 3.67, 3.67]
- q4_1m phases candidate t=1 compute_ms: [14.0, 14.0, 13.0, 13.0, 13.0]  load1 [3.22, 4.16, 4.16, 4.16, 3.91]
- q4_1m phases candidate t=4 compute_ms: [14.0, 14.0, 14.0, 14.0, 13.0]  load1 [3.22, 4.16, 4.16, 4.16, 4.16]
- q4_1m phases candidate t=12 compute_ms: [14.0, 15.0, 14.0, 13.0, 13.0]  load1 [3.22, 4.16, 4.16, 4.16, 4.16]
- q5_1m e2e candidate t=1 e2e_ms: [649.0, 671.0, 643.0, 647.0, 646.0]  load1 [3.41, 3.41, 3.41, 3.41, 3.46]
- q5_1m e2e candidate t=4 e2e_ms: [402.0, 391.0, 394.0, 391.0, 394.0]  load1 [3.41, 3.41, 3.41, 3.46, 3.46]
- q5_1m e2e candidate t=12 e2e_ms: [348.0, 349.0, 348.0, 346.0, 344.0]  load1 [3.41, 3.41, 3.41, 3.46, 3.46]
- q5_1m phases candidate t=1 compute_ms: [10.0, 11.0, 10.0, 10.0, 10.0]  load1 [3.67, 3.62, 3.62, 3.62, 3.62]
- q5_1m phases candidate t=4 compute_ms: [10.0, 10.0, 10.0, 11.0, 11.0]  load1 [3.67, 3.67, 3.62, 3.62, 3.62]
- q5_1m phases candidate t=12 compute_ms: [12.0, 10.0, 10.0, 10.0, 11.0]  load1 [3.67, 3.67, 3.62, 3.62, 3.62]
- q6_1m e2e candidate t=1 e2e_ms: [682.0, 684.0, 682.0, 680.0, 687.0]  load1 [3.26, 3.24, 3.24, 3.24, 3.14]
- q6_1m e2e candidate t=4 e2e_ms: [396.0, 397.0, 400.0, 397.0, 397.0]  load1 [3.24, 3.24, 3.24, 3.24, 3.14]
- q6_1m e2e candidate t=12 e2e_ms: [353.0, 354.0, 356.0, 350.0, 353.0]  load1 [3.24, 3.24, 3.24, 3.14, 3.14]
- q6_1m phases candidate t=1 compute_ms: [50.0, 50.0, 51.0, 52.0, 50.0]  load1 [3.46, 3.46, 3.26, 3.26, 3.26]
- q6_1m phases candidate t=4 compute_ms: [17.0, 16.0, 16.0, 16.0, 16.0]  load1 [3.46, 3.46, 3.26, 3.26, 3.26]
- q6_1m phases candidate t=12 compute_ms: [16.0, 16.0, 16.0, 16.0, 16.0]  load1 [3.46, 3.46, 3.26, 3.26, 3.26]
- parse_1m e2e candidate t=1 e2e_ms: [676.0, 642.0, 653.0, 642.0, 644.0]  load1 [2.97, 2.89, 2.89, 2.89, 2.74]
- parse_1m e2e candidate t=4 e2e_ms: [388.0, 389.0, 397.0, 390.0, 391.0]  load1 [2.97, 2.89, 2.89, 2.89, 2.89]
- parse_1m e2e candidate t=12 e2e_ms: [341.0, 344.0, 348.0, 348.0, 344.0]  load1 [2.89, 2.89, 2.89, 2.89, 2.74]
- parse_1m phases candidate t=1 parse_ms: [634.0, 633.0, 630.0, 710.0, 659.0]  load1 [3.14, 3.14, 2.97, 2.97, 2.97]
- parse_1m phases candidate t=4 parse_ms: [380.0, 382.0, 379.0, 409.0, 389.0]  load1 [3.14, 3.14, 2.97, 2.97, 2.97]
- parse_1m phases candidate t=12 parse_ms: [336.0, 335.0, 339.0, 342.0, 347.0]  load1 [3.14, 3.14, 3.14, 2.97, 2.97]
- filter_sel0_1m phases candidate t=1 compute_ms: [13.0, 13.0, 16.0, 14.0, 13.0]  load1 [2.74, 2.74, 2.74, 2.68, 2.68]
- filter_sel0_1m phases candidate t=4 compute_ms: [6.0, 5.0, 6.0, 5.0, 6.0]  load1 [2.74, 2.74, 2.68, 2.68, 2.68]
- filter_sel0_1m phases candidate t=12 compute_ms: [5.0, 5.0, 6.0, 5.0, 5.0]  load1 [2.74, 2.74, 2.74, 2.68, 2.68]
- filter_sel1_1m phases candidate t=1 compute_ms: [12.0, 12.0, 13.0, 13.0, 13.0]  load1 [2.68, 2.54, 2.54, 2.54, 2.54]
- filter_sel1_1m phases candidate t=4 compute_ms: [5.0, 5.0, 5.0, 5.0, 6.0]  load1 [2.68, 2.68, 2.54, 2.54, 2.54]
- filter_sel1_1m phases candidate t=12 compute_ms: [4.0, 5.0, 5.0, 5.0, 6.0]  load1 [2.68, 2.54, 2.54, 2.54, 2.54]
- filter_sel50_1m phases candidate t=1 compute_ms: [19.0, 19.0, 19.0, 18.0, 18.0]  load1 [2.5, 2.5, 2.5, 2.5, 2.38]
- filter_sel50_1m phases candidate t=4 compute_ms: [7.0, 7.0, 7.0, 7.0, 7.0]  load1 [2.5, 2.5, 2.5, 2.38, 2.38]
- filter_sel50_1m phases candidate t=12 compute_ms: [7.0, 7.0, 7.0, 6.0, 7.0]  load1 [2.5, 2.5, 2.5, 2.38, 2.38]
- filter_sel100_1m phases candidate t=1 compute_ms: [32.0, 30.0, 29.0, 30.0, 35.0]  load1 [2.38, 2.35, 2.35, 2.35, 2.35]
- filter_sel100_1m phases candidate t=4 compute_ms: [11.0, 11.0, 11.0, 11.0, 11.0]  load1 [2.38, 2.38, 2.35, 2.35, 2.35]
- filter_sel100_1m phases candidate t=12 compute_ms: [13.0, 12.0, 13.0, 13.0, 13.0]  load1 [2.38, 2.38, 2.35, 2.35, 2.35]
- nunique_1m phases candidate t=1 compute_ms: [16.0, 16.0, 16.0, 16.0, 16.0]  load1 [2.21, 2.21, 2.12, 2.12, 2.12]
- nunique_1m phases candidate t=4 compute_ms: [15.0, 15.0, 16.0, 17.0, 16.0]  load1 [2.21, 2.21, 2.12, 2.12, 2.12]
- nunique_1m phases candidate t=12 compute_ms: [16.0, 16.0, 16.0, 16.0, 16.0]  load1 [2.21, 2.21, 2.12, 2.12, 2.12]
- str_group_100k phases candidate t=1 compute_ms: [12.0, 13.0, 12.0, 12.0, 12.0]  load1 [2.12, 2.12, 2.12, 2.12, 2.12]
- str_group_100k phases candidate t=4 compute_ms: [12.0, 13.0, 12.0, 12.0, 12.0]  load1 [2.12, 2.12, 2.12, 2.12, 2.12]
- str_group_100k phases candidate t=12 compute_ms: [12.0, 12.0, 13.0, 12.0, 12.0]  load1 [2.12, 2.12, 2.12, 2.12, 2.12]
- str_unique_100k phases candidate t=1 compute_ms: [12.0, 12.0, 12.0, 12.0, 13.0]  load1 [2.12, 2.12, 2.12, 2.12, 2.12]
- str_unique_100k phases candidate t=4 compute_ms: [12.0, 13.0, 12.0, 12.0, 12.0]  load1 [2.12, 2.12, 2.12, 2.12, 2.12]
- str_unique_100k phases candidate t=12 compute_ms: [12.0, 12.0, 12.0, 12.0, 13.0]  load1 [2.12, 2.12, 2.12, 2.12, 2.12]
- str_join_100k phases candidate t=1 compute_ms: [24.0, 24.0, 24.0, 24.0, 24.0]  load1 [2.12, 2.19, 2.19, 2.19, 2.19]
- str_join_100k phases candidate t=4 compute_ms: [24.0, 24.0, 27.0, 24.0, 24.0]  load1 [2.12, 2.19, 2.19, 2.19, 2.19]
- str_join_100k phases candidate t=12 compute_ms: [24.0, 24.0, 24.0, 24.0, 25.0]  load1 [2.12, 2.19, 2.19, 2.19, 2.19]
- str_group_300k phases candidate t=1 compute_ms: [43.0, 42.0, 42.0, 42.0, 42.0]  load1 [2.19, 2.19, 2.19, 2.19, 2.09]
- str_group_300k phases candidate t=4 compute_ms: [42.0, 42.0, 44.0, 42.0, 42.0]  load1 [2.19, 2.19, 2.19, 2.09, 2.09]
- str_group_300k phases candidate t=12 compute_ms: [42.0, 43.0, 42.0, 44.0, 43.0]  load1 [2.19, 2.19, 2.19, 2.09, 2.09]
- str_unique_300k phases candidate t=1 compute_ms: [42.0, 42.0, 44.0, 42.0, 42.0]  load1 [2.09, 2.09, 2.09, 2.09, 2.08]
- str_unique_300k phases candidate t=4 compute_ms: [42.0, 48.0, 42.0, 42.0, 43.0]  load1 [2.09, 2.09, 2.09, 2.09, 2.08]
- str_unique_300k phases candidate t=12 compute_ms: [43.0, 43.0, 42.0, 43.0, 42.0]  load1 [2.09, 2.09, 2.09, 2.09, 2.08]
- str_join_300k phases candidate t=1 compute_ms: [92.0, 91.0, 91.0, 90.0, 90.0]  load1 [2.08, 2.08, 2.08, 2.0, 2.0]
- str_join_300k phases candidate t=4 compute_ms: [91.0, 91.0, 96.0, 90.0, 91.0]  load1 [2.08, 2.08, 2.0, 2.0, 2.0]
- str_join_300k phases candidate t=12 compute_ms: [93.0, 92.0, 91.0, 91.0, 90.0]  load1 [2.08, 2.08, 2.08, 2.0, 2.0]
- str_group_1m phases candidate t=1 compute_ms: [132.0, 127.0, 127.0, 126.0, 127.0]  load1 [2.0, 2.16, 2.06, 2.06, 1.98]
- str_group_1m phases candidate t=4 compute_ms: [154.0, 126.0, 127.0, 127.0, 128.0]  load1 [2.16, 2.16, 2.06, 2.06, 2.06]
- str_group_1m phases candidate t=12 compute_ms: [130.0, 128.0, 131.0, 130.0, 128.0]  load1 [2.16, 2.16, 2.16, 2.06, 1.98]
- str_unique_1m phases candidate t=1 compute_ms: [126.0, 127.0, 126.0, 127.0, 127.0]  load1 [1.98, 1.9, 1.9, 2.15, 2.15]
- str_unique_1m phases candidate t=4 compute_ms: [152.0, 127.0, 131.0, 131.0, 128.0]  load1 [1.98, 1.98, 1.9, 2.15, 2.15]
- str_unique_1m phases candidate t=12 compute_ms: [140.0, 128.0, 129.0, 182.0, 127.0]  load1 [1.98, 1.9, 1.9, 2.15, 2.15]
- str_join_1m phases candidate t=1 compute_ms: [362.0, 360.0, 357.0, 360.0, 354.0]  load1 [2.22, 2.36, 2.25, 2.47, 3.31]
- str_join_1m phases candidate t=4 compute_ms: [366.0, 359.0, 366.0, 358.0, 355.0]  load1 [2.22, 2.36, 2.25, 2.47, 3.31]
- str_join_1m phases candidate t=12 compute_ms: [389.0, 362.0, 360.0, 366.0, 360.0]  load1 [2.22, 2.36, 2.25, 2.47, 3.31]
- lp_group_100k phases candidate t=1 compute_ms: [31.0, 31.0, 30.0, 31.0, 30.0]  load1 [3.13, 3.13, 3.13, 3.13, 3.13]
- lp_group_100k phases candidate t=4 compute_ms: [31.0, 31.0, 31.0, 30.0, 31.0]  load1 [3.13, 3.13, 3.13, 3.13, 3.13]
- lp_group_100k phases candidate t=12 compute_ms: [31.0, 31.0, 32.0, 31.0, 31.0]  load1 [3.13, 3.13, 3.13, 3.13, 3.13]
- lp_unique_100k phases candidate t=1 compute_ms: [31.0, 31.0, 32.0, 30.0, 31.0]  load1 [3.13, 3.04, 3.04, 3.04, 3.04]
- lp_unique_100k phases candidate t=4 compute_ms: [33.0, 31.0, 31.0, 30.0, 31.0]  load1 [3.04, 3.04, 3.04, 3.04, 3.04]
- lp_unique_100k phases candidate t=12 compute_ms: [31.0, 31.0, 30.0, 31.0, 31.0]  load1 [3.04, 3.04, 3.04, 3.04, 3.04]
- lp_join_100k phases candidate t=1 compute_ms: [59.0, 61.0, 61.0, 62.0, 59.0]  load1 [3.04, 3.03, 3.03, 3.03, 3.03]
- lp_join_100k phases candidate t=4 compute_ms: [60.0, 62.0, 67.0, 62.0, 61.0]  load1 [3.04, 3.04, 3.03, 3.03, 3.03]
- lp_join_100k phases candidate t=12 compute_ms: [61.0, 60.0, 61.0, 61.0, 60.0]  load1 [3.04, 3.04, 3.03, 3.03, 3.03]
- lp_group_300k phases candidate t=1 compute_ms: [90.0, 86.0, 83.0, 89.0, 83.0]  load1 [3.03, 2.87, 2.87, 2.87, 2.72]
- lp_group_300k phases candidate t=4 compute_ms: [85.0, 88.0, 84.0, 83.0, 82.0]  load1 [2.87, 2.87, 2.87, 2.72, 2.72]
- lp_group_300k phases candidate t=12 compute_ms: [85.0, 84.0, 83.0, 83.0, 83.0]  load1 [2.87, 2.87, 2.87, 2.72, 2.72]
- lp_unique_300k phases candidate t=1 compute_ms: [83.0, 83.0, 85.0, 81.0, 82.0]  load1 [2.72, 2.66, 2.66, 2.66, 2.69]
- lp_unique_300k phases candidate t=4 compute_ms: [84.0, 83.0, 83.0, 82.0, 82.0]  load1 [2.72, 2.66, 2.66, 2.66, 2.69]
- lp_unique_300k phases candidate t=12 compute_ms: [89.0, 84.0, 89.0, 82.0, 83.0]  load1 [2.72, 2.66, 2.66, 2.66, 2.69]
- lp_join_300k phases candidate t=1 compute_ms: [185.0, 189.0, 185.0, 180.0, 181.0]  load1 [2.69, 3.43, 3.24, 3.24, 3.14]
- lp_join_300k phases candidate t=4 compute_ms: [183.0, 186.0, 184.0, 197.0, 190.0]  load1 [2.69, 3.43, 3.24, 3.24, 3.14]
- lp_join_300k phases candidate t=12 compute_ms: [189.0, 183.0, 183.0, 184.0, 182.0]  load1 [2.69, 3.43, 3.43, 3.14, 3.14]
- q1_100k phases candidate t=1 compute_ms: [1.0, 1.0, 1.0, 1.0, 1.0]  load1 [3.14, 3.14, 3.13, 3.13, 3.13]
- q1_100k phases candidate t=4 compute_ms: [1.0, 1.0, 0.0, 0.0, 1.0]  load1 [3.14, 3.14, 3.13, 3.13, 3.13]
- q1_100k phases candidate t=12 compute_ms: [1.0, 0.0, 1.0, 1.0, 1.0]  load1 [3.14, 3.14, 3.13, 3.13, 3.13]
- q2_100k phases candidate t=1 compute_ms: [1.5, 1.62, 1.62, 1.62, 1.62]  load1 [3.13, 3.13, 3.13, 3.13, 2.96]
- q2_100k phases candidate t=4 compute_ms: [0.75, 0.75, 0.62, 0.62, 0.62]  load1 [3.13, 3.13, 3.13, 3.13, 2.96]
- q2_100k phases candidate t=12 compute_ms: [0.75, 0.75, 0.88, 0.75, 0.88]  load1 [3.13, 3.13, 3.13, 2.96, 2.96]
- q3_100k phases candidate t=1 compute_ms: [2.0, 2.0, 3.0, 3.0, 2.0]  load1 [2.96, 2.96, 2.96, 2.96, 2.96]
- q3_100k phases candidate t=4 compute_ms: [2.0, 2.0, 2.0, 2.0, 2.0]  load1 [2.96, 2.96, 2.96, 2.96, 2.96]
- q3_100k phases candidate t=12 compute_ms: [2.0, 2.0, 2.0, 2.0, 2.0]  load1 [2.96, 2.96, 2.96, 2.96, 2.96]
- q4_100k phases candidate t=1 compute_ms: [2.0, 2.0, 2.0, 1.0, 1.0]  load1 [2.96, 2.96, 2.96, 2.96, 2.96]
- q4_100k phases candidate t=4 compute_ms: [2.0, 2.0, 2.0, 1.0, 2.0]  load1 [2.96, 2.96, 2.96, 2.96, 2.96]
- q4_100k phases candidate t=12 compute_ms: [1.0, 2.0, 2.0, 2.0, 2.0]  load1 [2.96, 2.96, 2.96, 2.96, 2.96]
- q5_100k phases candidate t=1 compute_ms: [2.0, 2.0, 1.0, 1.0, 1.0]  load1 [2.96, 2.96, 2.96, 2.96, 2.96]
- q5_100k phases candidate t=4 compute_ms: [2.0, 1.0, 1.0, 1.0, 1.0]  load1 [2.96, 2.96, 2.96, 2.96, 2.96]
- q5_100k phases candidate t=12 compute_ms: [1.0, 2.0, 2.0, 2.0, 2.0]  load1 [2.96, 2.96, 2.96, 2.96, 2.96]
- q6_100k phases candidate t=1 compute_ms: [5.0, 6.0, 5.0, 5.0, 5.0]  load1 [2.96, 2.96, 2.96, 2.8, 2.8]
- q6_100k phases candidate t=4 compute_ms: [2.0, 2.0, 2.0, 2.0, 2.0]  load1 [2.96, 2.96, 2.8, 2.8, 2.8]
- q6_100k phases candidate t=12 compute_ms: [2.0, 2.0, 2.0, 2.0, 2.0]  load1 [2.96, 2.96, 2.96, 2.8, 2.8]
- ctl_q1_1k phases candidate t=1 compute_ms: [0.05, 0.05, 0.05, 0.04, 0.04]  load1 [2.8, 2.66, 2.66, 2.66, 2.6]
- ctl_q1_1k phases candidate t=4 compute_ms: [0.05, 0.05, 0.05, 0.05, 0.05]  load1 [2.8, 2.8, 2.66, 2.66, 2.6]
- ctl_q1_1k phases candidate t=12 compute_ms: [0.05, 0.05, 0.05, 0.05, 0.05]  load1 [2.8, 2.8, 2.66, 2.6, 2.6]
- ctl_q2_1k phases candidate t=1 compute_ms: [0.05, 0.06, 0.05, 0.06, 0.05]  load1 [2.6, 2.71, 2.58, 2.58, 2.69]
- ctl_q2_1k phases candidate t=4 compute_ms: [0.05, 0.06, 0.06, 0.06, 0.05]  load1 [2.6, 2.71, 2.58, 2.58, 2.58]
- ctl_q2_1k phases candidate t=12 compute_ms: [0.06, 0.06, 0.06, 0.06, 0.06]  load1 [2.71, 2.71, 2.71, 2.58, 2.69]
- ctl_q3_1k phases candidate t=1 compute_ms: [0.33, 0.33, 0.33, 0.3, 0.3]  load1 [2.69, 2.69, 2.69, 2.69, 2.69]
- ctl_q3_1k phases candidate t=4 compute_ms: [0.3, 0.33, 0.3, 0.3, 0.3]  load1 [2.69, 2.69, 2.69, 2.69, 2.69]
- ctl_q3_1k phases candidate t=12 compute_ms: [0.33, 0.33, 0.33, 0.3, 0.33]  load1 [2.69, 2.69, 2.69, 2.69, 2.69]
- ctl_q4_1k phases candidate t=1 compute_ms: [0.3, 0.3, 0.3, 0.3, 0.28]  load1 [2.69, 2.69, 2.69, 2.69, 3.44]
- ctl_q4_1k phases candidate t=4 compute_ms: [0.3, 0.28, 0.28, 0.28, 0.28]  load1 [2.69, 2.69, 2.69, 2.69, 3.44]
- ctl_q4_1k phases candidate t=12 compute_ms: [0.3, 0.3, 0.3, 0.3, 0.28]  load1 [2.69, 2.69, 2.69, 2.69, 3.44]
- ctl_q5_1k phases candidate t=1 compute_ms: [0.25, 0.25, 0.25, 0.28, 0.25]  load1 [3.44, 3.44, 3.44, 3.44, 3.44]
- ctl_q5_1k phases candidate t=4 compute_ms: [0.28, 0.25, 0.28, 0.28, 0.25]  load1 [3.44, 3.44, 3.44, 3.44, 3.44]
- ctl_q5_1k phases candidate t=12 compute_ms: [0.28, 0.28, 0.25, 0.28, 0.28]  load1 [3.44, 3.44, 3.44, 3.44, 3.44]
- ctl_q6_1k phases candidate t=1 compute_ms: [0.2, 0.23, 0.2, 0.2, 0.2]  load1 [3.44, 3.44, 3.44, 3.44, 3.44]
- ctl_q6_1k phases candidate t=4 compute_ms: [0.23, 0.23, 0.23, 0.23, 0.23]  load1 [3.44, 3.44, 3.44, 3.44, 3.44]
- ctl_q6_1k phases candidate t=12 compute_ms: [0.23, 0.23, 0.23, 0.23, 0.23]  load1 [3.44, 3.44, 3.44, 3.44, 3.44]

