load (1-min) over the run: 7.38-8.71; 90 processes; depth 10
| mode | 1 thr | 2 thr | 4 thr | 8 thr | 12 thr | speedup (max thr vs 1) | checks equal |
|---|---|---|---|---|---|---|---|
| 0 fold (leaf back) | 10.0 ms (raw 28, 10, 10; cpu 0.11 s) | 5.0 ms (raw 7, 5, 5; cpu 0.11 s) | 3.0 ms (raw 6, 3, 2; cpu 0.13 s) | 2.0 ms (raw 4, 2, 2; cpu 0.16 s) | 2.0 ms (raw 3, 1, 2; cpu 0.17 s) | 5.0x | yes |
| 2 fresh map, input dropped | 15.0 ms (raw 20, 15, 15; cpu 0.15 s) | 8.0 ms (raw 12, 8, 8; cpu 0.17 s) | 5.0 ms (raw 5, 5, 5; cpu 0.19 s) | 3.0 ms (raw 3, 2, 3; cpu 0.22 s) | 3.0 ms (raw 3, 2, 3; cpu 0.22 s) | 5.0x | yes |
| 4 in-place map | 4.0 ms (raw 4, 4, 4; cpu 0.07 s) | 2.0 ms (raw 2, 2, 3; cpu 0.07 s) | 1.0 ms (raw 1, 1, 1; cpu 0.09 s) | 1.0 ms (raw 1, 1, 1; cpu 0.12 s) | 1.0 ms (raw 1, 1, 1; cpu 0.14 s) | 4.0x | yes |
| 5 fresh map + fold (both die) | 24.0 ms (raw 24, 24, 25; cpu 0.42 s) | 13.0 ms (raw 13, 13, 12; cpu 0.42 s) | 6.0 ms (raw 7, 6, 6; cpu 0.44 s) | 4.0 ms (raw 4, 4, 4; cpu 0.52 s) | 4.0 ms (raw 4, 3, 4; cpu 0.54 s) | 6.0x | yes |
| 9 no leaf work | 0.0 ms (raw 0, 0, 0; cpu 0.03 s) | 0.0 ms (raw 0, 0, 0; cpu 0.04 s) | 0.0 ms (raw 0, 0, 0; cpu 0.05 s) | 0.0 ms (raw 0, 0, 0; cpu 0.06 s) | 0.0 ms (raw 0, 0, 0; cpu 0.08 s) | - | yes |
| 11 fold over a List, Lst.pmap (T5.3's shape) | 10.0 ms (raw 10, 10, 10; cpu 0.12 s) | 5.0 ms (raw 5, 5, 5; cpu 0.11 s) | 5.0 ms (raw 5, 5, 5; cpu 0.13 s) | 5.0 ms (raw 5, 5, 5; cpu 0.15 s) | 5.0 ms (raw 5, 5, 5; cpu 0.18 s) | 2.0x | yes |
