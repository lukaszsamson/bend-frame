
## exe cand, mode 3 (chunked, pre-chunked source)
# 75 processes, 1-minute load 2.06..3.13; compute = CX.run_x over a pre-chunked source, ms per run (window of 8 runs / 8)
| op | 1 thr: median (raw per process) | 4 thr: median (raw per process) | 12 thr: median (raw per process) | 4-vs-1 | 12-vs-1 | 16.8 G2 | hashes |
|---|---|---|---|---|---|---|---|
| filter | 6.25 (6.25, 6.19, 6.31, 6.25, 6.25) | 1.88 (1.88, 1.88, 1.81, 1.88, 1.88) | 1.06 (1.12, 1.00, 1.12, 1.00, 1.06) | 3.33x | 5.88x | >= 3.0x | equal |
| q1 | 2.50 (2.50, 2.50, 2.50, 2.50, 2.50) | 0.88 (0.81, 0.88, 0.88, 0.88, 0.88) | 0.62 (0.62, 0.62, 0.62, 0.69, 0.62) | 2.86x | 4.00x | >= 3.0x | equal |
| q2 | 2.62 (2.56, 2.62, 2.62, 2.62, 2.56) | 0.81 (0.81, 0.81, 0.81, 0.81, 0.75) | 0.69 (0.62, 0.69, 0.69, 0.69, 0.75) | 3.23x | 3.82x | >= 3.0x | equal |
| q3 | 13.44 (13.62, 13.31, 13.44, 13.44, 13.38) | 9.88 (9.88, 9.88, 9.88, 9.88, 10.12) | 9.81 (9.75, 9.69, 9.88, 9.81, 9.94) | 1.36x | 1.37x | >= 2.0x | equal |
| q5 | 14.19 (14.25, 14.19, 14.19, 14.06, 14.19) | 10.44 (10.38, 10.50, 10.44, 10.44, 10.44) | 10.31 (10.31, 10.31, 10.38, 10.25, 10.31) | 1.36x | 1.38x | >= 1.5x | equal |

## exe cand, mode 4 (reference, flat env)
# 75 processes, 1-minute load 2.06..3.13; compute = Exec.run_phys over a flat env (the reference), ms per run (window of 8 runs / 8)
| op | 1 thr: median (raw per process) | 4 thr: median (raw per process) | 12 thr: median (raw per process) | 4-vs-1 | 12-vs-1 | 16.8 G2 | hashes |
|---|---|---|---|---|---|---|---|
| filter | 6.81 (6.88, 6.88, 6.75, 6.75, 6.81) | 6.81 (6.81, 6.81, 6.69, 6.81, 6.75) | 6.75 (6.75, 6.75, 6.81, 6.75, 6.81) | 1.00x | 1.01x | >= 3.0x | equal |
| q1 | 2.19 (2.25, 2.25, 2.19, 2.19, 2.19) | 2.25 (2.25, 2.19, 2.25, 2.25, 2.25) | 2.25 (2.25, 2.25, 2.25, 2.25, 2.25) | 0.97x | 0.97x | >= 3.0x | equal |
| q2 | 2.31 (2.31, 2.38, 2.31, 2.38, 2.25) | 2.38 (2.38, 2.38, 2.31, 2.38, 2.38) | 2.31 (2.31, 2.31, 2.25, 2.25, 2.31) | 0.97x | 1.00x | >= 3.0x | equal |
| q3 | 10.12 (10.12, 10.19, 10.12, 10.12, 10.19) | 10.12 (10.12, 10.06, 10.19, 10.12, 10.44) | 10.06 (10.06, 10.06, 10.06, 10.12, 10.12) | 1.00x | 1.01x | >= 2.0x | equal |
| q5 | 8.31 (8.31, 8.38, 8.25, 8.31, 8.38) | 8.31 (8.31, 8.25, 8.38, 8.31, 8.31) | 8.44 (8.62, 8.25, 8.44, 8.25, 8.44) | 1.00x | 0.99x | >= 1.5x | equal |
hash filter: equal across binaries and modes
hash q1: equal across binaries and modes
hash q2: equal across binaries and modes
hash q3: equal across binaries and modes
hash q5: equal across binaries and modes

| exe | op | chunked 1 thr | reference 1 thr | chunked / reference |
|---|---|---|---|---|
| cand | filter | 6.25 | 6.81 | 0.92 |
| cand | q1 | 2.50 | 2.19 | 1.14 |
| cand | q2 | 2.62 | 2.31 | 1.14 |
| cand | q3 | 13.44 | 10.12 | 1.33 |
| cand | q5 | 14.19 | 8.31 | 1.71 |
