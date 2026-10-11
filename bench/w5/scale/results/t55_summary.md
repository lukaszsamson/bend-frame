# T5.5 batched compute (bench/w5/scale/t53b.py; base = 6be63d5, cand = T5.5), PROVISIONAL

uptime before / after the main run:
```
19:54  up 24 days,  9:13, 24 users, load averages: 9.09 15.59 24.36
20:06  up 24 days,  9:26, 24 users, load averages: 5.63 7.54 14.51
```
The 15 reference q5 records of the main run were invalid (mode 4 built q5's products Source from an empty frame: chk 0) and were removed; the q5 reference cells were rerun with the fixed mode 4 (load 5.2-6.4).

## exe base, mode 3 (chunked, pre-chunked source)
# 75 processes, 1-minute load 4.9..14.82; compute = CX.run_x over a pre-chunked source, ms per run (window of 8 runs / 8)
| op | 1 thr: median (raw per process) | 4 thr: median (raw per process) | 12 thr: median (raw per process) | 4-vs-1 | 12-vs-1 | 16.8 G2 | hashes |
|---|---|---|---|---|---|---|---|
| filter | 7.38 (7.25, 7.06, 7.44, 7.56, 7.38) | 2.50 (2.50, 2.81, 2.50, 2.44, 2.50) | 1.88 (2.50, 2.00, 1.88, 1.81, 1.88) | 2.95x | 3.93x | >= 3.0x | equal |
| q1 | 3.31 (3.19, 3.38, 3.25, 3.31, 3.44) | 1.31 (1.31, 1.38, 1.31, 1.25, 1.25) | 1.25 (1.25, 1.25, 1.38, 1.31, 1.25) | 2.52x | 2.65x | >= 3.0x | equal |
| q2 | 3.38 (3.38, 3.31, 3.44, 3.38, 3.38) | 1.25 (1.31, 1.88, 1.25, 1.25, 1.25) | 1.12 (1.25, 1.12, 1.12, 1.12, 1.12) | 2.70x | 3.00x | >= 3.0x | equal |
| q3 | 14.75 (15.69, 14.94, 14.69, 14.69, 14.75) | 10.62 (11.44, 10.62, 10.50, 10.62, 10.56) | 10.56 (10.50, 10.94, 10.44, 10.75, 10.56) | 1.39x | 1.40x | >= 2.0x | equal |
| q5 | 15.19 (15.38, 15.00, 15.00, 15.19, 15.38) | 11.00 (11.69, 11.00, 11.00, 10.44, 10.88) | 10.94 (10.94, 10.94, 10.69, 11.12, 10.81) | 1.38x | 1.39x | >= 1.5x | equal |

## exe cand, mode 3 (chunked, pre-chunked source)
# 75 processes, 1-minute load 4.98..14.82; compute = CX.run_x over a pre-chunked source, ms per run (window of 8 runs / 8)
| op | 1 thr: median (raw per process) | 4 thr: median (raw per process) | 12 thr: median (raw per process) | 4-vs-1 | 12-vs-1 | 16.8 G2 | hashes |
|---|---|---|---|---|---|---|---|
| filter | 7.00 (7.12, 6.88, 7.19, 7.00, 7.00) | 2.00 (2.19, 2.00, 2.00, 2.00, 2.00) | 1.25 (1.38, 1.56, 1.25, 1.19, 1.25) | 3.50x | 5.60x | >= 3.0x | equal |
| q1 | 2.81 (2.81, 2.81, 2.88, 2.62, 2.75) | 0.94 (0.94, 0.88, 0.94, 0.88, 0.94) | 0.75 (0.69, 0.81, 0.81, 0.69, 0.75) | 3.00x | 3.75x | >= 3.0x | equal |
| q2 | 2.81 (2.75, 2.88, 2.75, 2.81, 2.88) | 0.94 (1.00, 0.94, 0.94, 0.94, 1.00) | 0.69 (0.75, 0.75, 0.62, 0.69, 0.62) | 3.00x | 4.09x | >= 3.0x | equal |
| q3 | 14.25 (14.75, 14.12, 14.25, 14.25, 14.50) | 10.44 (11.44, 10.50, 10.44, 10.25, 10.25) | 10.12 (11.12, 10.81, 10.00, 10.06, 10.12) | 1.37x | 1.41x | >= 2.0x | equal |
| q5 | 14.81 (14.75, 14.75, 14.81, 15.06, 15.00) | 11.00 (11.62, 11.06, 11.00, 10.56, 10.81) | 10.94 (10.75, 10.94, 11.00, 11.06, 10.81) | 1.35x | 1.35x | >= 1.5x | equal |

## exe cand, mode 4 (reference, flat env)
# 75 processes, 1-minute load 4.9..14.61; compute = Exec.run_phys over a flat env (the reference), ms per run (window of 8 runs / 8)
| op | 1 thr: median (raw per process) | 4 thr: median (raw per process) | 12 thr: median (raw per process) | 4-vs-1 | 12-vs-1 | 16.8 G2 | hashes |
|---|---|---|---|---|---|---|---|
| filter | 7.12 (8.06, 7.12, 7.12, 6.88, 7.31) | 7.12 (7.12, 6.81, 7.06, 7.12, 7.12) | 7.25 (7.25, 7.62, 6.88, 7.12, 7.31) | 1.00x | 0.98x | >= 3.0x | equal |
| q1 | 2.50 (2.44, 2.56, 2.50, 2.38, 2.50) | 2.31 (2.31, 2.31, 2.38, 2.25, 2.38) | 2.31 (2.31, 2.38, 2.25, 2.25, 2.31) | 1.08x | 1.08x | >= 3.0x | equal |
| q2 | 2.56 (2.38, 2.69, 2.31, 2.56, 2.56) | 2.56 (2.69, 2.56, 2.56, 2.56, 2.50) | 2.44 (2.50, 2.38, 2.44, 2.50, 2.44) | 1.00x | 1.05x | >= 3.0x | equal |
| q3 | 10.81 (12.56, 10.81, 10.69, 10.81, 10.81) | 10.81 (11.19, 11.06, 10.69, 10.81, 10.62) | 10.94 (10.94, 11.00, 10.94, 10.25, 10.69) | 1.00x | 0.99x | >= 2.0x | equal |
| q5 | 8.94 (8.94, 9.06, 8.69, 8.88, 9.00) | 8.56 (8.88, 8.56, 8.56, 8.56, 8.88) | 8.69 (8.56, 9.00, 8.94, 8.69, 8.62) | 1.04x | 1.03x | >= 1.5x | equal |
hash filter: equal across binaries and modes
hash q1: equal across binaries and modes
hash q2: equal across binaries and modes
hash q3: equal across binaries and modes
hash q5: equal across binaries and modes

| exe | op | chunked 1 thr | reference 1 thr | chunked / reference |
|---|---|---|---|---|
| base | filter | 7.38 | 7.12 | 1.04 |
| base | q1 | 3.31 | 2.50 | 1.32 |
| base | q2 | 3.38 | 2.56 | 1.32 |
| base | q3 | 14.75 | 10.81 | 1.36 |
| base | q5 | 15.19 | 8.94 | 1.70 |
| cand | filter | 7.00 | 7.12 | 0.98 |
| cand | q1 | 2.81 | 2.50 | 1.12 |
| cand | q2 | 2.81 | 2.56 | 1.10 |
| cand | q3 | 14.25 | 10.81 | 1.32 |
| cand | q5 | 14.81 | 8.94 | 1.66 |
