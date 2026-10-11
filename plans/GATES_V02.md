# v0.2 gate report (M_02 W8 / W6.5)

Plan: plans/M_02.txt (gates G1-G6 in section 0, rollout D7, measurement protocol section 5). Thresholds: M_02 section 0,
DESIGN.md 16.8 (engine, proposed at W0) and 17.8 (strings and reader, proposed at W0). Taken 2026-10-11 by the W8 agent.

## Verdict in one paragraph

**The machine was never quiet** (1-minute load before the runs 2.4-3.7, during them 1.4-5.8; M_02 section 5 requires
< 2 before a gate run), so **every timing below is PROVISIONAL and the timing gates G2 and G3 are UNEVALUATED**, exactly
as section 5 prescribes ("report provisional observations and leave gates unevaluated"; no sample was rejected after it was
seen). Each timing row still carries the provisional observation and whether it would meet its threshold, failing cells
included. The gates that do not depend on load are evaluated: **G1 met** (0 failing cases), **G4 met** for the frozen 1M
sales workload (RSS is a high-water mark, identical across repetitions), **G5 met**, **G6 met** (exact counts). Provisionally
NOT met even on a loaded machine: G2 for q3, q4, q5 and the parse (the 16.8 / 17.8 revised targets included), and the 1k
controls of q3 and q5 (G3 "within 10%"). No geometric mean is used anywhere.

## How it was measured

| what | command (from the worktree root) | records | load (1 min) |
|---|---|---|---|
| A: every frozen workload, baseline 3612482 vs candidate, default reader (v0.2) + reference executor, 1 / 4 / 12 threads, 5 fresh interleaved processes per cell | `python3 bench/m2/run.py run --label w8-ref-prov --engine reference --provisional` | `bench/m2/results/w8-ref-prov.{jsonl,md}`: 1,440 processes, 0 invalid | start 3.58; per process 1.4-5.8, median 2.5 |
| B: the same workloads, candidate, v0.2 reader + chunked executor | `run.py run --label w8-chunked-prov --engine v02,chunked --binaries candidate --provisional` | `w8-chunked-prov.*`: 720, 0 invalid | start 3.67; 1.9-4.2 |
| C: e2e of q1-q5 over `scan_csv`, read at collect into chunk leaves, both binaries | `run.py run --label w8-scan-prov --engine v02,chunked,scan --modes e2e --only q1_1m q2_1m q3_1m q4_1m q5_1m --provisional` | `w8-scan-prov.*`: 150, 0 invalid | start 3.44; 1.9-3.7 |
| C2: the same scans, default reader + reference executor, candidate | `... --label w8-refscan-prov --engine reference,scan ... --binaries candidate` | `w8-refscan-prov.*`: 75, 0 invalid | 2.4-2.7 |
| D: the candidate's v0.1 reader (still selectable), parse | `... --label w8-v01parse-prov --engine v01 --only parse_1m --binaries candidate` | `w8-v01parse-prov.*`: 30, 0 invalid | 2.1-2.7 |
| E: 1k-control check with the v0.1 reader on the candidate | `... --label w8-ctl-v01-prov --engine v01 --only ctl_q3_1k ctl_q5_1k --threads 1` | `w8-ctl-v01-prov.*`: 20, 0 invalid | 3.3 |
| F: pre-chunked compute (G2 as 16.8 defines it: inputs already chunked), batched 8 runs per window | `python3 -I bench/w5/scale/t53b.py bench/w5/scale/results/w8_t53b.jsonl --modes 3 4 --procs 5` | `bench/w5/scale/results/w8_t53b{.jsonl,_summary.md}`: 150 processes, hashes equal | 2.06-3.13 |
| G6: instrumented copy / allocation counts, 1 thread | `make m2-g6 LABEL=w8` | `bench/m2/results/g6-w8.{jsonl,md}`: 64 processes, all valid | n/a (exact counts) |

Binaries: `build/m2/baseline/driver` (git archive of 3612482) and `build/m2/candidate/driver` (src hash 16e2fecde1, the W8
tree with the reader flip, commit 3b57c14 / 4cf2e52; the checkout was dirty only in docs), both by Bend 2.0.36 from the
same `bench/m2/driver.bend`. Apple M2 Pro (8 P + 4 E cores), 32 GB, AC power, no thermal warning recorded. Every result
was validated after the clock against `bench/m2/expected.json` (frozen from the baseline): 0 invalid in 2,435 timed
processes and 64 instrumented ones. Cells are "median [min..max]" of 5 processes in ms unless noted; `S12` = median at
1 thread / median at 12 threads of the SAME workload and binary.

## G1 correctness (evaluated: MET)

| requirement | measured on the W8 tree | status |
|---|---|---|
| `make ci` green | `make ci` exit 0, "ci: all gates passed", 13 min 29 s at commit 3b57c14 (the flip; load 4-8): 203/203 tests, proofs + verdict ALL PROOFS CHECK, 92/92 mutations, bench-check, diff-smoke, csv-fuzz-smoke, fork-audit, consumer-check, coverage 762/54/0. Re-run on the final tree: plans/STATUS.md "W8" | met |
| old / new EXECUTOR differential (reference vs chunked at grains 2^0 / 2^2 / 2^4 / 2^14, plus eager / raw / collect / full and the Polars oracle) | fresh seeds: 8001 Raw 2,000; 8002 Dictionary 2,000; `make diff-chunked SEED=8011` (8011 Raw 2,000, 8012 Dict 2,000, 8013 Raw deep 500, 8014 Dict deep 500); 8021 Raw deep + joinstress 1,000; 8022 Dict deep + joinstress 1,000: **11,000 cases, 0 failing, 0 crashes, 0 oracle errors** (programs inadmissible for the eager-vs-lazy check by 15.9 counted apart, as always). Earlier: T5.3 13k+ cases, T5.5 seeds 1-4 and 601-604, `make diff-smoke` (400 per ci run) | met |
| interpreter vs native | seed 8031, 500 cases, `--backend both --chunked`: 0 failing, 0 crashes on either backend | met |
| CSV (v0.2 reader vs v0.1) | W6.4: 10,000 cases x 7 piece sizes + 2 chunk-mode reads per case (W6.6); W8 fresh seed 8041: **5,000 cases x 7 pieces, 44,936 reads compared, 0 differences**; ci's `csv-fuzz-smoke` 2 x 1,500; every CSV test and the adversarial corpus with the default flipped (203/203) | met |
| >= 10,000 release cases across seeds | 11,500 generated program cases + 5,000 CSV files at W8 alone, 0 failing | met |
| F32 bit-equal to v0.1 except the NaN-payload relaxation; no new tolerance | every m2 result hashed with F32 as bits (NaN canonical) against the frozen baseline outputs: 2,499 processes valid; `make diff-reduce SEED=8051 REDUCE_N=2000`: no finding | met |

## G2 scaling, 12 vs 1 thread (UNEVALUATED: provisional observations)

The M_02 target is >= 3x compute at 12 vs 1 thread on q1-q6 and >= 4x parse. W0 proposed per-query thresholds (16.8) and
a revised parse target (17.8: ">= 2x end to end and >= 4x on the fork phase"); neither set was frozen on a quiet machine
(DESIGN.md 16.8 / 17.8 headers; plans/STATUS.md "Open decisions"), so both are listed. 16.8 defines the compute cells on
inputs that are already chunked (F); the other columns show what the default executor (A) and the chunked engine over eager
flat frames (B, conversions inside the window) do with the same query.

| cell | M_02 | revised at W0 (proposed, where) | F: pre-chunked chunked engine, 1 / 12 thr (ms), S12 | A: reference executor, S12 | B: chunked from flat frames, S12 | provisional observation | status |
|---|---|---|---|---|---|---|---|
| q1 compute | >= 3x | >= 3x (16.8) | 2.50 [2.50..2.50] / 0.62 [0.62..0.69]: **4.00x** | 3 / 3 ms: 1.00x | 8 / 4 ms: 2.00x | meets 3x on chunked inputs only | unevaluated |
| q2 compute | >= 3x | >= 3x (16.8) | 2.62 [2.56..2.62] / 0.69 [0.62..0.75]: **3.82x** | 3 / 3 ms: 1.00x | 18 / 6 ms: 3.00x | meets 3x on chunked inputs | unevaluated |
| filter 50% (16.8 probe) | (>= 3x) | >= 3x (16.8) | 6.25 [6.19..6.31] / 1.06 [1.00..1.12]: **5.88x** | 8 / 8 ms: 1.00x | 19 / 7 ms: 2.71x | meets | unevaluated |
| q3 compute | >= 3x | >= 2x; 3x aspirational (16.8) | 13.44 [13.31..13.62] / 9.81 [9.69..9.94]: **1.37x** | 12 / 11 ms: 1.09x | 22 / 15 ms: 1.47x | **NOT met** (group_by runs flat: T5.3 item 3) | unevaluated |
| q4 compute | >= 3x | >= 1.3x (16.8) | not covered by F (sort runs flat) | 13 / 13 ms: 1.00x | 13 / 14 ms: 0.93x | **NOT met** (one radix sort, serial) | unevaluated |
| q5 compute | >= 3x | >= 1.5x (16.8) | 14.19 [14.06..14.25] / 10.31 [10.25..10.38]: **1.38x** | 10 / 10 ms: 1.00x | 10 / 10 ms: 1.00x | **NOT met** (flat join + flatten) | unevaluated |
| q6 compute (describe) | >= 3x | >= 2x (16.8) | not covered by F (eager describe) | 49 [48..50] / 16 [16..17] ms: **3.06x** (the column fork) | 50 / 16 ms: 3.12x | meets 3x | unevaluated |
| parse 41 MB, end to end (read + walk) | >= 4x | >= 2x end to end (17.8, 17.10 item 1; DESIGN 14 "v0.2 W0 strings / reader" item 1) | - | 632 [632..642] / 334 [333..336] ms: **1.89x** (e2e mode 640 / 342: 1.87x) | 634 / 339: 1.87x | **NOT met**, either target (serial producer: 17.10) | unevaluated |
| parse, fork phase | - | >= 4x on the fork phase (17.8) | not measured separately at W8; DESIGN 16.10 "Fork audit" ESTIMATES ~5-6x from the instrumented scheduler build | - | - | no W8 measurement | unevaluated |
| e2e q1-q5 over scan_csv into chunk leaves (W6.6) | (report) | - | C: q1 616 / 316 (1.95x), q2 644 / 335 (1.92x), q3 626 / 328 (1.91x), q4 633 / 335 (1.89x), q5 636 / 327 (1.94x) ms; baseline 3,982-4,028 / 1,822-1,862 ms (2.15-2.19x) | C2 (reference executor): 620-640 / 329-346 ms, 1.85-1.92x | - | bounded by the parse | report only |
| distinct-string and join cells | report (16.8) | report | - | str group / unique / join 1M: 0.98x / 0.98x / 1.01x; nunique 1.07x (baseline 1.58x / 1.59x / 0.98x / 2.02x) | the same, 0.98-1.00x | the new coder and join are sequential by design (17.3.3) | report only |

## G3 one-thread targets (UNEVALUATED: provisional observations)

Candidate = default reader + reference executor (run A) unless noted; 1 thread.

| cell | M_02 | W0 proposal (16.8 / 17.8) / W3 interim | baseline 3612482 | candidate | provisional observation | status |
|---|---|---|---:|---:|---|---|
| q1 compute | <= 3 ms | keep (16.8) | 10 [9..10] | 3 [2..3]; batched (F mode 4) 2.19 | meets | unevaluated |
| q2 compute | <= 3 ms | keep (16.8) | 7 [6..8] | 3 [3..4]; batched 2.31 | meets (median at the limit, batched below) | unevaluated |
| q3 compute | <= 12 ms | keep, conditional on W3 (16.8); W3 interim <= 15 | 20 [19..21] | 12 [11..13]; batched 10.12 | at the limit unbatched (the 13 ms of earlier runs is inside this range), below it batched; W3 interim met | unevaluated |
| q4 compute | <= 20 ms | keep (16.8); W3 interim <= 25 | 40 [40..41] | 13 [13..14] | meets | unevaluated |
| q5 compute | no > 10% regression vs baseline | keep (16.8) | 17 [16..18] | 10 [10..11] (0.59x) | meets (faster) | unevaluated |
| q6 compute | <= 60 ms | keep (16.8; W1c) | 98 [97..99] | 49 [48..50] | meets | unevaluated |
| n_unique over 2^20 distinct shuffled U32 | <= 30 ms | - | 1,803 [1,771..2,075] | 16 [15..16] | meets | unevaluated |
| distinct-string group_by, 1M | <= 2 s | <= 1.5 s (17.8) | 12,458 [12,416..12,660] | 125 [123..127] | meets | unevaluated |
| distinct-string unique, 1M | <= 2 s | <= 1.5 s (17.8) | 12,517 [12,436..12,935] | 126 [124..128] | meets | unevaluated |
| distinct-key join 1M x 1M | <= 2 s | <= 2 s (17.8) | 4,186 [4,159..4,255] | 356 [351..366] | meets | unevaluated |
| coder, 1M distinct short keys | (in <= 2 s) | <= 0.4 s (17.8) | - | not timed alone at W8; bounded by the group_by cell above (125 ms includes it) | meets by the bound | unevaluated |
| sort words of a distinct Raw string column, 1M | - | <= 1.0 s (17.8) | - | not in the frozen workload list; not measured at W8 (W2 pk ranks measured it provisionally, IMPLEMENTING "W2 pk ranks") | no W8 number | unevaluated |
| read of a 1M-distinct str column | - | <= 1.5 s / <= 0.8 s (17.8) | - | not in the frozen list; not measured at W8 | no W8 number | unevaluated |
| 41 MB parse, 1 thread | <= 2 s | <= 1.5 s (17.8) | 3,966 [3,952..3,989] | 632 [632..642] (v0.1 reader on the candidate, D: 3,911) | meets | unevaluated |
| 41 MB parse, 12 threads | <= 0.6 s | keep (17.8) | 1,814 [1,805..1,818] | 334 [333..336] | meets | unevaluated |
| 1k control q1 (500 per window) | within 10% | - | 0.042 ms | 0.036 (0.86x) | meets | unevaluated |
| 1k control q2 (500 per window) | within 10% | - | 0.042 | 0.038 (0.90x) | meets | unevaluated |
| 1k control q3 (40 per window) | within 10% | - | 0.175 [0.150..0.175] | **0.275 [0.275..0.275] (1.57x)** | **NOT met**: a fixed per-query cost, not the reader (E: 0.300 with the v0.1 reader on the candidate vs 0.175) | unevaluated |
| 1k control q4 | within 10% | - | 0.275 | 0.300 (1.09x) | meets (at 9%) | unevaluated |
| 1k control q5 | within 10% | - | 0.200 [0.175..0.200] | **0.250 [0.250..0.250] (1.25x)** | **NOT met** (same: E 0.275 vs 0.200 with the v0.1 reader) | unevaluated |
| 1k control q6 | within 10% | - | 0.525 | 0.200 (0.38x) | meets | unevaluated |
| growth 100k / 300k / 1M, time per row and per input byte | report | per-row time at 1M <= 2x that at 100k (17.8, coder) | - | str group: 120 / 137 / 125 ns per row, 4.70 / 5.29 / 4.82 ns per byte; str unique: 120 / 137 / 126 ns, 4.70 / 5.29 / 4.86 ns/B; str join (bytes of both files): 230 / 293 / 356 ns per row, 4.91 / 6.18 / 7.46 ns/B (1M / 100k per row 1.55x); long-prefix keys 100k / 300k: group 300 / 277 ns per row (5.36 / 4.94 ns/B), unique 300 / 273, join 590 / 607 ns per row (5.47 / 5.62 ns/B) | meets the 2x rule; no superlinear step at these sizes (not a worst-case claim) | report only |

The q3 / q5 1k regression: the controls of q1 / q2 / q4 / q6 are at or below v0.1, q3 and q5 (both with a group_by and a
small string sort) cost ~0.1 ms more per query with EITHER reader (run E), so it is a fixed cost of the v0.2 compute path
at small sizes (group_by / its key coding most likely; not diagnosed at W8). 100k-row q3 / q5 are equal to v0.1 (2 vs 2 ms).

## G4 memory (evaluated for the frozen workload: MET)

Peak RSS (`/usr/bin/time -l`, MB) does not move with load: the 5 repetitions of a cell agree within 1-4 MB.

| cell | target | baseline 3612482 | candidate (default reader, reference executor) | candidate v02,chunked | status |
|---|---|---:|---:|---:|---|
| q1-q6 at 1M rows, `phases` (inputs preserved: the clone kept, as Polars) | <= 600 MB | 1,323-1,346 (1-12 thr) | 224-234 at 1 thr, 257-314 at 12 thr (q6 314 max) | 226-258 at 1 thr, 267-310 at 12 thr | **met** |
| q1-q6 at 1M rows, `e2e` (consumed inputs) | <= 600 MB | 1,315-1,324 | 190-201 at 1 thr, 223-281 at 12 thr | 192-281 | **met** |
| q1-q5 e2e over scan_csv (C, C2) | <= 600 MB | 1,315-1,325 | C2 (reference executor): 190-233 | C: 186-236 | **met** |
| parse share (17.8 proposal) | <= 400 MB at 1-12 thr | 1,314-1,320 | 216 / 227 / 249 at 1 / 4 / 12 thr | 216-253 | met (proposal) |
| distinct-string group_by / unique 1M (not the frozen sales workload) | report | 870-943 | 622-647 | 622-651 | report: above 600 MB |
| distinct-key join 1M | report | 1,254-1,284 | 1,030-1,057 | 1,030-1,060 | report: above 600 MB |
| long-prefix join 300k | report | 1,071-1,088 | 867-885 | 867-882 | report: above 600 MB |

Live / retained storage per phase (G4's second sentence) is G6's table 3 / 4 (`g6-w8.md`): after the parse the frame is 33.6 MB
live for 28 MB of flat lower bound (1.20, the power-of-two blocks); the v0.2 reader allocates 1,392 MB in 83 M allocations to
parse the 41 MB file against v0.1's 4,036 MB in 352 M (the remaining allocations are the File API's per-byte cons cells).

## G5 proofs (evaluated: MET)

| requirement | measured | status |
|---|---|---|
| every changed proved production path keeps its theorem chain | 231 laws (149 at the baseline), all proven over the production functions; no v0.1 law weakened, dropped or turned into a hypothesis; `release_run` unchanged; DESIGN.md 8.2 lists every v0.2 law section and the tested-only parts | met |
| new chunked / fused kernels have content laws; --verdict passes | LAWS sections 18 (fused kernels), 19 (peepholes), 20 (Filter + Select), 21 (chunk trees, incl. `croom_of_cap` discharging CRoom per leaf), 22 (chunked wrappers); `make proofs` and `make verdict` ALL PROOFS CHECK in `make ci` | met |
| no @unsafe, foreign workaround or assumed equivalence | none in src/, LAWS.bend, PROOF*.bend (`--verdict` refuses `@unsafe`); `Array.fork` unused | met |
| in-place mutation controls for new kernels / bridges | 92 mutations (78 new), all rejected, the unmutated copy accepted (`make mutation-check`) | met |
| dictionary hypotheses stay conditional | `Probe`, `EncProbe`, `MergeProbe`, `FindProbe` unchanged (W2.6 not done) | met |
| tested-only parts listed | the chunked runner, the v0.2 reader, the coder, the rank stage, the radix pipeline, n_unique, describe's fused pass, the balanced list forks, the scheduler (DESIGN.md 8.2) | met (as a listing; none is proven) |

## G6 phases and copies (evaluated: MET)

| requirement | measured | status |
|---|---|---|
| parse, preparation, compute and output reported separately, plus end to end | A's `phases` mode: read / walk / prep (the preservation clone) / compute / check (hash) per cell, and the `e2e` mode; e.g. q1 1 thread: parse 637, prep 3, compute 3, check 1 ms, e2e 633 ms (baseline 3,965 / 1 / 10 / 1, e2e 3,973) | met |
| allocated / copied bytes, instrument overhead apart | `g6-w8.md`: exact counters per phase (instrumented binaries, never timed); compute-phase `blk_copy` bytes q1-q5 baseline 8.39 / 16.78 / 37.75 / 12.58 / 16.78 MB -> candidate 0 / 0 / 0.00 / 0 / 0.00 MB; q6 104.9 -> 0 MB; compute allocations q1 29.4 -> 7.4 MB, q2 42.0 -> 12.6, q3 96.9 -> 23.7, q4 123.0 -> 37.3, q5 88.5 -> 44.7, q6 245.1 -> 94.4 MB; the chunked engine from flat frames allocates more (q1 32.5, q2 83.2, q3 73.3 MB: the conversions) | met |
| W3 interim: clone bytes on q1-q5 down >= 50% | down 100% (all five 0 MB in the compute phase) | met |
| performance gates in a controlled job, not in noisy CI | `make ci` runs correctness only; timing lives in bench/m2 (this report) | met |

## D7 rollout status

| step | status |
|---|---|
| runnable baseline frozen at 3612482 with its oracle artifacts | yes (`make m2-baseline`, `bench/m2/expected.json`) |
| engine selector and representation boundary | yes (`Engine`, `CsvEngine`; DESIGN.md 16.5) |
| new layout and fusion opt-in until G1-G6 and clean-consumer checks pass | fusion: on in the default executor since T4.x (proven per kernel, G5); chunked layout: opt-in, NOT flipped (G2 not met on q3-q5) |
| default flip separate from removal | the READER default flipped at W8 (commit 3b57c14, its own commit; DESIGN.md 14 "W8"), on G1 (exact) and provisional parse / RSS evidence while G2-G3 are unevaluated: a DEVIATION from "until G1-G6 pass", taken on the orchestrator's instruction and recorded; nothing removed |
| removal of the v0.1 reader / reference executor | NOT done; needs a stabilization period, two independently reproduced full gate runs with the new default on a quiet machine, and a reproducible final baseline run |
| consumer, mutation and hosted-platform checks | consumer-check and mutation-check green in `make ci`; hosted CI (no remote) and Linux never run |

## What should block calling v0.2 "done" (gate view)

1. No timing gate was evaluated: a quiet-machine run of this same sequence (bench/m2/README.md "W8: reproducing the gate
   report") is still owed, twice per D7 before any removal.
2. G2 is provisionally not met for q3, q4, q5 and the parse (also against the W0-revised targets): the stages that dominate
   them (group_by, the radix sort, the join, the serial CSV producer) do not fork. Either accept these as the v0.2 limits
   (the README and CHANGELOG state them) or schedule a chunked group_by / partitioned sort.
3. The 16.8 / 17.8 thresholds were never formally frozen; this report uses them as proposed.
4. The 1k-row q3 / q5 controls regress 1.25-1.57x (G3 "within 10%"), independent of the reader.
5. The reader default flip precedes G2-G4 evaluation (D7 deviation above); the orchestrator decides whether that stands.
