# Changelog

## 0.3.0 (unreleased): the stabilisation release (plans/M_03.txt)

- **Independent verification restored on the pinned Bend 2.0.39.** `bend PROOF.bend --verdict` (BendTT, the Lean-checked kernel)
  prints ALL PROOFS CHECK again (~30 s). It had overflowed the machine stack since 2.0.38 (bendlang/bend#1984): the translation
  expanded the type-level def `FZW(c)` (a Sigma) of PROOF_filtsel.bend at its 17 uses; the Sigma is now written inline (the
  proof terms are unchanged). `make verdict` stays in `make ci`; `make verdict-probe` checks the translation alone. No reduced
  assurance in this release.
- **Proofs:** 242 laws (241 + `where_contents`, LAWS section 23: `Kernel.where`, the kept-row list of a selective filter, puts
  each kept row's index at its cursor in row order, the compaction's contract), 107 in-place mutation controls (104 + 3 on
  `Kernel.where`). Still tested only, now stated explicitly (DESIGN.md 8.3): the selective filter's gather (`Frame.take_rows`),
  the join's build side and direct ids, group_by's direct codes and key combine, the fused runner `Eval.runz`.
- **Targeted tests of the v0.2 fast paths** (expected values from independent Python models, `bench/v03/`):
  `tests/regress/V03_boundaries.bend` (the v0.3 Astra review's 102 cases), `V03_fastpaths.bend` (140 cases at the switch-over
  points: key spans 2^20 - 1 / 2^20, code ranges either side of 2^22, join spans 65535 / 65536 with each side smaller,
  selective filters at kept = h/8 and h/8 + 1, eager / lazy / chunked), `V03_fastpaths_big.bend` (native, 25 cases at
  600,000-row and 40,000-row boundaries), and four reader-validity fixtures in `tests/csvadv` read by every corpus test against
  the v0.1 reader. `make test-mutation-check` (in ci) requires these tests to fail under the v0.3 review's mutations.
- **Tooling on 2.0.39:** `make fork-audit` runs both halves again (the emitted C's task table and segment names changed);
  `scripts/test.sh` runs `#! native` tests as binaries (the three CSV lane tests: the interpreter lane got 3-7x slower in
  2.0.37, bendlang/bend#1983) and the per-file limit is back to 300 s; the PDS-H comparator compares nulls, NaN and signed
  infinities by class (self-test: 19 cases) and `make tpch-check` (sf 0.01) is in ci; `make coverage-check` fails ci when the
  committed `docs/COVERAGE.md` is stale; `toolchain-check` only warns on uv; the CI workflow reads the Bend 2.0.39 archive
  sha256 from `TOOLCHAIN` (checked against the release; the workflow has still never run).
- Docs: README's laws paragraph opens with the honest coverage sentence (M_03 section 4); stale `peep_f4_cell` premise text,
  counts and the selective-filter wording corrected.

## Unreleased: toolchain moved to Bend 2.0.39 (2026-10-31)

- `TOOLCHAIN` pins Bend 2.0.39 (was 2.0.36). Library code is unchanged; everything else that broke was Bend, not the library:
  - **Base changed `String.eq`** to `Cmp.is_eq(String.order(a, b))` (a loop `String.order.go` over an accumulator, no longer `String.cmp`). `Laws.str_eq_refl` / `Laws.str_eq_sound` (PROOF_lib.bend) are re-proven over `String.order.go` (`str_ord_refl`, `str_ord_lt`, `str_ord_gt`, a new `str_sound_step`); `make proofs` and `make mutation-check` (104/104) are green again.
  - **Runtime flags are now `+RTS --threads N -RTS`**; a bare `--threads N` reaches `IO.args` as an ordinary argument (the bench driver then tried to open the file "1"). `scripts/bench.sh`, `scripts/baseline.sh`, `bench/m2/run.py`, `bench/m6.py`, `bench/hc.py`, `bench/strbench.py`, `bench/w2/campaign.sh`, `bench/w4/run.py`, `bench/w5/*` use the new form. The `bench/spikes/` scripts and the historical result files keep the 2.0.36 spelling.
  - `scripts/test.sh` default per-file limit 120 s -> 900 s (see the next point).
- Open against 2.0.39 (drafts in `plans/issues/bend_2_0_39.md`): `bend PROOF.bend --verdict` (and `-o PROOF.bendtt`) die with "the machine stack overflowed" (2.0.36: ALL PROOFS CHECK in ~40 s), so `make verdict` / `make ci` fail at that gate; `bend FILE.bend` (run mode) uses ~10x the memory and runs 3-7x slower than 2.0.36 on the CSV tests (`tests/csvlane.bend`: 8 min, `csvprod`: 4 s -> 14 s, 0.5 GB -> 5.7 GB peak RSS). Binaries built with `-o` are unaffected.
- Performance on 2.0.39 (native, 1 thread, interleaved with 2.0.36 binaries, loaded machine): q1-q6 compute at 1M rows and the parse are within noise of 2.0.36 (parse 625-650 ms vs 655-673 ms). The `File.read_at` floor probe is unchanged (~105-125 ms for 41 MB). Parse is ~95% of end-to-end time in every q1-q6 e2e cell (compute is 4-55 ms); the largest compute cells are `str_join_1m` (500 ms), `str_group_1m` / `str_unique_1m` (~175 ms).

## Unreleased: reader peak memory (2026-11-01)

- The v0.2 reader no longer builds validity it throws away. A lane that finds no null in its region hands on a one-slot
  validity holding 1 (`Col.vtrim`, read with wrapping indices like the array of ones it replaces; the region's array is
  freed as the lane ends), and the combine counts a column's nulls first and, with none, never allocates or fills the
  column's 2^d validity array (`Csv.v2.nb`, `Csv.v2.vcopy`). Values, validity, dictionary codes and errors are unchanged
  (`make csv-fuzz-smoke`: 2 x 1500 cases x 7 piece sizes, 0 differences from the v0.1 reader; `make diff-smoke` 0 failing;
  `make test` 209/209 with TEST_TIMEOUT=3000).
- Peak footprint of one `read_csv` (`bench/mem/probe.bend read`, 1 thread): tpch lineitem (85 MB, 1.2M rows) 469 -> 303 MB,
  orders 91 -> 66 MB, sales_1000000 209 -> 154 MB, hc t_1000000 480 -> 448 MB; Polars 2.0.0 one thread: 185, 43, 101, 72 MB.
  bench/tpch driver (all nine queries) 677 -> 594 MB.
- What remains is the runtime's: freed blocks are reused only within their size class (the lanes' ~4096-slot parts can
  never become the 2^21-slot columns), filed as bendlang/bend#1986; and a String costs 16 bytes per character (the
  distinct-string file), bendlang/bend#1987. Repros in plans/issues/ (`allocclass.bend`, `strmem.bend`).

## Unreleased: performance on a PDS-H-style workload (2026-11-01)

New workload `bench/tpch/` (README there): TPC-H-shaped tables and nine PDS-H queries (Q1, Q3, Q4, Q5, Q6, Q10,
Q12, Q13, Q18) written with the public facade, a native driver, Polars twins and a checker; `make tpch`. Profiling it
with `sample` found four hot spots, fixed without touching any proven function (`make proofs`: ALL PROOFS CHECK). The
data contract is unchanged: every query matches Polars at sf 0.01 and 0.2; `make test` passes 209 of 209 (`tests/csvlane.bend` needs a limit above the default 900 s under load: 14 min, the 2.0.39 run-mode
slowness noted above), `make check` passes, `make diff-smoke` has 0 failing cases and `make bench-check` is identical.
- Joins build the key pair table over the smaller input, not always the right one (`Join.side`), and a first word key
  over a narrow range (span < max(2^16, 2 (nl + nr))) takes direct-address ids with no hashing (`Join.word`).
- A filter keeping at most 1/8 of the rows gathers the kept rows once by position before the (unchanged) compaction
  (`Eval.filter.sel`, `Frame.take_rows`, `Kernel.where`).
- group_by codes a word key directly while its span is below max(2^20, 2n) (`Grp.direct`; was 2^20, so a 1.2M-value
  key took a radix sort), and combining keys no longer densifies after each key (`Grp.combine`): one densify at the end.
- sf 0.2, one thread, loaded machine: the nine queries 384 -> 284 ms in total (Q5 2.2x, Q4 1.6x, Q3 1.5x, Q6 / Q18
  1.35x); the sales q1-q6 cells are unchanged within noise. Remaining gaps and why they stay: bench/tpch/README.md.

## 0.2.0 (performance milestone, 2026-10-11; not published)

The plan is `plans/M_02.txt`; the gate report is `plans/GATES_V02.md`. **The v0.1 data contract (`DESIGN.md` 15) is unchanged**: the same values, validity, names, row order, F32 bits (the existing NaN-payload relaxation aside), errors and error order, for every operation, eager and lazy. No new API surface beyond the engine and reader selectors.

Candidate claim, as far as the gates demonstrate it: "owned chunks and fused kernels reduce copying and improve measured throughput; parallel execution preserves the documented semantics on the supported paths". The load-independent gates are met: correctness (G1), memory on the frozen 1M workload (G4) and the phase / copy report (G6); the proof gate G5 is PARTIAL (the new kernels and peepholes have theorems, but the fused runner that the default `select` / `with_columns` / `filter` path now executes is not proven equal to the v0.1 runner the typing theorems cover; see "Verified scope" and "Not claimed"). **Every timing number below is PROVISIONAL**: the shared machine was never quiet (1-minute load >= 2 before every run), so by M_02 section 5 the timing gates G2 and G3 are recorded as UNEVALUATED, with the provisional observation beside each cell (several are not met even provisionally; `plans/GATES_V02.md` lists every one).

**Release status: experimental; macOS arm64 only (Linux x86-64 and hosted CI have never run); performance PROVISIONAL; the M_02 thread-scaling goals are incomplete.** In one true sentence: 1.7x to 113x faster on one thread depending on the workload, about 4-7x less peak memory on the sales workload, and threads help the CSV parse (1.9x), `describe` (3x) and scan-fed row-wise plans under the opt-in chunked engine (4x), while the default executor does not yet scale with threads.

### Changes

- **CSV reader (the default since 0.2.0).** A sequential producer of flat packed bytes in 240 KiB pieces with the record boundaries found in the same walk (`src/csvprod.bend`), ONE balanced fork of typed lanes over the regions (`src/csvlane.bend`: a generated one-def tokenizer, typed loops with cold private records, no per-cell string or list), and a sequential combine in region order that keeps v0.1's error precedence and dictionary codes (`Csv.v2.*` in `src/csv.bend`). The v0.1 reader is kept, selectable (`csv_engine_v01()`, `read_csv_engine`, `collect_engine`), and is the pinned reference of the CSV tests and fuzz.
- **Distinct-key strings.** A flat presized hash coder (`src/hcode.bend`; first-appearance ids, hash hits compared against the strings) and a lexical rank stage by radix refinement (`src/ranks.bend`) replace the Base-Map coder in group_by, unique, Raw n_unique, Raw sort keys and Dictionary ranks; the join probes a packed flat string table sequentially (no table clone per split).
- **Evaluator fusion** (on in the default executor): literal operands as scalars (F1), null-propagating zips with validity in one loop (F2), total casts inside the zip (F3), `fill_null` with the dtype default as a validity change (F4), filter predicate mask and count in one pass (F5), up to four aligned columns compacted per loop (F6), and the Filter + plain Select step at the plan root (F8). Kleene logic and fallible casts are not fused.
- **Fewer copies.** A liveness pass moves single-reference columns and borrows where a kernel hands the buffer back; group_by moves dead inputs and codes its key without a clone; the join copies its table only at a split; describe borrows and fuses its count / sum / min / max; `slice` is one range copy; `Sort + Head` gathers only the kept rows of the exact full argsort; the radix sort reads keys in place with one scan pass, skips sorted words and ping-pongs two buffers; n_unique is a radix sort plus a run count.
- **Chunked engine (opt-in).** Owned chunk trees (`src/chunks.bend`), generated chunked kernel wrappers (`src/ckernels.bend`) and a chunked executor (`src/cexec.bend`) behind `collect_with(engine_chunked(), ..)`: row-wise operators fork over leaves of 2^14 rows; sort, join, group_by, unique and describe run the flat code behind a boundary; a `scan_csv` whose consumer is row-wise is read straight into chunk leaves by the v0.2 reader. Exact against the reference engine on every differential case.
- **Parallel shape.** Every parallel let follows one rule found in this milestone (the Bend 2.0.36 scheduler's fork-shape rule, `DESIGN.md` 16.10): a forking def matches and forks and calls nothing non-flat before its parallel let; `make fork-audit` checks it statically (68 parallel lets in 28 files at 0.2.0, 0 findings) and is part of `make ci`.
- **Tooling.** `bench/m2/` (the frozen workload harness against the pinned baseline 3612482, with an instrumented copy / allocation mode, `make m2-g6`), `make diff-chunked` (G1), `make csv-fuzz` / `csv-fuzz-smoke` (the v0.2 reader against v0.1), `make fork-audit`; `make ci` now also runs `csv-fuzz-smoke` and `fork-audit`, and `diff-smoke` runs every case through the chunked engine too.

### Measured (PROVISIONAL; `plans/GATES_V02.md`, `bench/m2/results/w8-*.jsonl`)

Against the pinned v0.1 baseline (3612482), same driver, Apple M2 Pro, medians of 5 fresh interleaved processes, load 1.4-5.8 (so: PROVISIONAL), 1M rows, 1 thread unless noted:

- CSV parse of the 41 MB sales file: 3,966 -> 632 ms (6.3x); 1,814 -> 334 ms at 12 threads. Peak RSS of the 1M-row q1-q6 runs: 1,315-1,346 MB -> 190-314 MB (G4's 600 MB met).
- Compute (default executor): q1 10 -> 3 ms, q2 7 -> 3, q3 20 -> 12, q4 40 -> 13, q5 17 -> 10, q6 98 -> 49 (16 at 12 threads); end to end (parse + compute) 3.97-4.06 s -> 0.63-0.68 s.
- n_unique over 2^20 distinct U32 1,803 -> 16 ms; group_by / unique over 1M distinct strings 12.5 s -> 0.13 s; the 1M distinct-key join 4.2 s -> 0.36 s.
- Thread scaling (12 vs 1): parse 1.89x; describe 3.1x; with the opt-in chunked engine on inputs born chunked (a `scan_csv` plan with a row-wise first consumer) q1 4.0x, q2 3.8x, a 50% filter 5.9x, q3 / q5 1.4x; sort, join, group_by and unique do not scale; **the default executor does not scale on q1-q5 (about 1.0x)**. From eager frames the chunked engine is slower than the default at one thread (q1 8 vs 3 ms, q2 18 vs 3, q3 22 vs 12) and still 1.3-2x slower at 12 threads (4 / 6 / 15 vs 3 / 3 / 11): use it only over `scan_csv` plans with row-wise first consumers, on several threads.
- Limits beyond the sales workload: the 1M distinct-string `group_by` / `unique` peak near 630 MB and the distinct-key join near 1 GB (the 600 MB gate covers the frozen sales workload only); the v0.2 reader allocates ~1.39 GB in ~83 M allocations for the 41 MB file; no streaming; no performance guarantee against adversarial hash collisions.
- Copies: the compute phase of q1-q6 copies no array block (q3 and q5: under 5 kB; v0.1: 8-105 MB per query), exact counts from the instrumented build (`make m2-g6`).
- Small inputs (PROVISIONAL, one loaded run made after the W8 measurements): the 1k-row q3 / q4 / q5 controls take 0.100 / 0.050 / 0.100 ms per query against v0.1's 0.175 / 0.325 / 0.200 (`bench/m2/results/ctlfix-prov.jsonl`). At W8 q3 and q5 had regressed 1.57x / 1.25x: every radix sort allocated and prefix-summed a 2^17-slot histogram regardless of n; inputs of up to 2^14 slots now sort with 8-bit digits (`Radix.s8`; `make radix-check`). Every other cell is equal or faster. `make radix-check` covers both radix paths on 90 inputs, including the dispatch boundary (16383, 16384, 16385, 32768 rows), the empty input and heavy duplicates.

### Verified scope

241 laws in `LAWS.bend` (149 in 0.1.0; 82 added by the W8 close, 10 more by the B1 fix), all proven in `PROOF*.bend` over production functions, checked by `bend PROOF.bend` and `--verdict`; no axiom, no `@unsafe`, no open law. They fall in three groups of different weight, and the original gate G5 ("every changed proved production path keeps its theorem chain") is recorded as PARTIAL in `plans/GATES_V02.md`:

1. **Preserved theorems about existing functions** (the 149 v0.1 laws): none weakened, dropped or turned into a hypothesis; the Dictionary probe hypotheses stay conditional; `release_run` is unchanged. The evaluator typing theorems (`run_typed`, `eval_full_typed`, `eval_expr_typed`) are about `Eval.full` / `Eval.expr` / `Eval.run`, which since 0.2.0 the default `select` / `with_columns` / `filter` path no longer executes: those verbs run `Eval.runz(Eval.fuse(Eval.mark(compile)))`, and the equivalence of `runz` to `run` is not stated (`LAWS.bend` section 19 header).
2. **New local kernel and peephole theorems, each at stated instances and premises** (82 laws: `range_cell`, and sections 16-22): section 18's fused-kernel laws are each at ONE template instance while production instantiates the kernels for u32 / i32 / f32; section 19's peephole laws are one instance per peephole (`peep_f4_cell` was stated under a zero-payload premise; the post-review B1 fix below removed it); section 22 is 14 laws over 53 generated chunked wrappers, 4 of them (sum, min, max, popcount) on the chunked runner's path. New facts that matter beyond their kernels: `croom_of_cap` derives v0.1's `CRoom` hypothesis for per-leaf compaction; `sort_head_run` / `collect_obs` relate the physical runner `collect` executes to `Exec.run_pure`; `filter_select_run` proves the Filter + Select step.
3. **Unproven integration**: the fused runner `Eval.runz` as a whole, the chunked runner's `CX.*` walks and the `Eval.runz` call in each leaf, the v0.2 reader, the string coder, the rank stage, the radix sort, n_unique, describe's fused pass, the balanced list forks, and native execution.

- `make mutation-check`: 104 in-place mutations of production functions (14 in 0.1.0; 92 at the W8 close, 12 added by the B1 fix), all caught, the unmutated copy accepted.
- Tested only (`DESIGN.md` 8.2): the fused runner `Eval.runz` (tests/eval_fused: 473 expressions against the unfused evaluator, and every differential), the chunked executor (no theorem relates it to `Exec.run_pure`), the v0.2 reader, the string coder, the rank stage, the radix sort pipeline, n_unique, describe's fused pass, the balanced list forks, and the native scheduler.

### Testing

- 209 test programs (files) in `make test` (158 in 0.1.0; 203 at the W8 close; six added after the reviews: `tests/csv_bom.bend`, `tests/agg_median_zero_sign.bend` and four B1 regressions under `tests/regress/V02_B1_*`), 0 XFAIL. `docs/COVERAGE.md`: 816 operation x kind cells, 762 covered, 54 n/a with a reason, 0 missing.
- G1 differential counts are in `plans/GATES_V02.md` (generated cases through the reference and the chunked engine at four grains, Raw and Dictionary, deep plans, join stress, interpreter vs native; the CSV fuzz of the v0.2 reader against v0.1 at seven piece sizes).
- `make ci` green on the 0.2.0 tree (time and result in `plans/STATUS.md` "W8").

### Deviations from the plan (each recorded in `DESIGN.md` 14, v0.2 entries)

- G2 parse target revised at W0 from >= 4x to ">= 2x end to end and >= 4x on the fork phase" (`DESIGN.md` 17.8, 17.10 item 1): the File API returns cons lists on the IO thread, so the producer is serial. The G2 / G3 per-query thresholds of 16.8 / 17.8 were proposed at W0 and never frozen on a quiet machine.
- The chunked engine converts lazily (only where an operator needs the other representation), runs group_by flat, and reports data errors by a flat rerun; the reader picks chunks or a flat frame by the scan's consumer. The facade takes no chunk frame (results are flattened once).
- The group_by aggregate fork, the column-gather fork after a sort and a fused group_by scatter were built, measured and removed (no gain on this runtime); describe's column fork is kept.
- Not done: W2.5 (owned-partition coder), W2.6 (Dict index on flat arrays), W7 (flat string storage; deferred per `DESIGN.md` 17.11), a chunked group_by or partitioned parallel sort.
- D7 says the new layout stays opt-in "until G1-G6 pass"; the READER default was flipped on G1 (exact on every CSV test, the 10,000-case fuzz x 7 piece sizes, the adversarial corpus), G4 and provisional parse evidence while G2 / G3 are unevaluated (`DESIGN.md` 14 "W8"). The chunked ENGINE was not flipped. Nothing was removed (removal is a later explicit gate).

### Not claimed

- That every kernel forks, or that thread scaling is general: sort, join, group_by and unique stages do not scale with threads; F32 sums are one sequential pass by contract (`DESIGN.md` 15.5.3); the CSV producer is serial (File API), so the parse scales about 2x end to end.
- That any timing gate passed: no measurement was taken on a quiet machine.
- That the default execution path is covered by the evaluator typing proofs: it runs the fused runner `Eval.runz(Eval.fuse(Eval.mark(compile)))`, which no theorem relates to `Eval.run`; nor that the chunked runner's `CX.*` walks, or any template instance beyond the stated ones, are proven.
- That the chunked engine is a faster executor in general: from eager frames it is slower than the default (see Measured).
- That the reader default flip was gated: it was taken before G2-G4 were evaluated (see Deviations).
- Linux, x86-64 or hosted-CI portability: only macOS arm64 has ever run.
- That hashing or the CSV reader is linear in the worst case (collisions, skew, long records): growth is reported per row and byte at 100k / 300k / 1M, not bounded.
- A verified chunked engine, reader, coder or sort (tested only), Polars compatibility, native runtime correctness; everything 0.1.0 did not claim.

### Known limits

- The machine for every number: Apple M2 Pro (8 P + 4 E cores), shared with other jobs; Bend 2.0.36 native. Linux and hosted CI have never run.
- Peak RSS and times are workload-dependent; small inputs (under 2^14 rows) run the flat loops with no fork.

### Fixed after review

- **B1 (release blocker, both v0.2 reviews): `fill_null(neg(x), 0.0)` answered -0.0 on the null rows of an f32 column** (`1 / that`: -inf instead of +inf), in every engine; v0.1 and Polars answer +0.0. F32 `neg` wrote -0.0 under its nulls and the F4 fusion read that slot as the fill value. Fixed at the producers (the numeric unary maps write the dtype default under a null in their own masked loop; a valid -0.0 stays -0.0), in F4 (it resets the null slots itself: one in-place pass, or one masked copy of a borrowed column) and at the facade (`from_columns` resets the null slots of a column built from raw buffers: a dirty u32 slot made the chunked engine's tree sum wrong). The data contract is v0.1's again, bit for bit. The audit of every producer and the remaining premises is `DESIGN.md` 14 "v0.2 post-review: the null-slot invariant".
- Detection of the class: `src/p0.bend` checks that every null slot holds the dtype default (F32 by its bits); the differential driver fails any result, in any engine or chunk grain, that breaks it (class `P0`), the CSV fuzz compares it, and ~15 % of generated cases (all of them with `--features nullslot`) build a null producer feeding `fill_null` and a sign-sensitive consumer. Regressions: `tests/regress/V02_B1_*.bend`, including the review's two reproductions.
- Proofs: 241 laws (was 231): F4's cell law no longer assumes the null slot holds the default, and new laws state that the masked neg / abs / sqrt leave null slots at the default; 104 mutation controls (was 92).

## 0.1.0 (experimental release candidate, 2026-10-10; not yet published)

The first release, an EXPERIMENTAL one (plans/STATUS.md Decisions, 2026-10-10): the default optimizer is R1 only (adjacent `head` merging), the Dictionary string assurance is conditional (`Probe` / `EncProbe` hypotheses; index completeness is not proven), and the remaining proof work is deferred (R2-R5 as theorems, the grouped scatter invariant for `group_by`, Dictionary completeness and rank order). The release claim: a small Bend-native dataframe library with tested ETL operations, verified core buffer operations and evaluator typing, and a result-preserving default optimizer under documented input and runtime assumptions.

Not claimed: Polars compatibility, a verified engine, verified sort/group/join partitioning, CSV completeness, floating-point accuracy, native runtime correctness.

Toolchain: Bend 2.0.36, Lean 4.34.0 (for `--verdict`), Polars 2.0.0 for the reference side (pins in `TOOLCHAIN`).

### License

Apache-2.0 (`LICENSE`, `NOTICE`). `src/csvparse.bend` is a fork of the MIT-licensed hub package
`bend-csv-parser@0.1.0.1` and keeps its MIT notice.

### What is in it

- Five nullable dtypes (`Bool`, `U32`, `I32`, `F32`, `Str`) with no implicit casts; checked column and frame builders.
- Eager verbs and lazy plans with one data semantics: `select`, `with_columns`, `filter`, `sort` (stable, multi-key), `group_by`, inner / left / semi / anti joins, `head`, `slice`, `tail`, `drop`, `rename`, `unique`, `concat_vertical`, `describe`, `show`, `dump`.
- Expressions: casts (strict `cast`, lenient `try_cast`), arithmetic incl. `floor_div` / `mod` with floor rounding, comparisons, Kleene `and` / `or`, `when`, `is_in`, `clip`, `is_between`, `fill_null`, `abs`, `sqrt`, string predicates and `len_chars`, and the reductions `sum mean min max count len first last n_unique std var median`, in `group_by` and as global reductions.
- Lazy plans: schema and type errors before any row is read (`collect_schema`), binding validation (`validate_bindings`), `explain`, a default optimizer that merges adjacent `head`s, and an opt-in `optimize_full` (filter merge, predicate and projection pushdown, head sink).
- CSV: reading with type inference or explicit schemas, a bounded scan prefix for lazy scans, a streaming reader, writing with quoting and F32 formatting options; the contract is `DESIGN.md` 15.6.
- `Str` columns stored as plain strings or as a Dictionary (codes into distinct entries); the readers choose per column by cardinality, which gave 5-20x on the string-keyed benchmark queries at 1M rows.
- One numeric policy: a shared F32 total order (NaN greatest, `-0.0 == 0.0`), Neumaier-compensated F32 sums with a non-finite guard, wrapping integer arithmetic.
- A 2^23 row cap, checked before allocating.
- `DF.dump`, a typed text form of a result (dtypes, validity, F32 bits, errors), used by the tests and the differential checks.

### Verified scope

- 149 laws in `LAWS.bend`, all proven in `PROOF*.bend` over the production functions, checked by `bend PROOF.bend` and by `bend PROOF.bend --verdict` (BendTT). No axiom, no `@unsafe`, no open law.
- The default optimizer (adjacent `head` merging, R1 only) is proven result-preserving over the production runner `Exec.run_pure` for every plan and environment (frames and errors), scan plans included (scans live in an unnamed `scans` field of the environment; `hmerge_keeps_scans` / `release_keeps_scans` prove the optimized plan reads the same scans in the same order). Not proven: that `Plan.schema` and `Exec.validate` agree for `Optimize.release(p)` and `p` (true by inspection), and the IO materialisation `Exec.mat` itself.
- The evaluator is proven type-sound: an expression the shared analysis (`A.Expr.analyse`, used by `select`, `with_columns` and `filter`) accepts yields the predicted dtype and height, failing only where a strict cast may. The 20 older expression-typing laws (`LAWS.bend` section 2) are about `X.Expr.type`, which production uses only for `group_by`.
- Buffer and column contents: gather, compact (filter), the validity combinators, iota, the U32 sum and popcount folds, head, slice (U32), concatenation's append, the in-place null reset (`Eval.fix`, every column kind) and selection (`fill_null` on strings, `when`'s string storage), and the Dictionary string operations that keep every decoded string (encode, decode, merge, recode, find, gather, compact, append).
- Hypotheses the laws take rather than prove: row counts that fit the buffers (`CRoom`, `CatFits`), and for Dictionaries that each hash probe stops at an empty slot or at the key. `DESIGN.md` section 8 has the assurance matrix and the exact list of what is tested but not proven.
- Mutation evidence: eleven fixtures (`tests/proof_negative/`) mutate a renamed copy of a production function and try the production proof term against it (five are name-sensitive per their headers: an unmutated renamed copy is refused too, so they show a copy is rejected); and `make mutation-check` mutates 14 production functions in place and requires `bend PROOF.bend` to fail each time (all 14 caught).

### Testing

- 158 test programs (files; each holds many cases, so this is not an assertion count) in `make test`, regression tests for every defect of the two pre-release reviews, and `docs/COVERAGE.md`, the operation x case matrix (774 cells: 727 covered, 47 n/a with a stated reason, 0 missing) with a def-call report over `src/`.
- Goldens for six benchmark queries at 1k, 100k and 1M rows: q1, q2, q4, q5 equal Polars' output, q6 is within rtol 5e-5, and q3 is checked against the exact-rational F32 reference (`bench/golden.py`), not Polars (Polars' grouped f32 sum differs by an ulp or two: tiny fixture `inland`, Polars 96373.4141, reference 96373.4062). `make bench-check` covers 1k and 100k; 1M needs `CHECK_MAX=1000000 BENCH_MODE=check scripts/bench.sh`; the tracked 1k golden (`bench/golden/n1000`) is regenerated by each run.
- `make ci` runs: toolchain-check, check, runner-check, diff-driver-check, test, proofs, verdict, mutation-check, bench-check, diff-smoke (200 strict cases each in Raw and Dictionary storage, then the F32 reduction check), consumer-check and coverage. Every differential and reduction failure exits 1. Larger runs (`make diff`, `make diff-reduce`) are manual.
- A differential generator: eager vs raw-lazy vs optimized-lazy, and against a Polars-based oracle, in Raw and Dictionary string storage (22,000 generated cases in the M6 run, 0 failing), plus F32 reductions against an exact reference (`make diff-reduce`).

### Fixed after review

Two independent reviews of the first release candidate (`plans/REVIEW_V01_FABLE.txt`, `plans/REVIEW_V01_ASTRA.txt`) led to these changes before publication; `plans/STATUS.md` lists every finding and its disposition.

- Scan source identity: a CSV scan's frame was bound under the name `#scan<k>` and a user `source("#scan0", ..)` silently read it (`concat([source "#scan0" x=[1], scan x=[2]])` gave `x=[2, 2]`). Scans now live in a separate, unnamed `scans` field of `Env`; no name is reserved. New laws `hmerge_keeps_scans` / `release_keeps_scans`; `release_run` now speaks about scan plans directly. Regressions `tests/regress/V01_a_*` and `V01_b_*` (every lazy verb over `scan_csv` against the eager verb over `read_csv`).
- Differential exit status: `make diff` without `--strict` exited 0 on a failure the shrinker labelled a known defect. Any failure now exits 1 (classification only labels); `bench/diff/tests/test_exit.py` is the permanent driver regression; `reduce.py` has no allowlist.
- CI additions: `diff-driver-check`, `diff-smoke` (bounded strict Raw and Dictionary runs plus the reduction check), `mutation-check`, `consumer-check` and `coverage` are part of `make ci`; the runner self-test's timing margins were made robust under load.
- Mutation check: `scripts/mutation_check.sh` mutates 14 production functions in place (not renamed copies) and requires the proofs to fail.
- Coverage matrix: `scripts/coverage_matrix.py` and `docs/COVERAGE.md` (727 covered, 47 n/a with reasons, 0 missing), with gap-filling tests (`tests/coverage/`) and Polars twins (`bench/coverage/`).
- Documentation: the benchmark equivalence claim (q3), the `bench-check` scope, the exact scope of `release_run`, the mutation-evidence wording, the "failures fail the build" claim, test counting (files, not assertions), CI and platform status, and several stale comments (`LAWS.bend`, `tests/regress/B03_b_*`, `bench/diff/README.md`) were corrected.
- License: Apache-2.0 (noted above).

### Known limits

- Performance at 1M rows on one thread: 0.9-17x Polars' time (2-3.5x on the string-keyed queries); no thread scaling (12 threads ~1.0x of 1); peak RSS about 1.3 GB vs Polars' 168 MB; group_by / unique / join over fully distinct string keys 30-330x slower than Polars. Numbers in `bench/README.md`.
- Not proven, tested only: `optimize_full`, the cell values of most evaluator operations, sort, group_by and join, CSV, every floating-point result, Dictionary lookups that answer "absent".
- Out of scope: F64/I64/U64, dates, lists, structs, maps, window functions, rolling/cumulative, explode/pivot, regex, full/cross/as-of/non-equi joins, Parquet/IPC/SQL, streaming, GPU, automatic parallel scheduling, the Explorer API.
- Deliberate differences from Polars are listed in `README.md` ("Differences from Polars").
- The CI workflow (`.github/workflows/ci.yml`) has never run: the repository has no remote, so the workflow and its Bend archive checksums are untested. `make ci` runs the same gates locally. macOS arm64 is the only platform built and tested; Linux x86-64 has never been run.
