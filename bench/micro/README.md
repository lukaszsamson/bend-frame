# bench/micro: the perf-review probes, preserved

Two native microbenchmarks written for `plans/REVIEW_PERF_ASTRA.txt` (Bend 2.0.36, commit 3612482), copied
verbatim from `plans/perf_review_20261011/` so they survive as a regression reference for the v0.2 milestone
(M_02 section 5: "Preserve/reproduce the audits' source-backed probes under bench/micro/"):

- `ops.bend`: input of 2^20 distinct consecutive U32 values; modes `select` / `headselect` / `move` (run 64
  times) and `nunique` / `unique` (once). Input construction is before `IO.now`; the summary line (sum and
  rows through `DF.dump`) is printed after the clock.
- `maps.bend`: the same input, 128 increment maps; `flat` (full-buffer maps in sequence), `par` (split and
  rejoin for every map) and `pipeline` (split once, 128 maps inside each leaf chunk, rejoin once), six fork
  levels. Shows that ANode splitting copies (blk_half / blk_node) and that owned chunks amortise it. Prints
  `sum=... cells_ok=True` (an untimed cell-by-cell comparison).

`REPRO.txt` is the original reproduction note (its paths still say `plans/perf_review_20261011/`; the
sources are identical here). The original raw results (`results.json`, `cell_checks.json`) stay in
`plans/perf_review_20261011/`: 3 fresh processes per cell on a loaded machine, exploratory, not gate data.

They are diagnostic probes, not replacement kernels. They import `frame.bend` and `src/kernels.bend`, so
`make check` compiles them against whatever the checkout currently is.

## Running

    make m2-micro LABEL=name                      # builds into build/m2/micro, 3 processes per cell, 1/4/12 threads
    python3 bench/m2/run.py micro --label name --procs 5 --threads 1 4 12 [--rebuild]

Results: `bench/m2/results/micro-<label>.jsonl` (one record per process: command, ms, the printed check
lines, peak RSS, load before/after, commit). The runner interleaves the cells, prints the medians and
verifies that the check lines are identical in every process. By hand:

    mkdir -p build/m2/micro
    ~/.bend/bin/bend bench/micro/ops.bend -o build/m2/micro/ops
    build/m2/micro/ops --threads 1 select

Numbers from a loaded machine are provisional (see `bench/m2/README.md`). To inspect the native array
lowering: `~/.bend/bin/bend bench/micro/maps.bend -o /tmp/maps.c` and search `blk_half`, `blk_node`,
`blk_copy` (they allocate/copy; ANode is not a zero-copy view).
