# Agent brief (v0.2 performance milestone)

Project: bend-frame, a Polars-2.0-inspired dataframe library in Bend, at
/Users/lukaszsamson/claude_fun/bend-frame. Bend binary: ~/.bend/bin/bend
(2.0.36, pinned in TOOLCHAIN, not on PATH). Lean 4.34 via elan, so
`bend PROOF.bend --verdict` works. Polars 2.0.0 lives in the uv project under
bench/ (`cd bench && uv run python ...`). Machine: Apple M2 Pro, 8 P + 4 E
cores, 32 GB.

Read before you start:
- plans/M_02.txt: the milestone plan. It is authoritative. Your task names its
  work package (W0..W8) and the design decisions (D1..D7) it touches.
- plans/REVIEW_PERF_FABLE.txt and plans/REVIEW_PERF_ASTRA.txt: the findings the
  plan acts on, with file:line references and measured probes.
- DESIGN.md §15 (the frozen v0.1 data contract: it does NOT change in v0.2),
  §16 (the v0.2 performance design, once W0 has written it), §14 (deviations).
- IMPLEMENTING.md: Bend pitfalls. Every section; it saves hours.
- /Users/lukaszsamson/claude_fun/bend/guide/GUIDE.md and guide/SHADERS.md
  (`bend guide shaders`). SHADERS.md is the only first-party text on writing
  fast parallel Bend; read its Machine, Data, Ownership, Cost model and Do not
  sections before you write a kernel. `~/.bend/bin/bend base <Name>` prints Base.

## The charge you are working against

The Bend author: "models are extremely good at writing correct Bend code and
proofs, but they suck at writing fast Bend. They use linked lists for
everything, clone unnecessarily, and are utterly incapable of parallelizing the
right way." Both perf reviews found this true on specific paths of this code
base. Treat the rules below as review criteria: a change that breaks one of
them needs a measurement in your report that justifies it.

1. No linked structure whose length scales with ROWS or BYTES. A Bend `String`
   is a cons list of chars and `List` is a cons list: fine for column names,
   expressions, plans, schemas; wrong for cells, rows, file contents, hash keys
   in a hot loop. Row data lives in flat `Array<U32>` buffers (F32 as bits,
   dictionary codes, validity). If you must hold strings, hold them in a table
   indexed by flat code arrays and touch each distinct string O(1) times.
2. No copy without a reason. `Array.clone`, `Column.clone`, `Frame.get_cloned`,
   `Dict.clone`, `Str.copy` are O(n). Prefer, in order: move (last use), borrow-
   and-return (take the buffer, hand it back in the result), reuse a dead
   operand's buffer for the output of a same-type map/zip. Every remaining clone
   on a row-sized buffer carries a comment saying why a move cannot work, and
   copy BYTES are counted in the G6 instrumentation.
3. Parallelism has exactly one right shape here: ONE balanced binary fork tree
   (`a b = f(x) g(y)`, both halves of similar cost) over a USER-DEFINED tree of
   owned chunks, ending in flat tail loops with enough work per leaf (a job
   under ~0.3-0.5 ms loses to the pool wake-up). Concretely:
   - Never fork by matching/rebuilding an `Array`'s ANode: the native lowering
     copies both halves (blk_half / blk_node). Never use `Array.fork` (@unsafe;
     --verdict refuses the file).
   - Never 1-vs-rest chains down a list; split lists/trees in halves.
   - Fuse before you fork: fewer, fatter passes first, then fork the fat pass.
   - Lanes must not share a mutable affine table; give each lane owned data or
     a costed copy. A `+` value read by every lane costs an atomic per read.
   - One fork tree per operator chain, not a split/rejoin per kernel: build
     chunks once and keep them through compatible operators.
   - F32 sums stay one sequential Neumaier pass in row order (D4). Only U32
     modular sum/count/popcount and proven min/max combines may tree-reduce.
   - THE SCHEDULER SHAPE RULE (DESIGN §16.10, measured): in a def with a
     parallel let, run nothing before the fork but matches and FLAT helpers.
     A call to a fork-free but non-flat def (list split/append, clone walks,
     cut helpers) in the branch arguments becomes a task that stops the grow
     pass; the subtree then runs on one thread and the whole tree tops out at
     ~2x. Build the work tree in a sequential prelude, fork by match only,
     join in the continuation. Nested forks inside an already-drained task do
     not add parallelism. Check with bench/w5/scale/forkaudit.py.
4. Write flat loops the compiler can make flat: a def with no parallel let, no
   closure apply, no non-flat call and no non-tail self call compiles to one
   native tail loop (`spin_N` in the C). No per-row allocation in a leaf loop
   (no per-row `Maybe`/`Some`/tuple boxes: use a single-constructor record or
   two branch-free templates). Pass constants as `~` templates.
5. Hot types: a type that is `+`-shared ANYWHERE in the program is refcounted
   EVERYWHERE (2x measured on the parser). Keep hot-loop types private and
   un-shared; check the emitted C of the real, imported program, not only a
   microprogram.
6. Verify in the emitted C (`~/.bend/bin/bend file.bend -o file.c`): in a hot
   def, `term_peek` is a borrow; `term_keep`, `ctr_take`, `rfc_seal` are counts;
   `blk_copy`, `blk_half`, `blk_node` are copies. Name the spin loop of every
   kernel you add and say what it allocates per row (should be nothing).

## Correctness and proof rules (unchanged from v0.1, never weakened for speed)

- Gates you keep green: `make test`, `make check`, `make proofs`; `make verdict`
  if you touched LAWS.bend, PROOF*.bend or anything they import (src/ is
  imported by the proofs). `make diff-smoke` after any engine change.
- The v0.1 data contract (DESIGN §15) is frozen: same values, validity, names,
  row order, F32 bits (except the existing NaN-payload relaxation), errors and
  error precedence. No new tolerance, no new exclusion.
- No `@unsafe`, no foreign workaround, no assumed equivalence. A kernel that
  replaces a proven kernel keeps its theorem chain (prove the new one or prove
  it equal to the old one). New kernels on proven paths get content laws, with
  in-place mutation controls (scripts/mutation_check.sh pattern). --verdict
  accepting a well-typed prototype is NOT evidence of equivalence.
- Tests: tests/**/*.bend, `#|` expected lines (scripts/test.sh). Work out the
  expected value before you run. `#! xfail <ID>` for a pinned known defect.

## Measurement rules (M_02 §5)

- Time native binaries, never the JS interpreter. `--threads N` is a runtime
  flag of the native binary. `IO.now` has 1 ms resolution: batch sub-ms cells.
- Other agents are running on this machine. Your numbers are PROVISIONAL: run
  `uptime` before and after, record load, interleave baseline and candidate,
  >= 5 fresh processes per cell, report medians AND raw samples. Gate numbers
  are taken by the orchestrator on a quiet machine with the W0 harness
  (bench/m2/); do not claim a gate passed from a loaded run.
- A speedup is reported against the pinned baseline (commit 3612482) built the
  same way, plus the result validated (dump or checksum) after the clock.

## Process

- Stay inside the files your task assigns you. Others edit other files at the
  same time; if you need a change elsewhere, keep it minimal and additive and
  say so in your report.
- Append Bend lessons to IMPLEMENTING.md under a heading named after your task
  (performance lessons especially: what the C showed, what was slow and why).
  Record deviations from the plan or contract in DESIGN.md §14.
- Don't commit unless your task says so. The orchestrator reviews and commits.
- Report: files changed, test/proof/diff results, before/after numbers with
  load and raw samples, emitted-C findings, deviations, open issues, and what
  the next agents need to know.
