# Agent brief (v0.1 release work)

Project: bend-frame, a Polars-2.0-inspired dataframe library in Bend, at
/Users/lukaszsamson/claude_fun/bend-frame. Bend binary: ~/.bend/bin/bend
(2.0.36, not on PATH). Lean 4.34 is installed via elan, so
`bend PROOF.bend --verdict` works. Polars 2.0.0 lives in the uv project
under bench/ (`cd bench && uv run python ...`).

Read before you start:
- plans/M_01.txt: the release plan. It is authoritative. Your task names its
  section and milestone.
- plans/REVIEW_ASTRA.txt and plans/REVIEW_FABLE.txt: the defects the plan
  fixes, each with a reproduction.
- DESIGN.md §15 (the v0.1 contract, once it exists) and §14 (deviations).
- IMPLEMENTING.md: Bend pitfalls. Every section; it saves hours.
- /Users/lukaszsamson/claude_fun/bend/guide/GUIDE.md as needed.
  `~/.bend/bin/bend base <Name>` prints Base defs.

Rules:
- Gates you must keep green: `make test`, `make check`, `make proofs`.
  Run `make verdict` if you touched LAWS.bend, PROOF*.bend or anything they
  import.
- Tests: tests/**/*.bend, with `#|` expected lines (see scripts/test.sh).
  Work out an expected value before you run, then confirm it. Never paste
  output in as the expectation without checking it.
- A test that pins a known defect carries an `#! xfail <ID>` line; the runner
  reports it as XFAIL. When you fix the defect, delete that line.
- Stay inside the files your task assigns you. Other agents are editing
  other files at the same time. If you need a change in a file you don't
  own, make it minimal and additive, and say so in your report.
- Append Bend lessons to IMPLEMENTING.md under a heading named after your
  task. Record any deviation from the plan or contract in DESIGN.md §14.
- Don't commit. The orchestrator reviews and commits.
- Report: files changed, test/proof results, deviations, open issues, and
  what the next agents need to know.
