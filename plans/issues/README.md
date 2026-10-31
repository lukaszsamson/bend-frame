# Upstream issue drafts (not filed)

Drafts for issues found while building bend-frame v0.2. Filing is the maintainer's call. Each one has a
standalone reproduction next to it.

| draft | for | repro | status |
|---|---|---|---|
| `polars_nan_join.md` | pola-rs/polars | `polars_nan_join.py` (run with Polars 2.0.0) | draft; search existing issues first |
| `bend_fork_shape.md` | bendlang/bend | `forkshape.bend` (Base only) | draft |
| `bend_file_buffer.md` | bendlang/bend | `readfloor.bend` (Base only; reads `data.csv`) | draft |
| `bend_2_0_39.md` | bendlang/bend | this repository (`bend PROOF.bend --verdict`; `tests/csvprod.bend`) | filed: verdict overflow as bendlang/bend#1984 (2.0.38 regression, minimal repro in the issue), run-mode memory as bendlang/bend#1983 (`File.read_bytes` commits `max` bytes on the JS lane since 2.0.37); the `+RTS` item is not a bug (documented in the 2.0.38 notes) |
