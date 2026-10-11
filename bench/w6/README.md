# bench/w6: CSV producer and lane (W6.1 / W6.2) -- tests' harness, bench probe, tools

Production code: `src/csvprod.bend` (the piece producer) and `src/csvlane.bend` (the lane). Design:
DESIGN.md section 17 (17.4 D6 reader, 17.5 chunk hand-off, 17.6 obligations); lessons and the numbers:
IMPLEMENTING.md "W6.1 / W6.2". Neither is wired into `Csv.read` / `Csv.scan` yet (W6.3).

| file | what |
|---|---|
| `gen_adv.py` | writes `tests/csvadv/*.csv` (102 adversarial files) and `cases.bend`; the expected values are never stored: the reference is the v0.1 reader at test time |
| `cases.bend` | GENERATED list of the adversarial cases (name, schema letters, header, separator) |
| `hx.bend` | test helpers: read a file as bytes / as text (`File.read`), write files, small list utilities, the piece sizes (1 .. 1 MiB) |
| `cmp.bend` | comparing two `DF.dump` texts without deep recursion (hash + length, first differing character), one-line outcome |
| `rd.bend` | the TEST-SIDE reader: header step (from csvparse), `Pr.regions`, one balanced fork of `Ln.lane` over the regions, combine (malformed, ragged, first bad cell, concatenation, Dictionary merge): the shape W6.3 integrates |
| `probe.bend` | the bench probe (below) |
| `run_probe.py` | interleaved fresh-process runner: load, wall / user, instructions retired, cycles, RSS, raw samples in JSONL |
| `cops.py` | per-loop reference-count / copy / allocation counts of an emitted C file, loops found by their locals' names |
| `gen_tk.py` | writes `Tk.go2` (the tokenizer loop, one flat def) into `src/csvlane.bend` |
| `results/*.jsonl` | raw samples of the provisional runs |

Tests (`make test` runs them): `tests/csvprod.bend` (region starts equal the reference parser's record starts for
every case x 15 piece sizes, from offset 0 and from the second record), `tests/csvlane.bend` (typed columns,
errors, lines and text of the first bad cell: DF.dump equal to the v0.1 reader, 15 piece sizes, Dictionary and raw
strings), `tests/csvlane_lines.bend` (the lines of the kept rows), `tests/csvlane_f32.bend` (20,000 generated
texts, F32 bits equal to `F32.read`), `tests/csvlane_utf8.bend` (UTF-8 decoding equal to `File.read`). A case
name as the first program argument runs just that case (`bend tests/csvlane.bend quoted_nl`).

## Probe

    ~/.bend/bin/bend bench/w6/probe.bend -o build/w6/probe
    build/w6/probe [--threads N] <file> [piece] [pack|lanes|ref] [schema] [raw]
    python3 bench/w6/run_probe.py bench/w6/results/NAME.jsonl 5 'build/w6/probe --threads 1 bench/data/sales_1000000.csv 245760 lanes' ...

`pack`: the producer alone; `lanes`: producer, then the fork over the regions (read_ms, fork_ms), then untimed one
checksum per column; `ref`: v0.1's `Csv.read_with` with the same checksums (they must be equal). Schema letters:
U u32, I i32, F f32, B bool, S str (Dictionary parts), N skipped (a tokenizer-only run); default `USSUFFB` (the sales
file); `raw` reads Str columns as raw rows. The probe imports frame.bend: it is the real, hot-types build.
Numbers taken on a shared machine are PROVISIONAL (record `uptime`; gate numbers are the orchestrator's, bench/m2).
