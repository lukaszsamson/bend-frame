# W0 strings / reader spikes (disposable)

Feasibility spikes for the v0.2 performance milestone, work package W0, design decisions D5
(strings) and D6 (reader): plans/M_02.txt, the design they support is DESIGN.md section 17.
Nothing here is production code; `src/` is untouched (the spikes import it read-only).
Every number is PROVISIONAL: the machine was shared (1-minute load 12-25 during the campaign,
up to 260 earlier, another agent's baseline runs concurrently); gate numbers are taken by the
orchestrator on a quiet machine with the W0 harness (bench/m2/).

## Build and run

    tools/build.sh                     # every spike binary + its emitted C into build/
    tools/campaign.sh [t1 t2 t3 t4 t5 t6]   # the measurement campaign (results/*.jsonl)
    python3 tools/adv.py               # T5b adversarial differential (build/rd_adv = rd_frame,
                                       #   copied by build.sh so a running campaign keeps its binary)
    python3 tools/tables.py            # the DESIGN.md 17.9 tables from results/*.jsonl
    python3 tools/summ.py results/t5_scale.jsonl ms read_ms fork_ms merge_ms max_rss_mb load
    python3 tools/hot.py build/rd_frame.c CON SCON     # which constructors are refcounted
    python3 tools/cops.py build/rd_frame.c 16777216ull # count/copy/alloc ops per spin loop

The reader spikes read `bench/data/sales_1000000.csv` (regenerate with
`cd bench && uv run python gen.py` if missing); `bench/data` in a worktree may be a symlink to
the main checkout's. `pk_cold`, `cnt_cold`, `cnt_hot`, `hs_solo` take no file argument and must
run from the repository root.

## Files

| file | task | what |
|---|---|---|
| coder.bend | T1, T2, T6 | the distinct-key coder `Hc.code` (presized flat open addressing, three `Array<U32>`: hash, first row + 1, id) vs `Sort.str_codes_par` / `str_codes` (modes `new`, `old`, `oldseq`); lexical ranks after coding: `rrad` (radix refinement over packed big-endian UTF-8 words), `rnew` (merge sort over a flat code-point buffer), `rmap` (Base Map over the distinct entries), `rold` (today's `Sort.str_words`); `t6` (hashing cons strings vs a flat UTF-8 buffer). Key shapes: distinct, prefix (31-char shared prefix), skew (half the rows in 8 keys), equal, low (1000 keys), uni (NUL, UTF-8 length boundaries, U+10FFFF, prefixes) |
| probe.bend | T3 | parallel coding with OWNED HASH PARTITIONS (rows moved into 2^L partitions by hash bits, one fork over the partition tree, each lane its own table, global first-appearance remap from the entries' first rows, codes and strings moved back) vs the sequential borrowed coder; same codes |
| rd.bend | T5 | the piece reader library: producer (File.read_at pieces -> packed bytes + lexical scan -> record-aligned regions), balanced fork over regions, tokenizer into flat field-index arrays, typed column loops (u32, f32 fast path + F32.read slow path, bool, str with a per-region byte-range coder), UTF-8 decoding with the runtime's rules, ordered dictionary merge, concatenation |
| rd_drv.bend | T5 | driver body: phases timed, checksums, canonical error (`malformed`, `ragged <line> <width>`, `bad <column> <line>`, `ok`); type string per column (U S F B, other letters skip the column: phase decomposition) |
| rd_frame.bend | T4, T5 | the reader INSIDE a program importing frame.bend (hot String/List), plus `ref` (today's `Csv.read_with`, same checksum) and `hstep` (today's parser alone) |
| rd_solo.bend | T5 | the same reader without frame.bend (List is still hot there: the schema list is shared across lanes) |
| pk_cold.bend | T4 | the producer alone with List cold |
| cnt_cold.bend, cnt_hot.bend, cnt.bend | T4/T5a | the File API floor: File.read_at pieces whose byte lists are only counted (List cold / hot) |
| hs_solo.bend | T4 | today's parser (File.read + H.step) in a program importing only csvparse.bend (cold) |
| tools/run.py | all | fresh processes, interleaved, `uptime`-style load before/after, time(1) RSS, raw JSONL |
| tools/adv.py | T5b | adversarial cases x 15 piece sizes, spike vs reference |
| tools/summ.py, hot.py, cops.py, build.sh, campaign.sh | | analysis / build helpers |

## Results (raw samples)

`results/*.jsonl`: one record per process (command, rep, load before/after, wall/user/sys,
max RSS, the program's JSON). `results/superseded/` holds a first T1-T3 campaign whose timed
regions also freed the input strings (the rows were dropped before the clock stopped); the
programs now keep the rows alive past the clock (`keep` field) and the campaign was re-run.
The summary tables are in DESIGN.md section 17.9.

## Known spike limitations (not design limitations)

- Header handling: the spike marks only the first region "header pending" and passes it on
  only through empty regions; a file whose first region holds only blank lines before the
  header loses its header (tools/adv.py case `lead_blank`, piece sizes <= 7). The design
  parses the header sequentially before the regions (DESIGN 17.4.1).
- The dtype-count / header-width check, inference, headerless names and EncAuto storage are
  not implemented (explicit schema, Dictionary storage for Str); see DESIGN 17.4.5.
- The first bad cell is reported by (column, line); its text is not decoded.
- UTF-8 packing for ranks assumes code points <= U+10FFFF (DESIGN 17.3.2 gives the fallback).
