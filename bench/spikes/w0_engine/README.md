# W0 engine spikes (v0.2 performance milestone, plans/M_02.txt)

Disposable probes behind DESIGN.md section 16 (the v0.2 engine design). They import `src/*.bend`
and copy nothing into production; `src/`, `LAWS.bend` and `tests/` are untouched. Every number here is
PROVISIONAL: the machine was shared (1-minute load 17-33 during the sweeps, up to 110 earlier), medians
of 5 fresh processes per cell with the load recorded per sample in `results/*.jsonl`. Gate numbers are
taken by the orchestrator on a quiet machine with the W0 harness.

Build and run (Bend 2.0.36, from the repo root; `--threads N` is the native binary's runtime flag):

```sh
B=~/.bend/bin/bend
$B bench/spikes/w0_engine/s1_chunks.bend -o build/s1 && build/s1 --threads 12 q1chunk 14 20
$B bench/spikes/w0_engine/s2_align.bend  -o build/s2 && build/s2 --threads 12 ragged 14 20
$B bench/spikes/w0_engine/s3_reduce.bend -o build/s3 && build/s3 --threads 12 usum 14 20
$B bench/spikes/w0_engine/s4_owner.bend  -o build/s4 && build/s4 --threads 1 colclone 64
$B bench/spikes/w0_engine/laws_spike.bend            # 113 TODOs = 107 inherited from PROOF_contents' closure + 6 stated open here
$B bench/spikes/w0_engine/laws_spike.bend --verdict  # the same under BendTT
sh bench/spikes/w0_engine/run_s1.sh 5 10             # the S1 sweep -> results/s1.jsonl
sh bench/spikes/w0_engine/run_s234.sh 5 10           # S2/S3/S4   -> results/s{2,3,4}.jsonl
python3 bench/spikes/w0_engine/summarize.py bench/spikes/w0_engine/results/s1.jsonl
$B bench/spikes/w0_engine/s1_chunks.bend -o build/s1.c && python3 bench/spikes/w0_engine/cstats.py build/s1.c --min-params 8
```

Each binary takes `<mode> <grain log2> <reps>` (S4: `<mode> <reps>`), runs `reps` repetitions in one
`IO.now` window with the outputs dropped (the root row count kept as the data dependency), then one
untimed verification run whose checksum the flat and chunked variants must share. The header of each
`.bend` lists its modes.

## S1 chunk layout and grain (`s1_chunks.bend`, results/s1.jsonl, s1_hirep.jsonl)

Chunk tree `UL{n, d, a} | UN{rows, l, r}` (user type, O(1) to match: no blk_half / blk_node), 2^20 rows,
leaves of 2^grain rows; one balanced parallel let per node, flat loops at the leaves. ms per rep,
medians of 5 processes, load 17-23:

| cell (1M rows)                                  | 1 thr | 4 thr | 12 thr |
|-------------------------------------------------|------:|------:|-------:|
| q1 today (2 clones, bcast, 2 zips, popcount, 7 compactions) | 8.7 | | |
| q1 today, 3 compactions (projection pushdown)   | 5.8   |       |        |
| q1 fused flat (pred+count in place, 3-col compaction) | 3.3 |     |        |
| q1 chunked grain 2^13 / 2^14 / 2^15 / 2^16      | 3.6 / 3.6 / 3.5 / 3.4 | 1.1 / 1.3 / 1.1 / 1.2 | 0.8 / 0.8 / 0.8 / 0.9 |
| q1 chunked 2^14, 40 reps (resolution check)     | 3.3 (fused flat) | 1.18 | 0.93 |
| q2' today (4 clones, cast, mul, bcast, sub, mul, fix) | 5.7 | | |
| q2' fused flat (one 4-input loop with validity) | 1.9   |       |        |
| q2' chunked 2^13 / 2^14 / 2^15 / 2^16           | 2.2 / 2.1 / 2.1 / 2.1 | 0.7 / 0.7 / 0.7 / 0.7 | 0.5 / 0.9* / 0.5 / 0.7 |
| q2' chunked 2^14, 40 reps                       | 2.08 (fused flat) | 0.68 | 0.62 |
| build 7 chunk trees from flat + flatten 1 back  | 6.3 (any grain) | | |

(* one noisy cell; min 0.4.) Raw samples with load per process: `results/s1.jsonl`.

Readings: fusion alone gives 2.6x (q1) and 3x (q2') at one thread; the chunk tree costs nothing at one
thread (3.5 vs 3.3; 2.1 vs 1.9); 12 threads give 3.5-4.4x over the chunked 1-thread time, ~11x over
today's q1. Per-leaf work at 2^14: q1 3.5 ms / 64 leaves = 55 us, q2' 33 us; the fork iteration is a
fixed ~0.3-0.5 ms, so at 1M rows the grain does not matter between 2^13 and 2^16 (16-128 leaves); the
knee is the fork overhead, not the leaf size. The chunk build is 0.8-0.9 ms per 1M-row column (a range
copy) and flatten 0.6 ms: converting a flat 7-column frame costs more than the fused query (6.3 vs 3.3 ms),
so the representation boundary (DESIGN 16, D7) must sit at the source, and conversions are charged.

## S2 alignment (`s2_align.bend`, results/s2.jsonl)

| cell                                                       | 1 thr | 4 thr | 12 thr |
|------------------------------------------------------------|------:|------:|-------:|
| ragged aligned zip (filtered id + region, 316k rows, 64 ragged leaves) | 0.7 | 0.3 | 0.2 |
| concat zip (UN over two filtered frames, 128 leaves)       | 1.3   | 0.5   | 0.4    |
| misaligned: lockstep detection (grain 2^14 vs 2^13)        | 0 (an O(shape) walk) | | |
| misaligned: re-cut B to A's partition (flatten + chunk by partition) | 2-3 ms (two passes) | 1-2 | 1-2 |
| rechunk after the 30%-selective filter (64 -> 32 leaves)   | 0.1   | 0.0   | 0.1    |

Filter compacts every column of a leaf with the leaf's mask, so the outputs are ragged but aligned by
construction; the lockstep zip needs no alignment work. Concat is one node (partitions compose, O(1)).
Different partitions arise only across frames (horizontal joins of frames chunked differently, an
externally built column); normalising B to A's partition costs two passes (flatten, then chunk by A's leaf
sizes: `UBP`). Rechunk merges sibling leaves that fit one leaf bottom-up, forked, deciding by row counts
only, so every column of a frame takes the same shape without a shared plan.

## S3 reductions and coarse forks (`s3_reduce.bend`, results/s3.jsonl)

| cell                                            | 1 thr | 4 thr | 12 thr |
|-------------------------------------------------|------:|------:|-------:|
| U32 sum, flat fold                              | 0.7   | 0.7   | 0.7    |
| U32 sum, chunk tree (per-leaf fold, add at nodes) | 0.7 | 0.3   | 0.2    |
| F32 Neumaier, flat (Kernel.fsum's loop)         | 1.9   | 1.7   | 1.7    |
| F32 Neumaier, sequential in-order leaf walk     | 4.7   | 4.3   | 4.8    |
| q3-like 4 aggregates over gids, sequential      | 3.9   | 4.3   | 4.2    |
| the same forked 2x2 across aggregates (3 gid clones charged) | 4.5 | 3.3 | 3.7 |
| 7 columns gathered by one perm, sequential      | 8.8   | 6.7   | 6.2    |
| the same forked over a column tree (2 perm clones per node) | 8.4 | 6.0 | 6.9 |

The F32 leaf walk is an open issue: the SAME compiled loop (`spin_33`, the NS state unboxed into two
u32 registers, no allocation) costs 2.5x when driven by the explicit-stack walk, at every grain
(2^10..2^20, i.e. even one leaf) and in either run order (`fsumr`); the C shows no per-row difference.
W5 must re-measure the serial F32 pass over chunks in situ before relying on the walk; the fallback is to
reduce F32 columns from a flattened copy (one pass) or keep reduction inputs single-leaf. Forking across
the 4 aggregates and across 7 gathers did not pay on this loaded machine (load 30: the 12 lanes were not
free); the expected gain on a quiet machine is bounded by the longest lane (one F32 scatter, 1.3 ms) and
the clones (0.2 ms each).

## S4 ownership (`s4_owner.bend`, results/s4.jsonl; 1 thread)

| cell (20 reps, ms per rep)                          |       |
|-----------------------------------------------------|------:|
| today's ICol: Frame.get_cloned of a 1M F32 column   | 0.20  |
| borrow-and-return: Frame.take + Frame.replace       | 0.00  |
| Kernel.map into a fresh output                      | 0.80  |
| the same map in place into the dead operand         | 0.80  |
| group F32 sum, Array<NS> (boxed record per group)   | 1.40  |
| the same over two Array<F32> (s, c)                 | 1.30  |

A column clone is 0.2 ms per 4 MB; a move is free. In-place reuse of a dead operand buys nothing over a
fresh output (the allocation is a block, the loop is the same tight `spin`), so D2 is about moves and
borrows, not in-place maps. The boxed `NS` accumulator in `Array<NS>` costs nothing measurable over two
F32 arrays (the compiler unboxes the single-constructor record in registers; in the array it is a boxed
cell per group, not per row).

## Emitted C (`cstats.py` over build/s1.c, build/s3.c, build/s4.c)

Every fused leaf loop compiles to one `spin_N` with zero `term_keep` / `ctr_take` / `rfc_seal`, zero
`blk_copy` / `blk_half` / `blk_node` and no per-row `term_ctr`: `spin_27` (14 params) is `C3.go`, the
3-column compaction; `spin_28` (14 params) is `R4.go`, the 4-input q2' loop; `spin_33` is the F32 fold
with the `NS{s, c}` record unboxed into `u32 r2, u32 r3`; `spin_50` in s4.c is the in-place map (read,
write, read-next, nothing else). The spin loops with `term_ctr` are the tree builders (one node per leaf,
`CID_S1_CHUNKS_FL/UL`), and `blk_new` appears only where a leaf or output array is allocated. The runtime
reads blocks directly (`BLK_SHR 0`: `blk_loc` is `term_loc`, no refcount per access).

## S5 proof feasibility (`laws_spike.bend`)

Type `CL{n, d, a} | CN{rows, lrows, l, r}` (the node stores its left child's row count), models `crows`,
`ccell`, `WFChunks`, `ShapeWF`, `Leafwise`, `CompactLeafwise`, `kidx`; kernels `cmap_not` (chunked
`Kernel.mask_not`, parallel let per node) and `ccompact` (per-leaf `Kernel.compact_keep`, counts carried
out first in the pair). Proven, `bend` and `--verdict` (113 TODOs = 107 open laws inherited from
PROOF_contents' import closure + the 6 stated-open laws below; a mutated copy of `Leafwise` with `xor 2`
is refused with a type error, not a TODO):

- `cmap_shape` (c): the chunked map keeps the row counts and `ShapeWF` (bundled induction: a live child
  can be passed to ONE lemma, so counts and shape come back together).
- `cmap_leafwise` (a'): the chunked map is the flat map leaf by leaf, a pure node congruence whose leaf
  lemma is PROOF_contents' `map_cell` (the term behind the production law `mask_not_cell`); 8 lines.

Stated, open (the gap):

- `cmap_not_cell` (a, logical cells): needs `sub_lt_of_lt_add` (k < a + b, not k < a, no wrap => k - a < b
  over words). The toolkit bridges U32 to Nat for comparisons (`B.cmp_nat_u`, `B.le_nat_u`,
  `PST.lt_nat_of_u`) and has `B.add_sub`, but no `to_nat` of `U32.add` / `U32.sub`: 60-150 lines of new
  word work. The recommended design avoids it: kernel laws in congruence form (`Leafwise`), and ONE
  offset-form flatten bridge in the style of `append_cells` (`rdN(o, U32.add(off, k))`, Nat `CatFits`).
- `ccompact_leafwise` / `ccompact_rows` (b): the leaf lemma is the production `compact_contents` (CSpec)
  under `CRoom`; `CRoom` must come from the leaf capacity (`croom_of_cap`: 0/1 words and n <= 2^d give the
  cursor k <= i < n < 2^d), which LAWS section 11 leaves as a hypothesis. ~80-150 lines (an invariant
  k <= i by induction, Room-style). The node case is counts only (no arithmetic beyond the addition).
- `wf_map_out`: WFArray of the map's output (PROOF_contents has it inside the `MC` invariant; expose it).

Reusable as leaf lemmas unchanged: `map_cell` / `zip` instances (`mask_not_cell`, `mask_and_cell`,
`mask_or_cell`), `iota_cell`, `gather_contents` (per leaf when the index array is leaf-local),
`compact_contents` + `compact_keeps_mask`, `u32_fold_sum` / `popcount_sum` (per-leaf folds; the node
combine is `U32.add` associativity, trivial), `append_cells` (rechunk's leaf merge), `mask_data_cell`,
`choose_cell`. What is new: the two Type-valued predicates, the congruence inductions (short), the offset
bridge, `croom_of_cap`, and lawful combines for min/max.
