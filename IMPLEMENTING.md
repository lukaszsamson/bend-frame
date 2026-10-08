# Implementer notes

Practical lessons gathered while building bend-frame. Read after DESIGN.md
(§2, §9, §14). Append what you learn; keep entries short.

## M1 (dtype, err, kernels, column, fmt.show)

- **Imports prefix everything**, constructors and patterns too; def names keep
  their dots: `K.Kernel.map(~..)`, `D.DType.show`, `D.SBool{b}`,
  `C.AllValid{}` (bare `AllValid{}` is refused), `C.CU32{..}`, `C.Frame{..}`.
  Aliases used across the codebase: `D` dtype, `E` err, `K` kernels,
  `C` column, `F` fmt. Base `Done/Fail/Some/None` need no prefix.
- **No law stubs in `src/`**: an open law in an imported file makes every
  importing program refuse to run ("1 TODO found"). Use a def returning
  `Fail{InvalidOperation{"..: not implemented yet"}}` instead.
- **No negative literals**: `-2.0` is a parse error; use `F32.neg(2.0)`.
- **Validity**: `Column.take_valid(c) -> Column & Valid` leaves `AllValid`
  behind; `Column.set_valid(c, v)` puts it back. `Valid.materialize(v, d)`
  gives a mask (ones for `AllValid`); `Valid.get/clone/count/gather/compact`.
- **Building columns**: `Column.mk_w(t, len, depth, valid, data)` for
  Bool/U32/I32 from a `DType` tag; `Kernel.depth_for(len)`.
- **Accessors hand the column back** (`Column.len/dtype/depth/cell/scalars/
  null_count/to_scalars/clone`): destructure the pair in a helper parameter.
- `Column.gather(c, perm, n) -> Column & Array<U32>` returns the perm back;
  out-of-range indices wrap, so for join misses zero the validity word after.
- `Column.compact(c, mask, kept)` returns the mask back (filter many columns
  with one mask); `Frame.filter_mask(f, mask, kept)` consumes it.
- `Kernel.compact`/`compact_keep` leave garbage past `kept`.
- `Frame.get_cloned` clones in place (order preserved). `Frame.put` on an
  empty frame adopts the column length as height. `Frame.select_names`
  rejects duplicates. `Frame.info(f) -> Frame & FInfo{h, names}`.
- **Loops**: no mutual recursion — a recursive def plus non-recursive step
  helpers called in its argument list (see `Cols.*`, `Frame.select.*`).
  Helpers above callers. `match` on a parameter before any destructuring let.
  `case h <> t` rejects `+h`; write `case +h <> t`.
- **Tests**: `C.Frame.from_columns` plus a small `mk(name, scalars, dtype)`
  helper (see `tests/frame_ops.bend`).
- `Fmt.show`: width `max(3, name, dtype, cells)`; >10 rows shows 5 / `...` /
  5; F32 via `F32.show` (`2.0` prints `2`).

## M3 (csv, Fmt.fixed)

- **Match order = parameter order.** A nested `match` must go in parameter order:
  `def f(rows, k)` that matches `k` first then `rows` is refused ("can't be matched in this
  position ... matched after a match on a later binder"). Put the shrinking/fuel parameter
  first (`Csv.take_rows(k, rows)`).
- **Hub imports prefix too**: `import bend-csv-parser@0.1.0.1/core.bend as H` gives
  `H.parse_sep`, `H.Parsed{rows}`, `H.Rejected{}`, type `H.Ans`. Constructor of a type
  defined in a module is `V.CsvOpts{..}` (module alias + type name), a def is `V.Csv.parse`.
- **A call that answers `Maybe`/`Result` is matched in a helper's parameter** (`Csv.su32(U32.read(s))`),
  never `match U32.read(s):` (R3). IO steps follow the same rule: bind the step result
  `o : Result<&1,&1,U32&String,File> <- File.open(..)` and hand it to a helper (`Csv.read.opened`)
  that matches it, so an open failure is an `IoError` value (`IoError 2: No such file or directory`).
- `+x` is needed on every param used twice, including `Nat` (`+n: Nat`), `Maybe` and `List<&2,_>`
  params threaded through recursion (`+prec`). `case +r <> rt` when `r` is used twice.
- **Pipeline (linear):** hub parse -> rows (List of Lists) -> drop blank lines (more than one
  column) -> ragged check -> `Csv.tr` (transpose: reverse the rows once, cons each field onto a
  column accumulator) -> per column: infer from the first `infer_rows` fields (early-out Bool
  accumulators, no per-field allocation), `Csv.conv` to `Scalar`s, `Column.from_scalars`.
  Strict check pass (`Csv.bad`) only for explicit dtypes or when inference saw a prefix.
- **Output text**: build lines by a right fold over the columns (`pre ++ cell ++ rest_line`) and
  `String.concat` the lines: `String.append` copies only its LEFT operand, so right-nested
  appends are linear. `String.join`/`String.concat` in Base are right-nested already.
- **Parallel let in `Csv.cols`** (`a b = Csv.col.inf(..) Csv.cols(..)`): columns build in
  parallel natively, parse of sales_100000.csv 506 ms -> ~290 ms, 1M rows 6.2 s -> ~3.6-4.2 s.
- **Fmt.fixed is exact, not `floor(x*10^p+0.5)`**: an f32 times 10^4 loses bits (26002.8594 is not
  representable), so the f32 is decomposed with `F32.bits` into `M*2^e`; the fraction is held as
  7 limbs of 24 bits and multiplied by 10 per digit (the carry out of the top limb is the
  digit); one extra digit + "remainder nonzero" gives round-half-even exactly like Python/Rust.
  Integers >= 2^23 expand in base 10^7 by repeated doubling. Verified against Python
  `f"{x:.Np}"` on ~300 random f32 values for p in {0,2,4,9} and byte-identical on all
  `bench/golden/*.csv` (`tests/csv_golden.bend`). Precision is capped at 9.
- `F32.bits(x)` is the IEEE-754 bit pattern; `U32.shrn/shln(x, n: Nat)` shift by a Nat.
- Tests that read `bench/...` use repo-relative paths and rely on `scripts/test.sh` cd'ing to the
  root; `tests/csv_file.bend` writes `/tmp/bend_frame_test.csv`.

## M2 (schema, expr, eval)

- **Tree evaluation with a Type-kinded state**: compile the tree to postfix
  Data code first (`Eval.compile(e, acc)`: plain structural recursion with
  the recursive calls in argument position), then run ONE loop over the code
  with the state `EvSt{frame, ResT(stack)}` (`Eval.run`). No mutual
  recursion, no destructured call results, errors short-circuit as `Fail`.
  Reuse this shape for any interpreter over `Plan`/`Expr` that threads a
  frame.
- **Keywords you cannot use as names**: `Kind` (type name) and `is`
  (parameter name). Error: `expected : a name (got the keyword ..)`.
- **Multi-scrutinee `match a b` must follow parameter order**; otherwise
  `'d' can't be matched in this position`. Swap the parameters.
- `match f():` on a call is refused even in tests (`match base():`): add a
  `k(.., r)` helper. `(f, m) = r` followed by `match m:` is fine.
- Nested patterns work: `case Some{D.I32{x}}`, `case Lit{D.SNull{}}`,
  `case Slot{kb, b} <> Slot{ka, a} <> rest`, overlapping rows like
  `case D.TBool{} D.TBool{}` then `case D.TBool{} _`; `case other:` as the
  last catch-all binder.
- `List.map` is `List<&1>` only (`expected List<&1, Field> / observed
  List<&2, Field>`): write the 3-line recursion for `List<&2, _>`.
- Template lambdas may call defs with `+` params: `~(a => b =>
  Eval.i32_min(a, b))` where `i32_min(+a, +b)`; passing the def itself
  (`~Eval.i32_min`) is refused (R5). A template lambda that uses its
  argument twice (`~(x => pick(is_gt(x, 0.0), f(x), ..))`) is inlined into
  the kernel and fails there as `x (consumed more than once)` with a
  `Location: Kernel.map_maybe.go~0`: move the body into a def with `+x`.
- **`Kernel.compact`/`compact_keep` need an output with MORE than `kept`
  slots** (`depth_for(kept + 1)`): dropped rows are written into slot `k`,
  which wraps to slot 0 when `kept = 2^d`. `Column.compact` does this now.
- **Validity**: binary ops AND masks, reusing the other side's mask when one
  side is `AllValid` (no pass); `Eval.fix(c)` resets null slots to the
  default (one in-place pass, `Kernel.mask_data`) only when a mask exists.
  Rely on the invariant (null slot = default) but aggregations still skip
  nulls explicitly (`Eval.dropnull` compacts valid rows, then the dense
  kernels run).
- **Aggregating**: `Eval.agg(op, column)` is column-level (no typing), 1-row
  result. For group_by: `X.Expr.split_agg(e)` gives `AggSplit{op, inner}`,
  evaluate `inner` with `V.Eval.full(f, inner)` (literals broadcast to the
  height, so `Agg{Len, lit 1}` scatters height ones), name =
  `X.Expr.name(e)`, dtype = `X.Expr.type(e, schema)`.
- **Measured natively at 1M rows** (12 threads): column clone ~0-3 ms,
  `u32 + lit` 4 ms, `f32 * lit` 2 ms, q2's revenue expression 6-10 ms,
  `bool & (u32 > lit)` 4 ms, masked `f32 + f32` 4 ms, `sum f32` (Kahan)
  5 ms, masked `mean` 6 ms, `filter` 12 ms, `cast u32 -> str` 37 ms, but
  `str == lit` / `str < lit` ~100 ms (~95 ns per row: cons-list strings).
- Test helpers used by all eval tests: `cs(c)` prints `dtype=[cells]`,
  `fs(f)` prints `h=N name:dtype=[..] | ..` (see `tests/eval_arith.bend`);
  much easier to reason about than `Fmt.show` tables.

## M4 (plan, exec)

- **Interpreters over a tree that thread a Type value** (Exec over `Plan`,
  threading `Env` + a stack of frames): compile to postfix `Instr` code
  (`Exec.compile(p, acc)`, recursive calls in argument position; a Join is
  `compile(l, compile(r, IJoin <> acc))`), then ONE loop. The loop may be IO:
  `do IO<St>: st2 : St <- Exec.step(i, st); Exec.loop(t, st2)` passes the
  termination check (the recursive call sits inside the bind's lambda).
- **Optimizer passes that sink something down a tree** use a "pending"
  parameter instead of re-matching a rebuilt node (which would not be
  structural): `Opt.push(p, ps)` carries the conjuncts to apply on top of
  `p`, `Opt.head(p, n)` the row limit, `Opt.proj(p, need, top)` the needed
  names. Each is plain structural recursion on `p`; leftovers are re-wrapped
  (`Opt.wrap`, `Opt.hwrap`) where they stop.
- `Plan.optimize` guards on `Plan.schema(p)`: an ill-typed plan comes back
  unchanged, so rewrites only ever see well-typed plans (sound pushdown needs
  "every Filter predicate is bool, no aggregation outside GroupBy").
- **Reuse the eager checks for schema rules** so lazy and eager agree:
  `Plan.schema` calls `J.Join.schema` (join.bend) and `G.Grp.validate`
  (groupby.bend), and `S.Schema.project.chk` for DuplicateColumn.
- `as` is a keyword (a test helper `def as(..)` fails as `expected : a
  defined name / observed : as`); BSD `sed` has no `\b`, use `perl -pi -e`.
- A Bend file reached through a SYMLINK resolves its relative imports from
  the link's target directory: a scratch copy of `src/` must copy the file
  under test, not link it.
- Projection pushdown inserts `Select{[Col ..]}` over a Source/ScanCsv in
  source column order; Exec runs a plain-`Col` Select as
  `Frame.select_names` (moves columns, no clone), so the inserted projection
  costs nothing and makes every later Filter/compaction touch fewer columns.

## M5 sort/groupby

- **Radix beats `List.sort` by 30-50x** natively: a stable LSD counting sort
  over `(word, row)` `Array<U32>` pairs is ~10 ms per 16-bit pass at 1M rows;
  `List.sort` of Data records is ~0.9 s at 1M. Map every key to an
  order-preserving U32 word (`Sort.words`) and sort words, never values.
- **Strings are the cost**: one pass that only walks 1M short strings
  (hashing) is ~120-150 ms; `String.eq` per row ~250 ms; a Map lookup per row
  ~350 ms sequential (~210 ms in 8 parallel blocks). `Array.get` copying the
  string is NOT the bottleneck (swap-out instead of get saves ~15%). So: code
  each string column once, then work on U32 codes. Hash-then-verify is not
  cheaper than the Map (the verification is another full string pass).
- `Map.to_list` is sorted in `String.order` (crit-bit trie, lo before hi):
  list position = rank, no string sort needed.
- **Destructuring order follows parameter order too**: `(a, s) = r` then
  `(out, cs) = st` is refused when `st` is a parameter declared before `r`
  ("can't be matched in this position"); destructure in parameter order.
- A tuple state with a `+` field in the middle/end (`(t, g, f, +next) =
  st`) failed with "an annotated term (cannot infer)"; putting the Data
  scalar first (`(+next, t, g, f) = st`) works.
- A 1-slot array (`Array.new(U32, 0n, 1)`) reads the same slot for every
  index (indices wrap): a free "all ones" mask / constant input for a
  scatter. `C.Valid.materialize(v, 0n)` gives exactly that for `AllValid`.
- `Kernel.compact`-style "write slot `next`, advance by a 0/1 flag" records
  each new group's first row without a branch (`Grp.dens.put`); the output
  needs more than n_groups slots.
- Parallel let over an `ANode{xs, ys}` split (`l r = f(xs) g(ys)`): the
  left block holds rows `[0, 2^(d-1))`; the right block's logical length is
  `n - min(n, 2^(d-1))` (may be 0). Rebuild with `ANode{..}`.
- Native timings (12 threads, `bench/m5_sort.bend`, `bench/m5_groupby.bend`
  over sales_*.csv; each job includes nothing but the op):
  | op | 100k | 1M |
  |----|------|----|
  | sort u32 (random) | 4 ms | 22 ms |
  | sort f32 (random) | 3 ms | 13 ms |
  | sort region, price desc, id (q4, 7 cols gathered) | 17 ms | ~220 ms |
  | sort id desc (7 cols gathered) | 5 ms | ~105 ms |
  | group_by region, 4 aggs (q3-style) | 17 ms | ~190 ms |
  | group_by product (64 groups) | 31 ms | ~260 ms |
  | group_by region, product (512 groups) | 33 ms | ~320 ms |
  | group_by id (all distinct) | 4 ms | ~60 ms |
  | n_unique/first/min over a str column | 69 ms | ~650 ms |
  The 1M string-keyed numbers are dominated by string coding and by
  gathering string columns.
- Polars reference checks used `bench/.venv` (polars 2.0): every expectation
  of tests/sort_*.bend and tests/groupby_*.bend was produced by Bend and
  compared with Polars (`maintain_order=True`); a 1M-row 4-key sort and a
  16-group, 14-aggregation group_by over sales_1000000.csv matched Polars
  (floats to f32 rounding).

## M5 join

- **Hash tables without Base `Map`**: open addressing over flat arrays, 2^b
  slots at load <= 1/2, slot = `U32.div(h * 2654435769, 2^(32-b))` (top bits;
  `U32.div`/`shrn` are as cheap as `and` natively). A probe loop whose exit
  depends on an array read: a non-recursive `look` helper destructures the
  read(s) and answers a Type record with a `Bool` field (`PK{ka, kb, ids,
  more}`), and the loop matches it beside the fuel: `match n pk: case 0n
  PK{..} / case _ PK{.., False{}} / case 1n+p PK{.., True{}}` (Base's `Map`
  uses the same idea with `Tuple{key, False{}}` on a pair). Flat `U32` arrays
  beat an `Array<Record>` (no heap cell per slot); a 1M-row pair-table probe
  is ~10 ms.
- **String keys**: FNV-1a over `Chr{c}` (`Str.hash`, tail recursive) and an
  own `Str.eq` (Base `String.eq` goes through `String.cmp`, which rebuilds
  both strings). Dictionary-encode the small side once, probe the big side
  per row; a miss/null is the code `DEAD = 2^32-1`.
- **Walking strings is memory bound.** On parsed 1M-row data, one hash walk
  per row is most of a join's time (~70 ms of q5's ~100 ms, the equality walk
  ~25 ms). Forking the probe over `ANode` halves (`Probe.fork`, 16 blocks,
  each with its own table copy passed as a `DD{a, b}` PARAMETER: a recursive
  def cannot destructure a computed clone pair, and a helper that does would
  be mutual recursion) gives ~1.5x (160 -> 100 ms). Deep-copying the table
  per lane (no shared refcounts) changed nothing measurable.
- **Benchmarking pitfalls (native)**: (1) the first touch of a frame right
  after `Csv.read` is slow (summing a parsed u32 column: ~400 ms, then 1 ms):
  walk every buffer once, untimed, before the clock (`force` in
  `bench/join_bench.bend`); (2) dropping is NOT free for big trees: freeing a
  1M-row frame with string columns costs ~300 ms (a `Frame.take` that drops
  the rest, or a result dropped inside the timed region, dominates the
  measurement) - keep results alive until after `IO.now`; (3) repeated
  parses/clones in one process drift (heap growth): one measurement per
  process. Clones made by `Array.clone(String, ..)` share the string cells
  (refcounts) and time differently from the original.
- **Gather wrap trick**: DEAD indices wrap to the last slot of a `2^d > g`
  array; counts/starts arrays get that slot zeroed, so a dead left row finds
  0 matches with no branch. Left-join misses gather right row 0 and are then
  nulled with `Join.fix` (validity AND valid_r, `Kernel.mask_data`), keeping
  the "null slot = default" invariant.
- Errors seen: `'r' can't be matched in this position` when a pair param is
  destructured after a later param was matched (`match st` then `(c, x) = r`
  needs `st` BEFORE `r` in the parameter list); `a template applied to closed
  ~ arguments (rs is a variable here)`: a `~(u => ..)` timing lambda cannot
  capture a do-bound variable - time inline with `IO.now` steps instead.

## Goldens

- **Module alias vs def prefix**: `bench/queries.bend` defines `Q.q1`; the tests alias
  `exec.bend` as `Q`, so import the queries as `QS` and call `QS.Q.q1(a, b)`.
- A golden test: `scan_csv` both fixtures (infer), `match s p: case Done{+a} Done{+b}` then
  `Lazy.collect(QS.Q.qK(a, b), P.Env.empty())` and `Csv.render(f, Some{4})`; the `#|` block
  was generated from the golden file with a script, never typed.
- **Polars lazy vs eager differ in the last f32 bit of group sums**: the golden (lazy) has the
  sequential-f32 result, `df.group_by().sum()` (eager) the correctly rounded one. Check an
  oracle mismatch by recomputing with both numpy f32 sequential and Kahan before blaming the
  value pipeline (q2's revenues were bit-identical; only the sum differed).
- **describe is one Kahan mean + one Kahan sum of squares + one radix sort** per column; the
  sort supplies min/max/quantiles. Pitfalls hit: a helper that calls a later-defined helper
  ("expected a filled definition ... unfilled law") means the order is wrong, helpers go above
  callers; a param used twice (`nm` in a tuple and in a call) needs `+nm`; match
  `Done{C.Frame{h, C.Named{nm, c} <> Nil{}}}` nested patterns work.
- Describe verification recipe: a random CSV with nulls (u32, i32, f32, str, bool) per size
  n in 1..1001, `describe` in Bend vs `pl.read_csv(schema=..).describe()`, tolerance 1e-3
  relative; Polars prints Bool min/max as 1.0/0.0, bend-frame as `true`/`false` (DESIGN 14).
- Importing `eval`/`sort` into `fmt.bend` makes every `csv`-importing test compile those modules too (not measurable in `make test`).
