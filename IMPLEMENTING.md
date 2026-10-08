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

## M6 (LAWS.bend, PROOF.bend)

- **Rewrite direction**: `%e : P` with `e : {a == b}` needs `_` in P at the
  places of `b` (the RIGHT side); the goal becomes P with `a`. To replace a
  computed term `f(p)` by its known value, flip the hypothesis first:
  `%Equal.sym(T, f(p), Done{s}, ok) : {g(_) == ..}`. The checker prints
  `expected` (the goal) and `observed` (P with b) when it does not match.
- **Quantities are enforced in proofs**: a hypothesis spent twice
  (`and_left(.., h)` and `and_right(.., h)`) needs `+h` in the LAW binder; a
  Data value passed to two lemmas needs `+` (a `case P.Filter{e, +x}` pattern
  works); an `-erased` param cannot be passed to a live parameter, and a
  recursive call inside a `%e : P` rewrite is a live use. Arrays and other
  Type values cannot be `+`: a lemma matches them once and must hand the
  rewritten array back as a Sigma witness for the next lemma.
- **Hypotheses cannot be rewritten in place**: return a function type
  `{H} -> {G}`, rewrite inside it, then `h => ...`. Lambda bodies take
  statement lines (`h =>` on its own line, then `%e : P`, then the term);
  a tuple component can hold `(%e : P; {==})` inline.
- **Refutations**: `Fail == Done` through `res_disc(A, r)` (Fail -> Unit,
  Done -> Empty) with `%h : res_disc(A, _); Unit{}`; the motive must send the
  RIGHT side of `h` to the goal's type (`{True == False}` needs the motive
  with `False -> Empty`, `{False == True}` the one with `True -> Empty`).
- **Multi-scrutinee matches reduce when the first column decides**:
  `Plan.schema.filter.k(Fail{e}, agg, s)` with `agg` a variable reduces to
  `Fail{e}` (the `case Fail{e} _` row), but `Done{other} _` with `other` a
  variable is stuck: list the four non-bool dtypes.
- **`case other:` does not refine the goal**: a goal
  `Opt.merge.f(e, other)` stays stuck; write the eight constructors.
- **Higher-order lemma params work**: `unary(-f: Res -> Res, fails: @e: E.Err ->
  {f(Fail{e}) == Fail{e}}, ..)` called with `r => P.Plan.schema.select(es, r)`
  and `e => {==}`; the induction hypothesis of the main law is passed as
  `o => h => Laws.merge_pass_keeps_schema(x, o, h)` (p08's idiom).
- **Template proofs**: a proof over a template kernel is itself a template
  def (`map_go_slots(~T: Data, ~U: Data, ~f: T -> U, ..)`), recursion
  allowed, the step lemma takes the IH as a lambda. `Array.new(T, 1n+p, v)`
  computes to `ANode{Array.new(T, p, v), ..}` and `U32.shln(1, 1n+p)` to
  `U32.shl(U32.shln(1, p))`, so "2^d slots" is `U32.shln(1, d)` directly.
- **Negative-test your laws**: change a claim (`shln(2, d)`) and confirm
  `SOME PROOFS FAIL` before trusting a first-try ALL PROOFS CHECK.
- Full check of 48 laws: ~0.45 s. `--verdict` needs Lean v4.34.0 (absent).

## M0 (test runner, toolchain, CI)

- **`#! xfail <ID>` is a plain comment to bend**: a test file with that line first
  compiles and runs as usual. `scripts/test.sh` reports `XFAIL` when its check fails and
  `XPASS` (a failure) when it passes; delete the line when the defect is fixed.
- **Parallel runs keep order**: `TEST_JOBS=n` runs `xargs -P n bash -c check_one`. Each
  worker writes `r<i>.log` and `r<i>.status` under the temp dir, and the report is replayed
  in file order, so `TEST_JOBS=4` and `TEST_JOBS=1` print the same text. Two tests that
  write the same file would race under `TEST_JOBS>1`; none do today.
- **Bend cannot be pinned through `install.sh`**: it installs the latest release. CI downloads
  `releases/download/v<ver>/bend-<ver>-<target>.tar.gz`, checks the sha256 copied from
  `flake.nix` (the release's own pins), unpacks into `~/.bend` (the install.sh layout) and
  checks `bend version`.
- **numpy 2.5.3 wheels need Python 3.12+**: `bench/pyproject.toml` requires `>=3.12`
  (it was `>=3.10`, which made `uv lock` fail).
- **`make ci` relies on `uv sync --locked`** in CI, so a `pyproject.toml` change without a
  relock fails the build instead of silently resolving.
- **Peak RSS**: `/usr/bin/time -l` on macOS reports `maximum resident set size` in bytes;
  GNU `-v` reports kbytes. `scripts/baseline.sh` handles both.

## M0 T1/B05 (DF.dump, typed comparator)

- **Hex printing**: Base has no hex printer. `Dump.hex(n: Nat, +x: U32)` recurses on the Nat FIRST
  (`Dump.hex(p, U32.shrn(x, 4n)) ++ digit(U32.and(x, 15))`: high digit first, linear). With `x` first
  the termination check refuses it ("a decreasing self-call: arguments are read left to right").
- A `Char` is `Chr{code: U32}` and holds a Unicode code point (not a UTF-8 byte): `IO.print` of
  `Chr{233}` writes the two UTF-8 bytes, so strings with non-ASCII text round-trip through dumps.
  `SCon{Chr{c}, SNil{}}` builds a one-char string; literals understand `\t \n \" \\`.
- `F32.bits` of `F32.div(0.0, 0.0)` is `0x7fc00000`, `F32.neg(that)` is `0xffc00000`, `inf - inf` is
  `0x7fc00000`; `F32.neg(0.0)` is `0x80000000`. There is no `F32.from_bits`; to get a specific NaN
  payload into a test you need `Column`/CSV, so payload cases live in the Python comparator tests.
- A recursive def that builds its answer from a helper which itself calls the recursion is mutual
  recursion and is refused as "unfilled law": `Dump.rows` + `Dump.rows.k(p, step(..))` failed; thread
  the state as a PAIR PARAMETER and build the next state in a non-recursive `next` helper called in
  the argument list (`Dump.rows(p, Dump.rows.next(st))`). Collect row lines newest-first in a list and
  `String.concat` the reversed list at the end (appending to a growing left operand is quadratic).
- `(c, +xs) = r` is needed when a list taken from a pair result is used twice.
- Dump of `bench/data/sales_1000.csv` (7 columns, 1000 rows) takes ~0.4 s interpreted; it is
  byte-identical to `bench/dump_polars.py` run on the same CSV with an explicit schema.
- `IO.print(DF.dump(r))` prints the dump's trailing newline plus one more; the runner trims the
  whole text and `check.py --dump` ignores trailing blank lines.

## M0 regressions (tests/regress, bench/contract)

- **`case` is a keyword too** (`def case(..)` is refused like `as`, `is`, `Kind`).
- **Regression shape**: build each input with a def (`t()`) and call it once per run: a frame is
  consumed by the eager run and by each lazy env (`R.env1("t", t())`); the Source plan comes from
  `R.src("t", t())` (Plan is Data, so `+p` reuses it). `R.three(tag, eager, plan, env, env)`.
- **Expectation blocks are generated**, not typed: `bench/contract/regress_expect.py` has one spec per
  file; `--write` replaces everything from the first `#|` line down. Python must open the .bend files
  with `newline=""` (universal newlines turn a CR inside an expectation into LF). CSV text is printed
  through `Dump.quote` so no raw CR/TAB ends up in a test file.
- Every printed block must end in `\n` so `IO.print` leaves the blank separator line the generator
  emits (`R.schema`, `R.render` add it).
- **Pending tests can be type-checked** before their API exists: copy `src/` and `frame.bend` to a
  scratch dir, append one-line stubs of the missing defs (`floor_div = Bin{Div}`, `try_cast = Cast`,
  ...), copy the `.bend.txt` files to `<scratch>/tests/regress/*.bend` with `lib/`, and run
  `bend --check-only`. All ten pending files pass that check.
- A negative proof fixture (`SOME PROOFS FAIL`) passes `scripts/test.sh` but fails `make check`
  (`--check-only` exits 1), and its expected text includes the source excerpt around the failing
  line: keep a blank line after the def, or the excerpt quotes the `#|` block itself.
- Polars 2.0.0 quirks met while deriving expectations: a header `"c""d"` reads back as `c""d`;
  `"+5"` casts to u32 5 (the contract refuses it); f32 `sum([1e8, 1, -1e8])` is `0.0` eagerly while
  Neumaier gives 1.0; `MIN // -1` is MIN; a quoted `""` makes an inferred column str.
- NaN bits in expectations are the interpreter's on this machine (arm64: `0/0` and `inf - inf` give
  `0x7fc00000`). x86-64 produces `0xffc00000` for invalid operations; if CI on Linux x86-64 runs the
  test suite, NaN-producing cases (B03-a/b/c/f/n, as dump_basic already) may need a NaN-canonicalising
  dump comparison.

## M1 B01/B04 (shared analysis, cardinality, sources)

- **A let inside a `case` is transparent to the checker**: `+ok = Opt.sinks(es, Plan.schema(x))`
  then `Opt.hwrap(Opt.hstop(ok, n), Select{es, Opt.head(x, Opt.hpass(ok, n))})` keeps the recursion
  structural, and a proof about it states the goal with the let inlined
  (`P.Opt.hstop(P.Opt.sinks(es, P.Plan.schema(x)), n)` written out). Use this to make a pass
  decide per node without two recursive calls (computing both branches and picking one doubles the
  work per level).
- **Proofs over a record**: a lemma that needs the dtype of `q & e` matches `rq: E.Res(A.Ana)` with
  nested patterns `case Done{A.Ana{D.TBool{}, rs, k, tot, loc}}:` (one case per dtype, as with
  `Expr.type`); the remaining fields stay variables and the goal still reduces, because the dtype
  projection never inspects them.
- **Keep a law true by guarding its function instead of rewriting it**: restricting `Opt.merge`
  pair by pair would break `merge_pass_merges` / `merge_fixed_point` / `merge_idempotent`; running the
  unchanged pass only when a whole-plan check holds (`Opt.merge_if(Opt.fsafe(p), p)`) keeps all four.
- **Height is not locality**: `x - mean(x)` has one value per row (KRow) but each value reads all
  rows. Anything that changes which rows an expression sees (head sink, filter merge, pushdown) needs
  "no reduction inside", not only "row-shaped".
- **Use counting at compile time**: post-processing the postfix code (`Exec.mark`: is there a later
  `ISource` of the same name?) is simpler than threading a counter through the IO loop's state.
- `perl -i` over several files does not reset `$.` between them; run line-number edits one file at
  a time.

## M1 B02 (csvparse, scan prefix)

- **Forking a hub module**: copy `core.bend` from `~/.bend/lib/<hash>/core.bend` into `src/`, keep its
  license text (here MIT, copyright nohzafk, not the project author) in the header, and delete the
  import. Constructors of its types are used through the importing alias (`H.CsvCell{..}`, `H.CsvRec{..}`).
- **Extra state in a walk costs little**: two more `U32` arguments (line counter, record start line) and
  a `CsvCell` / `CsvRec` node per field / record cost about +11% on `Csv.read` of a 7-column 100k-row
  file. A per-record line list that is only read on the error path is built next to the columns.
- **`File.read` mangles UTF-8 cut at the end of a chunk** (`a\xc3` + `\xa9` becomes a replacement
  char): read chunks with `File.read_at` (bytes, `List<&2, U32>`), cut at the last LF byte (never inside
  a sequence) and decode with an own decoder. A loop that adds a continuation byte by byte needs
  `need` / `cp` state arguments; compute each next-state value in a small `Bool.pick` helper called in the
  recursive call's argument list (no `match` after the `bs` match, no mutual recursion).
- **A non-tail-recursive def over a 64K-element byte list overflowed the stack** in the interpreter
  (`bend: memory fault (machine stack overflow?)`); build the string reversed in an accumulator and
  `String.reverse` it. 100k-element non-tail recursions over records/cells (Csv.conv, Csv.tr) are fine.
- **Termination of a counting loop that must stop early**: the structural argument has to come first
  and be passed as `p` / `t` itself. For "stop after the n-th event" keep walking the list but freeze the
  state with an `act` flag computed once (`+act = U32.is_gt(m, 0)`) and applied in each helper
  (`Csv.sc`); do not replace the Nat by a computed value.
- **An IO loop over chunks** (`Csv.pre.loop`): the loop def holds the bind and the recursive call; the
  step is a separate def returning `IO(PSt)` (the Exec.loop shape); the state is a Type sum
  `PRun{..} | PEnd{r}` and the loop stops on `PEnd`; the fuel is the file size + 2 (a `Nat` is a number
  natively, so a 40M fuel is free); each step closes the file when it makes `PEnd`.
- **`A & B` is a Type, not Data**: a pair parameter cannot be `+dp`; destructure it as the FIRST
  parameter of a helper (`(done, pend) = dp` then `match eof`), or the matches on earlier parameters are
  refused ("can't be matched in this position").
- `sed '/start/,/end/d'` with an `end` pattern that never matches deletes to the end of the file; a
  stale `mv` of a pending test is recoverable with `git show HEAD:<path>`.

## M1 B02 review (CSV)

- **Re-reading an element is not structural recursion**: a decoder that must "push the byte back"
  (U+FFFD for a broken sequence, then read the same byte afresh) cannot recurse on the unconsumed list.
  Do both in one step instead: `+n = Bool.pick(U32, bad, 0, need)` and push up to two chars
  (`push(emit(b, n), cp(b, n, ..), push(bad, 65533, acc))`), with every next-state value computed from `n`.
- **`match` cannot follow a bind inside `do`** ("a match heads a def body, not a term"): hand the bound
  value to a helper def that matches it (as `Csv.read.opened` does).
- The runtime's `File.read` decoder (`io_str` in bend2/comp.ts) is WHATWG-style: leads C2..F4, narrowed
  second-byte ranges after E0/ED/F0/F4, U+FFFD + reprocess on a break, U+FFFD for a truncated tail;
  Python's `bytes.decode('utf-8', 'replace')` gives the same code points, handy for expected outputs.
- A per-cell `needs_q` walk over numeric cell texts on write cost nothing measurable (F32.show dominates).

## M1 B03 (numerics)

- **Base number readers**: `U32.read` refuses `"+5"`, `" 2"`, `""`, `"-0"` and overflow
  (`"4294967296"`); `F32.read` accepts `nan`, `NaN`, `inf`, `-inf`, `1e3`, `.5`, `5.`, `+5`,
  refuses `1_0`, `0x10`, `""`, a trailing space, but SKIPS LEADING whitespace (`" 3"` -> 3).
- `F32.to_u32` saturates negatives to 0 and truncates (`2.9` -> 2, `4294967040.0` exact); range
  and NaN checks must come first. `F32.show(2147483648.0)` is `"2147483600"` (shortest form).
- **NaN bits propagate**: `F32.neg(0/0) + 1` keeps `0xffc00000`; only the dump canonicalises.
- A `type` can be declared in the middle of a module (`K.NS` in kernels.bend); its constructor
  from another module is `K.NS{s, c}`, also as a pattern.
- `Bool.pick` evaluates both arms: fine for pure scalar code (`Bool.pick(Maybe<&2, U32>, ok,
  Some{F32.to_u32(x)}, None{})`), but keep expensive or failing work behind a `match`.
- Spec-file edits: when a scripted replacement's NEW text ends a file, it carries the file's
  final newline; anchors that end mid-line then gain a stray line break (`bend --check-only`
  reports `expected 'def', 'type' or 'law'`).
- A strict operation that must report the first failing row cheaply: run the lenient one on a
  clone, compare null counts (`Column.null_count`), and only on a mismatch walk the two validity
  masks (`Valid.materialize(v, 0n)` gives the 1-slot all-ones array for AllValid).

## M1 B04-i (row cap) and B02 leftovers

- **`import` lines must precede every def/type** in a module: an `import ./err.bend as E` appended
  with a section at the end of a file fails with `expected 'def', 'type' or 'law' / observed 'i'`.
  Add imports at the top.
- **Self-recursion must shrink an EARLIER argument first** ("arguments are read left to right: each
  passed unchanged until one shrinks"): `Csv.lead(go: Bool, rows)` recursing on `rows` with a changed
  `go` is refused; put the shrinking list first (`Csv.lead(rows, go)`, `match rows go`).
- A def may not match a computed value, so `(blank, r2) = Csv.lead.is(r)` followed by a call is
  refused as "a parameter or field scrutinee"; compute the Bool with a tiny helper called twice and
  duplicate the record with `+r` / `+rt` in the `case`.
- **A guard that costs nothing on the success path**: carry the `Maybe<&2, E.Err>` from
  `K.Kernel.check_rows` as the FIRST parameter of a small `match` helper (`Column.fs.cap`,
  `Csv.rows.c`, `Join.fill.c`, `GroupBy.run.h`) and put the allocating call in the `None` arm.
- **Parameterise a cap for cheap tests** by threading it through the `.cap` entries (`+cap: U32`
  first), with the public def calling the `.cap` one at `max_rows()`. A literal 65536-element list
  built with a non-tail recursive `keys.go` overflows the machine stack (`memory fault (machine stack
  overflow?)`); build big test columns directly (`C.CU32{65536, 16n, C.AllValid{}, Array.new(U32, 16n, 1)}`).
- **U32 totals wrap**: the join's output-row sum is saturated (`Tot.sat`: `s = t + m; s < t -> MAX`;
  once at MAX it stays there, MAX + m wraps below MAX) so that the cap sees it. Do the same for any
  count that can exceed 2^32 before a guard (M3 concat).
- A zero-column frame `C.Frame{8388609, Nil{}}` carries a height without data: the cheap way to
  test an over-cap path that needs no column (group_by with a literal key).

## M1 B04-i / B02 diff review

- **An early-exit walk under strict evaluation**: `Csv.width(rows, go)` (first non-blank record's
  width) follows `Csv.lead`'s shape: the recursive call is an ARGUMENT of the `.k` chooser, so it is
  always evaluated, and the `go = False{}` arm must answer at once (`case other False{}: 0n`). Then the
  walk costs one step past the first non-blank record, not the whole file, and its (non-tail) depth is
  the number of leading blank lines only.
- **Validate options before IO**: a check that sits in the pure parser (`Csv.parse_with`) runs after the
  file is opened and read, so a missing file reports `IoError` while a pure-first entry (`scan`) reports
  the option error. Put the same `Maybe<&2, E.Err>` chooser in front of `File.open` (`Csv.read_chk`).
- Timing note: reading the 1M-row bench CSV before and after b4eda5e (5 alternating runs each,
  3.2-3.7 s both) shows no measurable cost from the added `U32.from_nat(List.length ..)` count and
  the `+rt` duplication in `Csv.lead`.

## M1 diff fixes (NEW-1 static checks first, NEW-2 interpreter stack)

- **The interpreter is the JS lane and recurses on the host stack**: about 2^15 nested non-tail calls
  overflow it (`bend: memory fault (machine stack overflow?)`; Bun's RangeError mapped by
  bend2/comp.ts). Measured: Base `List.length` of 20,000 elements is fine, 40,000 crashes. A
  cons-guarded recursion (`f(h) <> go(t)`) counts too (no TRMC), and so do Base `String.concat`,
  `List.replicate`, `List.length` and `String.append` over its LEFT operand (`body ++ "x"` with a long
  body). Native binaries do not have the limit, so a test that only runs natively will not show it.
- **Per-row loops on any path a result takes must be tail calls**: map into a reversed accumulator,
  then `List.reverse` (tail recursive in Base); count with a tail-recursive `K.Kernel.count(~T, xs, 0)`;
  join newest-first lines with `Dump.cat(lines, acc) = Dump.cat(t, h ++ acc)` (copies one short line
  per step) instead of `String.concat(List.reverse(..))`. Recursion over columns, keys or the
  characters of one cell is fine.
- **Keep one big frame alive at a time in interpreter tests**: three 202,800-row results alive at once
  (a helper taking eager + raw + opt results) made a test 4x slower (41 s, high sys time); printing
  each summary before the next `collect` (do-block steps) brought it to ~9 s.
- **Test a big result by a summary of its dump** (chars, lines, FNV-1a over the code points; a tail
  loop over the string) and build the same dump text in Python for the expectation.
- **Eager static checks mirror Plan.schema without touching it**: the proofs unfold `Grp.validate`,
  `Plan.sort.miss` and `Plan.schema.*`, so new eager checks are separate defs with the same rules
  (`Eval.static`, `Grp.static`, `Sort.miss`) placed in front of the evaluation, not edits of the
  shared ones.
- `(f, i) = r` then `match i:` on the destructured component is accepted (`Sort.frame.b`).

## T2.3 (F32 reductions vs an exact reference, bench/diff/reduce*.py)

- **A literal list of ~10k elements overflows the interpreter's stack** ("machine stack overflowed
  (a deep recursion, or a literal too large to expand)"). Build big columns from chunks of ~100
  literals, one `def` per chunk (`def c_x0() -> List<&2, D.Scalar>: [...]`), joined by
  `List.concat(&2, D.Scalar, [c_x0(), c_x1(), ...])`; a 10k-row frame then costs ~0.4 s per use.
  A frame def is re-evaluated at every call, which is fine for eager/lazy runs of one case.
- There is no `F32.from_bits`: write an f32 literal as its shortest decimal (`model.f32_text`), and put
  an `in` dump of the frame in the same program so a parse that differs in a last bit is caught by
  comparing the dumped bits with the intended ones (none differed in 2 x 2000 cases, subnormals and
  3.4e38 included).
- **`DF.dump` makes sums comparable bit for bit**: Neumaier + guard (15.5.3) is deterministic, so the
  reference is a numpy float32 re-implementation of the algorithm plus a rigorous error bound against
  exact integer arithmetic (every f32 is an integer multiple of 2^-149). Bend equals the model in
  every case, eager, grouped, lazy and in describe.
- The std of a CONSTANT column is not 0 under 15.5.4: `fsum(x)/n` rounds twice, so for
  `n * x` not representable the mean is x +- 1 ulp and std = `sqrt(n delta^2/(n-1))` (e.g. 46 copies of
  123456.79 -> std 0.0079). Polars answers 0.0. Within the contract; a post-pass `m = m` correction
  would need a contract change (not made).
- DESIGN.md 15.5.4 quotes `std [1,2,4] = 1.5275252`, `var = 2.3333333` (correctly rounded values); the
  algorithm as specified (squares rounded to f32) gives 1.5275253 / 2.3333335, one ulp above, and Bend
  does exactly that (tests/diff/r0006.bend pins it).
- Neumaier's `c` is an f32: `[1e8, 1e16, 1, .5, -1e8, -1e16, .25]` sums to 0.25, not 1.75 (the bound
  `gamma^2 * sum|x|` allows ~2.6e3). It is the specified result, not a defect.

## M1 cleanup (describe min/max, CSV stack safety, oracle null text)

- **A tail loop is not free natively**: turning `Csv.conv` (`scalar(h) <> conv(tl)`) into accumulate +
  `List.reverse` made the 100k-row native parse of sales_100000.csv ~30% slower (~340 -> ~440 ms), and the
  write of 1M rows ~20% slower. The non-tail cons recursion compiles to something cheaper than a loop
  with an accumulator and a second pass. Nothing hid in the interpreter's stack either: the JS lane
  overflows at about 2^15 nested non-tail calls, so a plain recursion over 100,000 rows crashes.
- **Unrolling is the cheap compromise**: a per-row recursion that matches 16 list cells per call
  (`case x0 <> x1 <> .. <> x15 <> tl: f(x0) <> .. <> f(x15) <> go(tl)`, a one-cell `go1` for the
  remainder via `case other`) keeps the native speed (parse +1..2%, write +8%) and the depth at n/16.
  Used in `Csv.conv`, `Csv.rec_lines`, `Csv.cells`, `Csv.zip`, `Csv.zip_pre`, `Csv.join`. Use real tail
  loops where the loop is not on the hot path (`Csv.take_rows`, `Csv.drop_blank`, now skipped when
  `Csv.any_blank` finds no blank record).
- **A `+s: String` parameter used once per row overflows the interpreter's stack**, whatever the
  unrolling: `zip_pre(a, b, +pre: String)` with `pre ++ x ++ y` crashed a 100k-row render. Pass the
  separator as a `U32` and build `SCon{Chr{sep}, x ++ y}` instead.
- **Keeping the record list alive costs ~7% natively**: passing `data` (the CsvRec list) down to
  `Csv.col.chk` for its error lines (instead of the small `rec_lines` list) held every record until
  the columns were built. Keep the lines list.
- **Measure native parse with interleaved runs** (`build/bench file.csv parse`, read_ms + first_walk_ms,
  15-25 runs, compare medians): the noise of one run is +-10%.
- describe: min/max come from `Eval.agg Min/Max` (K.Kernel.fmin/fmax, 15.5.2), the quantile rows stay
  the stable sort's nearest rank, which is Polars `describe` (interpolation="nearest" is its default).
  A `match` cannot scrutinise a computed value (`match U32.is_eq(..)` is refused): give the test its
  own def with a Bool parameter, and a helper must be defined above its caller (no mutual recursion).
- bench/diff: the oracle's `Expr.show` of a typed null literal is Bend's `lit(null).cast(<t>)`
  (`Cast{Lit{SNull}, t}`), not `lit(null)`.

## M2 proofs (P0, name equality, Exec.run_pure, R1)

- **The rewrite rule, once and for all**: `%e : P` with `e : {a == b : T}` needs the
  current goal to be `P[_ := b]` and leaves `P[_ := a]`. So to replace a term X in the
  goal by Y you need `e : {Y == X}` and `_` at X. With `h : {X == Y}` you can only
  replace Y by X (`%h : {.. _ ..}` with `_` at Y); to replace X by Y flip it:
  `%Equal.sym(T, X, Y, h)`. The checker's `expected` is the goal, `observed` is
  `P[_ := b]`; when they differ only at the rewritten spot, flip. (Most of this
  milestone's checker iterations were this one mistake.)
- **Base `U32` is `Word(32n)`**, a 32-bit little-endian word of `Bool`s (`WCon{bit,
  tail}`, head = least significant), and `Word.cmp` compares the tail first. Lemmas
  about `U32.min`, `is_le`, `String.eq` are inductions on the word length: `match n:
  case 0n / case 1n++p: match x y: case WCon{+a, +t} WCon{+b, +u}` with the tails'
  comparison passed as a parameter `c: Cmp` plus `e: {Word.cmp(p, t, u) == c}` and
  matched (`+` on everything used twice, including `p`). `cmp_eq` (EQ means equal) and
  `cmp_flip` (comparing the other way gives the opposite verdict) make the rest
  derivable without new inductions (`gt_trans` from `lt_trans` through flip).
- **`String.eq` IS provable**: `Char.cmp(Chr{U32{x}}, Chr{U32{y}})` computes to
  `((Chr{U32{x}}, Chr{U32{y}}), Word.cmp(32n, x, y))` once the chars are matched three
  deep (`case SCon{Chr{U32{+x}}, +t1} SCon{Chr{U32{+y}}, +t2}`), and `String.cmp.fin` /
  `.rec` destructure literal pairs by computation. Pass `Word.cmp(32n, x, y)` and
  `String.cmp(t1, t2)` as parameters, match / destructure them in helpers.
- **A `-` (erased) parameter can be used in a rewrite but not matched**: "a live
  scrutinee (a - scrutinee matches only in a dead region)". A Type-kinded value
  (array, column, frame, runner state `Q.St`) can therefore be passed to exactly ONE
  lemma that matches it. Consequences:
  - a lemma that case-splits on such a value and whose conclusion the caller must
    combine with another lemma hands the value back as a Sigma witness with an equation
    to the original: `head_step_w(n, m, st) -> &s: Q.St -> {s == st} & {step(.., s) ==
    ..}`; the caller rewrites its goal from `st` to `s` with the first component (types
    are erased, so `st` may still appear there) and passes `s` on. The witness cascade
    goes all the way down (`col_head_w` -> `cols_head_w` -> `frame_head_w` ->
    `head_step_w`), rebuilding the value from its matched fields (`{==}` proves the
    rebuilt value equals the matched one).
  - two codes run from one state are compared by a parallel induction that consumes
    the state once per step and carries a continuation hypothesis for the suffix
    (`loop_pre(w, b1, b2, st, h: @s -> {loop(b1, s) == loop(b2, s)})`); never rewrite
    the two sides separately with the same state.
  - helper lemmas whose subject appears only in equations take it erased (`-st`,
    `-a`): then the caller can pass the same value live to the one lemma that needs it.
- **A computed witness cannot be destructured in a let**: "a match cannot scrutinize a
  computed value: give it its own def". `(c2, ec, hc) = col_head_w(col, n, m)` is
  refused; pass `col_head_w(col, n, m)` as a parameter `w` to a helper and destructure
  `w` there (`cols_head_cons`, `set_get_k3`). Pairs of equalities too: split
  `pass_barrier` into two one-equation lemmas rather than destructure a computed pair.
- **Law binders may be function types and erased types**: `for rf: @s: Q.St -> {.. :
  Q.St}` and `for -T: Data` parse and check (`head_pass_run`, `wf_new`,
  `array_get_pure`); a law may have no binders at all (`wf_frame_empty`).
- **`match` order again**: a nested match on an EARLIER parameter after matching a
  later one is refused; write one multi-scrutinee match in parameter order (`match bits
  d:` with all four rows).
- **Templates under --verdict**: a law or lemma whose type applies a template kernel
  (`K.Kernel.gather.go(~T, ..)`) to a quantified `-T: Data` is accepted by `bend
  PROOF.bend` but `--verdict` answers "mismatch between the TypeScript implementation,
  and the formalized BendTT kernel" and validates nothing. State such laws at a concrete
  instance (`~U32`). Generic laws over Base `Array.get`/`Array.set` (not templates) are
  fine.
- **Type-valued predicates** (`def WFColumn(c: C.Column) -> Type`) may match affine
  values and use a parameter once per branch like any def; `Unit` / `Empty` / `A & B`
  / `{a == b : T}` are the connectives; proofs are tuples (`(hl, hv)`) and `Unit{}`.
- **Importing a module that fills laws**: `PROOF.bend` importing `PROOF_schema.bend`
  etc. counts their `def Laws.x` as filling `LAWS.bend`'s laws (same file, imported by
  each). A fixture that uses a lemma from a split file must import THAT file
  (`PROOF_kernels.bend as Pf`): `PROOF.bend` does not re-export its imports (the call
  parses as a non-template and fails on `~`).
- **Negative fixtures**: the expected block includes a source excerpt with line numbers;
  keep a blank line after the failing def and generate the `#|` block from the actual
  output after checking by eye that the failure is the theorem's (mutated rule in
  `expected`, real rule in `observed`), not a parse error.
- Full check of 71 laws: `bend PROOF.bend` ~1.0 s wall (1.3 s CPU), `--verdict` ~1.1 s wall.
