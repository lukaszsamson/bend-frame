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

## M3 table verbs (drop, rename, slice, tail, unique, concat, semi / anti)

- **No recursion through a `List<&2, Plan>` field.** `f(Many{t})` after `case Many{h <> t}` passes
  `bend` and `--check-only`, but `--verdict` answers "mismatch between the TypeScript implementation
  and the formalized BendTT kernel" (the type alone is fine). Anything PROOF.bend imports must recurse
  on direct subterms: an n-ary node becomes a chain of binary nodes plus an index field.
- **`A & B` is never Data**, so `List<&2, String & String>` cannot be a Plan field. The Data pair is
  `Sigma<&2, &2, String, x => String>`: literals `("a", "b")`, patterns `case (a, b) <> t:` and
  `(a, b) = p` all work, and a def `RenamePair() -> Data` can name it in annotations.
- **New Plan constructors in the proofs are mechanical**: every proof that splits on `P.Plan` treats
  a barrier node exactly like `Sort` (unary) or `Join` (binary) as long as its schema rule has the shape
  `Plan.schema.<verb>(args.., Plan.schema(x))` with a Fail passing through (identity for slice / tail).
  Copying the Sort / Join case blocks with a throwaway script (renaming the constructor,
  the instruction and the schema helper) checked first time, `--verdict` included. Compiling the unary
  verbs to one `ITable{op}` instruction keeps the Instr case splits at one new case.
- **A template lambda cannot capture**: a mask for semi vs anti is two closed lambdas chosen by a
  `match` (`~(m => Bool.to_u32(U32.is_ne(m, 0)))` / `is_eq`), not one lambda over a captured flag.
- `Plan.lines` (explain) is not in the proofs, so it can take an extra flag (`cont`: the left input of
  a Concat chain prints no header). A `+acc` lets one arm keep `acc` and the other extend it under
  `Bool.pick` (both arms are evaluated, which is fine for pure text).
- Semi / anti need no new hashing: the join's CSR counts per left id (`counts[accl[i]]`, DEAD ids read
  the zeroed wrap slot) give a 0/1 mask, `Kernel.popcount` the kept count, `Frame.filter_mask` the rows.
- `DF.then(r, f => DF.then(o, g => DF.semi_join(f, g, ..)))` works in examples: a (non-template)
  lambda may capture a frame it uses once.
- The diff generator's old `e_concat_vertical` (go -> step -> go) was mutual recursion and never
  compiled; a loop def with a non-recursive step helper (`step(st, h, i, s0)`) is the shape.

## M3 expressions (when, is_in, clip, strings, std / var / median)

- **A literal parameter in a per-row kernel**: a template lambda cannot capture a value (is_in's
  list, clip's bounds, a pattern). Pass it as a Data argument every step sees:
  `K.Kernel.map_p(~T, ~P, ~U, ~(p => x => f(p, x)), n, d, a, +param, z)`; bundle two bounds in a
  small Data record (`W2{lo, hi}`, `F2{lo, hi}`). A template argument may be a type expression
  (`~List<&2, U32>`).
- A lambda that uses its argument twice (`~(g => v => g + g - v)`) fails inside the kernel as
  `x (consumed more than once)`: put the body in a def with `+g` (`Grp.med.key`).
- `Eval.snd(~T, ~A, r)` needs `A: Data`; for an `Array & Array` pair write a small def that
  destructures it (`Eval.msnd`).
- **A let inside `do`** (`+d0 = DF.dump(r)` between binds) is refused ("expected a pattern");
  compute it in a helper def's argument list (`R.agree.txt`).
- A def used before its definition fails as "an unfilled law" even across sections:
  `Eval.when` could not call `Eval.pred` (defined in the filter section, below); copy the
  4-line rule (`Eval.when.c`) rather than move shared code.
- Two passes over one array: `K.Kernel.fold` hands the array back, so the first pass's state can
  seed the second (`Eval.ssd`: the Neumaier state of the sum, then a `VS{m, s, c}` record carrying
  the mean through the second fold). Grouped two-pass: scatter, map the accumulators to the
  per-group value, `K.Kernel.gather` it back to rows by the group ids, scatter again.
- **A per-group sort without per-group work**: two stable radix passes, the value's order word
  first, then `group * 2 + null flag`, give every group a sorted run of its valid values followed
  by its nulls; `Radix.pre.go` (exclusive prefix sums in place) over the group sizes gives each
  run's start. `Radix.sort(n, d, (words, perm))` carries any permutation, so the second pass
  sorts the gathered keys with the first pass's permutation.
- An example module can be imported by a test (`import ./../examples/x.bend as S1`, `S1.main()`):
  the example's own `./../frame.bend` import resolves from the example's directory. Running
  `bend f | head` reports "a short write on a standard stream"; harmless.
- Checking expectations: the f32 bits for std / var / median came from
  `bench/diff/oracle.reduce_` (`cd bench && uv run python`), the contract's algorithm in numpy
  float32; the sales table from Polars 2.0.0 directly.

## M4 (string experiment: Raw / Dictionary storage, streaming CSV reader)

- **A second storage behind one constructor**: `CStr{len, depth, valid, data: ST.Strs}` with
  `ST.Strs = SRaw{Array<String>} | SDict{codes, dict}` (src/strs.bend) kept every proof that
  only moves `data` (head, len, dtype, the witness lemmas) unchanged; only `WFColumn`'s Str case
  had to name the storage (`WFStrs`). A sixth Column constructor would have needed a new case in
  every 5-way match of src/ and of the proof files. Code that reads a Str column's strings writes
  `ST.Strs.decode(n, d, x)` (one gather) or, per value, `ST.Strs.map / map_maybe / map_p` (per
  dictionary ENTRY for a Dictionary, then a gather by code).
- **Code 0 is always the empty string**: a null row holds code 0, so it decodes to "" exactly as a
  Raw null slot holds ""; `decode` is a plain gather and `fix` (null slots to the default) is
  `mask_data` on the codes. Null stays validity, never an entry.
- **Bend has no global counter**: a dictionary's `tag` can only be a fingerprint (FNV mix of
  the entries in code order); equal tags are verified entry by entry (`Dict.same`) before two
  columns' codes are compared directly; otherwise the smaller dictionary is re-coded into the
  larger (`Dict.recode`, a miss is `Dict.miss()`, never equal to a code).
- **Ordering through ranks**: Base `Map.to_list` walks the crit-bit trie in code-point order with
  a prefix first, the order `String.is_lt` implements, so `Dict.ranks` (k Map inserts) gives sort
  words, min / max and `<` over two dictionaries (merge one into the other, rank the merged
  entries once). Checked by `tests/strs_decode.bend` against the Raw paths.
- **`col == lit` without n string comparisons**: `Eval.do2` broadcasts a 1-row Str side as a
  one-entry Dictionary when the other side is a Dictionary column (`Eval.fitd`), so the generic
  Dictionary x Dictionary comparison re-codes the 2-entry literal dictionary (2 probes) and
  compares codes; next to a Raw column the old broadcast is kept (no cost in the Raw default).
- **The native allocator punishes chunked work**: free lists are LIFO per lane, so memory freed by
  one chunk is handed out scattered to the next; per-chunk time of the same parse rose from 65 ms
  to ~200 ms over 40 x 1 MiB pieces (and from 34 to ~220 ms re-parsing ONE 1 MiB chunk 40 times in
  a pure loop), while one big piece runs at the first piece's speed. Strings built by Bend (a byte
  list decoded with `Csv.u8`) degrade worse than the strings `File.read` returns (fresh C-side
  allocation): read pieces with `File.read` (after a small `File.read_at` probe for the last LF,
  so no UTF-8 sequence is split) instead of decoding bytes in Bend. Dropping a big structure
  unread (erasure) is also slower than consuming it (4.5 s vs 1.7 s for the 1M records).
- **Take each record apart once**: `+recs` duplicated for a ragged walk, a blank walk, a count and
  the transposition cost more than the walks themselves; one tail walk (`Csv.tw`) over the records
  NEWEST first (the parser's order: no reversal) skips blanks, notes the first ragged record (the
  last one met), counts, collects lines and transposes (columns come out oldest first).
- **Per-piece arrays, concatenated once**: setting cells one by one into one growing column array
  (`ANode{old, Array.new(..)}` doubling) between the parser's allocations was slower than filling a
  small array per piece in a tight loop and copying the parts once at the end
  (`K.Kernel.copy_into`); with one piece the part IS the column (no copy).
- **An early exit from a per-row loop** (EncAuto falls back to Raw at a cell): thread `(go, state)`
  as a pair parameter, compute the next pair in a step helper, `match cs` first, destructure the
  pair in the case and `match go` on the component; the False arm returns the cells left
  (`Ds.go` -> `DSwitch{i, rest, st}`). A recursive call inside a match on a destructured
  component is still structural on `cs`.
- `Bool.pick` evaluates both arms: an op dispatcher over a linear frame must `match` an enum
  (bench/strbench.bend `Op`), never chain `Bool.pick`s that each consume the frame.
- **A proof over a storage sum type** (M4 after merging M5's `cell_pure`): give the storage
  its own model (`LAWS.scell`: Raw slot / Dictionary entry of the row's code) and prove the
  storage accessor pure against it once (`strs_get_pure(s, i) : {Strs.get(s, i) == (s,
  scell(s, i))}`), then pass that EQUATION (not the `&x: T -> ...` witness of `get_at_w`) to the
  column-level lemma, whose `-data` stays erased: `%Equal.sym(.., e) : {Column.cell.s(.., _) ==
  ..}` rewrites `Strs.get(data, i)` in one step. The Dictionary case is two witnesses in a
  chain (code, then entry), each in its own helper so the matched `Dict{..}` fields are
  parameters. It checked first time; keep the helper order (callees above callers).
- **Measuring on a shared machine**: run the storages of one cell back to back in one
  repetition (rotating their order) and freeze the binaries in a copy (`strbench.py --bin
  build/m4bin`): `make bench-check` / `scripts/bench.sh` rebuild `build/bench` and would swap
  the binary under a running campaign. Do not run `make test` / `make diff` (hundreds of
  compiles) during a campaign: the 1-minute load went from ~5 to 25-33 and the 1M parse
  times rose ~30 %; the ratios between interleaved storages held, the absolute numbers did not.
- **Merging the P2 typing proofs onto the storage sum type** (M4 after M5 part 2): the
  witness style (`&y: T -> {f(x) == (x, y)}`) needs the ANSWER as a value, so a pure-model
  equation (`strs_get_pure`) is not enough: write the witness by the same case split
  (`strs_get_w`: Raw slot via `get_at_w`; Dictionary code, then entry), not as
  `(scell(x, i), strs_get_pure(x, i))`, which consumes x twice. A source `match xa xb` with a
  catch-all `case a b` does not reduce in a proof until both scrutinees are constructors:
  split `xa` first, then `xb` only under the case that names it (`fill_str_w`), passing the
  rebuilt constructor (`ST.SDict{ca, da}`) where the source passes `a`. Likewise
  `match k od: case KFull{} _:` still needs `od` split for the KFull case (`fitd_f`).
  A generated proof file is changed in its generator (scripts/proofgen/gen_evalrun.py), then
  regenerated; `git diff` of the output is the review.

## M3 facade leftovers (DF.column, schema, height, collect_show)

- **A Data alias works inside a pair type**: `-> C.Frame & Schema()` (frame.bend's `Schema()` is Data)
  type-checks, as does `DF.Frame() & DF.Schema()` in a test helper's annotation. Writing the list type
  out (`List<&2, S.Field>`) is the fallback, not a necessity.
- **A facade def may share a name with a parameter**: `def schema(f)` sits beside
  `scan_csv_schema(path, opts, schema: ..)`; the parameter shadows inside its own body, and
  `--check-only` accepts both.
- **Pair results stay pairs in the facade**: `C.Frame.height` answers `Frame & U32`, so `DF.height` is
  the same annotation; a test reads it through a helper `hgt.s(x: DF.Frame() & U32)` that destructures
  `(f, h) = x` (the frame is unused there, as in `show.s`).
- **An IO wrapper over an existing IO result** follows `write_csv.io`: `do IO<String>:` with a typed
  bind `r : E.ResT(C.Frame) <- Q.Lazy.collect(p, env)` and `return show(r)`.
- **Test expectations**: `IO.print` adds the newline, so a table or an error line prints as one line
  with no blank separator; a null cell in a column of width 3 is five spaces between the bars.

## M5 proofs (P1 buffer contents: distinct paths, gather, compact, map/zip/iota, fold)

- **The rewrite direction, as a rule of thumb**: with `e : {a == b}` the hole `_` marks b in the
  goal and a replaces it. So to replace X by Y in the goal you need `e : {Y == X}` and the hole
  at X; a hypothesis `h : {X == Y}` replaces Y by X as it is, and X by Y only after
  `Equal.sym`. Nearly every first-try failure in this milestone was this; the checker's
  `expected` is the goal and `observed` is the motive with b, so a mismatch at one spot means
  flip.
- **Reusable (`+`) destructured components**: `(b, +x, +ea, e1, ex) = w` works for Data (U32,
  equalities over U32 / Bool / Array<T>); the LAST component of a Sigma cannot be marked `+`
  ("cannot infer" at Pair), nor can an equality over a pair type (`{.. == (b, n) : Array<T> &
  U32}`). Put the component that must be reused earlier in the Sigma or use it once (one
  rewrite with several holes replaces every occurrence at once).
- **Type-valued goal defs with erased array parameters** (`GGoal(f, j, d, -src, -out, -perm,
  -r)`, `MC`, `CK`, `CS`...) keep the rewrite motives short: the hole goes at a def ARGUMENT
  (`%ep : GGoal(.., _, (_, x))`) and conversion unfolds the def and the kernel step. In a
  Type-valued def an erased `-a: Array<T>` may be mentioned in any number of equalities and
  passed to other erased parameters; a live array parameter may be passed on once (to
  `WFArray`). The holes must still match the goal's syntax up to conversion: when the kernel
  has computed one step, state the next shape as its own def (`GGoal` -> `GMid` -> `GSet` ->
  `GC`) rather than guessing the computed term.
- **Forall hypotheses are affine.** `g: @k -> {..}` and the `fj` component of `set_other_w`
  can be applied once; `+g` is refused ("must be Data"), and a variable cannot be passed as a
  template argument (`~g`; only a literal lambda instantiates a template). So an invariant that
  needs the write facts for many positions cannot be transported row by row. What works:
  arrays are duplicable (`clone_eq` / `clone_wf` rebuild two live copies with equations to the
  original, by induction over the tree), finite Type-level chains are duplicable by induction
  (`croom_dup`), so the remaining run is analysed twice on separate copies (compact: `ckeep`
  for the row just written, `cspec_run` for the rows to come) and the two facts are restated to
  one copy through the clone equations (`row_clause`).
- **Reading an array hands it back live**: `get_w(a, i) -> &b -> &x -> {b == a} &
  {Array.get(a, i) == (a, x)} & {x == rd_at(a, i)}`; after rewriting the pending read in the
  goal, rewrite `a -> b` everywhere (hole at every a) and continue with b. `rd_at(T, a, i)` as a
  live TERM consumes a: pass the Data value x and its equation instead.
- **Match order**: a nested `match` on an earlier parameter after matching a later one is
  refused; write `match a c:` with both. A destructuring let of a parameter after another let is
  fine, but destructure parameters in parameter order (`(hj, room2) = room` before `(perm2, ..)
  = w` when room comes first).
- **Termination reads arguments left to right**: a recursive proof def whose shrinking argument
  is not first must pass every earlier argument unchanged; put the Nat fuel first (`room_of(f,
  d, j)`, not `room_of(d, j, f)` when j changes).
- **Never write a concrete all-ones 32-bit word** (`ones(32n)`): `Word.to_nat` of it normalises
  to 2^32 - 1 successors and the checker overflows its stack. "Maximal" is stated as "nothing
  compares GT to it" (`IncSpec` False case), and the contradiction uses `U32.cmp(N, j) == GT`.
  `U32.to_nat(0)` and `U32.shln(1, d)` are fine (small or stuck).
- **The BendTT kernel (`--verdict`) is stricter than `bend` on templates**: (1) a template
  lambda must be spelled identically wherever it must be the same term: the laws about
  `Kernel.popcount` use `~(acc => x => U32.add(acc, x))` exactly as `kernels.bend` does, and an
  alpha-renamed copy `(x2 => y => ..)` in a helper made `--verdict` answer "mismatch" while
  `bend` accepted it; (2) a `%` rewrite whose replaced term contains a template application
  (`Array.set(U, out, j, f(x))`) is refused: carry the value as a variable `y` with `ey : {y ==
  f(x)}` (`map_step2`, `zip_step3`). Bisect such a failure by cutting the file at def boundaries
  (laws dropped) and instantiating each template def at U32 in a probe def; an uninstantiated
  template is not checked by BendTT at all.
- **Laws over templates**: state the law at an instance (`K.Kernel.mask_not(n, d, a)`,
  `K.Kernel.compact_keep(~U32, ..)`), prove the template def with its conclusion written over
  the unfolded loop (`K.Kernel.map.go(~T, ~U, ~f, U32.to_nat(n), 0, Array.new(U, d, z),
  Array.get(T, a, 0))`), and let the law's side unfold the wrapper (as `mask_not_slots` did).
- **A `(%e : P; t)` rewrite needs an expected type**: it cannot be the right-hand side of a
  plain let (`+h = (%e : P; t)` is "cannot infer"); use it in argument position or restate.
- **A `match` stays stuck on a computed Bool**: `Kernel.depth_for.go(0n, n, d, U32.is_le(..))`
  does not reduce to `d` while the exit test is open, so an `Empty.absurd` motive must spell
  the goal with the unreduced call.
- **Long hole patterns**: when the goal is a deep production unfolding (`Column.slice` ->
  `gather.c` -> `Valid.gather.k` -> `Kernel.gather.go`), generate the proof text from a script
  with the recurring sub-terms as variables (`gen_slice.py`): the patterns are too long to
  type twice without a slip.
- **Timings**: 90 laws, `bend PROOF.bend` ~0.6 s wall / 1.7 s CPU; `--verdict` ~2.0 s wall.

## M5 proofs (P2 evaluator typing: operations, the stack machine, Eval.full / Eval.expr)

- **Erased forall binders exist**: `@-x: A -> B`. A hypothesis about affine values that the
  lemma applies itself (`hex: @-f3: C.Frame -> @-stk3: List<&1, V.Slot> -> {Eval.exec(h, i, f3,
  stk3) == EvSt{f3, Eval.app1(h, i, stk3)}}`) must bind them erased, or applying it consumes the
  frame and the stack the lemma still needs. The caller fills it with `f3 => stk3 => {==}`; this
  is how a step lemma generic in the instruction `i` makes `Eval.exec(h, i, ..)` (a match on i)
  reduce without a case split.
- **A term over an affine value in a live Data position consumes it**: `wrap_w(.., Laws.clen(c),
  ..)` or `X.Cast.total(Laws.cdtype(c), to)` passed to a `+n: U32` / `+tot: Bool` parameter is a
  second use of `c` (and an erased `-f` cannot feed `Laws.fschema(f)` to a live parameter at
  all). Make the parameter erased when it only appears in types (`resw_len(-tot, .., -n2, ..)`),
  or hand the number out as a Data witness beside the value: `len_k` (Column.len pinned to n),
  `height_dup` (Frame.height with the height as a U32), `schema_dup` (Frame.schema with the
  schema as a Data list, by induction over the columns through `dtype_w` and `col_dup2`).
- **Sigma witness ordering**: the LAST component cannot be marked `+` when destructured, so a
  fact needed twice goes earlier (`&f2 -> &n -> {n == fheight f} & {height f == (f2, n)} & {f2 ==
  f}`: `+n` and `+en`, the frame equation last and used once).
- **`match x` after a destructuring let is refused** ("matched after a local statement"):
  destructure inside each case (`agg_stepc_*`: `match op:` first, `(ed, el) = hc` per case).
- **The induction hypothesis as a forall hypothesis**: `IH(e, s, h)` is a 12-binder dependent
  function type (code suffix, frame, stack, shape, the two frame facts, the stack invariant, the
  record fields, the analysis equation); the law passes `acc2 => f2 => .. => ha2 =>
  Laws.run_typed(e2, s, h, acc2, f2, ..)` and the node lemma applies it once per operand (a
  forall hypothesis is affine). Closing over `+` Data (e2, s, h) only; the affine values are
  binders.
- **Ana injectivity through projections**: `Equal.cong(A.Ana, D.DType, a => A.Ana.dtype(a), ..)`
  on `L.done_inj(..)` gives `{t2 == t}` with the SUB-record on the left, exactly the direction
  the goal rewrite `%et : RunW(h, _, ..)` wants (goal has the law's t at the hole, becomes the
  record's t2). Compute `+ea = L.done_inj(..)` once and project three times.
- **Symbolic shape tests instead of case splits**: `Eval.do2.a` / `do3.a` compute `n`, `bad` and
  the fits from `SKind.is_full` of the slot kinds; with the kinds as variables the terms are
  stuck but can be passed as they are to a lemma whose hypothesis is `{bad == False}` and whose
  length fact is `{fitlen(..) == klen(comb(..), h)}`, each proven once by a 9- / 27-case lemma
  (`bad2_false`, `len2`, `bad3_false`, `len3`). The motive for the `is_ne(h, h)` rewrite is the
  normalized `Bool.or(_, Bool.or(_, False{}))` shape, which is convertible with the goal.
- **`(%e : P; t)` cannot be a let right-hand side**: wrap it in a lemma (`ana_along_s`) when the
  transported hypothesis is needed twice.
- **Probe files**: a probe in `build/probes/` importing `./../../LAWS.bend` and the PROOF files it
  reuses type-checks a lemma in isolation (`bend p.bend --check-only`; the "N TODOs" it reports
  are the laws the imported files do not prove). Iterate there, then paste into the generator.
- Timings: 116 laws, `bend PROOF.bend` ~1.2 s wall / 2.2 s CPU, `--verdict` ~2.9 s wall, on a
  machine with load average 14.

## M6 release-candidate validation (bench/m6.bend, scripts/consumer_check.sh)
- **Import paths take plain names only** (letters, digits, `_`, `-`): an absolute import of a path
  containing a `.` segment (`bend-frame-consumer.XXXXXX`) or macOS's `$TMPDIR` (`/var/folders/5t/..`)
  is refused ("an import path of plain names"); `/tmp/<name-with-dashes>/..` and relative `../clone/frame.bend`
  work. Both absolute (`import /abs/dir/frame.bend as DF`) and relative imports are fine. `bend --help`
  of 2.0.36 has no dry-run for `--publish`, so none is run.
- **An IO loop is one self-recursive def** whose `do` block binds the step's results and ends with the
  recursive call; a helper that calls the loop back is mutual recursion ("unfilled law"). The decreasing
  argument must come BEFORE any argument that changes in the self-call (`rp.loop(is6, q, left, i, ..)`, not
  `(.., i, left, ..)`). State that must be split first (a frame cloned into two) goes through a
  non-recursive helper called IN the argument list (`rp.loop(.., rp.split.n(kk))`).
- `match` cannot scrutinize a computed value (`match String.eq(a, b):`): give it its own def with a
  `+Bool` parameter. Constructors without fields need `{}` even as arguments (`True{}`).
- A file that defines `main` can still be imported for its helpers (`import ./main.bend as M`;
  `bench/m6.bend` reuses `M.force`, `M.fclone`, `M.job`, `M.load`).
- A native compile of a 200-case differential program takes 10-25 s on an idle machine and more than
  20 minutes when the machine's load average is above 50: `diff/run.py --backend both` then times out
  the compile (`--timeout` x 4) and bisects every batch. Run it when the machine is quiet, or with
  `--timeout 900 --jobs 3`.

## M5 part 3 proofs (P1 Dictionary strings: LAWS section 14, PROOF_strs.bend)

- **A Type-level hypothesis that a `match` reduces is consumed as a whole**: `hb: PC.IncLtU(bb, c, k)`
  is Data only after the case split on `bb`, so using it twice inside the True branch is "consumed
  more than once". Hand it to a helper with a `+hb: {U32.is_lt(c, k) == True{} : Bool}` parameter in
  the branch (`pre_lt`, `ehyp_lt`, `keepd_c`); the same for a lambda binder used twice
  (`+c2 => hc => keepd_c(.., hc, ..)`).
- **The last Sigma component cannot be `+`**: when it is needed twice, pass it on to a helper whose
  parameter is `+` (`code_id3` for `get_w`'s `{x == rd_at(a, i)}`, `mstep8a` for an `Ext`'s
  equation). A `(+more, e2) = ext` then `helper(.., e2, ..)` with `+e2` in the helper works.
- **Reading an array in a loop invariant**: `rdN(out, j)` as a live TERM consumes `out`, so a
  per-row invariant abstracts the code as a Data word with its equation (`EncRows`: `@code: U32 ->
  {code == rdN(U32, d, out, j)} -> ...`); the step transports the equation through `set_other_w`'s
  write facts (`Equal.trans(code, rdN(c1, j), rdN(out, j), ecode, (%same_false_lt .. ; fj(j)))`).
- **Rewrite direction, once more**: to INTRODUCE a stuck test into the goal (the goal has
  `rdN(out, j)`, `fj(j)` speaks about `Bool.pick(same_at(..), v, rdN(out, j))`) the equation is
  `same_false_lt(..) : {same_at(..) == False}` as it is (the motive at `False` converts to the
  goal); to REMOVE it (the goal already has the pick) it is `Equal.sym` of that. A nested
  `(%e : P; t)` used as the equation of an outer `%` is "cannot infer": name it (`same_at_of_eq`).
- **Dictionaries are `type .. is Type`**: an opaque `d: ST.Dict` can only be used once, and `dk(d)`
  in a live position consumes it. Entry counts travel as Data words beside the dictionary
  (`wf_ek: WFDictE(d, es) -> &d2 -> &k -> {d2 == d} & {k == dk(d2)} & {to_nat(k) == |es|} &
  WFDictE(d2, es)`; rewrite `d -> d2` in the goal and continue with d2). Equalities over
  `ST.Dict` can be `+` like those over arrays.
- **Facts about every entry are an affine forall; the entry LIST is Data**: state the invariants
  of a loop over the entries in the list model (`nthd(es, c)`, `Ext(es, es2)` with `ext_nth`,
  `ext_len`), never as "for every slot of the array". When a consumer needs the entry facts of
  a dictionary AFTER a theorem consumed its `WFDictE`, the theorem must answer them itself
  (`Keep` in `CodeW`): produce them from a SECOND clone of the array (`PC.clone_wf`, two
  `set_other_w` on equal copies, the two written arrays equal by `writes_eq`), one forall per
  consumer.
- **A hypothesis chain over an evolving affine value** (the probe per row: `EncProbe(f, i, a,
  d)` with the next element over `Pair.fst(Dict.code(d, rd_at(a, i)))`): keep the chain in the
  GOAL (`EMid2 := EncProbe(..) -> ..`), rewrite the goal's dictionary / string / result pair, then
  bind (`pr => ..`) and take it apart in a helper's parameter. Rewriting a hypothesis variable
  is impossible; rewriting the goal that mentions it is one `%`.
- **Per-step bounds**: counter arithmetic (`|es| <= to_nat(inc i)` with `Room(30n, inc i, f)` from
  `n < 2^30`) is cheap for ONE source of growth (encode); with two (merge: dst's entries plus
  src's) the clean derivation needs `U32.add` lemmas the word toolkit lacks, so `MergeProbe`
  carries the bound per step instead (honest, stated in DESIGN section 14).
- **`U32.to_nat(U32.shln(1, 30n))` in a type is harmless** (it stays stuck under the comparisons
  `nat_le_lt_trans` matches on); only `Word.to_nat` of a concrete all-ones word is fatal.
  `U32.is_lt(ST.Dict.miss(), U32.shln(1, 30n))` normalises to `False` cheaply (32-bit `Word.cmp`
  of two literals): `dict_miss_not_code` is a closed computation plus `lt_trans_u`.
- **Case splits on computed Bools in a cascade** (`Dict.same.k/u/t/v`): one Type-valued goal def
  per stage with the Bool as a parameter (`SU(bk, ..)`, `SV(bt, ..)`), the production call
  written with that Bool, and the law's proof passes the computed test with `{==}` as its
  equation; the law's goal converts to the first stage because `Dict.size` / `Dict.tag` reduce on
  the constructor.
- **Parameter order is binding**: a `+ec1: {Array.set(String, s1, k, s) == c1}` parameter must
  come after `s`; the checker reports "expected: a defined name" at the first forward reference.
- **Timings**: 138 laws, `bend PROOF.bend` ~1.6 s wall / 3.1 s CPU, `--verdict` ~4.6 s.

## M6 final pass (part-4 mutation fixtures, release docs)

- A mutation fixture for a law whose statement is a Sigma witness that NAMES the production
  function (`AppendW` mentions `K.Kernel.append`) needs a copy of the witness type with the
  mutated function in it (`MutAppendW`); the real proof term is then refused with the unfolded
  bodies in `expected` / `observed` (here `copy_into.go(.., U32.inc(na), ..)` vs `.., na, ..`).
  For a law stated as a plain equality over the kernel (`choose_cell`) the mutated law is the
  same text with `Mut.choose` in place of `K.Kernel.choose`.
- Keep the positive control (`<law>_copy`, same term, production function) in the same file:
  the expectation then holds exactly one error, so a mutation that also broke the control (or
  a control that stopped checking) changes the output and fails the test.
- Generate the `#|` block from the real output only after reading it: it must show one error,
  at the mutated law, mutated function in `expected`, production in `observed`.
- `bend <file> --publish` uploads the file, its transitive `./` imports and every file named
  exactly `LICENSE` beside a published file: for this repo that is `frame.bend`, the 19 files of
  `src/` and the root `LICENSE` (no `LICENSE` sits in `src/`).

## v0.1 review: scan source identity

- **Keep internal identities out of user namespaces structurally.** A reserved-name scheme
  (`"#scan<k>"` bound in the same `Env` as user frames) silently aliased a user Source of that
  name. Adding a field to the affine `Env` (`Env{frames, scans}`) cost four mechanical
  constructor edits in plan.bend and no proof change: no proof destructures `Env`, and the
  runner proofs treat `Exec.step(IScan ..)` as an opaque step (`rf(Q.Exec.step(i, st))`). A new
  `Plan` / `Instr` constructor would have added a case to every proof that matches on them.
- **A positional queue needs the producer and the consumer to walk the same order.** `Exec.mat`
  reads `Exec.compile(p, Nil)` and the runner compiles the same `p`; both are postfix, so scan k
  read is scan k taken. When the plan is optimised first, the two must see the SAME (optimised)
  plan; `release_keeps_scans` additionally proves the optimiser keeps the scan sequence.
- **Re-deriving a list lemma for another projection** (`Laws.srcs` -> `Laws.scans`) is a text
  transform of the proofs (`srcs_app` .. `hmerge_keeps_sources`): rename the projection, its
  element type in `List<&2, ..>` / `List.append(&2, .., ..)`, and swap the two `case` bodies in
  the `_app` lemma (the projected constructor conses, the other recurses). It checked first time.
- `List.reverse(&1, C.Frame, acc)` works on affine lists: accumulate frames newest-first in the
  IO loop, reverse once at the end.
- Show a regression catches the old defect: `git archive HEAD~1 | tar -x -C <scratch>`, copy the
  new test and its data in, run it there and diff (here 7 cases differ).

## T6 coverage matrix (scripts/coverage_matrix.py, tests/coverage/)

- Annotate a case with `#@ cover <ops> <kinds>` (or `#@ na <ops> <kinds> -- <reason>`) in the test
  file; the script checks that the file calls `DF.<op>(` or `<Alias>.e_<op>(` (a `tests/**/lib`
  wrapper). Per file, naming a (op, kind) both `cover` and `na` is an error: split the line so a
  claim says only what the file really does (`lit_u32` has no null case of its own; the null case
  is in the file that puts it beside a nullable column).
- Bend checks for these test files: a helper def must sit ABOVE its caller (`schema_text.k` before
  `schema_text`, "an unfilled law is a dead claim"); a parameter used twice needs `+` (`+tag`,
  `+es`, and also every U32 / Expr that goes into both the eager and the lazy call, e.g. `hd(+tag, +n)`);
  list cons is `x <> xs`, concatenation `List.append(&2, X.Expr, xs, ys)` (`++` is String only);
  `do` blocks need `x : T <- io` with the type written.
- `R.four` prints `raw same, opt same, full same` after the eager dump; its `R.four.text` is reusable
  for plans with no eager twin (`lazy3`, `scanC`) and for storage comparisons (`R.agree.v`).
  `IO.print` adds a newline after the text: end a helper's text with ONE `"\n"` at most.
- Expectations come from `bench/coverage/<name>.py` (a Polars 2.0.0 twin printing the same text,
  with the contract's departures patched by hand and marked `D:`), `bench/coverage/check.sh <name>`
  diffs it with Bend's output and `bench/coverage/bless.sh <name>` then writes the `#|` lines. A file
  with no line-by-line twin (`api_frames`, `api_plans`, `csv_storage`: Bend's own table / plan /
  storage text) uses `FORCE=1 bench/coverage/bless.sh <name>` and says so in its header.
- `DF.dump` prints every NaN as `0x7fc00000` (src/dump.bend); the Polars twin canonicalises NaN bits
  in `fx.show`. `F32.show` gives `nan`, `inf`, `-0`, `4294967000` where Polars writes `NaN`, `inf`,
  `-0.0`, `4294967000.0`: patch these by hand in a twin, nowhere else.
- `DF.lazy_concat_vertical([])` is `Concat{0, Source "", Source ""}`: `DF.validate_bindings` on it
  answers "source not in env: " (empty name) where `collect` / `collect_schema` answer the static
  "concat_vertical: no inputs" first. Not reachable through collect; do not use it as "a plan with
  no Source" (use `DF.scan_csv_schema`, which has none).


## W0 engine spikes (bench/spikes/w0_engine, DESIGN.md 16)

Performance lessons (what the C showed, what was slow and why; numbers PROVISIONAL at load 17-33):

- **A user-defined chunk tree is free to match.** `UL{n, d, a} | UN{rows, l, r}` over owned leaves: one
  parallel let per node, today's flat loop at the leaf. `cstats.py` over the emitted C: every fused leaf
  loop is one `spin_N` with zero `term_keep` / `ctr_take` / `rfc_seal`, zero `blk_copy` / `blk_half` /
  `blk_node`, no per-row `term_ctr`; `blk_new` only where an output array is allocated. `BLK_SHR` is 0 in
  the runtime: `blk_loc` is `term_loc`, a block read is a plain load.
- **Fuse first, then fork.** q1 today 8.7 ms -> fused flat 3.3 -> chunked at 12 threads 0.8; q2' 5.7 ->
  1.9 -> 0.5. The chunk tree costs nothing at one thread. Grain 2^13..2^16 is indistinguishable at 1M
  rows: the fixed ~0.3-0.5 ms fork iteration dominates, so an operator under ~2 ms of work gains little
  from 12 threads whatever the grain.
- **Chunking a flat frame costs more than the fused query**: 0.8-0.9 ms per 1M-row column (a range copy)
  plus 0.6 ms to flatten one back; 7 columns 6.3 ms vs q1 3.3 ms. Chunks are born at the source; never
  split/rebuild per operator (the review's 3.8x lesson, confirmed).
- **Single-constructor records are unboxed in registers**: `K.NS{s, c}` rides the F32 fold as `u32 r2,
  u32 r3` (`spin_33`), no allocation per row. In an `Array<NS>` it is a boxed cell per group, and the
  boxed group scatter costs the same as two F32 arrays (1.4 vs 1.3 ms): the `R{v, ok}` plan of W1d is
  sound, the `Array<KS>` of groupby is not the problem.
- **In-place reuse of a dead operand buys nothing**: `mapinplace` = `mapfresh` = 0.8 ms per 1M (the loop
  is the same `spin`; the fresh block is one `blk_new`). A first 2.5x gap was load noise. D2 is about
  moves and borrows (a column clone 0.2 ms per 4 MB, a take/replace 0), not in-place maps.
- **The F32 in-order leaf walk is 2.5x the flat fold with the same compiled loop** (4.7 vs 1.9 ms per 1M,
  at every grain incl. one leaf, in either run order: `build/s3 fsum 20 10`, `fsumr`). The C shows no
  per-row difference (`spin_32` -> `spin_33` in both). Unexplained; treat as an open issue to re-measure in
  situ before relying on chunked F32 reductions.
- **Coarse forks need free cores**: 2x2 across the four q3 aggregates and a column tree over 7 gathers
  showed no gain at load 30 (3.9 -> 3.3, 6.2 vs 6.9 ms); the perm/gids clones per split (0.2 ms each) are
  the price. Do not count on them for G2; measure on a quiet machine.
- **Measurement**: 10 reps of a 0.5-0.8 ms cell are at the 1 ms clock's resolution (+-12%); use 40 reps
  for 12-thread cells. Interleave cells per round; record `sysctl -n vm.loadavg` per process; a single
  sample under load can be 2x off (the `mapinplace` and `aggs_seq` first readings were).

Bend lessons (shapes that compile, R3/R4 with trees of arrays):

- **No helper may recurse back into the tree walker.** A recursive build/walk that must open a pair
  result (a range copy, a leaf fold, a gather) and continue uses the READ-AHEAD idiom: the walker takes
  the previous step's pair as a parameter, opens it itself, and makes the next call in its own argument
  list (`UB.go`, `FSum.walk`, `G.seq.walk` with a `pend: Nat` flag for "no pending result yet"). A
  recursive tree build cannot open the left child's result and recurse into the right one; build leaves
  with a tail loop and fold them into a balanced tree with a binary-counter stack (`US.merge`: leaf i
  merges `tz(i+1)` times; `US.collapse` for non-power-of-two counts). Flatten and in-order walks use an
  explicit work stack (`UF.go`), not recursion.
- **Match order = parameter order** also for `match f pend s:`; a later parameter cannot be matched
  before an earlier one ("can't be matched in this position"). A bare variable pattern (`case 0n rest:`)
  is not used anywhere in the code base; spell the constructors.
- **A def name's components are words, not numbers** (`mis.3` is refused: "a name (words joined by dots)").
- **Pairs as parameters, records as state.** A rep loop over Type-kinded state is a record (`FSt{f, acc}`)
  matched with nested patterns (`case 1n+p FSt{Flat{ok, ..}, acc}`); call results that are pairs go to a
  helper's parameter. A Sigma's LAST component cannot be `+`: carry the count FIRST (`U32 & CU`, `(+rl, l)
  = x`). `+` is refused on a Sigma-typed parameter (pass the components).
- **Templates**: `~f` is passed from one template def to another (as `Kernel.scatter.go` does); a
  template def must be above its callers like any def. `Bool.show` prints `True`/`False`: not JSON.
- **zsh**: `echo =====` fails (`=cmd` expansion); `echo '-----'`.
- **A parallel let in a Type-kinded match** (`case UN{+rows, l, r}: x y = f(l) f(r)`) compiles and forks;
  the join helper opens the two results as parameters.

Proof lessons (laws_spike.bend):

- **A live child goes to ONE lemma**: bundle what a node needs about its child (counts and shape) into one
  induction returning a Sigma; the law is the bundle. Helper lemmas take the trees as ERASED (`-l: CU`)
  parameters and only mention them in types; the live child is passed once to the recursive call.
- **State kernel laws leaf-wise (a node congruence) and prove the flatten bridge once in offset form**
  (`U32.add(off, k)`, as `append_cells`): the subtraction-addressed `ccell` model needs `k - a < b` from
  `k < a + b` over words, which the toolkit cannot yet say (no `to_nat` of `U32.add`/`U32.sub`).
- **The leaf lemma of the chunked map is `PC.map_cell` applied inside `k => hk => ...`**, with the template
  lambda spelled exactly as kernels.bend (`~(x => U32.xor(x, 1))`); `Kernel.mask_not` unfolds to it by
  conversion. `{==}` closes `{n == n}` goals after the parallel let reduces.
- **TODO counts are the evidence when a file imports LAWS.bend**: every imported open law counts (107 from
  PROOF_contents' closure); a filled law removes exactly one; a wrong proof is a type error, not a TODO
  (negative control: `xor 2` in `Leafwise`).
- `CRoom` has no producer: LAWS section 11 assumes it; the leaf-capacity argument (`croom_of_cap`) is a
  real new lemma for W5.

## W1b/e: n_unique by radix sort + run count, when.valid without a ones array

- **n_unique (word / F32 / Bool).** `Eval.nu.words(k, ws)` = `O.Radix.sort` of `(ws, scratch)` (the sort
  of Sort / median; the second array is a zeroed `Array.new(U32, d, 0)` the sort scatters alongside and
  nobody reads), then `Eval.nu.runs.go`: ONE flat tail loop, `acc += (x != prev)`. Bool is a presence
  fold (`or` of 1 + nonzero, then two bits). F32 maps `Kernel.fword` first, so every NaN is one word and
  -0.0 == 0.0 as before. Emitted C (`bend bench/m2_nunique.bend -o x.c`, `spin_244` there): no
  `term_keep` / `ctr_take` / `blk_copy` / `blk_half`, per row one `blk_read` and a branch-free 0/1
  (`spin_71`); nothing allocated per row. The k = 0 case is a `Bool` helper (`Eval.nu.runs.z`), because
  `Bool.pick` would still run the `k - 1` branch (U32 underflow = a 4-billion-iteration loop).
- **The old path hid an input-order cost.** `List.sort` on the cons list took 0.2 s on an ASCENDING
  1M-distinct column (the review's probe) but 1.7-2.5 s on a hashed (random-order) one; the radix path
  is order-independent (15 ms either way, F32 23 ms with its map). Measure n_unique on shuffled data.
- **Proofs mention `Eval.nuniq` by name**: `PROOF_evalops.aggdense_nu` states the witness per dtype; it
  now names `V.Eval.nu.w` / `V.Eval.nu.words` (the String instance of `Eval.nuniq` stays for Raw strings
  until W2). A replaced production term needs this one-line edit in the witness, not a new theorem: the
  proofs only state "n_unique is `Done{unit(SU32{w})}`", not what `w` is.
- **when.valid**: an AllValid side is the 1-slot ones array `C.Valid.materialize(C.AllValid{}, 0n)` (every
  index wraps to slot 0), but `Kernel.choose` WRITES its `a` operand in place, so only the AllValid-b
  position may use it; the AllValid-a case is a `Kernel.zip` of `(m[i] != 0) | mb[i]` (one fresh output
  array, the same as choose's allocation, minus the full ones array and its fill). Never pass the 1-slot
  array where a kernel writes it: every row would write slot 0.
## W1a/c join probe copies and describe (src/join.bend, src/fmt.bend)

- **W1a, the probe copied a table it never used.** `Probe.fork` took `DD{d1, d2}`, a pair made by
  `Dict.clone` at the call site (a deep copy: `Str.copy` per key char, 1.4 s of the 5.1 s distinct-key
  join at 1M), and a node cloned both halves again. A leaf used `d1` and dropped `d2`; at fork depth 0 the
  whole copy was dropped. Now the call site passes `Probe.dd(levels, d)`: `DD{d, stub}` when
  `levels = 0` (no copy at all) and one `Dict.clone` otherwise, and a node hands each child
  `Probe.dd(p, own)`: a clone only when that child splits again. 4 levels copy 15 tables (was 31),
  0 levels none; every block still ends with a private table (no shared string refcounts). Rows and
  order are unchanged (`tests/join_probe.bend`: 18 joins, 70000 left rows, checked against an independent
  Python join).
- **A split helper cannot be a separate def**: `Probe.fork` is recursive, the helper that opens the
  pair would have to call it back (no mutual recursion: a def must be above its callers), and
  `match Dict.clone(d):` / `dd = Dict.clone(d)` then `match dd:` are refused ("a match cannot scrutinize a
  computed value / a local binder"). The pair must arrive as a PARAMETER: build it at the call site with
  a non-recursive helper (`Probe.dd`) that decides whether a copy is needed.
- **Measured (M2 Pro, load average 15-60 from other agents, so provisional)**: distinct-key join (m6 hc
  join) 1M rows, 1 thread 5.4 s -> 3.6 s, 12 threads 6.9 s -> 4.0 s; 100k 0.50 s -> 0.28 s. Twelve
  threads are no faster than one: the forked probe is not where the time is, the build, the pair table and
  the result gathers are (W2 and the chunk work). Small build side (64 rows) and duplicate-heavy (4000
  rows, 400 keys x 10) joins are unchanged within noise: the probe is a small part of them.
- **W1c, describe cloned each numeric column five times** (the old comment "clone = refcount bump" was
  wrong: `Column.clone` is an O(n) buffer copy) and made six passes: cast, drop-null (compact + slice),
  mean (fsum), std (two folds), min, max, plus the sort. Now a numeric column is BORROWED
  (`Fmt.d.col` hands it back): `Fmt.d.cv.go` / `Fmt.d.cm.go` are one loop that casts to f32 (U32.to_f32,
  I32.to_f32, identity) and, with a validity mask, compacts (`out[k] = cv(x[i])`, `k += mask[i]`, out has
  `depth_for(kept + 1)` slots like `Column.compact`), returning source and mask; `DS{s, c, mn, mx}` folds
  the sum (Neumaier `Kernel.nm.add`, row order), `fmin`, `fmax` in ONE loop seeded with y[0] (the
  old `fold1` also folded row 0 against itself: same result); one squared-deviation fold around the mean
  (skipped for k < 2, the result is null anyway); the sort consumes the dense array. The only O(n)
  allocation per column is the dense array (plus the sort's own); no `Column.clone` on a numeric column
  (Str/Bool still clone once for Min/Max). Output bit-identical (`tests/fmt_describe_edge.bend`: expected
  text produced by the PRE-W1c build, dumped through DF.dump so f32 bits are compared; q6 CSV byte-equal at
  1k/100k/1M).
- **Emitted C** (`bend -o`, real imported bench program; names are erased to `spin_N`): fused
  count/sum/min/max fold = `spin_1001` (four `u32` accumulator registers, one `blk_read` per row, callee
  closure has 0 `heap_alloc`/`term_ctr`/`rfc_seal`/`term_keep`/`blk_copy`), cast loop `spin_1140`/`1141`,
  masked cast + compact loop one of them; squared-deviation fold likewise. Per row nothing is allocated.
  A quick way to find a loop in the anonymous C: scan for `WL_AGAIN` functions and the closure of the
  `spin_N(e,` callees they inline (a step template becomes an inlined `spin` helper that is NOT itself a
  loop; the flat loop is the one with `WL_AGAIN`).
- **Measured**: q6 at 1M rows, 1 thread, interleaved 7 rounds: base 107-109 ms, new 72-89 ms (median
  73 ms), 100k: 11 ms -> 7-8 ms. The plan's ~55 ms is not reached: the radix sort of the four dense
  columns (kept on purpose) and `from_scalars` are what is left; the number is provisional (load 15-18).
- A test needing a frame of 70000 rows builds the scalar lists with a Nat-fuel descending generator
  (`gen.go(~f, n, i, acc)`) and a `~(i => f(i))` template: no recursion depth issue, 70000 rows build in
  well under a second.
## W1d/f (unboxed fallible maps, range-copy slice)

Performance lessons (C read with a transitive callee audit; numbers PROVISIONAL, 1 thread, load 16-17):

- **What allocated was `Bool.pick` over constructors, not `Maybe` as such.** In the baseline C only the
  per-row functions written as `Bool.pick(Maybe<&2, U32>, c, Some{v}, None{})` (`Eval.lo31`, `u_fdiv`,
  `u_fmod`, `f2u`, `f2i_m`) built `term_ctr(CID_SOME, ..)` per row: `Bool.pick` is an ordinary call, both
  constructors are built before it chooses. A `Maybe` returned from a `match` (`Eval.kl.some.b`,
  `D.I32.floor_div.k` behind `i_fdiv` / `i_fmod`, `U32.read`) was already unboxed as two words (tag,
  value) and allocated nothing. So the Kleene and the i32 floor_div / mod passes did not get faster
  (1.10 vs 1.13, 2.13 vs 2.03 ms); lo31 4.9 -> 0.8 ms and u32 // 2.9 -> 0.9 ms per 1M (minus the 0.4 ms
  input clone of the kernel bench). Never feed constructors to `Bool.pick` in a row function; `match`
  the condition or return a single-constructor record.
- **`K.R{v: U, ok: U32}` (generic, `type R<-U: Data> is Data`) rides in registers**: the row function
  returns `o[0], o[1]` (two u32), `map_r.put` takes them as two u32 parameters; the `map_r` / `zip_r`
  loops and every callee have zero `term_ctr` / `term_keep` / `ctr_take` / `rfc_seal` / `blk_*` allocs.
  The String instance (`Strs.map_r`, per Dictionary entry) has a `blk_keep` per row: the string read.
- **Branch-free is not always faster**: computing the i32 floor quotient (two magnitudes, a div and a
  mod) on every row and masking with ok was ~15% slower (2.6 vs 2.2 ms) than a `match` on the failure
  test that skips the work; for u32 the masked form is right (one guarded `U32_QUO`).
- **`U32.div(x, 0) = 0`, `U32.mod(x, 0) = x`** in Base, and the C lowering is guarded
  (`(u32)y == 0 ? 0 : U32_QUO(x, y)`): an unconditional division in a row function is safe; mask the
  value with `U32.and(w, U32.sub(0, ok))` (`K.Kernel.r_w`) to keep the null slot at the default.
- **The range copy** (`Kernel.range.go`) is one `blk_read` + one `blk_write` per row, no allocation (the
  String instance keeps each string: `blk_keep`). Slice of 1M U32 rows 1.5 -> 0.8 ms, with a mask
  2.9 -> 1.7 ms (no 4 MB iota index, one read stream per buffer instead of two).

Proof lessons:

- **A range copy is the map proof with `f(a[k])` replaced by `rd_at(a, U32.add(off, k))`**: copy the
  `map_go` chain (hyp / res / goal / set / C shapes, `*next_lt/_b/_k`, `*_step1/2`, `*_zero`, `*_go`,
  `*hyp0`, `*_fin`) and change the read index; no template value, so no `y` / `ey` carrier. Spell the
  first read `Array.get(T, a, U32.add(off, 0))` in the kernel so every read has the same shape (the
  goal's `r` is `Array.get(T, a, U32.add(off, j))` at j = 0). It checked first time under bend and
  --verdict.
- **A content law over a constructor-only production term closes by conversion**: `slice_cell_u32` over
  the new `Column.slice` needed no pair-rewrites (the old gather version rewrote two pending pair
  results): `Equal.cong(.. SU32 ..)` of `range_cell` for AllValid, two `%` rewrites (mask cell, data
  cell) then `{==}` for a Mask. Keep production column builders as matches that return constructors
  (`Column.slice.r`), not pair-returning helpers, when a cell law must see through them.
- Typing proofs (`PROOF_evalops`) mention the production template terms verbatim: renaming
  `map_maybe` -> `map_r` and the template lambdas (`~(r => V.Eval.kl.r(r))`,
  `~(s => K.Kernel.r_of(~U32, U32.read(s), 0))`) is a text replacement; the witnesses (`kl_fin_w`,
  `cast_pw_w`) take the pair as a parameter and did not change.
## W0 strings/reader spikes (D5 coder and ranks, D6 reader; bench/spikes/w0_strings/)

Performance lessons from the W0 spikes (DESIGN.md section 17 has the design and the numbers;
all numbers provisional, shared machine, load recorded in results/*.jsonl).

- **Hotness is decided over the reachable code of the whole program, per constructor.** Read it
  in the emitted C: `CID_T[][2]` is `{arity, hot}` per constructor id (`tools/hot.py x.c NAME`).
  In any program importing frame.bend, String (SCon, Chr), List (Con), Some, CsvCell, CsvRec
  and ~200 more are hot; private single-constructor loop records (a 17-field tokenizer state)
  stay cold and travel unboxed in registers (spin arguments, no allocation per step). A type
  becomes hot from ONE owned second use anywhere (`(xs, xs)`); two borrowing reads do not.
- **The File API only returns cons lists**, built cell by cell on the IO thread (`io_list` /
  `io_str`), and with List hot every cell is rfc-sealed: building and walking 41 MB of
  `File.read_at` bytes costs ~113 ms cold, ~257 ms hot. Read pieces, walk each piece's list
  exactly once into a packed `Array<U32>` (4 bytes per word) and do every sequential scan in
  that same walk; never hold more than one piece as a list.
- **IO.fork / IO.spawn are green threads on the one IO loop**: no parallel IO-side work.
  Parallel work is only a pure parallel let (fork the parse AFTER the producer).
- **Freeing is timed where the last owner drops.** A `match` that binds a field it never uses
  drops it AT the match, i.e. before a following `IO.now()`: 1M short strings cost ~0.2 s to
  free, 1M 41-char strings ~0.7 s. Keep measured inputs alive past the clock (use them after it:
  the spikes' `keep` field); in kernels, hand string arrays back instead of dropping a copy.
- **Cons string walks**: hashing 1M strings laid out in allocation order costs 2-4 ns per code
  point (a flat UTF-8 buffer 0.2-0.6), a whole coder probe 80-130 ns per short key; `term_peek`
  on a hot cell is one more dependent load. Hash once, compare only on a hash hit, and touch each
  distinct string O(1) times (ranks pack the ENTRIES once, not the rows).
- **Checker idioms that cost time**: the termination check reads arguments left to right, so put
  the structurally shrinking argument first (`Hc.eq(x, y, ok)`, `Ms.sort(fuel, go, ...)`); no
  mutual recursion, so an early-exit loop carries a record with a `more`/`go` Bool and a
  NON-recursive step helper (`Hc.seek` + `Hc.look`, `Tr.l` + `Tr.l.chk`); a destructured tuple
  with `+` fields must put the Data scalars first (`(+qe, +qf, st) = r`, not `(st, +qe, +qf)`:
  "an annotated term (cannot infer)"); a `match` on a parameter must precede every local
  statement (`+d = ..; match t` is refused: compute `d` in the caller's argument);
  `case 1n++p ANode{..}` when the fuel is used twice; a name used as a constructor in two types
  is refused (`EQ` collides with Base `Cmp`'s `EQ`); `Bool.pick` evaluates both arms (choose
  between IO actions by matching a Bool parameter).
- **Exact f32 parsing in a flat loop**: for `[+-]digits[.digits]` with mantissa M <= 2^24 and at
  most 10 fraction digits, `F32.div(U32.to_f32(M), 10^fd)` is one correctly rounded division of
  exact values (Clinger), equal to `F32.read` (strtof) bit for bit (20,000 random cases); every
  other text goes through `F32.read` of the decoded field. `F32` is C `float` in the emitted C.
- **UTF-8 bytes keep code point order**: packed big-endian into U32 words they sort strings with
  U32 radix passes; a final key `min(bytes left, 8)` keeps a string before its extensions even
  when they continue with U+0000. Byte-level CSV tokenizing is exact because `"`, `,`, CR and LF
  are ASCII and the runtime decoder never turns a non-ASCII byte into them.
- **Per-region byte-keyed string tables may split one string** (two invalid byte sequences both
  decode to U+FFFD); never expose region codes: merge decoded entries into one ST.Dict in region
  order, which also reproduces v0.1's first-appearance codes exactly.
- **Where the 41 MB parse goes** (spike, 1 thread, in a frame.bend program): producer 0.32 s
  (serial: list build + pack + scan), tokenizer 0.40 s, each typed column 0.01-0.07 s, merge
  0.02 s; the fork phase scales 5.5x at 12 threads, the producer not at all (0.99 s -> 0.47 s;
  v0.1: 5.5 s -> 2.3 s, RSS 266-306 MB vs 1.23 GB).
