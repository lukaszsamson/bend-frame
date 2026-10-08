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
