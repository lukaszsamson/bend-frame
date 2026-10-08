# bend-frame — design

A columnar dataframe library for Bend 2 (checked against Bend 2.0.36), shaped
after Polars 2.0's eager/lazy API and Elixir Explorer's ergonomics, written so
that other agents can implement it module by module. Every type definition in
this document is checked by `probes/p21_design_sigs.bend` (`--check-only`
reports only "41 TODOs found": the open signature stubs) and every idiom is
proven by a runnable probe under `probes/` (`sh probes/run_probes.sh` → `PASS:
25 / 25`). Bend binary: `~/.bend/bin/bend` (not on PATH).

## 1. Goals, non-goals, Polars mapping

Goals (v1):

- Dtypes `Bool U32 I32 F32 Str`, nullable through a per-column validity mask.
- Eager `Frame` API: from lists / CSV, `head`, `select`, `with_columns`,
  `filter`, `sort` (stable, multi-key), `group_by + agg` (sum mean min max
  count first last n_unique), `join` (inner, left), `describe`, `show`, CSV
  write.
- An expression language (`col lit alias cast arithmetic comparisons boolean
  is_null fill_null aggregations`) with STRICT typing: no implicit casts, every
  mismatch is an `Err` value.
- A lazy `Plan` (Polars `LazyFrame`): a pure `Data` tree; `Plan.schema` resolves
  the output schema with no data (Polars `collect_schema()`), `Plan.optimize`
  does predicate pushdown, projection pushdown and filter merging, `Exec.run`
  executes.
- Row order: `select/with_columns/filter/head/sort` preserve or define order;
  `group_by` and `join` do NOT guarantee output order unless
  `maintain_order = True{}` (then first-appearance order of the left/key side).
- Laws in `LAWS.bend`, proofs in `PROOF.bend`: schema-level laws (`filter`
  keeps the schema, `select` is a projection, a projection has one field per
  name, `head` keeps `min(n, len)` rows), checked by `bend PROOF.bend`.

Non-goals / deferred (v2+): `F64/U64/I64` (Base lacks them, WONTFIX "SOON"),
`Date/Time`, `List`/`Struct`/`Map` dtypes (Polars 2 has `Map`; our schema layer
is ready for it, kernels are not), streaming/out-of-core, GPU kernels (measured
useless at this size, see §12), parallel merge sort, outer/semi/anti joins,
window functions, string ops beyond equality/ordering, bit-packed validity, a
JS/web build (works but untested).

Polars concept → bend-frame:

| Polars 2.0                  | bend-frame                                             |
|-----------------------------|--------------------------------------------------------|
| `Series` / `DataFrame`      | `Column` / `Frame` (Type-kinded: single owner)         |
| `Expr`                      | `Expr` (Data)                                          |
| `LazyFrame`                 | `Plan` (Data) + `Env` (the frames `Source` nodes name) |
| `collect_schema()`          | `Plan.schema(p) -> Res(List<&2, Field>)`               |
| `collect()`                 | `Exec.run(Plan.optimize(p), env) -> IO(ResT(Frame))`   |
| `pl.Null` + validity        | `Valid`: `AllValid{}` or `Mask{m: Array<U32>}` (0/1)   |
| strict dtype errors         | `Err.TypeMismatch{op, want, got}`                      |
| `maintain_order=True`       | `GroupBy{.., maintain_order: Bool, ..}`                |
| `scan_csv`                  | `Plan.ScanCsv{path, opts, schema}`                     |

## 2. Bend facts every implementer must follow (verified)

Each rule names the probe that proves it and, for refusals, the exact message.

R1. **Affine by default.** A second use needs `+` on the binder: `+x` in a
parameter, `+x = v`, `case 1n++p` (NOT `1n+p`) when `p` is reused,
`case ALeaf{+x}`, `(a, +g) = r`, and in a `do` block `+text : String <- m`.
Error: `expected : p / observed : p (consumed more than once)`. Only
`Data`-kinded values take `+`; `Array`, `Column`, `Frame`, closures, and
`List<&1, _>` are `Type` and can never be copied (p01, p05, p12, p15).

R2. **A def may only call defs declared ABOVE it.** Helpers go first. Calling
a later def reports `expected : a filled definition (an unfilled law is a dead
claim: live code cannot use it)`. Base's `law X` above / `def X` below trick
is NOT available to user files (WONTFIX #793), so no `.go/.if` ping-pong
(p11, p14, p17, p18).

R3. **`match` only on a parameter or a pattern-bound variable.** `match f(x):`
→ `a match cannot scrutinize a computed value: give it its own def`. A
let-bound local is refused too: `a match cannot scrutinize a local binder`.
A destructuring let `(a, x) = Array.get(..)` is a match and is refused the same
way. Consequences (p04, p09, p10, p15):
   - A call that answers a pair (`Array.get`, `Array.size`, `Map.pop`, any
     kernel) is taken apart ONLY in a helper's parameter: `def k(.., r: Array<T>
     & T): (a, x) = r; ..`, called as `k(.., Array.get(T, a, i))`.
   - A loop step receives the previous step's call results as pair-typed
     PARAMETERS and makes every call in the recursive call's argument list
     (Base's `Array.map.go` idiom). State threads through parameters; see
     `Kernel.map.go`, `Kernel.gather.go` in p21.
   - A loop's exit test or branch is a `Bool` parameter computed by the caller
     of that step and matched beside the fuel: `match f fits: case _ True{}:
     ..` (`Kernel.depth_for.go`, `Schema.find.go` in p08).
   - Prefer branch-free data flow over control flow: `Bool.pick`, `k + bit`
     (filter as compaction, p17), `Bool.to_u32`.

R4. **No forward references, no mutual recursion, mandatory termination.** The
shrinking argument must come first (`n: Nat` fuel or a structurally smaller
list/tree). Index loops over arrays take `n: Nat` fuel = `U32.to_nat(len)` and
a `+i: U32` counter (p15: a 2^22 fuel loop runs in 4 ms natively).

R5. **Generic array code must use templates `~T: Data`, never `-T: Type`.** An
erased type parameter over `Array<T>` checks but every compiled lane refuses
it: `Error: an open Array element type` (p02b, also in evaluator mode since an
IO main runs compiled). Templates monomorphize (p02). Template params come
FIRST in the parameter list (`expected : a plain binder (only leading binders
take ~)`), a `~` argument must be closed (no local variables), and a def with a
`+` parameter is not a plain function: pass `~(x => F32.show(x))`, not
`~F32.show` (`expected : @_:F32 -> String / observed : @+a:F32 -> String`),
(p04, p07).

R6. **Arrays.** `Array<T>` has 2^d slots (`Array.new(T, d, v)`, `[v : T*n]`),
indices wrap, `Array.get(T, a, i) -> Array<T> & T` for `Data` elements,
`Array.set(T, a, i, v) -> Array<T>`, `Array.swap` for Type elements,
`Array.clone(T, a)` for Data elements (O(n)). `Array.to_list` answers
`List<&1, T>` (show it with `List.show(~&1, ..)`). Matching `ANode{xs, ys}`
splits the array into two independent arrays (each a Type, each can go to one
side of a parallel let) and `ANode{xs, ys}` rebuilds it; both are O(n)-ish
(~1 ms per level at 4M floats, p15c). `Array<String>` works (p09, p14).

R7. **Tuples are Type.** `A & B` is `Sigma<&1, &1, ..>`, so it cannot live in
a `List<&2, _>` or be `+`. Declare a `Data` record instead (`KI{key, idx}`,
`Row{key, val}`) (p10, p11). Base's `Map.to_list` yields `Sigma<&2, &2,
String, _ => V>` pairs; destructure them as `(k, v) = kv` in a parameter.

R8. **`do` blocks** take `x : T <- m`, `x : T = v`, `+x : T <- m`, bare steps
and `return`; NOT a destructuring let (`expected : a pattern`) — open values in
a helper (p09). The last statement must have the block's type (bind the result
of a non-Unit step).

R9. **Lists.** `List<&1, T>` from `IO.args`/`Array.to_list` is Type; rebuild
the spine to get `List<&2, String>` (`promote`, p12). `List.sort(~A, ~le, xs)`
is a stable merge sort over `List<&2, A>` (100k elements: 73 ms native).

R10. **Numbers ⇄ text (p03).** `F32.show`: shortest round-trip digits, `2.0` →
`2`, `inf`, `nan`, `-2`; `F32.read` accepts `-1.5`, `1e3`, leading spaces, and
answers `None` on `abc`/empty; `U32.read` answers `None` on `-1`, empty,
overflow (`4294967296`) and trailing space (`"1 "`); `F32.to_u32(-1.0) = 0`.
Trim fields before parsing. I32 is vendored over U32 (p18).

R11. **Modules.** `import ./src/x.bend as X` from the root, `import ./x.bend
as X` from a sibling in `src/`; diamonds are fine (p19). An importing file sees
only the imported file's own defs (no re-exports). Hub: `import
bend-csv-parser@0.1.0.1/core.bend as Csv` fetches at check time into
`~/.bend/lib/0x<hash>` (0.1 s once cached) (p06, p16).

R12. **Laws and proofs (p08, p20).** A `law` without a def is an open claim;
`bend` prints `SOME PROOFS FAIL / Error: N TODOs found` and exits 1, so open
laws double as checkable signature stubs that live code may not call (p13).
`%e : P` rewrites occurrences of e's RIGHT side (marked `_` in `P`) into its
LEFT side: flip a hypothesis `h : {f(p) == Some{s}}` with `Equal.sym(T, f(p),
Some{s}, h)` before using it to replace `f(p)`. Injectivity of `Some` comes
from `Equal.cong` through `Maybe.default`; a `None == Some{x}` clash is refuted
through a motive `disc` (None ↦ Unit, Some ↦ Empty) and `Empty.absurd`. Laws
over Type-kinded values (a `Column` holding an `Array`) prove by case split
(p20). `--verdict` (Lean v4.34.0 via elan) rechecks them with the BendTT kernel.

R13. **Performance shape (p07, p15, p15b, p15c, p16; Apple M-series, 12
threads).** Flat `Array.get/set` loops: 4M floats summed in 4–6 ms, written in
1–2 ms (~1 ns/element). A heavy kernel (`sqrt·sin`) 16 ms flat; forked 6
levels on 12 threads 12 ms (1.3–1.8× at best: splitting costs ~1 ms per level,
the join rebuilds the spine, efficiency cores drag the balanced tree). Pure
structural `ALeaf/ANode` recursion that rebuilds the spine is 3–4× slower than
a flat loop. `!` (GPU) costs ~1.9 s per call here (shader build/transfer): not
for v1. CSV: 100k lines (2.2 MB) read 30 ms, split 100 ms, parse 33 ms, sort
73 ms, group_by through `Map` 65 ms, hub parser 70 ms.

## 3. Dependencies

- `bend-csv-parser@0.1.0.1/core.bend` (hash `0x64aa7934c3659ee6a818595494b38921`,
  181 lines, MIT, ships proofs): `Csv.parse(text) -> Ans` with
  `Parsed{rows: List<&2, List<&2, String>>} | Rejected{}`; `Csv.parse_sep(sep:
  U32, text)` for other separators. Handles quotes, CRLF, lone CR. Verified in
  p16 (70 ms / 100k rows, same as a naive split). We use it for READING; the
  writer is ours (quoting rule: a field containing `sep`, `"`, CR or LF is
  quoted, `"` doubled).
- Nothing else. `bend-kit-int` (1624 lines, U64 over `Word(64n)`, 68 µs/op) is
  rejected in favour of a vendored 80-line `I32` (p18 shows the exact code);
  `bend-kit-fmt` is rejected (Base `F32.show` already prints shortest digits;
  padding is three lines); `bend-parallel` (counting sort over U32 keys) is a
  candidate for a radix sort in v2; `bend-kit-csv` needs `bytes.bend` and
  speaks `Bytes`, not `String`.

## 4. Module layout and dependency order

Files, in import order (a file imports only files above it; no cycles). Tier:
[opus] tricky, [sonnet] moderate, [haiku] boilerplate.

```
frame.bend                 façade for `import bend-frame@x/frame.bend as DF`   [haiku]
LAWS.bend                  the claims (imports src/*)                          [opus]
PROOF.bend                 the proofs (imports LAWS.bend)                      [opus]
src/dtype.bend             DType, I32, Scalar                                  [haiku]
src/err.bend               Err, Res, ResT, Err.show                            [haiku]
src/kernels.bend           template array loops                               [sonnet]
src/column.bend            Valid, Column, Named, Frame + column ops           [sonnet]
src/schema.bend            Field, Schema ops, Frame.schema                    [sonnet]
src/expr.bend              UnOp/BinOp/AggOp/Expr, Expr.type/name/refs         [sonnet]
src/eval.bend              Eval.expr: dtype×op dispatch onto kernels           [opus]
src/sort.bend              argsort, multi-key stable sort, Sort.frame          [opus]
src/groupby.bend           GroupBy.run                                         [opus]
src/join.bend              Join.run (hash join on string keys)                 [opus]
src/csv.bend               Csv.read/parse/infer/write/render (+ hub parser)   [sonnet]
src/fmt.bend               Fmt.show (table), Fmt.describe                      [sonnet]
src/plan.bend              Plan, Env, Plan.schema, Plan.optimize               [opus]
src/exec.bend              Exec.run                                            [opus]
tests/*.bend               one IO main each, `#|` expectations                [haiku]
examples/*.bend            README programs                                     [haiku]
bench/gen.py, bench/*.bend M7 benchmark vs Polars                              [sonnet]
scripts/test.sh            the runner (§10)                                    [haiku]
README.md, LICENSE (SPDX-License-Identifier: MIT)                            [haiku]
```

All type definitions below are verbatim from `probes/p21_design_sigs.bend`
(checked). Signatures are given as the law stubs of that file; the implementer
turns each `law X: for a: A .. R` into `def X(a: A, ..) -> R:`.

### 4.1 src/dtype.bend [haiku]

```python
type DType is Data:
  TBool{}
  TU32{}
  TI32{}
  TF32{}
  TStr{}

type I32 is Data:
  I32{bits: U32}

type Scalar is Data:
  SNull{}
  SBool{b: Bool}
  SU32{v: U32}
  SI32{v: I32}
  SF32{v: F32}
  SStr{s: String}
```

- `DType.eq(a, b) -> Bool`, `DType.show(t) -> String` (`bool u32 i32 f32 str`),
  `DType.default(t) -> Scalar` (the slot value of a null: `False 0 0 0.0 ""`).
- `Scalar.dtype(s) -> Maybe<&2, DType>` (`None` for `SNull`), `Scalar.show`
  (`null`, `true/false`, `U32.show`, `I32.show`, `F32.show`, the string as is).
- `I32` (p18, vendored): `add sub mul neg is_neg cmp is_eq is_lt is_le is_gt
  is_ge show read to_f32 from_u32 to_u32 div mod`. `div`/`mod` by zero answer
  `0`/`a` (as `U32.div`), truncating toward zero. `cmp` flips the sign bit and
  compares unsigned. `read` accepts an optional leading `-` then `U32.read`.

### 4.2 src/err.bend [haiku]

```python
type Err is Data:
  ColumnNotFound{name: String}
  DuplicateColumn{name: String}
  TypeMismatch{op: String, want: String, got: String}
  ShapeMismatch{want: U32, got: U32}
  ParseError{line: U32, text: String}
  InvalidOperation{what: String}
  IoError{code: U32, text: String}

def Res(-A: Data) -> Data:
  Result<&2, &2, Err, A>

def ResT(-A: Type) -> Type:
  Result<&2, &1, Err, A>
```

`Err.show` formats exactly: `ColumnNotFound: <name>`, `DuplicateColumn:
<name>`, `TypeMismatch in <op>: expected <want>, got <got>`, `ShapeMismatch:
expected <want> rows, got <got>`, `ParseError at line <n>: <text>`,
`InvalidOperation: <what>`, `IoError <code>: <text>`. `Res(A)` is a monad
(`do Result<&2, &2, Err, A>:` works, p04); `ResT` carries Type payloads and is
matched, not chained.

### 4.3 src/kernels.bend [sonnet]

Flat, sequential, template loops; the bodies in p21 are the reference
implementation and must be copied as they are (they encode R3). Every kernel
takes `+n: U32` (logical length), `+d: Nat` (depth of the output) and consumes
its input arrays unless its signature hands them back.

```python
def Kernel.depth_for(+n: U32) -> Nat                       # least d with 2^d >= max(n,1)
def Kernel.map(~T: Data, ~U: Data, ~f: T -> U, +n: U32, +d: Nat, a: Array<T>, +z: U) -> Array<U>
def Kernel.zip(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +n: U32, +d: Nat, a: Array<T>, b: Array<U>, +z: V) -> Array<V>
def Kernel.fold(~T: Data, ~A: Data, ~f: A -> T -> A, +n: U32, a: Array<T>, z: A) -> Array<T> & A
def Kernel.compact(~T: Data, +n: U32, +d: Nat, a: Array<T>, mask: Array<U32>, +z: T) -> Array<T> & U32
def Kernel.gather(~T: Data, +n: U32, +d: Nat, src: Array<T>, perm: Array<U32>, +z: T) -> Array<T> & Array<U32>
def Kernel.scatter(~T: Data, ~A: Data, ~f: A -> T -> A, +n: U32, gids: Array<U32>, vals: Array<T>, acc: Array<A>) -> Array<A>
def Kernel.from_list(~T: Data, +xs: List<&2, T>, +z: T) -> U32 & Array<T>
```

Semantics: `map` `out[i] = f(a[i])`; `zip` `out[i] = f(a[i], b[i])`; `fold`
left fold answering the array back; `compact` writes `a[i]` at slot `k` and
advances `k` by `mask[i]` (0/1), answers `(out, k)` (p17); `gather` `out[j] =
src[perm[j]]`, answers `(out, perm)` (p10); `scatter` `acc[g[i]] = f(acc[g[i]],
v[i])` (p22); `from_list` pads to the next power of two with `z` and answers
the logical length (p14). Add: `Kernel.iota(n, d) -> Array<U32>` (`out[i] =
i`), `Kernel.const(~T, d, z)` = `Array.new`, `Kernel.to_list(~T, n, a) ->
Array<T> & List<&2, T>` (first `n` slots, in order), `Kernel.mask_and/or/not`,
`Kernel.popcount(n, mask) -> Array<U32> & U32`, `Kernel.all_eq(~T, ~eq, n, a,
b)`. A `Kernel.fork_depth() -> Nat` constant (default `0n`) reserves the M7
knob: forked variants split `ANode` for `fork_depth` levels with one parallel
let per node, then run the flat loop per block (shape of p15b `forked`); a
FIXED depth keeps F32 reductions deterministic across thread counts.

### 4.4 src/column.bend [sonnet]

```python
type Valid is Type:
  AllValid{}
  Mask{m: Array<U32>}

type Column is Type:
  CBool{len: U32, depth: Nat, valid: Valid, data: Array<U32>}
  CU32{len: U32, depth: Nat, valid: Valid, data: Array<U32>}
  CI32{len: U32, depth: Nat, valid: Valid, data: Array<U32>}
  CF32{len: U32, depth: Nat, valid: Valid, data: Array<F32>}
  CStr{len: U32, depth: Nat, valid: Valid, data: Array<String>}

type Named is Type:
  Named{name: String, col: Column}

type Frame is Type:
  Frame{height: U32, cols: List<&1, Named>}
```

Invariants (not type-enforced; `LAWS.bend` may state them): `len <= 2^depth`;
`data` has exactly `2^depth` slots; `Mask{m}` has `2^depth` slots of `0`/`1`
words and the slot of an invalid row holds `DType.default`; slots at or past
`len` are unspecified; `CBool.data` holds `0`/`1`; `CI32.data` holds two's
complement bits. Every column of a `Frame` has `len == height`; names are
unique; `cols` keeps column order.

```python
law Column.len:          for c: Column                               Column & U32
law Column.dtype:        for c: Column                               Column & DType
law Column.cell:         for c: Column  for +i: U32                  Column & Scalar      # SNull when invalid (p09)
law Column.from_scalars: for xs: List<&2, Scalar>  for t: DType      ResT(Column)         # SNull -> invalid; wrong dtype -> TypeMismatch
law Column.head:         for c: Column  for +n: U32                  Column               # len := min(n, len), array untouched (p20)
law Column.clone:        for c: Column                               Column & Column      # Array.clone per buffer
law Column.gather:       for c: Column  for perm: Array<U32>  for +n: U32    Column & Array<U32>   # rows perm[0..n), validity gathered too
law Column.compact:      for c: Column  for mask: Array<U32>  for +kept: U32 Column & Array<U32>   # Kernel.compact on data and validity
law Frame.height:        for f: Frame                                Frame & U32
law Frame.names:         for f: Frame                                Frame & List<&2, String>
law Frame.take:          for f: Frame  for +name: String             Frame & Maybe<&1, Column>   # removes the column
law Frame.put:           for f: Frame  for name: String  for c: Column   ResT(Frame)      # appends; DuplicateColumn / ShapeMismatch
law Frame.from_columns:  for cols: List<&1, Named>                   ResT(Frame)          # ShapeMismatch on unequal lens, DuplicateColumn
```

Also: `Column.slice(c, +off, +n)`, `Column.rename` (on `Named`),
`Column.null_count(c) -> Column & U32`, `Column.to_scalars(c) -> Column &
List<&2, Scalar>`, `Frame.replace(f, name, c)` (put or overwrite in place,
`with_columns` semantics), `Frame.get_cloned(f, name) -> Frame & ResT(Column)`
(take, clone, put back; what `Eval` uses for `Col`), `Frame.select_names(f,
names) -> ResT(Frame)`, `Frame.head(f, n)`, `Frame.filter_mask(f, mask, kept)`.
Column order after `with_columns`: existing names keep their position, new
ones append in expression order (Polars behaviour).

### 4.5 src/schema.bend [sonnet]

```python
type Field is Data:
  Field{name: String, dtype: DType}
```

`Schema` is `List<&2, Field>` (ordered, unique names).

```python
law Schema.find:    for s: List<&2, Field>  for +name: String      Maybe<&2, DType>      # p08 shape: hit carried as a parameter
law Schema.project: for names: List<&2, String>  for +s: List<&2, Field>   Res(List<&2, Field>)  # ColumnNotFound on a miss, in request order
law Schema.with:    for s: List<&2, Field>  for f: Field          List<&2, Field>       # replace in place or append
law Frame.schema:   for f: Frame                                  Frame & List<&2, Field>
```

Also `Schema.show(s) -> String` (`a:u32, b:f32`), `Schema.eq`,
`Schema.has(s, name) -> Bool`, `Schema.names`.

### 4.6 src/expr.bend [sonnet]

```python
type UnOp is Data:
  Neg{}
  Not{}
  IsNull{}
  IsNotNull{}
  Abs{}
  Sqrt{}

type BinOp is Data:
  Add{}
  Sub{}
  Mul{}
  Div{}
  Mod{}
  Eq{}
  Ne{}
  Lt{}
  Le{}
  Gt{}
  Ge{}
  And{}
  Or{}

type AggOp is Data:
  Sum{}
  Mean{}
  Min{}
  Max{}
  Count{}
  Len{}
  First{}
  Last{}
  NUnique{}

type Expr is Data:
  Col{name: String}
  Lit{v: Scalar}
  Alias{e: Expr, name: String}
  Cast{e: Expr, to: DType}
  Un{op: UnOp, e: Expr}
  Bin{op: BinOp, a: Expr, b: Expr}
  FillNull{e: Expr, v: Expr}
  Agg{op: AggOp, e: Expr}
```

```python
law Expr.name:   for e: Expr                         String        # Alias name, else the leftmost Col, else "literal"
law Expr.type:   for e: Expr  for +s: List<&2, Field> Res(DType)   # strict typing rules below
law Expr.refs:   for e: Expr                         List<&2, String>   # column names referenced (with duplicates)
law Expr.is_agg: for e: Expr                         Bool          # an Agg at the root or under Alias/Cast/Un/Bin
```

Typing rules (`Expr.type`; a violated rule is `TypeMismatch{op, want, got}`,
an unknown column `ColumnNotFound`):

| node                     | rule                                                                     |
|--------------------------|--------------------------------------------------------------------------|
| `Col{n}`                 | `Schema.find`                                                            |
| `Lit{SNull{}}`           | `TypeMismatch{"lit", "a typed literal", "null"}` (use `Cast(Lit null)`) |
| `Lit{v}`                 | `Scalar.dtype(v)`                                                        |
| `Alias{e, _}`            | type of `e`                                                              |
| `Cast{e, to}`            | `to`, if (type e, to) is in the cast table; else mismatch               |
| `Neg`                    | `I32`→`I32`, `F32`→`F32`                                                 |
| `Not`                    | `Bool`→`Bool`                                                            |
| `IsNull/IsNotNull`       | any → `Bool`                                                             |
| `Abs`                    | `I32`/`F32` → same                                                       |
| `Sqrt`                   | `F32`→`F32`                                                              |
| `Add Sub Mul Div Mod`    | both `U32` / both `I32` / both `F32` → same (`Mod` not on `F32`)         |
| `Eq Ne Lt Le Gt Ge`      | both the same dtype (any of the five) → `Bool`                           |
| `And Or`                 | both `Bool` → `Bool`                                                     |
| `FillNull{e, v}`         | same dtype both → that dtype                                             |
| `Agg{Sum/Min/Max, e}`    | numeric (`U32 I32 F32`) → same; `Min/Max` also on `Str`/`Bool`           |
| `Agg{Mean, e}`           | numeric → `F32`                                                          |
| `Agg{Count/Len/NUnique, e}` | any → `U32` (`Len` counts rows, nulls included; `e` is conventionally `Lit{SU32{1}}`) |
| `Agg{First/Last, e}`     | any → same                                                               |

Cast table (explicit only): `U32↔I32` (bits reinterpreted, no range check),
`U32→F32`, `I32→F32`, `F32→U32` (trunc, negatives → 0, as `F32.to_u32`),
`F32→I32` (trunc), `Bool→U32/I32/F32` (0/1), `U32/I32/F32/Bool→Str` (`show`),
`Str→U32/I32/F32/Bool` (`read`; a failed read is NULL, Polars `strict=False`
semantics — the only lenient path, and only through an explicit cast),
`T→T` identity. Null propagates through every op; `IsNull/IsNotNull/Count`
never answer null; `FillNull` replaces nulls of `e` by `v` row-wise.

### 4.7 src/eval.bend [opus]

```python
law Eval.expr:   for f: Frame  for e: Expr   Frame & ResT(Column)   # frame unchanged; aggregation answers a 1-row column
law Eval.scalar: for e: Expr                 Res(Scalar)            # constant folding for Lit-only trees
```

- `Col{n}`: `Frame.get_cloned` (clone, O(n)). The optimizer may later steal a
  column referenced exactly once; v1 always clones.
- `Lit{v}`: a column of `Frame.height` copies (`Array.new`), `SNull` refused by
  typing; literals broadcast.
- `Bin`: evaluate `a` then `b` (sequentially in v1; a parallel let `ca cb =
  Eval.expr(..) Eval.expr(..)` is impossible because both need the frame — the
  M7 option is to clone referenced columns first and evaluate the two subtrees
  over column environments in parallel), check `len` equality
  (`ShapeMismatch`), dispatch on `(op, dtype)` to `Kernel.zip` with the Base
  op (`~U32.add`, `~F32.mul`, `~(a => b => Bool.to_u32(F32.is_lt(a, b)))`,
  `~I32.add` ...). Validity: `AllValid` × `AllValid` → `AllValid`, else
  `Kernel.zip(~U32,~U32,~U32,~U32.and, ..)` of the masks (materialise
  `AllValid` as a mask of ones only when needed). Division by zero: `U32/I32`
  follow Base (`0`), `F32` gives `inf/nan` (IEEE), never an error.
- Comparisons on `Str` use `String.order`; on `Bool` compare the words.
- `Un`: `Kernel.map`. `IsNull` answers the inverted mask as data with
  `AllValid`.
- `Cast`: `Kernel.map` with the conversion; `Str→num` builds a new mask from
  the `Maybe` results (`Kernel.map` twice or one map into a `Data` pair record
  `Parsed{ok: U32, v: F32}` then two maps — keep it simple).
- `Agg`: `Kernel.fold` with a `Data` accumulator record per op (`SumAcc{s}`,
  `MeanAcc{s, n}`, `MinAcc{seen: Bool, m}`, `NUnique` via a `Set` of
  `Scalar.show` strings), skipping invalid rows (fold over `(value, valid)`
  pairs: zip the mask in, or fold with the mask as a second array through a
  dedicated `Kernel.fold2`). Empty input: `Sum=0`, `Count=0`, `Len=0`, `Mean/Min/
  Max/First/Last = null`, `NUnique=0` (see section 5 and 14 for the null rules). Polars `pl.len()` is `Agg{Len, Lit{SU32{1}}}`.
- Error strings use `DType.show` for `want/got` and the op's lowercase name.

### 4.8 src/sort.bend [opus]

```python
type SortKey is Data:
  SortKey{name: String, descending: Bool, nulls_last: Bool}

law Sort.argsort: for f: Frame  for keys: List<&2, SortKey>   Frame & ResT(Array<U32>)
law Sort.frame:   for f: Frame  for keys: List<&2, SortKey>   ResT(Frame)
```

Algorithm (p10 verified the pieces): for ONE key, `Kernel.to_list` the column
into `List<&2, KI>`-style `Data` records `(key, valid, idx)`, `List.sort` with
a `~le` per dtype that puts nulls first/last and flips for `descending`, then
write `perm[j] = idx` (`perm.go`). Multi-key: process keys from LAST to FIRST;
after the first pass hold `perm`; for each earlier key gather that key column
by `perm` (`Column.gather`), argsort the gathered column stably to `perm2`, and
compose `perm := gather(perm, perm2)` (`Kernel.gather(~U32)`). Stability of
`List.sort` makes the chain a lexicographic stable sort. `Sort.frame` gathers
every column once with the final `perm`. Output order is fully defined.

### 4.9 src/groupby.bend [opus]

```python
law GroupBy.run: for f: Frame  for keys: List<&2, Expr>  for aggs: List<&2, Expr>  for +maintain_order: Bool   ResT(Frame)
```

1. Evaluate each key expression (`Eval.expr`), require non-aggregate; build
   the per-row group key string: `Scalar.show` of each key cell joined with
   `\u{1f}`, nulls as `\u{0}null` (one group per distinct tuple, nulls group
   together as in Polars).
2. One pass over rows: `Map<&2, U32>` key → group id (`Map.pop` then `Map.set`,
   p11 idiom) and `gids: Array<U32>` (row → gid); keep `List<&2, Scalar>` per
   key column of first appearance for the output key columns (append gid order
   by consing and reversing).
3. For each `aggs[j] = Agg{op, e}` (anything else: `InvalidOperation{"agg
   expects an aggregation"}`): evaluate `e` to a column, then `Kernel.scatter`
   into an accumulator array of `n_groups` slots (`Sum`: add; `Count`: count
   valid; `Mean`: `Data` pair acc then a map; `Min/Max`: acc with a `seen`
   flag; `First/Last`: idx acc with `U32.min/max` of row indices then a
   gather; `NUnique`: per-group `Set` in a `Map` — slow path, documented).
   Invalid rows are skipped by scattering `valid` alongside (zip the mask into
   a `Data` record first).
4. Output frame: key columns (gid order = first appearance) then aggregate
   columns named `Expr.name(aggs[j])`. If `maintain_order = False{}` the
   implementation MAY emit groups in `Map.to_list` order instead (unspecified
   order, Polars contract); v1 emits first-appearance order in both cases but
   tests must not rely on it when `maintain_order = False{}`.

### 4.10 src/join.bend [opus]

```python
type JoinHow is Data:
  Inner{}
  Left{}

law Join.run: for +how: JoinHow  for left: Frame  for right: Frame  for left_on: List<&2, String>  for right_on: List<&2, String>   ResT(Frame)
```

Hash join: build `Map<&2, List<&2, U32>>` from the RIGHT key string (same key
encoding as group_by; null keys never match) to its row indices (consed, so
reversed: reverse each list at the end to keep right order); probe each LEFT
row in order, emitting `(li, ri)` pairs for every match (`Inner`) or one
`(li, none)` when there is none (`Left`), as two `List<&2, U32>` plus a
`List<&2, U32>` validity for the right side. Then `Kernel.from_list` to
`perm_l`, `perm_r`, `valid_r` and gather both frames; right key columns are
dropped; a right column whose name clashes gets the suffix `_right`
(Polars default). The left side's order is preserved; the right side's
match order is right-row order. Key dtypes must match (`TypeMismatch{"join",
..}`).

### 4.11 src/csv.bend [sonnet]

```python
type CsvOpts is Data:
  CsvOpts{sep: Char, has_header: Bool, infer_rows: U32}

law Csv.read:   for path: String  for opts: CsvOpts   IO(ResT(Frame))
law Csv.parse:  for text: String  for opts: CsvOpts   ResT(Frame)
law Csv.write:  for f: Frame  for path: String         IO(Frame & Result<&1, &1, (U32 & String), Unit>)
law Csv.render: for f: Frame  for prec: Maybe<&2, U32>  Frame & String     # Some{4}: floats with 4 decimals (the bench goldens)
```

`Csv.read`: `File.open/File.size/File.read/File.close` as in p05/p16
(`read_all`), `IoError` on a failed open (match the `Result`, do not `IO.try`,
so the error is a value). `Csv.parse`: hub `Csv.parse_sep(Char.to_u32(sep),
text)`; `Rejected{}` → `ParseError{0, "malformed csv"}`; header row = names
(`has_header = False{}` → `column_0 ..`); a trailing empty row (from a final
newline) is dropped; ragged rows → `ParseError{line, text}`. Inference per
column over the first `infer_rows` rows (0 = all), fields trimmed: all empty →
`Str` all-null; every non-empty field `U32.read`s → `U32`; else every field
`I32.read`s → `I32`; else every field `F32.read`s → `F32`; else every field in
`{true,false,True,False}` → `Bool`; else `Str`. Empty field = null (nullable
columns get a `Mask`). `Csv.render(f, prec)`: header, then rows, `\n` line ends, quoting
rule of §3, nulls as empty, `true`/`false` for Bool, `F32.show` for floats
when `prec = None{}`, else fixed `prec` decimals (`Fmt.fixed(x, prec)`: round
half away from zero through `F32.floor(x * 10^p + 0.5)`; `bench/golden/*.csv`
use 4). `Csv.write` renders with `None{}`.

### 4.12 src/fmt.bend [sonnet]

```python
law Fmt.show:     for f: Frame   Frame & String
law Fmt.describe: for f: Frame   Frame & ResT(Frame)
```

`Fmt.show` prints Polars' layout, ASCII only (safe through every lane):

```
shape: (3, 2)
+------+-----+
| name | age |
| ---  | --- |
| str  | u32 |
+======+=====+
| ann  | 31  |
| bob  | 42  |
| cy   |     |
+------+-----+
```

Column width = max over header, dtype and cells (`String.length`); a frame
taller than 10 rows shows the first 5 and last 5 with a `| ... |` row; nulls
print as empty cells; strings are not quoted. `Fmt.describe` answers Polars' layout
(`bench/golden/q6.csv` is the oracle): a `statistic: Str` column with the
rows `count null_count mean std min 25% 50% 75% max`, then one column per
input column. Numeric (`U32 I32 F32`) inputs become `F32` columns: `count` =
valid rows, `null_count`, `mean` over valid rows, `std` = SAMPLE standard
deviation (ddof = 1; `null` when count < 2), `min`/`max`, quantiles by
NEAREST rank over the sorted valid values (`idx = round(p * (count - 1))`,
half away from zero; `null` when count = 0). `Str`/`Bool` inputs become `Str`
columns with `count`, `null_count`, `min`, `max` (as text) and null elsewhere.
Also `Fmt.fixed(x: F32, prec: U32) -> String`.

### 4.13 src/plan.bend [opus]

```python
type Plan is Data:
  ScanCsv{path: String, opts: CsvOpts, schema: List<&2, Field>}
  Source{name: String, schema: List<&2, Field>}
  Select{exprs: List<&2, Expr>, input: Plan}
  WithColumns{exprs: List<&2, Expr>, input: Plan}
  Filter{pred: Expr, input: Plan}
  Sort{keys: List<&2, SortKey>, input: Plan}
  GroupBy{keys: List<&2, Expr>, aggs: List<&2, Expr>, maintain_order: Bool, input: Plan}
  Join{how: JoinHow, left_on: List<&2, String>, right_on: List<&2, String>, left: Plan, right: Plan}
  Head{n: U32, input: Plan}

type Env is Type:
  Env{frames: List<&1, Named.Frame>}

type Named.Frame is Type:
  NF{name: String, frame: Frame}

law Plan.schema:   for p: Plan   Res(List<&2, Field>)
law Plan.optimize: for p: Plan   Plan
```

A `Plan` is pure `Data` (copyable, printable, optimisable); the data lives in
`Env` (frames by name) or on disk (`ScanCsv`). `ScanCsv.schema` is the schema
the user declares or that `Lazy.scan_csv` infers from the header + a sample
at plan-build time (so `Plan.schema` stays pure).

`Plan.schema` rules (strict, data-free; p08 is the miniature with its laws):
`ScanCsv/Source` → their schema; `Select{es}` → `[Field{Expr.name e, Expr.type
e s}]` in order, `DuplicateColumn` on repeated output names; `WithColumns` →
`Schema.with` each; `Filter{p}` → input schema if `Expr.type(p) == TBool{}`,
else `TypeMismatch{"filter", "bool", got}`; `Sort` → input schema after
checking the keys exist; `GroupBy` → key fields (types of key exprs) then
`[Field{Expr.name a, Expr.type a}]`, each `a` must be `Expr.is_agg`; `Join` →
left fields, then right fields minus `right_on`, clashing names suffixed
`_right`, key dtypes equal; `Head` → input schema. Any aggregate inside
`Select/WithColumns/Filter` is `InvalidOperation` in v1 (no implicit
broadcasting of aggregations).

`Plan.optimize` (each rule must keep `Plan.schema` and the result):
1. Filter merging: `Filter{p, Filter{q, x}}` → `Filter{Bin{And, q, p}, x}`.
2. Predicate pushdown: `Filter{p, Select{es, x}}` → `Select{es, Filter{p', x}}`
   when every `Expr.refs(p)` is produced by `es` as a plain `Col` or
   `Alias{Col{c}, n}` (rewrite names through the alias: `p'`); likewise through
   `WithColumns` when `p` references no new/overwritten name; through `Sort`
   and `Head`? Through `Sort` yes (filter commutes with sort), through `Head`
   NO (changes the result).
3. Projection pushdown: compute the set of names needed above a node and insert
   `Select{[Col ..]}` directly over `Source`/`ScanCsv` (or narrow
   `ScanCsv.schema`, so the CSV reader parses only those columns) when the
   needed set is smaller than the source schema.
4. `Head{n, Head{m, x}}` → `Head{min n m, x}`; `Head` pushes below `Select/
   WithColumns` (fewer rows to evaluate).
No CSE beyond rule 1 in v1 (Bend has no sharing of equal calls, WONTFIX #812;
`Alias` + `Col` reuse is the user's CSE).

### 4.14 src/exec.bend [opus]

```python
law Exec.run: for p: Plan  for env: Env   IO(ResT(Frame))
```

Bottom-up: `ScanCsv` → `Csv.read` (IO); `Source` → take the frame from `Env`
(a frame may be named once; a plan that names it twice, e.g. a self-join,
gets a clone — v1: `InvalidOperation{"self join"}`); `Select` → evaluate
exprs in order into a fresh frame (`Frame.from_columns`); `WithColumns` →
`Frame.replace` each; `Filter` → `Eval.expr` → `Kernel.popcount` →
`Frame.filter_mask`; `Sort` → `Sort.frame`; `GroupBy` → `GroupBy.run`; `Join`
→ run both sides then `Join.run`; `Head` → `Frame.head`. `Exec.run` always
runs `Plan.schema` first and fails early with its error. The public
`Lazy.collect(p, env)` is `Exec.run(Plan.optimize(p), env)`.

### 4.15 frame.bend (façade) [haiku]

Thin wrappers so users need one import: `DF.read_csv(path) -> IO(ResT(Frame))`
(`CsvOpts{',', True{}, 100}`), `DF.from_columns`, `DF.show`, `DF.select`,
`DF.with_columns`, `DF.filter`, `DF.sort`, `DF.group_by`, `DF.join`,
`DF.head`, `DF.describe`, `DF.write_csv`, `DF.col(name)`, `DF.lit_u32/i32/
f32/str/bool`, `DF.alias`, `DF.cast`, `DF.add/sub/mul/div/mod/eq/ne/lt/le/gt/
ge/and/or/not/neg/is_null/fill_null`, `DF.sum/mean/min/max/count/first/last/
n_unique`, `DF.lazy_source(name, frame) -> Plan & Env`, `DF.scan_csv`,
`DF.collect`, `DF.collect_schema`, `DF.explain(p) -> String` (prints the plan
tree). Eager verbs are `Frame -> .. -> ResT(Frame)` and go through the same
`Eval`/`Sort`/`GroupBy`/`Join` entry points as `Exec`. Types are reached as
`import bend-frame@0.1.0/src/column.bend as C` etc. (publishing uploads every
imported file, so sub-modules are importable by path).

## 5. Null semantics (explicit)

A row is null iff its validity word is `0`. Arithmetic, comparisons, casts,
`Neg/Not/Abs/Sqrt`: null in → null out (mask AND). Boolean `And/Or` are Kleene
(`false & null = false`, `true | null = true`, else null). `IsNull`,
`IsNotNull`, `Count`, `NUnique`: never null. `FillNull(e, v)`: `e` where
valid, `v` otherwise (both masks combine: result null only where both null).
Aggregations skip nulls, except `NUnique` (null counts as one value) and
`First/Last` (the first/last row, null included); `Mean` of no valid rows is
null; `Sum` of none is `0`. Sorting: nulls first by default (`nulls_last = False{}`), stable among
themselves. Group keys: nulls form one group. Join keys: null never matches.
CSV: empty field ↔ null. `Fmt.show`: empty cell. Kernels compute over the
default slot value of null rows (`0`, `0.0`, `""`): never a crash, always
masked after.

## 6. Parallelism plan

Measured (R13): intra-column forks over a 4M-float `Array` give ≤1.8× on 12
threads for a heavy kernel and nothing for light ones; the GPU is out. v1 is
therefore sequential inside a column and parallel ACROSS independent work:

- `Select`/`WithColumns`/`GroupBy.aggs`: evaluate expression i and expression
  j in a parallel let when they share no frame (after cloning referenced
  columns into per-expression column environments) — M7, behind
  `Eval.parallel_exprs()`. Balanced: split the expression list in halves.
- `Join`: left and right inputs of a plan `Join` run in a parallel let
  (`Exec.run` is IO, so this is `IO.fork`/`IO.join`, GUIDE §IO), or purely
  when both sides are `Source`.
- `Kernel.fork_depth()` is the only intra-column knob; a kernel's fork depth
  is a compile-time constant (not thread-count dependent) so F32 sums are
  deterministic run to run.

## 7. Row-order guarantees (documented contract)

| op                        | order of output                                     |
|---------------------------|-----------------------------------------------------|
| select/with_columns/filter/head/cast/fill_null | input order                    |
| sort                      | by keys, stable (ties keep input order)             |
| group_by                  | unspecified; first appearance when `maintain_order` |
| join inner/left           | left order; ties: right row order                   |
| describe                  | fixed statistic order                               |

## 8. Laws v1 (`LAWS.bend`) and how they are proven (`PROOF.bend`) [opus]

Status (M6): `LAWS.bend` states 48 laws over `src/`; `PROOF.bend` proves all
of them (`bend PROOF.bend` prints ALL PROOFS CHECK in ~0.45 s; `make proofs`).
No `@unsafe`, no foreign code. `bend PROOF.bend --verdict` also prints ALL
PROOFS CHECK under the independent BendTT kernel (~1 s; `make verdict`). A deliberately false claim (2^(d+1) slots) fails with
the expected/observed terms, so the claims are load-bearing. The miniature
probes p08/p20 remain as the pattern references.

Proven (`law x` in LAWS.bend, `def Laws.x` in PROOF.bend):

| group | laws |
|-------|------|
| Schema (schema.bend) | `project_nil`, `project_length`, `project_names` (a successful `Schema.project` has exactly the requested names, in order), `with_existing_keeps_width`, `with_new_appends` |
| Expr typing (expr.bend) | `dtype_eq_refl`, `alias_name`, `col_name`, `alias_type`, `alias_is_agg`, `agg_is_agg`, `col_refs`, `lit_type`, `col_type`, `cmp_type_bool` (any of `== != < <= > >=` over one dtype is bool), `arith_type` (`+ - * /` over one numeric dtype keep it), `mod_type`, `logic_type` (`& |` over bools), `cast_type` (an allowed cast has the target dtype), `is_null_type`, `is_not_null_type`, `counting_type` (count/len/n_unique are u32), `keeping_agg_type` (min/max/first/last keep the dtype), `sum_type`, `mean_type` (f32) |
| Plan.schema (plan.bend) | `source_schema`, `head_keeps_schema`, `filter_keeps_schema` (bool, non-aggregating predicate; the `Expr.is_agg(e) == False{}` hypothesis of section 14/M4), `filter_schema_is_input` (whenever a Filter resolves, it is the input schema: no side condition), `sort_keeps_schema` (keys exist, stated with `Laws.keys_exist`), `sort_schema_is_input`, `select_cols_is_project` (a Select of plain `Col`s IS `Schema.project`, errors included), `select_cols_names`, `with_column_keeps_width` (one expression whose name the input has) |
| Optimizer (plan.bend) | `head_pass_keeps_schema` (`Opt.head(p, n)` keeps the schema of EVERY plan, any pending limit), `merge_pass_keeps_schema` (`Opt.merge` keeps the schema of every well-typed plan), `merge_head_keeps_schema` (their composition), `merge_pass_merges` (after the pass no Filter sits on a Filter), `merge_fixed_point`, `merge_idempotent`, `head_pass_merges` (no Head sits on a Head) |
| Columns (column.bend) | `head_len` (`head(c, n)` has `min(n, len)` rows), `head_dtype` |
| Kernels (kernels.bend) | `mask_not_slots` (`Kernel.map`), `mask_and_slots` (`Kernel.zip`), `iota_slots` (`Kernel.iota_from`): the output array has exactly 2^d slots, through a pure model `Laws.slots` of `Array.size` |
| I32 (dtype.bend) | `i32_add_comm` (via Base's `U32.add_comm`), `i32_bits_roundtrip` |

Not provable or not true as stated, recorded here instead of as open laws:

- `Plan.schema(Plan.optimize(p)) == Plan.schema(p)` for the FULL pipeline:
  the predicate-pushdown (`Opt.push`) and projection-pushdown (`Opt.proj`)
  passes rename and filter column names through `String.eq` / `Names.has`;
  `String.eq` goes through `String.cmp` and `Char` comparison, so even
  `String.eq(n, n) == True{}` has no computational proof, and every fact of
  the form "the renamed predicate still types" or "`Opt.fkeep(s, names(s))
  == s`" is out of reach. Future: a `String.eq` reflexivity/soundness lemma
  in Base (or a `law` on `Names.has`) would unlock both passes. The two
  passes that do not touch names (merge, head) are fully proven.
- `Opt.merge` does NOT keep the schema of an ill-typed plan: `Filter{e,
  Filter{q, x}}` with `q : u32` fails with `TypeMismatch{"filter", "bool",
  "u32"}` while the merged `Filter{q & e, x}` fails with `TypeMismatch{"and",
  "bool", "u32"}`. This is why `Plan.optimize` guards on `Plan.schema(p)`
  (section 14/M4) and why the law carries the `Plan.schema(p) == Done{s}`
  hypothesis. Not a bug: the error text differs, never a Done schema.
- `with_columns_height` (eager, from the v1 sketch): `Eval.with_columns`
  runs in IO-free but Array-heavy code over `Frame`; a height law needs a
  model of every kernel (as `Laws.slots` models `Array.size`). Future.
- I32 `neg` involution, `add` zero/associativity: `U32.sub` is `Word.adc(..,
  True, True)`; Base proves only `Word.add_comm`. Bit-vector carry lemmas
  are future work (Base-level).
- `Kernel.compact` count `<= n` (filter length): a U32 inequality over
  `Word`s, same reason. The slots laws cover map/zip/iota; `compact` and
  `gather` would need an `Array.get` witness lemma (a copy of `swap_ex`).
- Fmt/Csv round trips: `F32.show`/`U32.show`/`F32.read` are primitives.
- Group_by/Join schema laws: `Grp.validate`/`Join.schema` go through
  `Names.has` (String.eq) for duplicate and clash checks. Future with the
  String.eq lemma above.

Proof toolkit (verified in PROOF.bend; see its header comment): unfold one
step with `{==}`; `%e : P` rewrites with `e : {a == b}` where `_` in P marks
b and becomes a (so flip hypotheses with `Equal.sym` before replacing a
computed term by its value); `Done`/`Some` injectivity via `Equal.cong` +
`Result.default`/`Maybe.default` (the payload itself as the default avoids
needing an inhabitant); refute `Fail == Done`, `False == True`, `True ==
False` through a motive and `Empty.absurd`; a value the code computes (a
dtype lookup, a sub-plan's schema, a kernel's read pair) is passed to a lemma
as a PARAMETER and matched there (p08); a hypothesis that must be rewritten
moves into the goal as a function type `H -> G`, is rewritten there and taken
back with `h => ...`; a schema rule over an input result is abstracted as a
function parameter `f` with a `fails: @e -> {f(Fail{e}) == Fail{e}}` witness
(`unary` in PROOF.bend) instead of one lemma per node; `match` on a `+x`
pattern binder when the proof spends it twice (law binders too: `for +s`);
Type-kinded values (arrays, columns) can be matched once and never copied,
so every array lemma hands the rewritten array back as a Sigma witness
(`&b: Array<T> -> {.. == b} & {slots(b) == k}`) and the next lemma takes it
as a parameter; template kernels are proven by template proof defs
(`map_go_slots(~T, ~U, ~f, ..)`) with the induction hypothesis passed as a
lambda to the step lemma (no mutual recursion). A `case other:` fallback
does not refine the scrutinee, so a goal that must compute on "any other
constructor" lists the constructors.

## 9. Idiom checklist for implementers (copy into every module's header)

1. Helpers above callers. No forward calls, no mutual recursion.
2. Shrinking argument first: `n: Nat` fuel for index loops, the list/tree for
   structural ones.
3. Take pair results apart in a helper's parameter; thread loop state as
   pair parameters; make every call in the tail call's argument list.
4. Branch on a `Bool` parameter computed by the previous step, or stay
   branch-free (`Bool.pick`, `k + bit`).
5. `~T: Data` templates for anything generic over arrays; template params
   first; closed `~` args; wrap `+`-param defs in a lambda.
6. `+` for every second use; `1n++p`; `ALeaf{+x}`; `(a, +g) = r`.
7. `Data` records instead of tuples inside lists or `+` values.
8. `List.show(~&1, ..)` for `Array.to_list`; `promote` `List<&1, String>`.
9. `do` blocks: no destructuring; bind non-Unit steps; `+x : T <- m`.
10. Errors are values (`Res`/`ResT`); `IO.die` only in `main`s of tests.

## 10. Testing convention

`tests/<area>_<case>.bend`: `import Base`, relative imports of `./../src/..`
(tests live one level below the root: `import ./../src/column.bend as C`;
the `..` path segment is accepted, verified by
`probes/p19_modules/tests/t_parent_import.bend`), one `def main() ->
IO(Unit)` printing lines, then trailing `#|<expected line>` comments (the
Bend repo's gates/test.ts rule: expected = every line starting with `#|`,
prefix stripped, in order). A test passes when `bend tests/x.bend` prints
exactly those lines. The runner `scripts/test.sh` already exists (another
agent wrote it; `make test`) and follows gates/test.ts: stdout+stderr merged,
trailing whitespace per line and the whole text trimmed, a non-zero exit
appends `exit N` (except when the expectation itself starts with `SOME PROOFS
FAIL` or `Error:`), 120 s per file, files with no `#|` lines must exit 0. Write
`#|text` with no space after `#|` (a `#| text` leading space survives on
multi-line expectations). `make proofs` runs `bend PROOF.bend`; add
`scripts/test.sh` + `make proofs` to CI. `probes/run_probes.sh` is the same
convention over `probes/`.

Tests run in the evaluator/JS lane (`bend file.bend`), ~0.2–1 s each: keep
data small (≤ 1k rows). Negative tests print `Err.show` output. Benchmarks are
native (`bend x.bend -o x && ./x`) and live under `bench/`, never in `tests/`.
`bend <file> --check-only` exits 1 while a law is open ("N TODOs found").

## 11. Milestones and acceptance tests

M1 dtype + err + kernels + column + fmt.show [haiku/sonnet]
 - `tests/column_from_scalars.bend`: build `U32/F32/Str/Bool/I32` columns with
   nulls from scalar lists, read cells back (`null` where `SNull`), `len`.
 - `tests/kernels_basic.bend`: map/zip/fold/compact/gather/scatter/from_list
   on small arrays (expected values as in p02, p10, p14, p17, p22).
 - `tests/frame_show.bend`: the exact table of §4.12 for a 3×2 frame with a
   null; `shape: (3, 2)` first line.
 - `tests/i32.bend`: p18's lines.

M2 schema + expr + eval (eager) [sonnet + opus]
 - `tests/expr_type.bend`: every row of the typing table, including three
   mismatches printed via `Err.show`.
 - `tests/eval_arith.bend`: `with_columns([alias(add(col a, lit 1), "c")])`
   on a frame with a null → `c` has the null; `filter(gt(col a, lit 3))`
   keeps the right rows; `select` reorders; `cast(str→f32)` makes `x` null.
 - `tests/eval_agg.bend`: sum/mean/min/max/count/first/last/n_unique over a
   column with nulls; empty-frame results per §4.7.

M3 CSV io [sonnet]
 - `tests/csv_parse.bend`: inline text with quotes, CRLF, empty fields,
   trailing newline → inferred schema `id:u32, name:str, score:f32,
   flag:bool`, heights, nulls; `Csv.render` round-trips to the same frame.
 - `tests/csv_file.bend`: write `/tmp/bend_frame_test.csv`, read it back,
   show it (p05 pattern); a missing path prints `IoError 2: No such file or
   directory`.

M4 plan + collect_schema + optimizer + exec [opus]
 - `tests/plan_schema.bend`: `Plan.schema` of a Select/WithColumns/Filter/
   GroupBy/Join/Head chain over a `Source`, and three early errors
   (unknown column, filter on u32, agg in select).
 - `tests/plan_optimize.bend`: `DF.explain` before/after shows the filter
   under the select, merged filters, projection at the source; the collected
   frames before/after optimisation `show` identically.
 - `tests/lazy_collect.bend`: `scan_csv` → filter → select → collect prints
   the expected table.

M5 sort / group_by / join [opus]
 - `tests/sort_multi.bend`: two keys, one descending, nulls first; stability
   witnessed by a third column.
 - `tests/groupby_agg.bend`: p11's groups with `maintain_order = True{}`
   (`a=2/7, b=2/4, c=1/4` shape), null key group, every AggOp.
 - `tests/join_inner_left.bend`: inner and left join on a `str` key with a
   duplicate on the right and a miss on the left (null right columns),
   `_right` suffix on a clash.
 - `tests/golden_q1.bend` .. `tests/golden_q6.bend`: run `bench/queries.py`'s
   q1..q6 (translated to `Plan`s) over `bench/fixtures/tiny.csv` +
   `bench/fixtures/products.csv`, print `Csv.render(result, Some{4})`; the
   `#|` lines are the contents of `bench/golden/q<k>.csv` (sales schema `id
   u32, region str, product str, qty u32, price f32, discount f32 (nullable),
   ok bool`; q2 = `with_columns(alias(mul(mul(cast(col qty, f32), col price),
   sub(lit 1.0, fill_null(col discount, lit 0.0))), "revenue"))`; q3 uses
   `Agg{Len, lit 1}` for `pl.len()`; q4 sorts by `region asc, price desc, id
   asc` then `head 10`; q6 is `describe` of four numeric columns).

M6 laws/proofs [opus]
 - `bend PROOF.bend` prints `ALL PROOFS CHECK` for every law of §8 except the
   stretch one; `scripts/test.sh` includes it.

M7 benchmarks [sonnet]
 - The harness exists: `bench/gen.py` (sales_1000/100000/1000000.csv +
   products.csv, seeded), `bench/queries.py` (q1..q6), `bench/run_polars.py`
   → `bench/results/polars.json` (`{query, n, seconds, threads}`; Polars 2.0,
   default threads and `POLARS_MAX_THREADS=1`), `scripts/bench.sh` with a
   `TODO bend side`. Deliver `bench/main.bend` (native: `bend bench/main.bend
   -o build/bench`), which parses each CSV once untimed, then times each
   `Lazy.collect` (best of 5, `IO.now`), writes `bench/results/bend.json` in
   the same shape, renders each result with `Csv.render(.., Some{4})` to
   `build/q<k>_<n>.csv`, and diffs the 1000-row results against goldens
   regenerated for that size (`golden.py` parametrised). Run with `--threads
   1` and default; fill the table in `bench/README.md`. Then decide
   `Kernel.fork_depth` and `Eval.parallel_exprs` from the numbers (expect:
   Bend within 10–50× of Polars on 1M rows, CSV parsing dominated by `String`
   cons cells; the untimed parse keeps the comparison about the engine).

M8 publish readiness [haiku]
 - `LICENSE` (`SPDX-License-Identifier: MIT` first line), `README.md` with
   the examples, `bend frame.bend --check-only` clean, `bend frame.bend
   --publish bend-frame@0.1.0.0` after `bend login` (a publish is permanent:
   the human runs it).

## 12. Risks and known limitations (from the probes)

1. **Every loop is a tail-recursive def with threaded pair parameters** (R3).
   Code volume is 2–3× a conventional implementation; the eval dispatcher is
   a large `match op dtype` table. Mitigation: kernels are templates, one
   helper per `(op, dtype)` is generated mechanically [haiku can fill tables
   from a spec].
2. **Column reads clone** (`Frame.get_cloned`): `a + b` costs two O(n) clones.
   Fine at 1M rows (ms), but the optimizer's "steal on last use" is the real
   fix (v2).
3. **Strings are cons lists** (`String = SCon{Char, ..}`): CSV parsing is
   ~100 ns/char-ish; a 100 MB file is minutes. Chunked `File.read_at` streaming
   and `Bytes` (bend-kit) are the v2 path. `String.length` is an intrinsic;
   other deep folds may overflow the JS lane past ~100k elements (WONTFIX
   #798): tests stay small, benchmarks run native.
4. **No GPU**: `!` measured 1.9 s per call for a 4M-float kernel (p15b);
   WONTFIX #1065 also keeps `!` to the root of an IO step.
5. **Intra-column parallel speedup is ≤1.8×** on this machine (R13); the plan
   is cross-expression parallelism (M7), unproven until then.
6. **`--verdict` needs Lean 4.34** (installed via elan); `make verdict` is the
   strong gate, `make proofs` the fast one.
7. **`Array` limits**: block class 31 (2^31 slots) and `Nat` < 2^48 (WONTFIX
   #779); `Array.new` of a computed value at depth ≥ 24 trips the 2^24 copy
   count on the C lane (#1267): a column may not exceed 2^23 rows per
   `Array.new` of a boxed default — allocate `Str` columns of ≥ 2^24 rows as
   joined halves (v2 problem; v1 caps `Kernel.depth_for` at `23n` and answers
   `InvalidOperation{"too many rows"}`).
8. **`F32` only** (no F64): sums of 1M values lose precision; `Mean` uses a
   pairwise-free running sum — document, do not fix in v1.
9. **Hub fetch at check time**: the first `bend` run of `src/csv.bend` needs
   the network; `~/.bend/lib` caches it. Pin by hash in a comment next to the
   name import.
10. **Exact refusals to expect while implementing** (search this file): `an
    open Array element type`; `a match cannot scrutinize a computed value
    (local binder)`; `an unfilled law is a dead claim`; `consumed more than
    once`; `only leading binders take ~`; `expected : a pattern` (destructure
    in `do`); `expected : Data / observed : Type` (a tuple or a `List<&1>`
    where Data is needed); `expected : List<&2, F32> / observed : List<&1,
    F32>` (`Array.to_list`).

## 13. Probe index (`probes/`, all pass: `sh probes/run_probes.sh`)

| probe | proves |
|-------|--------|
| p01_array_f32 | `Array<F32>` new/get/set, structural parallel sum, `1n++p` |
| p02_template_kernel / p02b_open_element_fails | `~T` kernels compile; `-T` is refused |
| p03_num_text | `F32/U32 show/read` edge cases |
| p04_result_err | `Err`, `Res/ResT`, `do Result`, computed-match helper |
| p05_strings_file | split/lines/trim, whole-file read/write, `+x <-` in `do` |
| p06_hub_import | `import name@version/file.bend` works |
| p07_parallel_bench, p15*, p16 | timings of §2 R13 (native) |
| p08_laws/ | schema plan miniature + 3 laws proven (sym, cong, disc, induction) |
| p09_column_types | `Valid/Column/Named/Frame`, `Map<&1, Column>`, cell read, helpers |
| p10_argsort_gather | argsort via `List.sort` + perm + gather, state threading |
| p11_map_groupby | `Map.pop/set` accumulation, `Map.to_list`, Data row records |
| p12_io_misc | `IO.args/now/thread_count`, `promote` |
| p13_signatures_only | open laws as checkable stubs (TODOs, exit 1) |
| p14_build_from_list | `depth_for`, `from_list` padding, exit test as parameter |
| p17_filter_compact | branch-free filter, masks as 0/1 words |
| p18_i32_vendored | the I32 module |
| p19_modules/ | `src/` relative imports, diamond |
| p20_type_law/ | a law over a Type-kinded `Column`, proven |
| p21_design_sigs | every type and signature of this document (41 stubs) |
| p22_scatter_run | the group_by scatter kernel |

## 14. Implementation deviations

Notes recorded by the implementers. All type definitions of sections 4.1-4.4
match `probes/p21_design_sigs.bend` verbatim; the items below are the only
differences, or conventions that other modules must follow.

### M1 (dtype, err, kernels, column, fmt.show)

1. **`src/fmt.bend` `Fmt.describe`** — old: `law Fmt.describe` (open claim);
   new: a `def` stub answering `(f, Fail{InvalidOperation{"Fmt.describe: not
   implemented yet (TODO)"}})`. Why: an open `law` in an imported file makes
   `bend` refuse to RUN any program that imports it ("1 TODO found"), so a
   law stub in `src/fmt.bend` would block every later test. Same signature.
   General rule: law stubs are for `--check-only` probes only, never in `src/`.
2. **Module prefixes.** An import `import ./x.bend as X` prefixes every name,
   constructors and types included, and the def names keep their own dots:
   `K.Kernel.map(~..)`, `D.DType.show`, `C.Column.cell`, `C.AllValid{}`,
   `C.CU32{..}`, `C.Named{..}`, `C.Frame{..}` (a bare `AllValid{}` is refused:
   `expected : a declared constructor`). Patterns too: `case D.SBool{b}`.
   Conventional aliases: `D` dtype, `E` err, `K` kernels, `C` column, `F` fmt.
3. **Kernel extras beyond 4.3**: `Kernel.iota_from(n, d, off)` (`out[i] = off +
   i`; `iota` is `iota_from(.., 0)`), `Kernel.compact_keep(~T, n, d, a, mask, z)
   -> Array<T> & Array<U32>` (like `compact` but hands the MASK back instead of
   the count, so one mask can filter several buffers/columns). `Kernel.
   all_eq(~T, ~eq, n, a, b) -> Bool` (both arrays consumed); `Kernel.
   popcount(n, mask) -> Array<U32> & U32`; `mask_and/or(n, d, a, b)`,
   `mask_not(n, d, a)`; `to_list(~T, n, a) -> Array<T> & List<&2, T>`.
   `Kernel.compact` writes the non-kept rows into slot `k` before overwriting:
   slots at or past `kept` hold garbage (unspecified, as DESIGN.md says).
4. **`Fmt.show` details the spec left open**: a column's width is
   `max(3, name, dtype, cells)` (3 = the `---` row); the elided row prints one
   `...` cell per column; a frame with no columns prints only
   `shape: (h, 0)`; booleans print `true/false`, floats with `F32.show`
   (`2.0` shows as `2`). `Scalar.show` prints booleans as `true/false`.
5. **`I32.read` is range checked** (`-2147483648..2147483647`, else `None`),
   beyond the "optional `-` then `U32.read`" of 4.1. Extra I32 defs:
   `I32.abs`, `I32.mag` (magnitude as U32; `abs(MIN) = MIN`).
6. **Column/Frame API additions** (all in `src/column.bend`): `Column.depth`,
   `Column.take_valid(c) -> Column & Valid` (leaves `AllValid` behind),
   `Column.set_valid(c, v)`, `Column.mk_w(t, len, depth, valid, data)` (a
   Bool/U32/I32 column over a word buffer from a `DType` tag), `Column.scalars
   (c, off, n)` (cells `off..off+n-1`), `Column.slice`, `Column.rename(Named,
   name) -> Named`, `Valid.get/clone/count/gather/compact/materialize`,
   `Frame.empty()`, `Frame.info(f) -> Frame & FInfo` (`FInfo{h, names}` Data).
   `Frame.get_cloned` clones IN PLACE (column order preserved), not "take,
   clone, put back" as 4.4 sketches, because put-back would move the column to
   the end. `Frame.put` onto a frame with no columns adopts the column's length
   as the height. `Frame.filter_mask(f, mask, kept) -> Frame` consumes the
   mask; `Column.compact(c, mask, kept) -> Column & Array<U32>` hands it back.
   `Column.gather(c, perm, n)` answers `(new column, perm)` (the source column
   is consumed). Output depth of gather/compact/from_scalars is
   `Kernel.depth_for(rows)`.
7. **Limits not implemented in v1 M1**: the `depth <= 23` cap of risk 7
   (`Kernel.depth_for` is uncapped, no `too many rows` error yet).
8. **`Fmt.fixed`** (4.12) is NOT implemented in M1; the CSV milestone owns it.

### M3 (csv)
- Added `Csv.parse_with` / `Csv.read_with` (strict explicit schema, `List<DType>` by position; empty list = infer). Wrong dtype count is `InvalidOperation`.
- `Csv.infer` returns `List<CsvField{name, dtype}>` (csv.bend does not import schema.bend); map to `Field` in glue.
- `Fmt.fixed` is exact round-half-even via F32 bit decomposition, not `floor(x*10^p+0.5)` (f32 loses bits); byte-identical to Python `f"{x:.4f}"` on all goldens.
- Blank lines skipped for multi-column CSVs; empty strings render unquoted (read back as null).

### M2 (schema, expr, eval)

All types and the signatures of 4.5-4.7 are as in `p21` (`Field`, `UnOp`,
`BinOp`, `AggOp`, `Expr`; `Schema.find/project/with`, `Frame.schema`,
`Expr.name/type/refs/is_agg`, `Eval.expr/scalar`). Differences and the
conventions later modules must follow:

1. **Eval is a compiled stack machine.** `Eval.compile(e, [])` turns an
   `Expr` into postfix `Instr` code (Data); `Eval.run` threads `EvSt{frame,
   ResT(stack)}` through one tail-recursive loop. Why: a recursive
   `Eval.go(f, e)` must thread the Type-kinded frame through both subtrees,
   which needs a helper below it (R2) or a destructured call result (R3).
   Every instruction is a whole-column op (one dtype dispatch + one flat
   template kernel). Internal types: `SKind` (`Kind` is a keyword), `Slot`,
   `Instr`, `EvSt`, `Out`, `SelSt`.
2. **Broadcasting** (Polars-like; 4.7 said only "literals broadcast"): each
   stack slot has a kind, `KFull` (frame height), `KLit` (1 row, literals
   only) or `KAgg` (1 row, aggregated). A binary op broadcasts a 1-row side to
   the other's length, so `col a > lit 3`, `col a - mean(col a)` (Full) and
   `sum(col a) + lit 1` (1 row) all work. `Eval.expr`: a `KLit` result is
   broadcast to the height, a `KAgg` result stays 1 row. `Eval.full(f, e)`
   (new) broadcasts both. An aggregation over a literal aggregates the
   1-row literal, as Polars (`sum(lit 2)` = 2, `mean`/`count`/`n_unique`/
   `first` likewise). The one exception is `Len`: `pl.len()` is encoded as
   `Agg{Len, lit 1}` and must count rows, so only `Len` over a literal
   broadcasts it to the frame height (Polars' own `lit(2).len()` = 1 is
   thereby not reproduced; nothing can tell the two apart in `Expr`).
   `Eval.kind(e)` gives the kind statically. Inside group_by, `Eval.full`
   broadcasts the aggregate's INPUT, so there `sum(lit 2)` is 2*group size
   (Polars: 2); group_by owns that.
3. **Eager ops added to eval.bend** (what `frame.bend`/`Exec` call):
   `Eval.select(f, es)`, `Eval.with_columns(f, es)`, `Eval.filter(f, pred)`,
   all `-> ResT(Frame)` consuming `f`. Each type checks EVERY expression
   against `Frame.schema(f)` before evaluating anything (first error in list
   order). `select`: output height = h if any expr is `KFull`, else 1
   (agg-select or literal-only, as Polars); 1-row outputs are broadcast; names `Expr.name`; `DuplicateColumn` /
   `ShapeMismatch` from `Frame.from_columns`. `with_columns`: every expr sees
   the INPUT frame (Polars), 1-row results broadcast to h, then
   `Frame.replace` in order; repeated output names are `DuplicateColumn`
   (Polars), checked after type errors. `filter`: `TypeMismatch{"filter",
   "bool", got}`; a null predicate row is dropped; a 1-row predicate
   broadcasts.
4. **Null semantics choices** (section 5, with Polars' exceptions):
   `And/Or` are Kleene (`false & null = false`, `true | null = true`,
   `true & null = null`, `false | null = null`); when both sides are
   `AllValid` the plain word op runs (no extra passes), otherwise each side
   is encoded as a state word (0 null, 2 false, 3 true), combined by one zip
   and split back into value + validity by `Kernel.map_maybe`; the result is
   `AllValid` if no row is null. `First/Last` return row 0 / row n-1 as is,
   null included (Polars; null of the dtype when the input is empty).
   `NUnique` counts null as one distinct value (`[1, null, 1, null]` = 2,
   all-null = 1, empty = 0). `Count` = valid rows, `Len` = rows. Empty or
   all-null input: `Sum 0`, `Count 0`, `Len` rows, `Mean/Min/Max` null.
   Every op result over a `Mask` column has its null slots reset to
   `DType.default` (`Eval.fix`, a pass only when a mask exists), so the 4.4
   slot invariant holds for every eval result.
5. **Numerics.** U32 `+ - *` and `Sum` wrap mod 2^32; I32 wraps two's
   complement (`MIN / -1 = MIN`, `abs(MIN) = MIN`); `U32/I32` `/` by 0 is
   0, `%` by 0 is the dividend (Base); F32 is IEEE (`x/0 = inf`, `-x/0 =
   -inf`, `0/0 = nan`). `Sum/Mean` over F32 (and `Mean` over U32/I32, via
   F32) use a compensated (Kahan) F32 sum (`Kernel.fsum`): risk 8 mitigated,
   ten `0.1` sum to exactly `1`. `Min/Max` on Str by `String.is_le`, on Bool
   false < true.
6. **Cast details.** `Str -> U32/I32/F32/Bool` parses the TRIMMED text;
   Bool accepts `true/false/True/False` (CSV inference set); a failed parse
   is null and an all-parsed result is `AllValid`. `F32 -> U32` is
   `F32.to_u32` (negatives 0), `F32 -> I32` truncates toward zero (out of
   range: whatever `F32.to_u32` answers). `U32 <-> I32` and `Bool ->
   U32/I32` only retag the word buffer (no pass). `Cast{Lit{SNull}, t}` is
   the typed null literal: `Expr.type` answers `t`, eval builds a null
   column. Cast mismatch message: `TypeMismatch{"cast", "castable to <to>",
   <from>}`.
7. **Expr.type error conventions** (op = lowercase name, `BinOp.name` etc.):
   arithmetic with a non-numeric left side `{op, "numeric", left}`, else
   unequal sides `{op, left, right}`; `mod` needs `"u32 or i32"`;
   comparisons `{op, left, right}`; `and/or` `{op, "bool", side}`;
   `neg/abs` `"i32 or f32"`, `not` `"bool"`, `sqrt` `"f32"`;
   `fill_null {fill_null, e, v}`; `sum/mean` `"numeric"`. Subexpression
   errors win over the node's own, left before right.
8. **Additions.** expr.bend: `Expr.show` (Polars-like text, for
   `DF.explain`), `Expr.split_agg(e) -> Maybe<&2, AggSplit{op, e}>` (an Agg
   at the root under at most Aliases: group_by's input form),
   `Expr.is_null_lit`, `UnOp/BinOp/AggOp.name`, `BinOp.symbol`,
   `DType.is_num/is_int/is_bool`, `Cast.ok(from, to)` (the cast table).
   `Expr.is_agg` also looks under `FillNull`. schema.bend: `Schema.show
   ("a:u32, b:f32")`, `Schema.eq`, `Schema.has`, `Schema.names`,
   `Field.show/eq`. `Schema.project` reports the first missing name in
   request order, THEN `DuplicateColumn` on a repeated name (so the
   `select_cols_is_project` law needs Plan.schema's Select to check types
   first, duplicates second). eval.bend helpers for later modules:
   `Eval.agg(op, c) -> ResT(Column)` (1 row, consumes c), `Eval.dropnull(c)`,
   `Eval.unit(s, t)`, `Eval.const_col(s, t, n)`, `Eval.bcast(c, n)`,
   `Eval.fix(c)`, `Eval.cast(to, c)`, `Eval.bin(op, a, b)`, `Eval.fill(a,
   b)`, `Eval.un(op, c)` (column-level, no type check). kernels.bend:
   `Kernel.mask_data` (in place: invalid slots := z), `Kernel.choose` (in
   place `a[i] := m[i] ? a[i] : b[i]`), `Kernel.fsum` (Kahan), `Kernel.
   map_maybe` (one pass to values + 0/1 ok mask).
9. **Bug fix in M1 code**: `Column.compact` now allocates
   `depth_for(kept + 1)` slots. `Kernel.compact/compact_keep` write every
   dropped row into slot `k`; with exactly `kept = 2^d` slots a dropped row
   after the last kept one wrapped into slot 0 and clobbered row 0 (a filter
   keeping 2 of [k, k, drop] rows returned a wrong first row). Callers of the
   raw kernels must give the output more than `kept` slots.
10. **Depth/mask slots.** A binary result has its LEFT operand's depth; an
    `AllValid AND Mask{m}` reuses `m` as is, so a mask may have a different
    (always >= len) slot count than `2^depth`. Kernels only touch slots
    `< len`; do not rely on "the mask has exactly 2^depth slots".

### M4 (plan, exec)

Types and signatures of 4.13/4.14 are as in `p21` (`Plan`, `Env`,
`Named.Frame`/`NF`, `Plan.schema`, `Plan.optimize`, `Exec.run(p, env)`).
Differences and decisions:

1. **Aggregations outside GroupBy are refused by `Plan.schema`** (as 4.13
   says): `InvalidOperation{"aggregation in select|with_columns|filter (v1:
   use group_by)"}`, checked per expression after its type. Eager `Eval`
   broadcasts aggregations (M2 note 2); the lazy layer deliberately does not,
   so every non-GroupBy operator is row-wise and predicate/Head pushdown are
   sound with no side conditions. Consequence for the laws:
   `filter_keeps_schema` needs the extra hypothesis
   `{X.Expr.is_agg(e) == False{} : Bool}`.
2. **Error order mirrors eager Eval** (M2 note 3): Select/WithColumns type or
   aggregation errors in list order, then `DuplicateColumn`
   (`Schema.project.chk`, so a Select of plain Cols reduces to
   `Schema.project`: `select_cols_is_project` is an induction showing
   `Plan.fields(map Col names, msg, s) == Schema.project.go(names, s)`).
   Filter: the predicate's type error, then `TypeMismatch{"filter", "bool",
   got}`, then the aggregation refusal. Sort: `ColumnNotFound` for the first
   missing key. GroupBy: `G.Grp.validate` (groupby.bend, same checks and
   messages as `GroupBy.run`), then `DuplicateColumn`. Join: `J.Join.schema`
   (join.bend, the function `Join.run` checks): `InvalidOperation{"join: no
   key columns"}`, `{"join: left_on and right_on must have the same
   length"}`, `ColumnNotFound`, `TypeMismatch{"join", l, r}`, right non-key
   fields whose name clashes with ANY left name get `_right`,
   `DuplicateColumn`. So `plan.bend` imports `sort`, `groupby`, `join`
   (types and checks), not only `exec.bend`.
3. **`ScanCsv.schema` is the file's full schema, fixed at plan-build time.**
   `Lazy.scan_csv(path, opts) -> IO(Res(Plan))` (in plan.bend) reads the file
   once and runs `Csv.infer` (header + first `infer_rows` rows); a user may
   also build `ScanCsv{path, opts, schema}` by hand. Exec reads with
   `Csv.read_with(path, opts, dtypes of schema)` (strict: a later row that
   does not parse is a `ParseError`) and then requires the file's names and
   dtypes to equal the plan's (`InvalidOperation{"scan_csv <path>: data
   schema [..] differs from the plan's [..]"}`); a Source's frame is checked
   the same way. Projection pushdown never narrows `ScanCsv.schema`; it
   inserts `Select{[Col ..]}` above the scan (4.13 rule 3's first option), so
   the CSV is still parsed whole (v2: a column subset in `Csv.read_with`).
   `Lazy.scan_csv` therefore parses the text twice per collect cycle (infer
   at build, read at run).
4. **Optimizer rules as implemented** (`Opt.merge`, `Opt.push`, `Opt.head`,
   `Opt.proj`, run in that order, each a separate structural pass; only on a
   plan whose schema resolves — an ill-typed plan comes back unchanged, so
   `Plan.schema(optimize(p)) == Plan.schema(p)` holds trivially on errors):
   predicates are split into `&` conjuncts and each sinks independently
   (unmovable ones stay, re-joined left to right); through `Select` when
   every column read is a plain `Col`/`Alias{Col}` output (renamed back,
   simultaneously); through `WithColumns` when it reads no produced name;
   through `Sort`; never through `Head`, `GroupBy`, `Join` (v1: no
   key-predicate pushdown into GroupBy, no side pushdown into Join). `Head`
   merges (`min`) and sinks below `Select/WithColumns`. Projection: the names
   needed above each node; at a Join the left side keeps its keys and every
   column a right non-key column clashes with (so `_right` names do not
   change), the right side keeps its keys and the columns whose OUTPUT name
   is needed; a leaf gets `Select{[Col ..]}` in source order when that drops
   a column, unless the nearest ancestor above any Heads is already a
   plain-Col Select; at least one column is kept (height). Not idempotent in
   general (an inserted projection is a new Select); run once.
5. **Additions.** plan.bend: `Plan.explain(p) -> String` (one node per line,
   children indented two spaces: `SOURCE n [schema]`, `SCAN CSV path
   [schema]`, `SELECT [exprs]`, `WITH_COLUMNS [..]`, `FILTER e`, `SORT BY
   [col("a") desc nulls_last, ..]`, `GROUP_BY [..] AGG [..] MAINTAIN_ORDER`,
   `INNER|LEFT JOIN ON [l = r, ..]` with left then right child, `HEAD n`;
   expressions via `Expr.show`), `Env.empty()`, `Env.add(env, name, f) ->
   Env & Plan` (prepends; answers the Source with the frame's schema),
   `Lazy.source(name, f) -> Env & Plan`, `Env.take(env, name) -> Env &
   Maybe<&1, Frame>`, `Lazy.scan_csv`. exec.bend: `Lazy.collect(p, env) =
   Exec.run(Plan.optimize(p), env)`; `Exec.compile` (postfix `Instr` code)
   and the `St{env, ResT(stack)}` IO loop. A plain-`Col` Select runs as
   `Frame.select_names` (no clone).
6. **Exec errors**: a Source whose name is not in the Env, or already taken
   (a self join), is `InvalidOperation{"source not in env (or used twice):
   <name>"}`; Env names are meant to be unique (`Env.take` drops an older
   frame of the same name when a newer one hits).

### M5 (sort, groupby)

Types and signatures of 4.8/4.9 are as in `p21` (`SortKey`, `Sort.argsort`,
`Sort.frame`, `GroupBy.run(f, keys, aggs, +maintain_order)`). Exec calls
`SO.Sort.frame(f, keys) -> ResT(Frame)` and `G.GroupBy.run(f, keys, aggs,
maintain_order) -> ResT(Frame)` (both consume the frame). Differences:

1. **Sort is a radix argsort, not a `List.sort` chain.** Every key column
   becomes an `Array<U32>` of order-preserving words (u32 as is, i32 `xor
   2^31`, bool 0/1, f32 bits mapped to a total order, str = rank among the
   column's distinct strings), `descending` xors the word with `2^32-1`, and
   keys are processed last to first with a stable LSD radix sort (2 passes of
   16 bits, a pass whose digit never varies is skipped) over `(word, row)`
   pairs; a key with a mask gets one more stable 1-bit pass on its null flag.
   Same contract (stable, lexicographic, nulls first by default and
   independent of `descending`), 30-50x faster than `List.sort` (1M u32/f32
   rows ~20-25 ms). Polars parity checked: NaN is the largest f32 (first when
   descending), `-0.0` ties with `0.0`, strings in code-point order (Polars:
   UTF-8 byte order, the same order). `Sort.frame(f, [])` is `Done{f}`; an
   unknown key is `ColumnNotFound`. `Sort.argsort` answers a permutation of
   `2^depth_for(h)` slots (first `h` meaningful).
2. **String ranks come from the Map's order.** `Map.to_list` walks Base's
   crit-bit trie in `String.order` (a shorter prefix first, then code points
   MSB first), so the list position of a key is its rank; no string sort.
   `Sort.str_codes_par` codes long columns (2^16+ rows) in 8 blocks in a
   parallel let and merges the blocks' Maps in first-appearance order: the
   codes are identical to the sequential ones (tests/sort_strcodes.bend).
3. **GroupBy does not build per-row key strings** (4.9 step 1-2). Each key
   column is dictionary-encoded once to dense codes (null = code 0): bool
   directly, u32/i32/f32 sort words by direct offset when their range is
   < 2^20 else by rank after a radix sort, str by the Map of point 2. Codes
   of several keys combine as `g * k_c + c` (re-densified through a direct
   table) while the cardinality product is <= 2^22, else by radix-ranking
   the pairs. A final densify pass numbers the groups in first-appearance
   order and records each group's first row.
4. **Output order is first appearance for both values of `maintain_order`**
   (4.9 allowed Map order for `False{}`; v1 ignores the flag). Tests must
   still not rely on the order when it is `False{}`.
5. **Aggregations are scatters** over the rows into an `n_groups` array
   and equal `Eval.agg` on each group's rows in input order: Kahan sums
   (`Sum` f32, `Mean`), wrapping u32/i32 `Sum`, `(seen, value)` `Min/Max`
   with Eval's fold order (`F32.min/max`, `String.is_le`, i32 signed),
   `Count` valid rows, `Len` rows, `First/Last` = the group's first/last ROW
   (null included, Polars), `NUnique` counts distinct values with null as one
   value (Polars). `NUnique` over f32 counts every NaN as ONE value and
   `-0.0 = 0.0` (Polars; top-level `Eval.agg` NUnique counts NaNs apart).
   Polars' `mean` of ints is f64; ours is f32 (no F64 in v1).
6. **Agg shapes accepted**: `Agg{op, e}` under at most `Alias`es, `e` with no
   aggregation inside (else `InvalidOperation{"agg expects an aggregation:
   <expr>"}` / `{"nested aggregation in agg: <expr>"}`). `Agg{Len, _}` is the
   group size (`pl.len()`); any other op over a literal-only `e` aggregates
   the literal once and repeats it per group (`sum(lit 2)` = 2, Polars).
   Keys may be any non-aggregate expression (named `Expr.name`); no keys is
   `InvalidOperation{"group_by needs at least one key"}`, an aggregated key
   `{"group_by key is an aggregation: <expr>"}`. Type errors (keys first,
   then aggs) come before these shape errors. Output names clash →
   `DuplicateColumn` (from `Frame.from_columns`).
7. **No new kernels/column helpers**: the loops live in sort.bend (`Sort.xmap`,
   `Sort.words`, `Sort.str_codes(_par)`, `Radix.sort/pass/flag`) and
   groupby.bend (`Grp.*`); groupby imports sort.bend.

### M5 (join)

Types and signatures of 4.10 are as in `p21` (`JoinHow{Inner, Left}`,
`Join.run(+how, left, right, left_on, right_on) -> ResT(Frame)`, consuming
both frames). Exec calls `J.Join.run(how, l, r, lo, ro)`; Plan.schema calls
`J.Join.schema(ls, rs, lo, ro) -> Res(List<&2, Field>)` (the same checks
Join.run makes first). Differences:

1. **No `Map` and no per-row key strings** (4.10 sketched a `Map<&2,
   List<&2, U32>>` over group_by-style key strings). Each key pair is encoded
   to `U32` codes: bool/u32/i32 the data word, f32 its bits (`0.0 == -0.0`,
   every NaN one key: Polars), str a dense id from an open-addressing string
   table built over the RIGHT column and probed by the left (forked over 16
   blocks when the left has >= 65536 rows and the table <= 4096 slots). More
   keys are folded into one dense id per row through a pair table
   `(id so far, code) -> id`. Right rows are grouped by id in CSR form
   (counts, prefix sums, rows in right order); left rows are sized, then
   `perm_l / perm_r / valid_r` written as flat arrays (not lists +
   `Kernel.from_list`). When every left row yields exactly one row (lookup
   joins: q5), `perm_l` is the identity and the left columns are not gathered.
2. **Order**: always left row order, the matches of a left row in right row
   order, for inner AND left (= Polars `maintain_order="left_right"`, as 7
   says). Polars 2.0's default inner order differs (it is unspecified there);
   `JoinHow` has no `maintain_order` field, none is needed.
3. **Output columns** as Polars with the default `coalesce`: every left
   column (keys included), then the right columns minus `right_on` (also when
   the key names differ), a right name equal to any left name gets `_right`;
   a clash that remains (e.g. the left already has `x_right`) is
   `DuplicateColumn`. Left-join misses (and an empty right side) give null
   right columns whose slots hold the dtype default.
4. **Errors, in this order** (`Join.schema`): `InvalidOperation{"join: no key
   columns"}`, `InvalidOperation{"join: left_on and right_on must have the
   same length"}`, then per key pair in order `ColumnNotFound` (left name
   first) and `TypeMismatch{"join", <left dtype>, <right dtype>}`, then
   `DuplicateColumn`. Strict typing: Polars silently casts u32 vs i32 keys to
   a supertype; bend-frame refuses. Null keys never match (Polars
   `nulls_equal=False`); `nulls_equal=True`, `validate`, `suffix` other than
   `_right`, outer/semi/anti/cross joins are not implemented.
5. **Additions** (join.bend only; no kernel/column changes): `JoinHow.show`,
   `JoinHow.is_left`, `Join.schema`, `Join.keys` (checked `KeySpec{l, r, t}`
   list), `Str.hash` (FNV-1a), `Str.eq`, `Str.copy`. Native timings (M-series,
   12 threads, parsed and forced frames, result kept alive): q5's join
   (sales x 64 products on `product`) 100k rows 11-13 ms, 1M rows 95-110 ms
   (inner and left alike; Polars 2.0: ~1.5 / ~12 ms); a u32 join 1M x 100k
   (`id`, 100k matches) ~280-360 ms, most of it freeing the 900k unmatched
   left rows' string cells during the gather. `bench/join_bench.bend`
   reproduces these.


### M5 (describe, goldens)

1. **`Fmt.describe` is implemented in `src/fmt.bend`** (supersedes the M1 stub of
   item 1 above). `fmt.bend` now imports `expr`, `eval` and `sort`; none of them
   imports `fmt` (only `csv` does), so there is no cycle and no separate module.
   Layout as 4.12: `statistic` + one column per input; the input frame comes
   back untouched (columns are cloned). Numeric columns are cast to f32,
   nulls dropped once; `mean` = `Eval.agg Mean` (Kahan), `std` = sqrt(Kahan sum of
   squared deviations / (count - 1)) (null when count < 2), `min`/`max`/`25%`/`50%`/
   `75%` read from one stable radix sort (`Sort.frame`), nearest rank
   `idx = round(p * (count - 1))`, half away from zero, computed in integers as
   `(m+2)/4`, `(m+1)/2`, `(3m+2)/4` with `m = count - 1`; verified equal to Polars 2.0
   (`describe`, `quantile(.., "nearest")`) on random frames with nulls for 13 sizes
   (1..1001) and on sales_1000000.csv (describe of 1M rows: ~100 ms native).
   `Str`/`Bool` columns: `count`, `null_count`, `min`, `max` as TEXT (Bool prints
   `true`/`false`; Polars prints 1.0/0.0 there), null elsewhere. All-null/empty
   numeric columns: `count 0`, `null_count n`, the rest null. No columns: just the
   `statistic` column. An input column named `statistic` gives `DuplicateColumn`.
2. **Group-by `Sum` over f32 is a plain sequential f32 add, not Kahan**
   (`Grp.nsum` in `groupby.bend`; `Mean` stays Kahan; `Eval.agg Sum` stays Kahan).
   Reason: `bench/golden/q3.csv` (written by Polars' LAZY group_by) has
   `revenue_sum = 96373.4141` for `inland`; the correctly rounded sum of the six
   f32 revenues is `96373.4062` (that is what Kahan and Polars' eager
   `df.group_by(..).sum()` give), the lazy engine accumulates in row order in f32
   and lands on `...4141`. Equal to Polars for small groups; for big groups
   Polars' lazy engine combines partial sums from parallel partitions, which no
   sequential order reproduces, so large-n f32 sums may differ in the last bits
   from either implementation. Consequence: lazy `GroupBy` Sum and column-level
   `Eval.agg Sum` can differ in the last ulp (item 5 of the M5 sort/group_by
   notes said they are equal).
3. **`bench/queries.bend`** (new) holds the six canonical queries as Plans for
   reuse by tests and benchmarks: `Q.q1..Q.q5(sales: P.Plan, products: P.Plan) ->
   P.Plan`, `Q.q6(sales: C.Frame) -> E.ResT(C.Frame)` (select id/qty/price/
   discount, then describe; eager like Polars). Import with a module alias that
   differs from `Q` (exec.bend is `Q` in the tests): `QS.Q.q1(..)`.
   `tests/golden_q1..q6.bend` run them over `tiny.csv`/`products.csv` (scans
   with an inferred schema) and compare `Csv.render(.., Some{4})` with the
   golden files byte for byte; `tests/fmt_describe.bend` covers mixed dtypes.
