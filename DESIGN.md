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

- (M1: forked into `src/csvparse.bend`, the hub import is removed, see 14 "M1 B02".) `bend-csv-parser@0.1.0.1/core.bend` (hash `0x64aa7934c3659ee6a818595494b38921`,
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
src/csvparse.bend          fork of the hub parser: CsvCell{text, quoted}, CsvRec{line, cells}
src/csv.bend               Csv.read/parse/infer/scan_fields/write/render       [sonnet]
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

### M0 (test runner, toolchain, CI)

1. **`scripts/test.sh` summary**: `PASS: p / total, XFAIL: x`, where `total` counts the
   tests not marked `#! xfail` (green iff `p == total`). An XPASS counts as a failure.
   Recursive (`tests/regress/`, `tests/diff/` included) and `TEST_JOBS=n` (default 1).
2. **`bench/pyproject.toml`**: `polars==2.0.0`, `numpy==2.5.3` (both pinned exactly),
   `requires-python >=3.12` (numpy 2.5.3 needs it; was `>=3.10`). `bench/uv.lock` refreshed.
3. **`make check`** also checks `frame.bend`, `examples/*.bend` and `bench/*.bend`.
   `make ci` = `toolchain-check check test proofs verdict bench-check`.
4. **`bench-check`** = `BENCH_MODE=check scripts/bench.sh`: correctness at 1k and 100k only.
5. **`TOOLCHAIN`** pins Bend 2.0.36, Lean 4.34.0, Polars 2.0.0, numpy 2.5.3, uv 0.12.23,
   Python 3.14.3; `make toolchain-check` fails on drift. CI installs these (see
   `.github/workflows/ci.yml`; macOS arm64 and Linux x86_64).

### M0 T1 / B05 (dump, comparator)

- `DF.dump` is implemented in `src/dump.bend` (`Dump.frame_k(f) -> Frame & String`, `Dump.frame`,
  `Dump.result`), not in `src/fmt.bend` as 15.1 sketches: the module is new and nothing else in
  fmt.bend changes. The facade has `DF.dump(r: ResT(Frame))` exactly as 15.1 and an extra
  `DF.dump_frame(f: Frame)` for an unwrapped frame. Grammar and rules are 15.1 verbatim (TAB
  separated, `0x` + 8 hex digits for f32, `\xHH` for C0 controls and U+007F, code points >= 128 raw).
- `bench/check.py` has two modes (typed CSV compare; `--dump` compare of two dumps) and
  `bench/dump_polars.py` writes the same text from a Polars DataFrame. The CSV mode types a column
  from the golden side, so `100000` vs `100001` and `nan` vs an integer fail; floats are exact unless
  `--ulp N` / `--rtol R` is given. scripts/bench.sh still passes `--rtol` (1e-5, 5e-5 at 1M) because
  `group_by` F32 sums are sequential adds.
- Stale "Kahan" comments in src/groupby.bend (`group_by` F32 sum is sequential, mean is
  compensated) were corrected; no behaviour change.

### M0 regressions (tests/regress, bench/contract)

- One file per 15.10 row (`tests/regress/<ID>_<topic>.bend`, one `#! xfail <ID>` each) rather than
  grouped files: the runner's xfail is per file, so a group would hide a fixed row behind an
  unfixed one. Shared helpers live in `tests/regress/lib/rx.bend` (`R.three` prints the eager,
  raw-lazy and optimised-lazy dumps under `-- <ID> <case> <api>` headers). Expected `#|` blocks are
  generated by `bench/contract/regress_expect.py` (Polars 2.0.0 where semantics match, the contract
  by hand elsewhere); `bench/contract/cardinality.py` reproduces 15.4's Polars column.
- Contract clarifications found while writing them (no contract change made): 15.4 C11
  (`a - mean(a)`) and C16 (`a > mean(a)`) are TypeMismatch for a u32 `a` under strict typing (mean
  is f32); the regressions use an f32 column. `DF.len()` is named `"literal"` by `Expr.name`
  (Polars: `"len"`); the regressions alias it. 15.6.1's "Polars: null for both" for a quoted `""` in
  a numeric column holds under an explicit schema only; under inference Polars makes that column str.
- Defects found beyond the 15.10 wording, folded into existing rows: `scan_csv` of a k > 1 column file
  with a blank line fails at collect with `csv schema: 1 dtypes for 2 columns` (B02-f); error line
  numbers count records, not physical lines, after a blank line (B02-f) or a multi-line field (B02-h,
  so B02-h needs a code fix, not only a test).
- B05-h's negative proof fixture is kept in `tests/regress/pending/` because `make check` runs
  `bend --check-only` on every `tests/**/*.bend` and an expected-failure fixture fails it.

### M1 B01/B04 (shared analysis, cardinality, sources)

- **The analysis lives in `src/analysis.bend`** (`A.Expr.analyse(e, s) -> E.Res(A.Ana)`, `A.AKind =
  KRow | KScalar | KRed`), not in expr.bend: it calls expr.bend's per-node typing helpers
  (`Expr.type.col/lit/cast/un.ok/bin.ok/fill/agg.ok`) on its sub-records' dtypes, so every dtype rule
  is still written once. `A.Ana.type(e, s)` is the dtype projection. `Expr.type` is NOT yet redefined
  as that projection (15.3.2): expr.bend cannot import the analysis (layering), and the agreement
  law of 15.3.2 is left for M2/M5.
- **The record has a fifth field, `local: Bool`** (no reduction anywhere in `e`). 15.3.2/15.4's
  height certificate "every expression KRow and total, list non-empty" admits `x - mean(x)` (KRow by
  the join table), and a Head sunk below it recomputes the mean over the first n rows
  (`B01_f "head2-over-centered"`). `Ana.preserving` = non-empty, every record KRow, total and local;
  a predicate may be merged / pushed only when total and local (`Ana.rowwise_total`); a row filter
  commutes with a Select / WithColumns whose expressions are all total and local (and, for Select,
  some KRow). Same strengthening is needed in the P2/P3 theorems.
- **Totality after the M1-A merge**: `Cast` is total iff `X.Cast.total(from, to)` (expr.bend, 15.5.5);
  `TryCast` is as total as its operand (failing cells become null); `Bin{FloorDiv/Mod/Div}` are total.
  The typed null literal (`Cast` or `TryCast` of `Lit{SNull}`) is a total KScalar.
- **Users of the analysis**: `Plan.schema` (Select/WithColumns fields, Filter predicate), Eval's
  `select` / `with_columns` / `filter` type check (`Eval.acheck`, `Eval.slot`) and select's height
  (`A.Ana.rows`), `Opt.head` / `Opt.push` / `Opt.fsafe`. `Eval.check` (X.Expr.type) stays for
  `Grp.validate`, so group_by keeps its own `"nested aggregation in agg: .."` text; `Eval.kind`
  (runtime-slot kind, used by groupby.bend) is untouched.
- **Error order inside one expression**: the analysis reports errors bottom-up, so a nested
  aggregation is found while typing; `filter(sum(sum(a)))` (a non-bool AND nested predicate) reports
  `nested aggregation` where 15.2.3 lists `TypeMismatch{"filter", ..}` first. At an `Agg` node the
  nested check precedes the reducer's dtype rule.
- **`Optimize.release` = `Opt.head(p, None)` only** (15.2.8). The task's "filter merge only for total
  row-wise predicates" is implemented in `Plan.optimize_full` as a whole-plan guard: `Opt.merge`
  (unchanged, so its four laws stand) runs only when every Filter predicate is total and local
  (`Opt.fsafe`); a plan with one fallible or reducing predicate gets no merging at all. `Opt.push`
  moves only total, local conjuncts, never across a fallible / reducing Filter, and only through
  Select/WithColumns certified by `Ana.rowwise_select` / `Ana.rowwise_with`. `Plan.optimize` is gone
  (tests/plan_optimize.bend now exercises `Plan.optimize_full` / `Lazy.collect_full`).
- **Use counting** is done on the compiled code: `Exec.mark` flags each `ISource{name, schema, last}`
  that is the last use of its name in postfix order; earlier uses `Env.clone` (new `C.Frame.clone`,
  added to column.bend), the last `Env.take`s. Equivalent to 15.7's `remaining` counter.
- **`Exec.validate`** walks the same compiled code (postfix order) instead of `Plan.sources`
  (`Plan.sources` exists as 15.7 names it). The duplicate reported is `C.Names.dup` over the env's
  names in env order (newest frame first, since `Env.add` prepends). `Exec.run` itself validates, so
  `collect_raw` (= `Exec.run`) and `collect_full` report binding errors exactly like `collect`.
- **LAW `filter_keeps_schema`** is restated over the analysis: hypothesis `A.Ana.type(e, s) ==
  Done{bool}`, and the `is_agg(e) == False` hypothesis is dropped (reductions are accepted). The
  head-pass and merge proofs were updated for the restricted `Opt.head` and the analysis-typed
  `Plan.schema.filter`; still 48 laws.
- The example and README show `DF.optimize_full` for the projection-pushdown illustration, since
  `DF.optimize` (release) no longer pushes projections. The bench (`Lazy.collect`) therefore runs
  without predicate/projection pushdown; its cost is to be measured (plan section 6).

### M1 B02 (CSV: csvparse, quotedness, physical lines, scan prefix)

- `src/csvparse.bend` is the hub parser's walk with two more loop arguments (the physical line counter and
  the line the current record started on) and two result types: `CsvCell{text, quoted}` and
  `CsvRec{line, cells}`. The hub import is gone (no network fetch at check time); the file keeps the
  hub package's MIT notice (copyright holder: nohzafk). The hub package's proofs do not cover the fork.
- Behaviour fixed (rows B02-a, b, c, f, h; B02-d, g, i, j, k pass and stay as tests; B02-e is now a
  facade test): quoted `""` is the empty string, unquoted empty is null, both on read and (via
  `Csv.quote`: an empty string is quoted) on write; blank lines count as physical lines; a short or
  long record, and a bad cell, report the record's first physical line (a `lines` list, one `U32` per
  data record, is built next to the columns and read only when an error text is built).
- `Csv.infer` (used by `scan_csv`) now applies the reader's shape checks to its text: blank lines are
  skipped for k > 1 columns, a ragged record in the prefix is the reader's `ParseError`. Before, a blank
  line made the inferred schema short, and collect failed with `csv schema: 1 dtypes for 2 columns`.
- Inference departure from the old code: a column whose cells are all empty after trimming, but with
  some unquoted non-empty whitespace (`" "`), is `str` (it used to be `u32` of nulls). Under an
  explicit schema a blank numeric cell is a null (it used to be a `ParseError`), as 15.6.1 says.
- `Csv.render_with(f, w: CsvWriteOpts)` replaces `render_with(f, prec, sep)`; `Csv.render(f, prec)` and
  `Csv.write(f, path)` keep their signatures. `Csv.write_with(f, path, w)`, `Csv.write_default()`,
  `CsvWriteOpts`, `Csv.scan_fields(path, opts)` and `Csv.scan_fields_with(path, opts, chunk)` are new.
- scan prefix (15.6.4): `Csv.scan_fields` reads 64 KiB chunks with `File.read_at` (bytes: `File.read`
  decodes a chunk and mangles a UTF-8 sequence cut at its end), cuts every chunk at its last LF, counts
  line ends outside quotes on the bytes (a `"` toggles the quote state, a doubled quote toggles it
  twice), stops at the `infer_rows + 1`-th such line end and decodes only the text up to it with an own
  UTF-8 decoder (`Csv.u8`; a malformed byte becomes U+FFFD). A line longer than the chunk doubles the
  chunk. The loop is bounded by a fuel of file size + 2 and ends at the first finished state. Quote
  parity on bytes ignores the reader's grammar: a stray quote inside a bare field (a malformed file)
  can flip it, and then the prefix may end early or late; the parse of the prefix reports the
  malformedness only if it is inside the prefix. `Lazy.scan_csv` (plan.bend) is now a 4-line wrapper
  over `Csv.scan_fields`.
- The reader still reads the whole file with one `File.read` and parses a `String` (the 1 MiB chunked
  reader is M4); `csvparse.bend`'s walk is tail recursive over explicit state so it can be resumed.
- Measured natively (bench/data/sales_100000.csv, `build/bench ... parse`, 5 runs each): `Csv.read`
  median 295 ms before, 327 ms after (+11%): an extra `CsvCell` / `CsvRec` node per field / record, the
  per-record `lines` list, the per-column `has_value` trim.

### M1 B02 review (CSV diff review: scan prefix, prefix decoder, writer quoting)

- scan prefix (15.6.4): the prefix counts only line ends outside quotes that END A NON-BLANK LINE
  (a line holding a byte other than CR / LF); the contract text says "line ends outside quotes".
  Counting blank lines left fewer than `infer_rows` data records in the prefix (the reader skips blank
  lines for k > 1 columns), so `scan_csv` froze another schema than `read_csv` infers (G4): for
  `a,b / 1,2 / blank x3 / x,y` and `infer_rows = 2` the scan froze u32 and collect failed with a
  ParseError on a file `read_csv` reads as str. A 1-column file (blank line = null record) now reads a
  little further than needed; the inference still takes the first `infer_rows` records, as the read does.
- The prefix decoder (`Csv.u8`) now follows the runtime's `File.read` decoder (`io_str`) byte for byte:
  a byte that breaks a sequence makes U+FFFD and is read again (it used to be swallowed, so in a
  Latin-1 file `caf\xe9,1` lost its `,` and the scan reported a ragged row the read does not see);
  leads are C2..F4 with the narrowed second-byte ranges after E0 / ED / F0 / F4 (overlongs and
  surrogates are U+FFFD, they used to decode); a sequence cut by the end of the text is U+FFFD.
  `tests/csv_scan_edge.bend` compares both decoders on a malformed-UTF-8 fixture.
- Writer (15.6.1 / 15.6.2 / 15.6.5): a number or bool cell that holds the separator is quoted like a
  str cell (`sep = '.'` writes `"1.5"`, `'-'` writes `"-4"`, `'e'` writes `"true"`); it used to be bare,
  so such a frame did not read back, against the 15.6.5 round-trip claim. Polars 2.0.0 writes these
  bare (and cannot read them back either); text equality with Polars is not part of the contract.
  No cost measurable on the 100k-row sales render (about 1.15 s both ways, native).
- Not changed (notes): a (0, 0) frame writes `"\n"` (Polars too), which reads back as one column named
  `""` with 0 rows; a leading blank line before the header makes a 1-column header `[""]` (Polars skips
  leading blank lines); `CsvOpts.sep` is not validated (`'"'`, CR or LF as separator give unreadable
  output); a lone CR at the very end of the input is dropped as a line end (elsewhere a lone CR is
  content); `read_csv_schema` of an empty file is `(0, 0)` without the dtype-count check.
  (Resolved in M1 B04-i / B02 leftovers below, except the (0, 0) write and the lone CR, which stay.)

### M1 B04-i (row cap) and B02 leftovers

1. **Row cap** (15.8): `K.Kernel.max_rows() = 8388608`, `K.Kernel.check_rows(n) -> Maybe<&2, E.Err>`
   and `K.Kernel.check_rows.cap(cap, n)` (the same guard with the cap as a parameter, the entry the
   tests use with a lowered cap; the text then names that cap). `src/kernels.bend` gained one
   `import ./err.bend as E` line at the top (imports must precede defs) and an appended section.
   `Kernel.depth_for` is unchanged (it loops to 32; the contract's "capped at 23" is not
   implemented, the guards make it moot). Paths guarded: `Column.from_scalars` (before the dtype
   check and any array, so an over-cap list with a misfit reports the cap: `C.Column.from_scalars.cap`), `Csv.rows` (number of data records after
   blank-line skipping and the shape checks, so a ragged or bad-dtype-count file reports that error
   first; `Csv.rows.cap`, `Csv.parse_with.cap`; every read, `read_with` and the `scan_csv` collect go
   through it), `Join.run` (`Join.fill.a`, from the `Tot` count of the CSR match counts, before
   `perm_l / perm_r / valid_r`; inner and left; `Tot.sat`), `GroupBy.run` (`GroupBy.run.h`: the
   input height, which bounds `ng`; ordered after `Grp.validate`'s static errors, before any key is
   evaluated). **D:** the join total saturates at 2^32 - 1 instead of wrapping (a 65536 x 65536 join
   would otherwise read 0 rows and pass), so such an error shows `4294967295` rather than the true
   count (it does not fit a U32). `Concat` does not exist yet: its cases are
   `tests/regress/pending/B04_i_concat_cap.bend.txt` (M3 must use `check_rows` over a saturating
   sum). No `DF.max_rows` was added to `frame.bend` (the contract exposes it only in `Kernel`).
2. **`CsvOpts.sep` / `CsvWriteOpts.sep`**: `"`, CR and LF are refused with
   `InvalidOperation{"csv: separator must not be a double quote, CR or LF"}` (`Csv.sep_err`) by
   `Csv.parse_with`, `Csv.read_with` (so `read`, `read_csv*`, `scan_csv_schema`'s collect; before the
   file is opened, review fix below), `Csv.infer`, `Csv.scan_fields_with` (before the file is opened) and the facade `write_csv_opts` (before the file
   is touched). The src-level `Csv.write_with` also refuses, with an `IoError 22` value (its result
   type has no `Err` channel), and the pure `Csv.render_with` is unguarded (it has no error channel).
   The contract said "any single char"; this narrows it (a `"` separator is ambiguous with quoting, CR
   and LF with line ends). Other chars, including non-ASCII, are unchanged.
3. **Leading blank lines**: with `has_header = True{}` the blank records before the header are
   skipped (`Csv.lead`), for read, infer and scan alike; physical line numbers of the later records
   are unchanged; a file of blank lines only is then the empty file. Without a header they stay data.
   Polars 2.0.0 does the same (checked). Without a header the column count is the first NON-blank
   record's (`Csv.width`; 1 when every record is blank), so `\n1,2\n3,4\n` is 2 columns whose
   leading blank line is skipped like any blank line in k > 1 columns (Polars: an all-null row, the
   15.6.2 departure); review fix below.
4. **`read_csv_schema` on an empty file** (or only blank lines with a header): `Csv.rows.none` runs
   the dtype-count check against 0 columns, so d > 0 dtypes is `"csv schema: d dtypes for 0 columns"`
   and `[]` still gives the `(0, 0)` frame. `tests/csv_edge.bend` "schema count empty" changed to the
   error.
5. **Kept and documented** (README, 15.6.2): writing a `(0, 0)` frame gives `"\n"`, which reads back as
   one column named `""` with 0 rows (Polars writes the same); a lone CR at the very end of the input
   is dropped as a line end (elsewhere a lone CR is content).
6. Tests: `tests/regress/B04_i_row_cap.bend` (spec `B04_i_row_cap` in `bench/contract/regress_expect.py`),
   `tests/regress/B02_m_sep_lead_blank_empty_schema.bend` (spec of the same name),
   `tests/regress/pending/B04_i_concat_cap.bend.txt` (spec `B04_i_concat_cap`).
7. **Review fixes** (diff review of b4eda5e): (a) `has_header = False{}` took the column count from
   the first record even when it was blank, so `\n1,2\n3,4\n` was one column and a
   `ParseError at line 2: expected 1 fields, got 2` (read, infer and scan alike); now `Csv.width`.
   (b) `Csv.read_with` opened and read the whole file before `Csv.parse_with` refused the separator,
   so a missing file with a bad separator was an `IoError` on read (and on a `scan_csv_schema`
   collect) but an `InvalidOperation` on `scan_csv`; it now refuses before opening. Cases added to
   `tests/regress/B02_m_sep_lead_blank_empty_schema.bend` (`nohdr-*`, `sep-read-*missing-file`).
   Audited and found complete for the code that exists: every path that sizes a frame or column
   from something other than an existing frame's height (`from_scalars`, `Csv.rows`, the join
   total) is guarded; eval broadcasts (`Eval.const_col`), filter/compact, sort and slice gathers,
   head, with_columns, the CSV prefix inference (no columns), `Frame.clone`, exec source cloning
   and dump are bounded by an input height. The CSV record count goes through
   `U32.from_nat(List.length ..)`, which could only wrap past 2^32 records (a file `File.read`
   cannot hold).

### M1 diff fixes (NEW-1 static checks first, NEW-2 interpreter stack)

1. **NEW-1: every eager verb checks statically before it evaluates** (15.9 "order of errors").
   `Eval.static` (select and with_columns: the analysis, then the duplicate output name;
   with_columns already did this, select found duplicates only in `Frame.from_columns` after
   evaluating); `Grp.static` (group_by: `Grp.validate`, then `DuplicateColumn` over keys then aggs,
   then the row cap, which used to come before the duplicate check); `Sort.miss` (sort: the first
   missing key in list order; `Sort.argsort` walks the keys last first and used to report the last
   missing one). `Grp.validate`, `Plan.sort.miss` and `Plan.schema` are unchanged (the proofs use
   them); the eager checks are new defs with the same rules. Filter and join were already
   static-first (`Join.run` calls `Join.schema` before any work, so a `_right` clash is
   `DuplicateColumn` before the row cap); head has no static check.
2. **15.9 admissibility rule** (new): eager-vs-lazy error agreement is required for single-verb
   programs and for multi-verb programs whose eager run reaches the first statically invalid verb
   without a data error; the rest are inadmissible for T2.1 (the generator already counted them
   apart). This narrows G2 as written ("errors too") for multi-verb programs.
3. **NEW-2: no per-row non-tail recursion on the result path.** The interpreter is the JS lane,
   which runs every non-tail call on the host stack; ~2^15 nested calls overflow it ("memory fault
   (machine stack overflow?)"), a cons-guarded recursion (`f(h) <> go(t)`) included, as do Base's
   `List.length`, `String.concat`, `List.replicate` and `String.append` (`++`) over its LEFT operand.
   Changed: `Dump.cell_list` (tail call into a reversed list, then `List.reverse`), the row lines
   (`Dump.cat` joins the newest-first lines with `line ++ acc`, replacing `String.concat` plus a final
   `++` whose left operand was the whole body), `Column.fs.words/f32s/strs/vwords` (reversed tail
   calls), `K.Kernel.count` (a tail-recursive list length) in `Kernel.from_list` and
   `Column.from_scalars.cap`. Checked in the interpreter: a 202,800-row x 5-column self join
   (eager, raw and optimised lazy) dumps (8.46M chars) in ~1.5 s each; a 448 x 448 self join
   (200,704 rows) dumps fully; `from_scalars` of 200,000 scalars; group_by, sort, filter, select,
   with_columns and `Fmt.show` over the 202,800-row frame.
4. **Still open (NEW-2 class, interpreter only)**: `Csv.read` of `bench/data/sales_100000.csv`
   (already before this change) and `Csv.render` / `write_csv` of a ~2^15-row frame overflow in the
   interpreter (`Csv.cells`, `Csv.zip`, `Csv.zip_pre`, `List.replicate`, `String.concat` in
   `Csv.render.t`, `List.length` over records in `Csv.rows`, ...); native runs are fine.
5. Tests: `tests/regress/NEW_1_static_checks_first.bend`, `tests/regress/NEW_2_interp_large_results.bend`
   (specs of the same names in `bench/contract/regress_expect.py`; NEW-2's expected dump summaries
   are computed there from a plain-Python join); `tests/diff/d0001.bend`, `d0002.bend` lost
   `#! xfail NEW-1`.

### M1 B03 (numerics: 15.5, rows B03-a..q)

1. **NaN cells dump as `0x7fc00000`** (`Dump.fbits`), whatever their sign and payload. 15.1
   rule 3 said "NaN prints the stored bits" and left NaN equality to the comparator; but NaN bits
   are not portable (arm64 makes `0x7fc00000` for `0/0` and `inf - inf`, x86-64 makes
   `0xffc00000`, and payloads propagate: `-NaN + 1` keeps `0xffc00000`), so the same program
   printed different dumps on the two CI machines. Canonicalising in the dump makes every test
   expectation portable; `bench/check.py --dump` still treats any two NaN cells as equal, so a
   Polars-side dump with another payload still compares. Values are unchanged (only the text).
2. **str -> f32 cast refuses leading whitespace**: Base `F32.read` skips it (`" 3"` reads as 3),
   which would trim on one side only; `Eval.read_f32` answers None for a cell starting with
   space / TAB / CR / LF, so 15.5.5's "as is, no trimming" (Polars) holds. `U32.read`/`I32.read`
   already refuse it.
3. **Where the policy lives**: `K.Kernel.fword` (the 15.5.2 order word; `Sort.fword` now calls it),
   `K.Kernel.fmin/fmax` (15.5.2 exceptions), `K.Kernel.nm.add/nm.result` and the Data type
   `K.NS{s, c}` (15.5.3 step), `K.Kernel.fsum` (Neumaier, used by eager Sum/Mean and describe),
   `Grp.nm` (the same step per group, sum and mean), `K.Kernel.first_drop`, `K.Kernel.zip_maybe`.
   Eager f32 `n_unique` counts distinct `fword`s (as group_by's codes do: B03-k).
4. **Strict cast** = `Eval.try_cast` of a clone, then null counts compared: equal means no valid
   cell failed (a conversion only adds nulls); otherwise the error row is the first row valid in
   the source and null in the result (`K.Kernel.first_drop`), the cell read from the source by
   `Column.data_cell` and shown by `Expr.show.lit`. Total pairs (`X.Cast.total`, in expr.bend for
   the analysis) skip the clone. `Eval.cast` is strict for every caller, including `Fmt.describe`'s
   numeric -> f32 cast (total).
5. **Integers**: `D.I32.floor_div` / `D.I32.floor_mod` -> `Maybe` (None = null) are the evaluator's
   `//` and `%`; `D.I32.div` / `D.I32.mod` stay the truncating helpers (`tests/i32.bend`). The u32 /
   i32 `Bin{Div}` kernels remain in `Eval.zip.u/i` only as unreachable cases (typing refuses).
6. **lit_i32** follows 15.2.1 D: (`Cast{Lit{SU32{v}}, TI32}` above range, `Un{Neg, ..}` of it for
   `lit_i32_neg`). `DF.i32`, `DF.i32_neg`, `D.I32.checked`, `D.I32.checked_neg`, `D.I32.from_bits`
   (`from_u32` kept as an alias) exist; `src/dtype.bend` now imports `src/err.bend`. `DF.lit_null`
   and `DF.try_cast`, `DF.floor_div` added.
7. **Goldens**: `bench/golden.py` writes q3 from `q3_reference` (exact rational sum of each group's
   f32 inputs rounded once to f32, ties to even; mean = that f32 / f32(count) in f32), not from
   Polars; the other queries stay Polars'. `bench/golden/q3.csv` `inland` 96373.4141 -> 96373.4062;
   `bench/golden/n1000/q3.csv` 5 of 8 `revenue_sum` cells move by 1-2 ulp. Bend matches the
   reference exactly at 1k and 100k (`make bench-check`: q3 identical). `--rtol` in
   scripts/bench.sh is unchanged (still needed by q6 at 100k). This reverses M5 (describe,
   goldens) note 2, as 15.5.3 says.
8. **Laws**: `Laws.is_arith` no longer contains `Div` (`arith_type` now covers `+ - *`: `/` is
   f32-only); PROOF.bend gains the `FloorDiv` cases. Still 48 laws, all proved.
9. **Not done here**: `AggOp` Std/Var/Median (15.2.5) are left to M3 (eager + grouped kernels,
   sort-based median per group). B03-b/h/k/n regressions now carry `#! xfail B04-a`: their eager
   and grouped runs pass, the lazy `select` of a reduction still needs B04-a. B04-j's eager and
   raw-lazy runs now match the contract; only the optimised runs differ (barrier rules, B04-j).

### T2.3 (F32 reductions against an exact reference; bench/diff/reduce.py)

1. **Result of 2 x 2000 generated cases (about 1.1M input rows each)**: sum and mean (eager `select`,
   eager and lazy `group_by`) and describe's mean/std equal the 15.5.3/15.5.4 step model bit for bit and lie
   within the derived error bound (bench/diff/README.md, "T2.3"); no numerical defect.
2. **15.5.4's "verified" `std [1,2,4] = 1.5275252`, `var = 2.3333333` are the correctly rounded values**;
   the specified algorithm and Bend give 1.5275253 / 2.3333335 (1 ulp above, inside the bound). The text
   of 15.5.4 is left as is; r0006 pins the algorithm's value.
3. **describe's min and max are not the 15.5.2 min/max** (open, `#! xfail NEW-T23-1`, `NEW-T23-2`):
   `describe` of `[NaN, 1, 2]` answers max `NaN` (min/max and Polars 2.0.0 skip NaN: 2), and of
   `[0.0, -0.0]` answers min `0.0` (the first tied row; min/max and Polars: `-0.0`). Cause: describe reads
   its extremes off the stable NaN-greatest sort. `std` of a constant column is not 0 (see IMPLEMENTING.md).
4. `Std/Var/Median` AggOps do not exist yet; the checks for them are in `reduce_ref.py`/`reduce.py` and
   switch on when `frame.bend` defines `DF.std`, `DF.var`, `DF.median`. describe's "50%" is the nearest
   rank, not the 15.5.4 median for even counts (checked as the nearest rank).

## 15. v0.1 contract (frozen)

The exact semantics every M1-M6 agent codes and tests against. Tables over prose;
"Polars" means Polars 2.0.0 as pinned in `bench/` (snippets recorded where a row is
not obvious). Where the plan (`plans/M_01.txt` section 2) left a choice open, the
decision and its one-line reason are marked **D:**. Deviations found while
implementing go to section 14, never silently into code.

Conventions used below. `ResT(Frame)` is `E.ResT(C.Frame)`; `Res(X)` is `E.Res(X)`.
Error rows name the constructor and the exact `what`/`op`/`want`/`got` strings;
`Err.show` renders them as in `src/err.bend`. "h" is the input height. "Eager" means a
`Frame -> ResT(Frame)` facade def over `src/`; "lazy" means a `Plan` node with a
`Plan.schema` rule, an `Exec` rule and an `explain` line. A verb listed as both has one
data semantics; the eager def and the lazy node call the same `src` function.

### 15.1 DF.dump: the typed oracle text (T1)

`DF.dump(r: ResT(Frame)) -> String` (facade, consumes `r`) over `Fmt.dump(f: Frame)
-> Frame & String` (src/fmt.bend, hands the frame back like `Fmt.show`). All
differential tests (T2) compare dumps, never CSV or `Fmt.show` text.

Grammar (lines end in `\n`; fields inside a line are separated by one TAB, `\t`;
no trailing whitespace; the final line also ends in `\n`):

```
dump     := frame | error
error    := "error" TAB errtext NL                 -- errtext = E.Err.show(e), verbatim
frame    := "frame" NL
            "height" TAB u32 NL                    -- Frame.height
            "width" TAB u32 NL                     -- number of columns
            col*                                   -- one per column, frame order
            row*                                   -- one per row, row order; none when width = 0
col      := "col" TAB dtype TAB qstr NL            -- dtype = D.DType.show: bool u32 i32 f32 str
row      := "row" (TAB cell){width} NL
cell     := "null" | "true" | "false" | u32 | i32 | f32bits | qstr
u32      := U32.show                               -- decimal, no sign, no padding
i32      := I32.show                               -- decimal, "-" when negative
f32bits  := "0x" hex{8}                            -- F32.bits(x), lowercase, zero-padded
qstr     := '"' ( esc | any code point except '"' '\' and U+0000..U+001F, U+007F )* '"'
esc      := '\"' | '\\' | '\n' | '\r' | '\t' | '\x' hex{2}   -- \xHH for the other C0 controls and U+007F
```

Rules:

| # | Rule |
|---|------|
| 1 | A null cell prints `null` whatever the dtype. Validity is observable only through `null`; the slot value under a null is never printed (slot invariant: it is `DType.default`). |
| 2 | A valid Str cell always prints quoted, so the empty string is `""` and is distinct from `null`. Names are quoted the same way (a name may contain TAB, quote or newline). |
| 3 | F32 prints its exact bit pattern: `1.0` is `0x3f800000`, `-0.0` is `0x80000000`, `0.0` is `0x00000000`, `+inf` `0x7f800000`, `-inf` `0xff800000`. NaN prints the stored bits. **D:** the comparator (bench/check.py and tests) treats any two NaN cells as equal; NaN payload is outside the contract (15.4) and differs between the interpreter and the native backend. Everything else is byte-exact, including `-0.0` vs `0.0`. |
| 4 | Bool prints `true`/`false`; U32 and I32 print as `Scalar.show` does (decimal). |
| 5 | `width 0` prints no `row` lines; the height is still `height h` (so eager `select([])` and a lazy `Select{[]}` are told apart by this line, B01-c). |
| 6 | Row lines carry exactly `width` cells; a dump is parsed with `line.split("\t")` after stripping the trailing `\n`; the only TABs are separators, because TAB inside a string is escaped. |
| 7 | `error` dumps carry `Err.show` text verbatim (it contains no newline: every `what` string is single-line by construction, 15.9). Eager/raw-lazy/optimised-lazy agreement (G2) is "equal dump text", for errors too (eager vs lazy: for the admissible programs of 15.9). |
| 8 | The comparator is itself tested with intentional mismatches (T1): a changed cell, a changed name, a changed dtype, a changed height, `""` vs `null`, `0x80000000` vs `0x00000000`, and two different NaN payloads (must compare equal). |

Example (3 rows, u32/f32/str; second row has two nulls, third string holds a TAB):

```
frame
height	3
width	3
col	u32	"id"
col	f32	"x"
col	str	"s"
row	1	0x3f800000	""
row	2	null	null
row	3	0x80000000	"a\tb"
```

Implementation notes for T1: `F32.bits` exists (used by `Sort.fword`, `Fmt.fixed`);
Base has no hex printer, so `Fmt.hex8(w: U32) -> String` is written in fmt.bend
(8 nibbles, MSB first, `0123456789abcdef`). `Fmt.dump` walks `Column.to_scalars`
per column and transposes to rows, or reads `Column.cell` row by row; either is
fine for tests (dumps are for frames of at most a few thousand rows).

### 15.2 API table (G4: every verb eager and lazy, one data semantics)

Legend. **Facade** is the `DF.` name in `frame.bend`; **src** is `module.Def` the
facade wraps; **E/L**: eager def / lazy Plan node (`lazy_<verb>` builds the node;
`Exec` runs the same src def). "Row order" is the output order. Errors are listed in
the order they are detected; `collect_schema` reports exactly the rows marked
*static*; data-dependent rows are *runtime* (15.7 says which `collect` adds).
Names of new Plan nodes and Expr nodes are normative; helper names inside src are
suggestions in the existing style.

Nullability, schema and order rules shared by every verb: no implicit coercion;
output names are `Expr.name` (15.3); a repeated output name is
`DuplicateColumn{name}` (first repeated name in output order) after type errors;
`maintain_order=False{}` is accepted and ignored (output is first-appearance /
left-row order anyway).

#### 15.2.1 Construction and results

| Facade (new unless marked) | src | Semantics | Errors |
|---|---|---|---|
| `DF.column(t: D.DType, xs: List<&2, D.Scalar>) -> ResT(Column)` | `C.Column.from_scalars(xs, t)` | checked nullable column; `SNull` is a null row | `TypeMismatch{"from_scalars", <t>, <scalar dtype or "null">}` on the first misfit; row cap 15.8 |
| `DF.t_bool() .. DF.t_str() -> D.DType`; `DF.s_null() / s_bool(b) / s_u32(v) / s_i32(i: D.I32) / s_f32(x) / s_str(s) -> D.Scalar` | constructors | dtype and scalar builders without a `src/` import | none |
| `DF.i32(v: U32) -> Res(D.I32)`, `DF.i32_neg(v: U32) -> Res(D.I32)` | `D.I32.checked(v)`, `D.I32.checked_neg(v)` | `v < 2^31` (`v <= 2^31` for neg) else error; `D.I32.from_bits(w)` is the explicit, unchecked reinterpretation (renamed from `I32.from_u32`, kept as an alias) | `InvalidOperation{"i32 out of range: <v>"}` |
| `DF.lit_i32(v: U32)` (exists), `DF.lit_i32_neg(v: U32)` (exists) `-> Expr` | `X.Lit{D.SI32{..}}` | **D:** stay total builders: for `v < 2^31` (`<= 2^31` neg) the literal; otherwise the expression `X.Cast{X.Lit{D.SU32{v}}, D.TI32{}}` (resp. its `Neg`), a strict cast that fails loudly when evaluated and is marked fallible by the analysis. Reason: a `Res`-returning literal cannot be nested inside an expression tree; the plan's goal (no silent wrap) holds. Deviation from plan 2.2d wording, recorded in 14 by M1. | runtime `InvalidOperation{"cast u32 to i32: row 0 holds <v>"}` |
| `DF.lit_null(t: D.DType) -> Expr` | `X.Cast{X.Lit{D.SNull{}}, t}` | the typed null literal (exists as an idiom; now named) | none |
| `DF.clone(f) -> Frame & Frame` | `C.Frame.clone` | O(n) deep copy, same order | none |
| `DF.schema(f) -> Frame & Schema`, `DF.height(f) -> Frame & U32` | `S.Frame.schema`, `C.Frame.height` | | none |
| `DF.then(r: ResT(Frame), k: Frame -> ResT(Frame)) -> ResT(Frame)` | facade | and_then: `Fail` passes through | |
| `DF.then_io(r: ResT(Frame), k: Frame -> IO(ResT(Frame))) -> IO(ResT(Frame))` | facade | and_then into IO (`write_csv`, `collect` chains) | |
| `DF.collect_show(p: Plan, env: Env) -> IO(String)` | `Q.Lazy.collect` + `DF.show` | the "DF.show for a Plan" of 2.1: collect, then the table or `error: ..` | as collect |
| `DF.dump(r: ResT(Frame)) -> String` | `F.Fmt.dump` | 15.1 | none |

#### 15.2.2 Sources and environments (B04, 15.7)

| Facade | src | Semantics | Errors |
|---|---|---|---|
| `DF.empty_env()` (exists), `DF.source(name, f) -> Env & Plan` (exists) | `P.Env.empty`, `P.Lazy.source` | | |
| `DF.add_source(env, name, f) -> Env & Plan` | `P.Env.add` | several named frames in one Env; the Plan is `Source{name, Frame.schema(f)}` | none here (duplicates reported by validate_bindings / collect) |
| `DF.validate_bindings(p: Plan, env: Env) -> Env & Res(Unit)` | `Q.Exec.validate(p, env)` | checks every `Source` of `p` against `env`: present, bound once, same schema; hands `env` back untouched | *static*: `InvalidOperation{"source not in env: <name>"}`, `InvalidOperation{"source bound twice in env: <name>"}`, `InvalidOperation{"source <name>: data schema [<env>] differs from the plan's [<plan>]"}` (first offending Source in plan postfix order) |
| `DF.collect(p, env)` (exists) | `Q.Lazy.collect` = `Exec.run(Optimize.release(p), env)` | validate_bindings first (its error wins over nothing else: `Plan.schema` errors come first, then bindings, then execution); a Source used k times clones k-1 times (15.7) | as above plus runtime errors |
| `DF.collect_raw(p, env)`, `DF.collect_full(p, env) -> IO(ResT(Frame))` | `Q.Exec.run(p, env)`, `Q.Exec.run(P.Plan.optimize_full(p), env)` | unoptimised / fully optimised execution (T2.1 compares the three) | same |

#### 15.2.3 Selection

| Verb | E/L: facade, node | Output schema | Null rule | Errors (static) | Order |
|---|---|---|---|---|---|
| select (exists) | `DF.select(f, es)`; `Select{exprs, input}` | fields `(Expr.name e_i, dtype e_i)` in list order; height by 15.4 | per expression | per expr in list order: typing (15.3), `nested aggregation` ; then `DuplicateColumn`; `select([])` is `(0, 0)` in both APIs | input order |
| with_columns (exists) | `DF.with_columns(f, es)`; `WithColumns{exprs, input}` | input fields, each output replacing the same-named field in place (dtype may change) or appended in list order; height = h always (scalars and reductions broadcast; on h = 0 they are empty columns) | per expression | typing in list order, `nested aggregation`, then `DuplicateColumn` among the OUTPUT names (`[lit 1 as x, lit 2 as x]`) | input order |
| filter (exists) | `DF.filter(f, pred)`; `Filter{pred, input}` | input schema | a null predicate row is dropped (Kleene) | pred typing, then `TypeMismatch{"filter", "bool", <got>}`, then `nested aggregation`; reductions inside `pred` are computed over the whole input (15.4) | input order, stable |
| head (exists) | `DF.head(f, n)`; `Head{n, input}` | input | | none | first `min(n, h)` rows |
| sort (exists) | `DF.sort(f, keys)`; `Sort{keys, input}` | input | nulls first unless `nulls_last`, independent of `descending`; among themselves nulls keep input order | `ColumnNotFound` for the first missing key; `sort(f, [])` is the identity | by keys, stable; F32 by the 15.5 order; Str by code points; Bool false < true |
| drop | `DF.drop(f, names)`; `Drop{names, input}` | input minus `names`, order kept; dropping every column keeps the height (`(h, 0)`, Polars) | | `ColumnNotFound{n}` for the first name not present (list order); a name repeated in `names` is allowed (Polars) | input |
| rename | `DF.rename(f, pairs: List<&2, String & String>)`; `Rename{pairs, input}` (`pairs` are `(from, to)`) | simultaneous: every `from` becomes its `to`, positions unchanged; swaps allowed; `(a, a)` allowed | | `ColumnNotFound{from}` (first missing, list order); `DuplicateColumn{from}` when a `from` repeats in `pairs`; `DuplicateColumn{name}` for the first repeated OUTPUT name in frame order (collision with an unrenamed column or two `to`s equal) | input |
| slice | `DF.slice(f, offset: U32, len: U32)`; `Slice{offset, len, input}` | input | | none; rows `[min(offset, h), min(offset, h) + min(len, h - min(offset, h)))`, i.e. `start = U32.min(offset, h)`, `count = U32.min(len, U32.sub(h, start))`: no overflow possible (U32 only, no negative offsets: **D** Polars' negative offsets are not offered) | input |
| tail | `DF.tail(f, n)`; `Tail{n, input}` | input | | none; `= slice(h - min(n, h), min(n, h))` | input |

#### 15.2.4 Combination and distinct

| Verb | E/L | Output schema | Row rule | Errors (static, in order) | Order |
|---|---|---|---|---|---|
| inner / left join (exist) | `DF.inner_join / left_join(l, r, left_on, right_on)`; `Join{how, left_on, right_on, left, right}` | left fields, then right fields minus `right_on`, a right name equal to ANY left name gets `_right` | keys compare by the 15.5 relation; null keys never match; left: unmatched left rows get null right columns | `InvalidOperation{"join: no key columns"}`, `InvalidOperation{"join: left_on and right_on must have the same length"}`, per pair `ColumnNotFound{left}` / `ColumnNotFound{right}` / `TypeMismatch{"join", <l>, <r>}` (no coercion), `DuplicateColumn`; row cap 15.8 (runtime) | left row order; a left row's matches in right row order |
| semi join | `DF.semi_join(l, r, left_on, right_on)`; `Join{J.Semi{}, ..}` | left fields only (no right columns, hence no `_right`, no right-side `DuplicateColumn`) | each left row at most once, kept iff some right row has equal (non-null) keys | the key errors above (same checks, same texts) | left row order |
| anti join | `DF.anti_join(..)`; `Join{J.Anti{}, ..}` | left fields only | kept iff no right row matches; a left row with a null key is KEPT (it matches nothing, Polars) | same | left row order |
| concat_vertical | `DF.concat_vertical(fs: List<&1, Frame>)`; `Concat{inputs: List<&2, Plan>}` | input 0's schema | all rows of input 0, then input 1, ... ; zero-column inputs concatenate heights (`(h1 + h2, 0)`) | `InvalidOperation{"concat_vertical: no inputs"}`; `InvalidOperation{"concat_vertical: input <i> schema [<s_i>] differs from input 0's [<s_0>]"}` (first i, names AND dtypes AND order must be equal; **D** no diagonal/relaxed mode); row cap 15.8 (runtime, sum of heights) | inputs in order |
| unique | `DF.unique(f, subset: List<&2, String>)`; `Unique{subset, input}` | input | keep first: row i is kept iff no earlier row has equal key tuple under the 15.5 relation (nulls equal nulls, as group_by); **D** `subset = []` means every column (Polars `subset=None`); a frame with no columns keeps `min(h, 1)` rows (Polars `(1, 0)`) | `ColumnNotFound{n}` for the first missing subset name; a repeated subset name is allowed (Polars) | input order (stable) |
| group_by (exists) | `DF.group_by(f, keys, aggs)`; `GroupBy{keys, aggs, maintain_order, input}` | key fields (named `Expr.name`), then agg fields | one group per distinct key tuple under the 15.5 relation, null keys form a group | `G.Grp.validate`: key typing, agg typing, `InvalidOperation{"group_by needs at least one key"}`, `InvalidOperation{"group_by key is an aggregation: <show>"}`, `InvalidOperation{"agg expects an aggregation: <show>"}`, `InvalidOperation{"nested aggregation in agg: <show>"}`; then `DuplicateColumn`. Agg shape stays `Alias*(Agg{op, row-wise e})`; `sum(x)/sum(y)` is two named aggs then a `with_columns` (2.1) | first appearance |

#### 15.2.5 Aggregation (reducers) and global reductions

All reducers are `X.Agg{op, e}` with `e` row-wise or scalar; they are allowed at any
depth of a `select` / `with_columns` / `filter` expression (eager AND lazy, 15.4)
and only at the root (under aliases) of a `group_by` agg. A reducer over a reducer
is `InvalidOperation{"nested aggregation: <Expr.show e>"}` (expression context) /
`{"nested aggregation in agg: <show>"}` (group_by). Input dtype `t`.

| op (`AggOp`) | facade | allowed `t` | result dtype | result on 0 valid rows | null/NaN rule |
|---|---|---|---|---|---|
| Sum | `DF.sum` | u32, i32, f32 | `t` | `0` (never null) | nulls skipped; ints wrap mod 2^32; f32 by 15.5.3 (NaN in -> NaN) |
| Mean | `DF.mean` | u32, i32, f32 | f32 | null | nulls skipped; 15.5.3; int inputs converted to f32 first (documented departure: Polars f64) |
| Min / Max | `DF.min / DF.max` | any | `t` | null | nulls skipped; f32: NaN skipped (all-NaN -> NaN), `min` prefers `-0.0`, `max` prefers `0.0` (15.5.2); Str by code points; Bool false < true |
| Count | `DF.count` | any | u32 | `0` | valid rows |
| Len | `DF.len()` | (`Agg{Len, lit 1}`) | u32 | `0` | rows, nulls included |
| First / Last | `DF.first / DF.last` | any | `t` | null | row 0 / row h-1 as is, null included |
| NUnique | `DF.n_unique` | any | u32 | `0` | distinct values under the 15.5 relation (all NaN one value, `-0.0 = 0.0`, both eager and grouped: fixes B03-k), plus one if any null |
| Std, Var (new) | `DF.std / DF.var` | u32, i32, f32 | f32 | null; also null when fewer than 2 valid rows | ddof = 1, 15.5.4; any NaN or inf among the values -> NaN (Polars) |
| Median (new) | `DF.median` | u32, i32, f32 | f32 | null | nulls skipped; 15.5.4 (NaN sorts greatest, as Polars) |

Typing errors: `TypeMismatch{<op name>, "numeric", <t>}` for Sum/Mean/Std/Var/Median
over bool/str (`AggOp.name`: `"std"`, `"var"`, `"median"`). **D:** `sum` over Bool
stays refused (not in 2.1; Polars allows it).

#### 15.2.6 Expressions

| Node (new unless marked) | facade | typing (15.3) | value rule | null rule | fallible |
|---|---|---|---|---|---|
| `Cast{e, to}` (exists; semantics change) | `DF.cast(e, t)`, `cast_f32`, `cast_u32` | `Cast.ok` table (15.3) | 15.5.5: every valid cell converted; first failing cell is an error | null -> null | yes for the fallible pairs of 15.5.5 |
| `TryCast{e, to}` | `DF.try_cast(e, t)` | same table | failing cells become null | null -> null | no |
| `Bin{Div, a, b}` (exists; typing change) | `DF.div` | f32 x f32 -> f32 only: `TypeMismatch{"div", "f32", <left>}` when the left is not f32, else `{"div", "f32", <right>}` | IEEE: `x/0 = ±inf`, `0/0 = NaN` | null -> null | no |
| `Bin{FloorDiv, a, b}` | `DF.floor_div` | u32 x u32 -> u32, i32 x i32 -> i32; `TypeMismatch{"floor_div", "u32 or i32", <left>}` / `{"floor_div", <left>, <right>}` | floor toward -inf (15.5.1) | null when either is null, when `b = 0`, and for i32 `MIN // -1` | no (null, not error) |
| `Bin{Mod, a, b}` (exists; semantics change) | `DF.mod` | u32/i32 same type (unchanged texts: `"mod"`, `"u32 or i32"`) | result has the divisor's sign (15.5.1); `MIN % -1 = 0` | null when either null or `b = 0` | no |
| `Bin{Add/Sub/Mul}` (exist) | | numeric same type | u32 wraps mod 2^32; i32 two's complement wrap; f32 IEEE | null -> null | no |
| comparisons `Eq..Ge` (exist; f32 semantics change) | | same dtype -> bool | 15.5.2 total order for f32 (`NaN == NaN`, `NaN > x`, `-0.0 == 0.0`); Str code points; Bool false < true | null -> null (no Kleene for `==`) | no |
| `And/Or/Not/IsNull/IsNotNull/FillNull/Neg/Abs/Sqrt` (exist) | | as today (`Neg/Abs`: i32 or f32; `Sqrt`: f32) | `abs(MIN) = MIN`, `neg(MIN) = MIN`, `sqrt(x<0) = NaN` | section 5 | no |
| `When{cond, a, b}` | `DF.when(cond, then, otherwise)` | `cond` bool else `TypeMismatch{"when", "bool", <got>}`; `a`, `b` same dtype else `TypeMismatch{"when", <a>, <b>}`; result dtype of `a` | row i = `a_i` where `cond_i` is true, else `b_i` (a null `cond_i` picks `b_i`, Polars) | result null iff the chosen branch is null | no |
| `IsIn{e, vals: List<&2, D.Scalar>}` | `DF.is_in(e, vals)` | every scalar's dtype equals `e`'s else `TypeMismatch{"is_in", <e dtype>, <scalar dtype or "null">}` (an `SNull` in the list is refused) | true iff some `v` equals the cell under the 15.5 relation; `vals = []` -> all false | null -> null | no |
| `Clip{e, lo: D.Scalar, hi: D.Scalar}` | `DF.clip(e, lo, hi)` | `e` numeric else `TypeMismatch{"clip", "numeric", <got>}`; `lo`, `hi` of `e`'s dtype else `TypeMismatch{"clip", <e dtype>, <bound dtype or "null">}` | `lo` if `x < lo`, else `hi` if `x > hi`, else `x`, with IEEE `<`/`>` for f32 so NaN passes through and `-0.0` is not clipped by `0.0`; `lo > hi` therefore gives `lo` for `x < lo` and `hi` otherwise (Polars `clip(8, 2)` of `[1, 5, 10]` = `[8, 8, 2]`) | null -> null | no |
| is_between (sugar, no node) | `DF.is_between(e, lo, hi)` (both closed), `DF.is_between_closed(e, lo, hi, c: X.Closed)` with `X.Closed = Both{} \| Left{} \| Right{} \| Neither{}` and `DF.closed_both() ..` | builds `And{cmp_lo, cmp_hi}` with `Ge/Gt` and `Le/Lt`; typing is the comparisons' (`"ge"`, `"le"`, ..) | `lo > hi` -> all false | Kleene: a null `e` gives null | no |
| `Un{LenChars, e}` | `DF.len_chars(e)` | str -> u32 else `TypeMismatch{"len_chars", "str", <got>}` | code points (`String.length`), `"" -> 0` | null -> null | no |
| `StrPred{op: StrPredOp, e, pat: String}`, `StrPredOp = Contains{} \| StartsWith{} \| EndsWith{}` | `DF.contains_literal(e, pat)`, `DF.starts_with(e, pat)`, `DF.ends_with(e, pat)` | str -> bool else `TypeMismatch{"contains_literal" / "starts_with" / "ends_with", "str", <got>}` | literal, case-sensitive, code-point equality, no normalisation; empty `pat` -> true; **D** the pattern is a literal String, not an Expr | null -> null | no |

`Expr.show` for new nodes (used by `explain` and error texts): `e.try_cast(t)`,
`(a // b)`, `when(c).then(a).otherwise(b)`, `e.is_in([v1, v2])`, `e.clip(lo, hi)`,
`e.str.len_chars()`, `e.str.contains_literal("p")`, `e.str.starts_with("p")`,
`e.str.ends_with("p")`, `e.std()`, `e.var()`, `e.median()`.

#### 15.2.7 IO

| Facade | src | Semantics | Errors |
|---|---|---|---|
| `DF.csv_opts(sep: Char, has_header: Bool, infer_rows: U32) -> R.CsvOpts` | constructor | `Csv.default() = CsvOpts{',', True{}, 100}`; `infer_rows = 0` means every row | |
| `DF.read_csv(path)` (exists), `DF.read_csv_opts(path, opts)`, `DF.read_csv_schema(path, opts, dtypes: List<&2, D.DType>) -> IO(ResT(Frame))` | `R.Csv.read`, `R.Csv.read_with` | whole file read once; 15.6 | `IoError{code, text}`; `ParseError{0, "malformed csv"}`; `ParseError{line, "expected <k> fields, got <g>"}`; `InvalidOperation{"csv schema: <d> dtypes for <k> columns"}`; `ParseError{line, "column <name>: cannot parse \"<text>\" as <dtype>"}`; row cap |
| `DF.scan_csv(path)` (exists), `DF.scan_csv_opts(path, opts) -> IO(Res(Plan))` | `P.Lazy.scan_csv` | reads a bounded prefix (15.6.4) to infer `ScanCsv.schema`; collect reads the whole file once, strictly, with the frozen schema | as read, plus at collect `InvalidOperation{"scan_csv <path>: data schema [<file>] differs from the plan's [<plan>]"}` |
| `DF.scan_csv_schema(path, opts, schema: Schema) -> Plan` | `P.ScanCsv{path, opts, schema}` | pure: no IO at plan time; the header must match `schema`'s names at collect | the frozen-schema error above (names), `ParseError` (values) |
| `DF.write_csv(r, path)` (exists), `DF.write_csv_opts(r, path, w: R.CsvWriteOpts)`; `DF.write_opts(sep: Char, include_header: Bool, float_precision: Maybe<&2, U32>) -> R.CsvWriteOpts` | `R.Csv.write`, `R.Csv.write_with`; `Csv.render_with` | 15.6.3 | `IoError` |

#### 15.2.8 Introspection

| Facade | Semantics |
|---|---|
| `DF.collect_schema(p)` (exists) | `P.Plan.schema`: every *static* error of 15.2 and nothing else (not IO, not bindings, not data-dependent cast failures; 15.7 has `validate_bindings` for bindings) |
| `DF.explain(p)` (exists) | `P.Plan.explain`; new lines: `SLICE <offset> <len>`, `TAIL <n>`, `DROP [a, b]`, `RENAME [a -> b, c -> d]`, `UNIQUE [a, b]` (`UNIQUE []` for all columns), `CONCAT` with every input indented below it, `SEMI JOIN ON [..]`, `ANTI JOIN ON [..]` |
| `DF.optimize(p)` (exists; meaning changes) | `P.Optimize.release`: the certified fragment only (R1 merge heads; R2-R5 as they are proven in M5; until then only R1 and the restricted head sink of B01). Nodes it does not know (Sort movement, GroupBy/Join pushdown, Unique, Concat, Semi/Anti, Slice, Tail, Drop, Rename, fallible or reduction expressions) are barriers: the pass recurses into their inputs but never moves anything across them. `collect` uses this. |
| `DF.optimize_full(p)` | `P.Plan.optimize_full`: today's four passes (merge, pushdown, head, projection), opt-in, excluded from the G6 guarantee, with the B01 head rule applied; `DF.collect_full` runs it |
| `DF.err_show`, `DF.schema_show`, `DF.show` (exist) | unchanged |

### 15.3 Typing additions and the expression analysis record (P2)

#### 15.3.1 Typing table additions (`Expr.type`, strict, left-to-right, first error wins)

| node | operands | result | error (constructor, op, want, got) |
|---|---|---|---|
| `Bin{Div}` | f32, f32 | f32 | `TypeMismatch{"div", "f32", <a>}` if `a != f32`; else `{"div", "f32", <b>}` if `b != f32` |
| `Bin{FloorDiv}` | u32,u32 / i32,i32 | same | `{"floor_div", "u32 or i32", <a>}`; `{"floor_div", <a>, <b>}` |
| `Bin{Mod}` | u32,u32 / i32,i32 | same | unchanged: `{"mod", "u32 or i32", <a>}`; `{"mod", <a>, <b>}` |
| `TryCast{e, to}` | `Cast.ok(t, to)` | `to` | `{"try_cast", "castable to <to>", <t>}`; `TryCast{Lit{SNull}, to}` is the typed null like `Cast` |
| `When{c, a, b}` | c bool; a, b same | dtype(a) | `{"when", "bool", <c>}`; `{"when", <a>, <b>}` |
| `IsIn{e, vals}` | every `v` has dtype(e) | bool | `{"is_in", <e>, <v dtype or "null">}` (first offending scalar) |
| `Clip{e, lo, hi}` | e numeric; lo, hi of dtype(e) | dtype(e) | `{"clip", "numeric", <e>}`; `{"clip", <e>, <lo or hi dtype or "null">}` (lo checked before hi) |
| `Un{LenChars}` | str | u32 | `{"len_chars", "str", <t>}` |
| `StrPred{op, e, pat}` | str | bool | `{"contains_literal" / "starts_with" / "ends_with", "str", <t>}` |
| `Agg{Std / Var / Median}` | numeric | f32 | `{"std" / "var" / "median", "numeric", <t>}` |
| `Agg{op, e}` with `Expr.is_agg(e)` | | | `InvalidOperation{"nested aggregation: <Expr.show (Agg{op, e})>"}` (new: today `Expr.type` accepts `sum(sum(x))`; group_by keeps its own text) |

`Cast.ok` is unchanged (T->T; u32<->i32; u32/i32/bool->f32; f32->u32/i32; bool->u32/i32;
anything->str; str->anything except... `Cast.ok(str, bool)` stays accepted with the
`true/false/True/False` spellings). Which pairs are *fallible* is in 15.5.5.

`Expr.name` (output column name) additions: `When{c, a, b}` -> `Expr.lname(a)` else
`"literal"` (Polars names the `then` branch); `TryCast`, `IsIn`, `Clip`, `Un{LenChars}`,
`StrPred`, `Agg{Std/Var/Median}` -> the name of `e`. `Expr.refs`: union of the
operands' refs left to right (`IsIn`, `Clip`, `StrPred` add none for their literals).

#### 15.3.2 The analysis record

One analysis serves `Eval` (eager), `Plan.schema` (lazy), `Optimize.release` (barrier
and height rules) and `GroupBy`:

```
# src/expr.bend
type AKind is Data:          # ("Kind" is a Bend keyword)
  KRow{}                     # one value per input row; result height = h
  KScalar{}                  # built from literals only; 1 row, broadcastable to any height
  KRed{}                     # a reduction of the input; 1 row, computed over all h rows

type Ana is Data:
  Ana{dtype: D.DType, refs: List<&2, String>, kind: AKind, total: Bool}

# the dtype / refs / kind / totality of e over schema s, or the first typing error
def Expr.analyse(e: Expr, +s: List<&2, S.Field>) -> E.Res(Ana)
```

`Expr.type(e, s) = Res.map(dtype, Expr.analyse(e, s))` and `Expr.refs`, `Expr.is_agg`
stay as cheap projections that agree with the record (a law in LAWS.bend: for a
well-typed `e`, `Expr.refs(e)` equals the record's `refs` and `Expr.is_agg(e)` iff
`kind = KRed`).

Kind join `k1 ⊔ k2`: `KRow ⊔ _ = KRow`; `KRed ⊔ KScalar = KRed`; `KScalar ⊔ KScalar =
KScalar` (this is today's `SKind.comb`). Rules per node (dtype as 15.3.1; refs is the
left-to-right union):

| node | kind | total |
|---|---|---|
| `Col{n}` | KRow | yes |
| `Lit{v}` | KScalar | yes |
| `Alias{e, n}` | kind(e) | total(e) |
| `Cast{e, to}` | kind(e) | total(e) ∧ `Cast.total(dtype(e), to)` (15.5.5) |
| `TryCast{e, to}` | kind(e) | total(e) |
| `Un{op, e}` (all ops incl. LenChars) | kind(e) | total(e) |
| `Bin{op, a, b}` (all ops) | kind(a) ⊔ kind(b) | total(a) ∧ total(b) (FloorDiv/Mod null on zero, Div is IEEE: all total) |
| `FillNull{e, v}` | kind(e) ⊔ kind(v) | both |
| `When{c, a, b}` | kind(c) ⊔ kind(a) ⊔ kind(b) | all three |
| `IsIn`, `Clip`, `StrPred` | kind(e) | total(e) |
| `Agg{op, e}` with kind(e) ∈ {KRow, KScalar} | KRed | total(e) |
| `Agg{op, e}` with kind(e) = KRed | error (nested aggregation) | |

Design notes for P2. (i) Totality is syntactic and conservative: `total = True{}`
means `Eval` of the node over a well-formed frame never answers `Fail` whatever the
data; a fallible node (`Cast` of a fallible pair, and nothing else) is a barrier for
every rewrite that can change which rows reach it (filter merge/pushdown, head sink) or
drop it (projection pruning) (section 6, R2-R5). (ii) `KScalar` vs `KRed` are kept
apart because a scalar is height-independent (a rewrite may evaluate it under a
different height) while a reduction is not; `Len` over a scalar is `KRed` (it counts
rows). (iii) The soundness theorem (P2) reads: for well-formed `f` with
`Frame.schema(f) = s` and `Expr.analyse(e, s) = Done{Ana{t, rs, k, tot}}`:
`Eval.full(f, e)` answers `(f', Done{c})` with `Column.dtype(c) = t`,
`Column.len(c) = h` when `k ∈ {KRow, KScalar}` and `1` when `k = KRed`, whenever
`tot` holds; when `tot` does not hold the same conclusions hold for every `Done`
answer, and a `Fail` is one of the 15.5.5 cast errors. `Eval` reads only the
columns in `rs`. The proof is by induction over `Eval.compile`'s postfix code with the
stack invariant "slot i carries the record of its subexpression".

### 15.4 Cardinality (2.2b): decision table

`h` = input height; `k` = the join of the kinds of the expressions of the node.
Polars column = Polars 2.0.0, same program (`uv run python`, snippets in
`bench/contract/cardinality.py` to be added by M0's regression author; results
recorded here).

| # | program | eager | lazy (raw and optimised) | Polars 2.0.0 (observed) |
|---|---|---|---|---|
| C1 | `select([])` | `(0, 0)` | `(0, 0)` | `(0, 0)` both APIs |
| C2 | `select([lit 1 as one])`, h = 3 | `(1, 1)` | same | `(1, 1)` |
| C3 | `select([lit 1 as one])`, h = 0 | `(1, 1)` | same | `(1, 1)` |
| C4 | `head(0)` then `select([lit 1])` | `(1, 1)` | `(1, 1)` (B01-a: the optimiser must not sink `head(0)` below the literal select) | `(1, 1)` |
| C5 | `select([lit 1])` then `head(0)` | `(0, 1)` | `(0, 1)` | `(0, 1)` |
| C6 | `select([sum(a)])` | `(1, 1)` | `(1, 1)` (lazy now accepts reductions) | `(1, 1)` |
| C7 | `select([sum(a)])`, h = 0 | `(1, 1)` = `[0]`; `mean/min/max/first/last` -> `[null]`; `count/len/n_unique` -> `[0]` | same | `[0]`, `[null]`, `[0]` |
| C8 | `select([lit 1 as x, sum(a)])` | `(1, 2)` | same | `(1, 2)` |
| C9 | `select([col a, lit 1 as x])` | `(h, 2)`, `x` broadcast | same | `(3, 2)` |
| C10 | `select([col a, sum(a) as s])` | `(h, 2)`, `s` broadcast; h = 0 gives `(0, 2)` | same | `(3, 2)`, `(0, 2)` |
| C11 | `select([a - mean(a)])` | `(h, 1)` KRow | same | `(3, 1)` |
| C12 | `select([sum(a) + lit 1])` | `(1, 1)` KRed | same | `(1, 1)` |
| C13 | `with_columns([sum(a) as s])` | `(h, w+1)`, broadcast; h = 0 -> `(0, w+1)` | same | `(3, 2)`, `(0, 2)` |
| C14 | `with_columns([lit 1 as s])`, h = 0 | `(0, w+1)` | same | `(0, 2)` |
| C15 | `with_columns([])` | `(h, w)` unchanged | same | unchanged |
| C16 | `filter(a > mean(a))` | reduction over all h rows, then the row-wise comparison | same (lazy now accepts) | `[3]` of `[1,2,3]` |
| C17 | `filter(sum(a) > 5)` (KRed predicate) | broadcast: all rows or none | same | all / none |
| C18 | `filter(lit true)` / `filter(lit false)` (KScalar) | all rows / no rows (`(0, w)`) | same | same |
| C19 | `filter(lit false)` over `select([lit 1])` | `(0, 1)` | `(0, 1)` **D:** Polars' lazy engine answers `(1, 1)` here (a 1-row scalar predicate is not applied); eager Polars answers `(0, 1)`. We follow the eager answer: a scalar predicate broadcasts to the input height everywhere. Intended departure, listed in README. | eager `(0, 1)`, lazy `(1, 1)` |
| C20 | `filter(lit null::bool)` | `(0, w)` | same | `(0, 1)` |
| C21 | `filter(..)`, h = 0 | `(0, w)` | same | `(0, 1)` |
| C22 | zero-column frame of height h (from `drop` of every column): `with_columns([lit 1 as o])` | `(h, 1)` | same | `(6, 1)` |
| C23 | zero-column, height h: `select([len()])` / `select([lit 1])` | `(1, 1)` = `[h]` / `[1]` | same | `[6]` / `[1]` |
| C24 | zero-column, height h: `head(2)`, `filter(lit true)`, `unique([])`, `concat([z, z])` | `(2, 0)`, `(h, 0)`, `(min(h,1), 0)`, `(2h, 0)` | same | `(2,0)`, `(6,0)`, `(1,0)`, `(12,0)` |
| C25 | `select([lit 2 .len()])` i.e. `Agg{Len, lit}` | `[h]` (our `len()` encoding; Polars' `lit(2).len()` = 1 is not reproducible, DESIGN 14 M2.2) | same | `[1]` (known, documented) |
| C26 | `group_by` on h = 0 | `(0, keys + aggs)` | same | `(0, 2)` |
| C27 | `select([a, a])` / two unaliased literals | `DuplicateColumn{"a"}` / `DuplicateColumn{"literal"}` | same (static) | DuplicateError |

Rule behind the table: `select` height = `h` if any expression is `KRow`, else `1`;
every 1-row output is broadcast to the height; `with_columns` and `filter` always
evaluate at height `h` (reductions over the full input first, then broadcast); a
zero-column frame keeps its height through every verb (`Frame{h, []}`); `select([])`
answers `Frame{0, []}`. Row preservation for the optimiser is the P2 fact "every
expression of the node is `KRow` and total, and the list is non-empty" (not "no `Agg`
node"): a `Select` all of whose expressions are `KScalar`/`KRed` is a *height barrier*
(C4), one that mixes is height-preserving.

### 15.5 Numeric policy (2.2c-e)

#### 15.5.1 Integers

| op | u32 | i32 | by zero | i32 `MIN`, `-1` |
|---|---|---|---|---|
| `+ - *`, `sum` | wrap mod 2^32 (documented) | two's complement wrap (`MIN - 1 = MAX`) | | |
| `/` | refused (`TypeMismatch{"div", "f32", "u32"}`): cast to f32 first | refused | | |
| `//` (`floor_div`) | `U32.div` | `floor(a / b)`: `q = trunc(\|a\| / \|b\|)`; if signs differ and `\|a\| mod \|b\| != 0` then `-(q + 1)` else `±q` | null | null (plan 2.2c; Polars answers `MIN`: intended departure) |
| `%` (`mod`) | `U32.mod` | `a - b * (a // b)` with the floor quotient: the result has the divisor's sign or is 0: `7 % -2 = -1`, `-7 % 2 = 1`, `-7 % -2 = -1` (Polars) | null | `0` (Polars `0`) |
| `abs`, `neg` | refused | `abs(MIN) = MIN`, `neg(MIN) = MIN` (wrap) | | |
| `mean` | f32 of the exact values (15.5.3) | same | | |

Polars snippet: `pl.DataFrame({'a':[7,-7,7,-7,MIN,5,0],'b':[2,2,-2,-2,-1,0,0]}, Int32)`:
`a // b = [3,-4,-4,3,MIN,null,null]`, `a % b = [1,1,-1,-1,0,null,null]`; u32 `7 // 0 =
null`, `7 % 0 = null`; `MIN - 1 = 2147483647`; u32 `4294967295 + 1 = 0`, `sum` wraps to `0`.

#### 15.5.2 The F32 relation (one order for `== != < <= > >=`, sort, group_by, unique, is_in, join keys)

Order key: `Sort.fword(x)` (sort.bend) is already the total order: `-inf < .. < -0.0 =
0.0 < .. < +inf < NaN`, every NaN (any payload, any sign) equal to every other NaN.
Contract: `x op y` for f32 is `Cmp op` of `U32.cmp(Sort.fword(x), Sort.fword(y))`.
Consequences (all verified against Polars 2.0.0 on
`x = [NaN, 1.0, -0.0, 0.0, inf, -inf, null]`): `x == x` -> all true (null row null);
`x > 0.0` -> `[T, T, F, F, T, F, null]`; `x < NaN` -> `[F, T, T, T, T, T, null]`; `x >= NaN`
-> `[T, F, F, F, F, F, null]`; `-0.0 == 0.0` true, `-0.0 < 0.0` false; sort ascending:
`[null, -inf, -0.0, 0.0, 1.0, inf, NaN]` (ties keep input order); descending:
`[null, NaN, inf, 1.0, -0.0, 0.0, -inf]`; `unique`: `[NaN, 1.0, -0.0, inf, -inf, null]`;
`n_unique = 6`; `is_in([NaN, 0.0])` -> `[T, F, T, T, F, F, null]`; group_by keys `[NaN, NaN,
-0.0, 0.0, null]` -> three groups `NaN, -0.0, null` (first-appearance representative).
Validity is separate: null is never NaN and NaN is never null.

Exceptions, all Polars-verified and tested as such: **min/max** skip NaN (`min/max`
of `[NaN, 2, 1]` = `1, 2`; of `[NaN, NaN]` = `NaN`), and on a tie between `-0.0` and
`0.0` `min` answers `-0.0`, `max` answers `0.0` (both input orders); **clip** uses
IEEE `<`/`>` (15.2.6); **first/last** copy the cell (`first([NaN, 2]) = NaN`).
Definition for min: `fmin(a, b) = b if isnan(a); a if isnan(b); a if a < b (IEEE); b if
b < a; else (equal: zeros) the one with the sign bit set`; `fmax` symmetric with the
sign-bit-clear zero.

#### 15.5.3 Accumulation: Neumaier with a non-finite guard

Used by `Sum`, `Mean`, `Std`, `Var` over f32 (and over u32/i32 for `Mean/Std/Var`
after an exact `U32.to_f32` / `I32.to_f32` of each cell, which rounds above 2^24),
eager and grouped, and by `describe`. State `(s, c)`, both f32, starting `(0.0, 0.0)`;
step for each valid cell `x` **in ascending row order** (a group's rows in the input
order of the frame; the grouped scatter visits rows `0..h-1` once, so each group sees
exactly this order):

```
t = s + x
if F32.is_finite(t):                       # finite partial sum: compensate
  c = c + (if |s| >= |x| then (s - t) + x else (x - t) + s)
# else: t is ±inf or NaN; c is left as it is and never used again
s = t
result = if F32.is_finite(s) then s + c else s
```

`is_finite(t)` is `U32.and(F32.bits(t), 0x7fffffff) < 0x7f800000`. Verified cases
(Polars 2.0.0 answers in brackets): `mean [inf, 1] = inf` [inf], `mean [1, inf] = inf`
[inf], `sum [inf, -inf] = NaN` [NaN], `sum [NaN, 1] = NaN` [NaN], ten `0.1` sum to
`0x3f800000` = 1.0 (Polars eager `0x3f800001`: the departure is in Polars' favour of
speed; T2.3 checks us against an f64 reference, not against Polars bits),
`mean` = `s_final / U32.to_f32(count)`. Group sums use the same step (reverses the
DESIGN 14 M5 note 2 decision; `bench/golden/q3.csv` is regenerated from the f64
reference with the ULP rule of T2.3, not from Polars' lazy engine). Reduction order is
part of the contract so that eager, raw-lazy and optimised-lazy agree bit for bit (G2).

#### 15.5.4 std / var (ddof = 1) and median

```
n = valid count (NaN counts as valid); if n < 2: std = var = null
m = fsum(x) / n                            # 15.5.3 over the valid cells
v = fsum((x - m) * (x - m)) / (n - 1)      # second pass, same order, each term in f32
var = v; std = F32.sqrt(v)                 # NaN or inf in the data -> NaN (Polars)
median: sort the valid cells by the 15.5.2 order (NaN greatest); n = 0 -> null;
        n odd -> cell[(n-1)/2]; n even -> lo*0.5 + hi*0.5 with lo = cell[n/2 - 1], hi = cell[n/2]
```

The even formula cannot overflow (`[-3e38, 3e38] -> 0.0`, Polars `0.0`;
`[3e38, 3e38] -> 3e38`) and gives `NaN` for `[inf, -inf]` (Polars NaN). Known sign
difference: `median([-0.0, 0.0])` is `0.0` here and `-0.0` in Polars (equal under
15.5.2; the T2.2 oracle canonicalises the sign of zero for median). Verified: `std
[1,2,4] f32 = 1.5275252`, `var = 2.3333333`; `std` of one value / empty / all-null =
null; `median [3,1,2] = 2`, `[4,1,2,3] = 2.5`, `[1,null,3,10] = 3`, `[1,NaN,3] = 3`,
`[] = null`. Result dtype f32 for u32/i32 inputs (Polars f64: documented).

#### 15.5.5 cast and try_cast

`cast` = strict (first failing valid cell -> `InvalidOperation`); `try_cast` = the same
conversion with failing cells set to null. Nulls pass through both. A pair is *total*
when no cell can fail (the analysis marks `Cast` of a total pair `total`).

| from -> to | conversion | fails when | total |
|---|---|---|---|
| T -> T | identity | never | yes |
| u32 -> i32 | same bits | `v >= 2^31` | no |
| i32 -> u32 | same bits | negative (bit 31 set) | no |
| u32 -> f32 | `U32.to_f32` (round to nearest even above 2^24: `4294967295 -> 4294967296.0`, Polars same) | never | yes |
| i32 -> f32 | `I32.to_f32` | never | yes |
| bool -> u32 / i32 / f32 | 0 / 1 | never | yes |
| f32 -> u32 | `trunc(x)` | NaN, ±inf, `x <= -1.0`, `x >= 4294967296.0` (checks as IEEE `x > -1.0 && x < 4294967296.0`; both bounds exact f32: `-0.5 -> 0`, `4294967040 -> 4294967040`, `2^32` fails) | no |
| f32 -> i32 | `trunc(x)` toward zero | NaN, ±inf, `x <= -2147483904.0` i.e. `x < -2147483648.0`, `x >= 2147483648.0` (`-2147483648.0 -> MIN`, `2147483520 -> 2147483520`, `2^31` fails) | no |
| u32 / i32 / f32 / bool -> str | `U32.show`, `I32.show`, `F32.show` (`1.0 -> "1"`, `-0.0 -> "-0"`, `NaN -> "nan"`; Polars `"1.0"`, `"-0.0"`, `"NaN"`: documented departure), `"true"/"false"` | never | yes |
| str -> u32 / i32 / f32 | `U32.read`, `I32.read`, `F32.read` of the cell **as is** (**D:** no trimming, Polars does not trim; the CSV reader trims its own numeric fields, 15.6) | the read answers `None` (`" 2 "`, `"x"`, `""`, `"+5"` for u32; `F32.read` accepts `nan`, `inf`, `-inf`, `1e3`, `.5`, `5.`, `+5`, rejects `1_0`, `0x10`, `""`) | no |
| str -> bool | `true / false / True / False` exactly | anything else (Polars refuses the cast entirely) | no |
| u32 / i32 / f32 -> bool | refused by typing (`Cast.ok`), as today | | |

Error text (both APIs, eager and lazy identical): `InvalidOperation{"cast <from> to <to>:
row <i> holds <cell>"}` with `<from>/<to>` as `DType.show`, `<i>` the 0-based row of
the cell in the column being cast, `<cell>` as `Expr.show.lit` (strings quoted, f32 by
`F32.show`). Polars 2.0.0 for reference: `conversion from `f32` to `u32` failed in
column 'f' for 1 out of 1 values: [-1.9]`. The row index makes a cast a barrier for
every row-changing rewrite (section 6).

Current defects this table fixes: `F32 -> U32` of negatives/huge/NaN is `0`
(`F32.to_u32`), `F32 -> I32` out of range is garbage, `U32 <-> I32` retag silently,
`Str -> X` nulls on failure under the name `cast`.

### 15.6 CSV contract (B02)

#### 15.6.1 Fields: quoted empty string vs null, both directions

The parser (`src/csvparse.bend`, forked from the hub parser) answers every field as
`CsvCell{text: String, quoted: Bool}`; a record is a list of cells; quotedness is
never dropped before the column is built. Reading, per column dtype:

| dtype | field | cell |
|---|---|---|
| str | quoted (`""`, `" "`, `"a"`) | the content verbatim, valid (so `""` is the valid empty string) |
| str | unquoted, empty | null |
| str | unquoted, non-empty | verbatim, valid (never trimmed: `" s "` keeps its spaces, Polars same) |
| u32 i32 f32 bool | content empty after trimming (quoted or not: `""`, `"  "`, empty) | null (Polars: null for both) |
| u32 i32 f32 bool | otherwise | parsed from the **trimmed** text (`" 1 "` -> `1`; **D** Polars does not trim and would infer str: documented departure, kept because dirty exports pad numbers) ; a failed parse is `ParseError` (strict) under an explicit or frozen schema, and makes the column str under inference |

Writing (`Csv.cell`): null -> empty field; valid str -> `Csv.quote`: quoted when the
text is empty, or contains the separator, `"`, CR or LF (a `"` is doubled); otherwise
bare. So `""` and null round-trip distinctly: `"",x` reads back `["", "x"]`, `,x` reads
`[null, "x"]`. Header names are quoted by the same rule (Polars: `"a,b","c""d","", e `).
Verified Polars 2.0.0 write of `['', None, 'x,y', 'q"q', ' s ', 'multi\nline']`:
`"",1,..` / `,,..` / `"x,y"` / `"q""q"` / ` s ` / `"multi\nline"`; our output is identical
for Str cells.

#### 15.6.2 Records

| case | behaviour | Polars 2.0.0 |
|---|---|---|
| separator | `CsvOpts.sep` (any single char except `"`, CR and LF, which `InvalidOperation{"csv: separator must not be a double quote, CR or LF"}` refuses on read, scan and write; `','` default); a field holding it is quoted | same (Polars: one byte) |
| escaped quote | `""` inside a quoted field is one `"` | same |
| multi-line field | CR/LF inside quotes belong to the field; CRLF and LF line ends both accepted | same |
| blank lines before the header (`has_header = True{}`) | skipped (physical line numbers unchanged; a file of blank lines only is the empty file); with `has_header = False{}` they are data like any blank line (the column count is the first non-blank record's) | skipped / null rows |
| blank line, 1 column | a null row (an empty field) | null row |
| blank line, k > 1 columns | skipped; error line numbers still count it | an all-null row (**D** departure: a blank line is almost always a trailing newline or padding) |
| ragged short row | `ParseError{line, "expected <k> fields, got <g>"}` (strict) | fills nulls (**D** departure: strict) |
| ragged long row | same `ParseError` | error |
| non-ASCII | UTF-8 text verbatim; `len_chars` counts code points (`"日本語"` = 3) | same |
| header only | `(0, k)` frame with str columns under inference, the given dtypes under a schema | same |
| empty file | `(0, 0)` frame (**D**; Polars `NoDataError`); with explicit dtypes the count is checked against 0 columns (`"csv schema: <d> dtypes for 0 columns"` for d > 0) | error |
| `has_header = False{}` | names `column_0 .. column_{k-1}` | same |
| line numbers in errors | 1-based physical line of the record's first line; the header is line 1 | |
| malformed quoting | `ParseError{0, "malformed csv"}` | error |

#### 15.6.3 Options

```
# src/csv.bend
type CsvOpts is Data:       CsvOpts{sep: Char, has_header: Bool, infer_rows: U32}          # exists; default (',', True, 100)
type CsvWriteOpts is Data:  CsvWriteOpts{sep: Char, include_header: Bool, float_precision: Maybe<&2, U32>}   # default (',', True, None)
```

Explicit schema: `Csv.read_with(path, opts, dtypes: List<&2, D.DType>)` by column
position (header gives the names); `dtypes = []` means infer; a count mismatch is
`InvalidOperation{"csv schema: <d> dtypes for <k> columns"}`. Inference: the first
`infer_rows` records (0 = all) decide per column in the order u32, i32, f32, bool, str
(`Csv.infer.col`); then EVERY record is checked against the inferred dtype when
inference saw only a prefix, so a later disagreeing row is a `ParseError`, not a
silent null (today's `check` flag; keep). F32 cells write as `F32.show` digits
(`1` for `1.0`, `-0` for `-0.0`, `nan`, `inf`, `1e-7`) or with exactly
`float_precision` decimals (`Fmt.fixed`, round half even). **D:** text equality with
Polars' write_csv is NOT part of the contract (Polars writes `1.0`, `-0.0`, `NaN`,
`1e+16`); value equality after reading both files back with the same schema is
(T2.2 reads Polars' CSV with `F32.read` and compares dumps).

#### 15.6.4 scan_csv: bounded prefix inference, one read at collect

`Lazy.scan_csv(path, opts)`: open; read 64 KiB (`File.read_at`, offset 0); while the
chunk holds fewer than `infer_rows + 1` non-blank line ends outside quotes (amended M1:
blank lines are skipped by the reader, so they do not count) and the file is not
exhausted, read the next 64 KiB; cut the text at the last line end outside quotes;
`Csv.infer` on that prefix (records that are complete within it); close. It never
reads the whole file (unless the file is smaller than the prefix) and never builds
columns. `collect` reads the file once (`Csv.read_with` with the frozen dtypes, 1 MiB
chunks in M4's csvparse), strictly: a value that does not parse under the frozen dtype
is `ParseError{line, "column <name>: cannot parse \"<text>\" as <dtype>"}`; a header
whose names or count differ from the plan's is `InvalidOperation{"scan_csv <path>: data
schema [<file schema>] differs from the plan's [<plan schema>]"}` (schemas shown by
`Schema.show`: `a:u32, b:str`). `DF.scan_csv_schema(path, opts, schema)` is pure and
skips inference. `collect_schema` of a scan is its frozen schema (never IO).

#### 15.6.5 Claims

No round-trip claim for numeric-looking strings under inference (`"007"`, `" 1 "`,
`"1.0"` in a str column come back as numbers unless a schema is given): README says so
(B02-k). Round trip IS claimed for: every dtype under an explicit schema written and
read by bend-frame (dump equality, NaN payload excepted), and `""` vs null.

### 15.7 Sources and Env (B04)

```
# src/plan.bend
type Env is Type:  Env{frames: List<&1, Named.Frame>}          # exists; names unique by contract
def Env.add(env, +name, f) -> Env & Plan                           # exists; prepends, total
def Plan.sources(p: Plan, acc: List<&2, String>) -> List<&2, String>   # every Source name, postfix order, with repeats
# src/exec.bend
def Exec.validate(p: Plan, env: Env) -> Env & E.Res(Unit)          # DF.validate_bindings
def Exec.run_pure(code, env) ...                                    # M2: the pure runner after source materialisation
```

| rule | text |
|---|---|
| presence | every `Source{name, s}` of `p` names a frame of `env`; else `InvalidOperation{"source not in env: <name>"}` |
| uniqueness | `env` binds each name once; else `InvalidOperation{"source bound twice in env: <name>"}` (checked before presence, over the whole env) |
| schema | `Frame.schema(frame) == s` (names, dtypes, order); else `InvalidOperation{"source <name>: data schema [<env schema>] differs from the plan's [<plan schema>]"}` (existing text) |
| order of checks | `Plan.schema(p)` errors first (static), then uniqueness, then presence and schema per Source in postfix order; `collect` = `Plan.schema`, then `Exec.validate`, then execution |
| use counting | `Exec.run` computes `uses(name)` = occurrences in `Plan.sources(p)`; at each `ISource` with `remaining(name) > 1` the frame is **cloned** (`Frame.clone`, column order kept) and left in `env`, `remaining` decremented; at the last use it is **taken** (`Env.take`, no copy). A self-join `Join{.., Source{t}, Source{t}}` therefore works and sees two identical frames |
| unused frames | frames of `env` not named by `p` stay in `env` and are dropped when `collect` returns (nothing is reported) |
| ownership | `collect(p, env)` consumes `env`; a caller who needs the frames afterwards clones them before building the env (`DF.clone`) |
| `collect_schema` | never looks at `env` (bindings are not static schema); README stops saying "collect refuses exactly what collect_schema refuses" and says "collect_schema predicts the static schema and type errors; validate_bindings predicts the binding errors; the rest is IO and data" |
| optimizer | `Optimize.release` runs after validation conceptually but is a pure plan rewrite; it never duplicates or removes a `Source` node, so `Plan.sources` (as a multiset) is invariant under it (a lemma in M5) |

### 15.8 Row cap 2^23 (2.2g)

`Kernel.max_rows() = 8388608` (2^23); `Kernel.check_rows(n: U32) -> Maybe<&2, E.Err>`
answers `Some{InvalidOperation{"too many rows: <n> exceeds 8388608"}}` when `n >
8388608`. `Kernel.depth_for` is capped at 23 and is **not** the guard. Every path that
allocates a frame or column of a height that is not bounded by an existing frame's
height calls the guard **before** allocating:

| path | guarded quantity | where |
|---|---|---|
| CSV parse (`Csv.rows`) | number of data records | before `Csv.cols` builds any column |
| `Column.from_scalars` (facade construction) | list length | before `Kernel.from_list` |
| `Join.run` (inner/left) | output row count = sum over left rows of `max(1, matches)` for left, matches for inner (computed from the CSR counts before gathering) | before `perm_l/perm_r` allocation; semi/anti never exceed the left height (unguarded) |
| `Concat` | sum of input heights (U32 add is checked for wrap: a sum that wraps is over the cap by definition) | before any gather |
| `GroupBy.run` | number of groups `ng <= h` | not needed (bounded), the cap is asserted anyway in the densify step for the proof invariant |
| `Eval.bcast`, `filter`, `gather`, `slice`, `head`, `unique`, `sort` | bounded by an input height | unguarded (a well-formed input is already under the cap) |
| `Env.add` / `Source` | frames come from guarded constructors | unguarded |

Implemented (M1 B04-i): `Kernel.max_rows`, `Kernel.check_rows`, and `Kernel.check_rows.cap(cap, n)`
(the guard with the cap as a parameter; its text names the cap it got). The paths that exist
today: `Column.from_scalars` (list length; `Column.from_scalars.cap`), `Csv.rows` (data records after
the shape checks; `Csv.rows.cap`, `Csv.parse_with.cap`), `Join.run` (`Join.fill.a`, the `Tot` count,
which saturates at 2^32 - 1 instead of wrapping), `GroupBy.run` (the input height, checked after the
type errors and before any key is evaluated: `ng <= h`). `Concat` waits for M3. See section 14 "M1 B04-i".

Tests exercise the guard function directly (`check_rows(8388608)` = `None`,
`check_rows(8388609)` = `Some`) and each path with a cheap over-cap request: a CSV
parse is tested through a `Csv.rows` entry taking a record count, a join of
2900 x 2900 equal keys (8.41 M output rows, refused before allocation), a concat whose
heights sum past the cap built from `Frame{h, []}` zero-column frames (no data), and
`from_scalars` through a counted-list entry. No test allocates 8 M rows.

### 15.9 Error catalogue (every text is one line; `Err.show` renders them)

| constructor | fields | raised by |
|---|---|---|
| `ColumnNotFound{name}` | | `Col` typing, `select_names`, sort keys, join keys (left first), `drop`, `rename` (from), `unique` subset |
| `DuplicateColumn{name}` | first repeated name | `select`/`with_columns`/`group_by`/`join`/`rename` outputs; `rename` repeated `from`; `from_columns`; `describe` (`statistic`) |
| `TypeMismatch{op, want, got}` | `op` = lowercase op name (`BinOp.name`, `UnOp.name`, `AggOp.name`, `"cast"`, `"try_cast"`, `"filter"`, `"join"`, `"when"`, `"is_in"`, `"clip"`, `"lit"`, `"from_scalars"`, `"fill_null"`) | typing (15.3); `"lit"` wants `"a typed literal"` got `"null"` for an untyped `Lit{SNull}` |
| `ShapeMismatch{want, got}` | heights | `Frame.put/replace`, a binary op over two full columns of different length (internal; unreachable from the facade) |
| `ParseError{line, text}` | `"malformed csv"` (line 0); `"expected <k> fields, got <g>"`; `"column <name>: cannot parse \"<text>\" as <dtype>"` | CSV |
| `InvalidOperation{what}` | `"aggregation in select (v1: use group_by)"` and its `with_columns`/`filter` twins are **removed** (reductions are accepted); `"nested aggregation: <show>"`; `"group_by needs at least one key"`; `"group_by key is an aggregation: <show>"`; `"agg expects an aggregation: <show>"`; `"nested aggregation in agg: <show>"`; `"join: no key columns"`; `"join: left_on and right_on must have the same length"`; `"concat_vertical: no inputs"`; `"concat_vertical: input <i> schema [..] differs from input 0's [..]"`; `"cast <from> to <to>: row <i> holds <cell>"`; `"i32 out of range: <v>"`; `"csv schema: <d> dtypes for <k> columns"`; `"scan_csv <path>: data schema [..] differs from the plan's [..]"`; `"source <name>: data schema [..] differs from the plan's [..]"`; `"source not in env: <name>"` (replaces `"source not in env (or used twice): <name>"`); `"source bound twice in env: <name>"`; `"too many rows: <n> exceeds 8388608"`; `"exec: malformed plan (stack underflow)"`, `"exec: malformed plan (not one result)"`, `"eval: unexpected .."` (internal, unreachable from well-typed plans) | |
| `IoError{code, text}` | OS code and message | `File.*` |

Any text that embeds user data (`<show>`, `<cell>`, `<name>`, `<path>`, `<text>`) may
contain a newline only through that data; the dump's `error` line is still the whole
`Err.show` string, and comparisons are exact.

**Order of errors within one verb (eager and lazy alike).** A verb makes ALL its static checks,
in `Plan.schema`'s order, before it evaluates any data; data errors (a failing strict `cast`,
`"i32 out of range"`, the row cap of 15.8, IO) come only after. Per verb:

| verb | static checks, in order |
|---|---|
| `select`, `with_columns` | the shared analysis (15.3: typing, nested aggregation) per expression in list order; then `DuplicateColumn` on the first repeated output name (`Eval.static`) |
| `filter` | the predicate's analysis error; then `TypeMismatch{"filter", "bool", got}` |
| `sort` | `ColumnNotFound` for the first missing key in list order (`Sort.miss`) |
| `group_by` | `Grp.validate` (types of the keys, then of the aggs; >= 1 key; no aggregation in a key; each agg's shape); then `DuplicateColumn` over keys then aggs (`Grp.static`); then the row cap |
| `inner_join`, `left_join` | `Join.schema` (key-list errors, `ColumnNotFound` left first, `TypeMismatch{"join", ..}`, `DuplicateColumn` after the `_right` suffix); then the row cap |
| `head` | none |

`collect` = `Plan.schema` of the whole plan, then `validate_bindings` (15.7), then execution
(whose verbs re-check the same rules and then evaluate).

**Eager-vs-lazy error agreement: admissible programs (T2.1).** An eager program runs its verbs
one at a time, each on the result of the verbs below it; `collect` types the whole plan first.
So G2's "equal dump text, errors too" (15.1 rule 7) is required for:
(a) every single-verb program (the table above makes eager and lazy agree), and
(b) every multi-verb program that is admissible: no verb has a static error, or the eager run
reaches the first statically invalid verb without a data error in a verb it ran before it (the
verb's inputs, and for a join both inputs).
A multi-verb program with a static error in a later verb and a data error in an earlier one
(for instance `sort([p])` over `select([cast(b, f32)])` where `p` does not exist and `b` holds a
non-number) is **inadmissible for T2.1**: eager reports the data error, lazy the static one, and
both are contract-conformant. The differential generator computes both answers in its oracle and
counts such programs apart (`inadmissible_for_T2.1`, bench/diff/README.md);
`tests/regress/NEW_1_static_checks_first.bend` pins one (`15.9-inadmissible`).

### 15.10 Defect table (both reviews; one regression test per row, `#! xfail <ID>` until fixed)

| ID | defect (one line) | contract row | milestone |
|---|---|---|---|
| B01-a | `Head{0}` sunk below a literal-only `Select` yields one row (Astra A) | 15.4 C4/C5, 15.2.8 optimize barrier | M1 |
| B01-b | lazy `Select{[]}` keeps the input height, eager gives `(0,0)` (Astra E) | 15.4 C1 | M1 |
| B01-c | hidden height of a zero-column frame becomes visible in a later `with_columns`/literal (Astra E) | 15.4 C1, C22-C24 | M1 |
| B01-d | constant predicate over a literal projection; Polars' lazy quirk documented as a departure | 15.4 C18-C19 | M1 |
| B01-e | zero-row inputs through literal-only / reduction / mixed selects and with_columns | 15.4 C3, C7, C10, C13, C14, C21, C26 | M1 |
| B01-f | `Opt.head` sinks below every Select/WithColumns regardless of kind; must use the analysis (KRow, total, non-empty) | 15.3.2, 15.4 rule | M1 (restricted), M5 (proven) |
| B02-a | reading `"",x` gives null for the quoted empty string (Astra B) | 15.6.1 | M1 |
| B02-b | writing a valid `""` emits an empty field, indistinguishable from null (Astra B) | 15.6.1 | M1 |
| B02-c | `scan_csv` reads and parses the whole file at plan build, again at collect (Astra G3, Fable 4) | 15.6.4 | M1 (prefix), M4 (chunked read) |
| B02-d | `write_csv` quoting of fields with separator / quote / newline untested (Fable 2) | 15.6.1 | M0 test |
| B02-e | separators other than `,` and write options not reachable from the facade | 15.2.7, 15.6.3 | M3 |
| B02-f | blank line handling differs between 1 and k columns and from Polars; undocumented | 15.6.2 | M1 doc+test |
| B02-g | ragged rows: short rows are errors here, null-filled in Polars; undocumented | 15.6.2 | M0 test, M1 doc |
| B02-h | non-ASCII fields, multi-line fields, escaped quotes not in the differential suite | 15.6.2 | M0 test |
| B02-i | explicit schema only via `src/` (`Csv.read_with`); dtype-count error text unverified | 15.2.7 | M3 |
| B02-j | numeric fields trimmed on read while Polars infers str for `" 1 "` | 15.6.1 (departure) | M1 doc+test |
| B02-k | README implies inference round-trips numeric-looking strings | 15.6.5 | M1 README |
| B03-a | grouped `mean` of `[inf, 1]` is NaN (Kahan `inf - inf`) (Astra C) | 15.5.3 | M1 |
| B03-b | eager `Kernel.fsum` has the same `inf - inf` contamination (Astra C audit) | 15.5.3 | M1 |
| B03-c | f32 `==`/`>` use raw IEEE: `NaN == NaN` false, `NaN > 0` false; keys use a total order (Astra D) | 15.5.2 | M1 |
| B03-d | integer `/` by zero answers 0, `%` by zero the dividend (Fable B1) | 15.5.1 | M1 |
| B03-e | `cast` f32 -> u32 of negative / huge / NaN answers 0 (Fable B2, Astra G5) | 15.5.5 | M1 |
| B03-f | `/` on integer columns truncates and keeps the integer dtype (Fable B3) | 15.5.1 (`div` refused, `floor_div`) | M1 |
| B03-g | `mean` of integers is f32: documented but missing from README differences (Fable B4) | 15.2.5 | M1 README |
| B03-h | grouped f32 `sum` is a plain sequential add; 1k-row q3 cells differ from Polars (Fable B5, Astra 1) | 15.5.3 | M1 |
| B03-i | `lit_i32(v)` with `v >= 2^31` is silently negative (Fable minor, plan 2.2d) | 15.2.1 | M1 |
| B03-j | u32 `+ - *` and `sum` wrap silently and undocumented (Fable minor) | 15.5.1 | M1 README |
| B03-k | top-level `n_unique` counts each NaN apart, grouped counts NaN once (DESIGN 14 M5.5) | 15.2.5 NUnique | M1 |
| B03-l | i32 `MIN // -1` and `MIN % -1` follow wrapping, contract says null / 0 | 15.5.1 | M1 |
| B03-m | f32 -> i32 out of range is garbage; u32 <-> i32 casts retag silently (Astra G5) | 15.5.5 | M1 |
| B03-n | f32 `min`/`max` depend on NaN position (`F32.min(NaN,1) = 1`, `F32.min(1,NaN) = NaN`) and on the sign of zero | 15.5.2 exceptions | M1 |
| B03-o | i32 `%` takes the dividend's sign (truncating); Polars and the contract: the divisor's | 15.5.1 | M1 |
| B03-p | str -> number `cast` nulls failures silently under the name `cast` | 15.5.5 | M1 |
| B03-q | str -> number `cast` trims; Polars does not | 15.5.5 | M1 |
| B04-a | eager accepts reductions in select/with_columns/filter, lazy refuses them (Fable B6, Astra G1) | 15.2.5, 15.4 | M1 |
| B04-b | a Source used twice (self-join) passes `collect_schema` and fails `collect` (Fable B8, Astra G4) | 15.7 use counting | M1 |
| B04-c | no facade for several named frames in one Env (Astra G4) | 15.2.2 `add_source` | M1 |
| B04-d | missing / duplicate bindings detected only during execution; `Env.take` silently drops an older duplicate | 15.7 `validate_bindings` | M1 |
| B04-e | frozen scan schema vs a changed file: error text names the file (exists, untested) | 15.6.4 | M0 test |
| B04-f | README: "collect refuses exactly what collect_schema refuses" is false (Fable B8) | 15.7 | M1 README |
| B04-g | join drops the right key even when `left_on`/`right_on` differ: undocumented (Fable B7) | 15.2.4 | M1 README |
| B04-h | `sum(x)/sum(y)` is not an accepted group_by agg; the surface is narrower than "nine reducers" suggests (Astra G2) | 15.2.4 group_by | M1 doc, M3 example |
| B04-i | the 2^23 row cap exists only as a comment (DESIGN 14 M1.7, Fable 2) | 15.8 | M1 |
| B04-j | once `cast` is strict, filter merge/pushdown and head sinking across a cast change which rows can fail (new hazard) | 15.3.2 totality barrier | M1 |
| B04-k | `maintain_order=False{}` is silently ignored | 15.2 shared rules | M1 README |
| B05-a | `bench/check.py` accepts `100001` vs `100000` (float tolerance applied to ints) (Astra F) | 15.1 rule 3 (exact non-floats) | M0 |
| B05-b | `check.py` accepts NaN vs an integer (`rel > tol` is false for NaN) (Astra F) | 15.1 rule 3 | M0 |
| B05-c | `check.py` splits on `,` instead of parsing CSV; quoted commas break it (Astra F) | 15.1 (dumps, not CSV) | M0 |
| B05-d | `scripts/bench.sh` `\|\| true` swallows mismatches and missing outputs (Astra F) | plan B05 | M0 |
| B05-e | stale "Kahan" comments in `check.py`, README, `groupby.bend` (Astra F) | 15.5.3 | M1 |
| B05-f | no CI workflow; `make check` excludes the facade and proofs (Astra 2) | plan T7 | M0 |
| B05-g | no test that eager, raw-lazy and optimised-lazy agree on the same data (both reviews) | plan T2.1, 15.1 rule 7 | M0 |
| B05-h | the proof negative check (`2^(d+1)` slots) is not a kept test (Fable 6) | plan T5 | M0 |
| B05-i | README overclaims: "byte-identical", "48 laws" without the schema/shape caveat (Fable 8, Astra 5) | plan G7 | M6 |
| NEW-1 | eager `select` / `group_by` evaluated data (a failing strict cast) before their static `DuplicateColumn` check, which lazy reports first; eager `sort` reported the LAST missing key; eager `group_by` checked the row cap before `DuplicateColumn` (bench/diff seed 1: tests/diff/d0001, d0002) | 15.9 order of errors | M1 (fixed) |
| NEW-2 | the interpreter (`bend file.bend`) overflowed the host stack on results of ~2^15 rows or more: `DF.dump` and `Column.from_scalars` recursed once per row (the native binary is fine) | 15.1, 15.8 | M1 (fixed for dump / from_scalars; CSV read / write still overflow, DESIGN.md 14) |

Rows marked M0 are fixed in M0 itself (harness and tests); every other row gets an
`#! xfail <ID>` regression in M0 (eager, raw-lazy and optimised-lazy where
applicable) and loses the marker when fixed.

### M0 review (dump location)
- The §15.1 oracle lives in `src/dump.bend` (`Dump.frame`, `Dump.frame_k` which hands the frame back, `Dump.result`), not `Fmt.dump` in `src/fmt.bend`; `DF.dump(r: ResT(Frame))` and `DF.dump_frame(f)` (consumes `f`). A frame whose columns are longer than its height dumps an extra `excess` line; shorter columns print `?` cells. Both are outside the §15.1 grammar, so `bench/check.py --dump` rejects them.
- `scripts/test.sh` skips `tests/**/lib/*.bend` (helper modules imported by tests).
