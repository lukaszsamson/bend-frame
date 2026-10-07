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
JS/web build (works but untested), `--verdict` runs (needs Lean 4.34 installed).

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
(p20). `--verdict` needs Lean v4.34.0, absent on this machine.

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
  Max/First/Last = null`, `NUnique=0`. Polars `pl.len()` is `Agg{Len, Lit{SU32{1}}}`.
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

A row is null iff its validity word is `0`. Arithmetic, comparisons, boolean
ops, casts, `Neg/Not/Abs/Sqrt`: null in → null out (mask AND). `IsNull`,
`IsNotNull`, `Count`, `NUnique`: never null. `FillNull(e, v)`: `e` where
valid, `v` otherwise (both masks combine: result null only where both null).
Aggregations skip nulls; `Mean` of no valid rows is null; `Sum` of none is
`0`. Sorting: nulls first by default (`nulls_last = False{}`), stable among
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

Proven in miniature by p08 and p20 (ALL PROOFS CHECK); the real ones are the
same statements over `src/`:

```python
law filter_keeps_schema:   # for p, +s, e, ok: {Plan.schema(p) == Done{s}}, t: {Expr.type(e, s) == Done{TBool{}}}
  {Plan.schema(Filter{e, p}) == Done{s} : Res(List<&2, Field>)}
law select_cols_is_project: # Select of plain Col exprs == Schema.project of the names
  {Plan.schema(Select{List.map(.. Col ..), p}) == Schema.project(names, s) : Res(List<&2, Field>)}
law project_length:        # a successful projection has one field per name
  {List.length(&2, Field, out) == List.length(&2, String, names) : Nat}
law head_keeps_schema:     {Plan.schema(Head{n, p}) == Plan.schema(p) : Res(List<&2, Field>)}
law sort_keeps_schema:     # given the keys exist
law head_len:              {snd(Column.len(Column.head(c, n))) == U32.min(n, snd(Column.len(c))) : U32}
law with_columns_height:   # eager: height of with_columns(f, es) == height of f, when Done
law expr_name_alias:       {Expr.name(Alias{e, n}) == n : String}
law optimize_keeps_schema: # STRETCH: {Plan.schema(Plan.optimize(p)) == Plan.schema(p)}; prove per rewrite rule first
```

Proof toolkit (from p08/p20): unfold one step with `{==}`; flip hypotheses
with `Equal.sym`; induct on lists with the step's computed `Maybe/Result`
values passed to a lemma as parameters; `Some`/`Done` injectivity via
`Equal.cong` + `Maybe.default`/`Result.default`; refute `Fail == Done` with a
`disc` motive and `Empty.absurd`; a law over a `Column` splits on its five
constructors. Mark reused law parameters `+s` (a Data schema used twice).
Open laws are allowed to ship as TODOs only in the stretch group.

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
6. **No `--verdict`** without Lean 4.34; `bend PROOF.bend` is the gate.
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
