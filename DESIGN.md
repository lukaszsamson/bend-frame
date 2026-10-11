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
src/radix.bend             Radix.sort, WS: the (word, row) LSD radix sort (T3.2; own file since W2.3)
src/hcode.bend             Hc.code: the flat distinct-key string coder (v0.2 W2.1, wired W2.3)
src/ranks.bend             Rk.words / Rk.dict: lexical ranks of string entries (W2.2, wired W2.3)
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
README.md, LICENSE (SPDX-License-Identifier: Apache-2.0 since 2026-10-10)   [haiku]
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
  CStr{len: U32, depth: Nat, valid: Valid, data: ST.Strs}   # M4: Raw or Dictionary storage

type Named is Type:
  Named{name: String, col: Column}

type Frame is Type:
  Frame{height: U32, cols: List<&1, Named>}
```

M4 (section 14, "M4 string experiment"): a Str column's data is `ST.Strs` (src/strs.bend),
`SRaw{data: Array<String>}` (one string per row) or `SDict{codes: Array<U32>, dict: Dict}`
(one code per row; `dict` holds each distinct string once, entry 0 is always `""`, a null
row holds code 0). Both decode to the same rows and every operation answers the same values.

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

## 8. Laws (`LAWS.bend`) and how they are proven (`PROOF*.bend`) [opus]

Status (v0.1 release candidate, after M5 part 4: P1 and P2 closed as scoped, P3 by the
fallback, both string storages in the P1 chain, the in-place kernels and concatenation
included; the v0.1 review's scan laws `hmerge_keeps_scans` / `release_keeps_scans` added
after it; v0.2 W1f added `range_cell`, the range copy behind `Column.slice`; v0.2 T3.1 added section 16,
the moves of the liveness pass; v0.2 T3.4 added section 17, the Sort + Head bounded gather and the
runner's physical step `Exec.run_phys`): `LAWS.bend` states 159
laws over `src/` in 17 sections; `PROOF.bend` imports
`PROOF_lib`, `PROOF_schema`, `PROOF_expr`, `PROOF_plan`, `PROOF_kernels`, `PROOF_exec`,
`PROOF_bits`, `PROOF_contents`, `PROOF_eval`, `PROOF_evalops`, `PROOF_evalrun`,
`PROOF_strs`, `PROOF_append`, `PROOF_inplace`, `PROOF_moves` and `PROOF_sorthead` (one file per area; `L.*` is the shared
toolkit, `B.*` the word-level toolkit) and proves all of them: `bend PROOF.bend` prints ALL
PROOFS CHECK in 1.7-2.3 s wall (3.3-3.6 s CPU, `make proofs`), `bend PROOF.bend --verdict`
prints it again under the independent BendTT kernel in 5.1-5.5 s wall (`make verdict`);
measured 2026-10-09 on the M2 Pro at a one-minute load average of 22-38 (a quiet machine is
faster). No `@unsafe`, no foreign code, no open law, no axiom. Eleven negative fixtures in
`tests/proof_negative/` (plan M_01 T5) show the claims are load-bearing: a slots law
falsified to 2^(d+1); a mutated copy of the production head rule `Opt.hmin` (the outer limit
wins) that the real R1 proof term is refused for; a copy of `Kernel.gather.go` reading the
source at the wrong index (plus one) that the real `gather_contents` term is refused for; a
copy of `Kernel.compact_keep.go` with a flipped mask (the cursor advances on a 0 word) that
the real `compact_contents` term is refused for; a copy of the release head pass
`Opt.hmerge` that sinks the limit below every Select (certificate or not) that the real
`hmerge_run` term is refused for; a copy of the unary evaluator in which Neg over i32
answers a u32 column (same words, wrong dtype) that the real `eval_un_typed` case is refused
for; a copy of the stack machine's `Eval.fit` that does not broadcast a 1-row side, refused
by the `fit_w` shape lemma behind `run_typed`; a copy of the string encoder's loop `Enc.go`
that gives every row code 0 (reusing the empty string's code) refused by the real
`strs_encode_cells` term; a copy of the dictionary re-coding loop `Dict.rc.go` that writes
the merge map at the wrong slot (c + 1) refused by the real `dict_merge_spec` term; a copy
of `Kernel.append` whose second `copy_into` starts at na + 1 (a gap at na, b's last row past
the end) refused by the real `append_cells` term (`append_right_offset.bend`); and a copy of
`Kernel.choose.go` with the mask inverted (a set word takes b's cell) refused by the real
`choose_cell` term (`choose_inverted_mask.bend`); each with the mutated function in the
checker's `expected` and the production one in `observed`, and (all but the slots fixture) a
positive control in the same file that states the production theorem with the same term and
checks.
`make check` skips these files (their expectation is a failure); `make test` runs them.

How strong the mutation evidence is (v0.1 review, plans/REVIEW_V01_FABLE.txt H2 and
plans/REVIEW_V01_ASTRA.txt section 3). The eleven fixtures mutate a RENAMED disposable copy
of a production function and try the production proof term against it. Five of them are
name-sensitive by their own headers (`gather_wrong_index`, `compact_flipped_mask`,
`choose_inverted_mask`, `encode_reuses_code`, `remap_wrong_slot`): the production proof term
is tied to the production name, so an UNMUTATED renamed copy is refused too, and those five
show "a copy is rejected", not "a wrong copy is rejected". The stronger check is
`make mutation-check` (`scripts/mutation_check.sh`, part of `make ci`): it copies the
proof-relevant tree, patches ONE production function IN PLACE (21 mutations over
`Kernel.gather`, `compact_keep`, `compact`, `choose`, `append`, `copy_into`, `Kernel.range`
(two patches: the write slot, the read offset; W1f), `Valid.range` (the slice's mask not
shifted; W1f), `Opt.hmin`, `Opt.hmerge` (two patches), `Dict.code`, `Enc.put`, `Dict.rc.put`,
`Eval.un`, the stack machine's `Eval.fit`, since T3.1 `Frame.lend` (two patches: it
answers the stand-in, it lends the wrong columns) and `Eval.mark` (two patches: a move although a
later expression reads the column, a move of a column the operator keeps; the proof of `mark_reads`
spells the production condition and fails first, restating it to the mutated one moves the failure
to `mark_moves_ok`'s own requirement, checked by hand), and since T3.4 `Sort.gh.k` (the bounded
gather keeps one row too many), `Sort.fh.c` (the missing-key check skipped), `Sort.frame_head` (no
keys keeps every row) and `Exec.run_phys.h` (the physical step heads one row too many)), runs `bend
PROOF.bend` and requires "SOME PROOFS FAIL"; the unmutated copy must say ALL PROOFS CHECK first.
All 25 are caught (nothing was weakened to make that true). It is a spot check of 21
functions, not a mutation test of every proof.

Proven (`law x` in LAWS.bend, `def Laws.x` in the PROOF file named):

| group (file) | laws |
|-------|------|
| 1 Schema (`PROOF_schema`) | `project_nil`, `project_length`, `project_names`, `with_existing_keeps_width`, `with_new_appends` |
| 2 Expr typing (`PROOF_expr`) | `dtype_eq_refl`, `alias_name`, `col_name`, `alias_type`, `alias_is_agg`, `agg_is_agg`, `col_refs`, `lit_type`, `col_type`, `cmp_type_bool`, `arith_type`, `mod_type`, `logic_type`, `cast_type`, `is_null_type`, `is_not_null_type`, `counting_type`, `keeping_agg_type`, `sum_type`, `mean_type` |
| 3 Plan.schema (`PROOF_plan`) | `source_schema`, `head_keeps_schema`, `filter_keeps_schema`, `filter_schema_is_input`, `sort_keeps_schema`, `sort_schema_is_input`, `select_cols_is_project`, `select_cols_names`, `with_column_keeps_width` |
| 4 Optimizer, schema level (`PROOF_plan`) | `head_pass_keeps_schema`, `merge_pass_keeps_schema`, `merge_head_keeps_schema`, `merge_pass_merges`, `merge_fixed_point`, `merge_idempotent`, `head_pass_merges`, `hmerge_keeps_schema`, `hmerge_merges` (the release pass `Opt.hmerge` keeps the schema and leaves no adjacent Heads) |
| 5/5b Columns, kernel shape (`PROOF_kernels`) | `head_len`, `head_dtype`, `mask_not_slots`, `mask_and_slots`, `iota_slots` (2^d slots through the model `Laws.slots` of `Array.size`) |
| 6 I32 (`PROOF_lib`) | `i32_add_comm`, `i32_bits_roundtrip` |
| 7 Names and numbers (`PROOF_lib`) | `u32_min_comm`, `u32_min_assoc` (from Word.cmp antisymmetry and transitivity, by induction over the 32-bit word), `str_eq_refl`, `str_eq_sound` (the runtime `String.eq` is reflexive and equal names are the same string: the P0 name-equality spike closed, no local `Str.eq` was needed), `names_has_head` |
| 8 The production runner (`PROOF_exec`) | `frame_head_head`, `head_step`, `head_merge_run` (R1 as a rule: `Exec.run_pure(Head{n, Head{m, x}}, env) == Exec.run_pure(Head{Opt.hmin(m, Some n), x}, env)` for every plan x, env, n, m), `head_pass_keeps_sources`, `head_pass_run` (R1 as the pass: `Opt.head` on the merge-only fragment, any pending limit, suffix code and runner state), `hmerge_keeps_sources`, `hmerge_keeps_scans` / `release_keeps_scans` (the release optimizer keeps every `IScan` instruction, path, options and frozen schema, in postfix order: `Exec.mat` reads the same files in the same order for `Optimize.release(p)` as for p), `hmerge_run` (the release head pass `Opt.hmerge` with any pending limit, suffix code and runner state, for EVERY plan), `release_run` (`Exec.run_pure(Optimize.release(p), env) == Exec.run_pure(p, env)` for every plan p and env, no hypothesis), `release_run_obs` (the same through `DF.dump`) |
| 9 P0 well-formedness (`PROOF_kernels`) | `u32_min_le`, `wf_new`, `wf_new_words`, `wf_frame_empty`, `wf_column_head`, `wf_frame_head` over the Type-valued predicates `WFArray`, `WFWords`, `WFMaskedW/T`, `WFValidW/T`, `WFColumn`, `WFColumnH`, `WFCols`, `WFFrame` (len <= 2^depth, perfect trees, 0/1 mask and bool words, null slots at the default, equal heights, unique names, the zero-column convention) |
| 10 Buffer contents (`PROOF_kernels`) | `array_get_pure` (`Array.get(a, i) == (a, rd_at(a, i))`: the real getter is pure and reads the model `rd`, which makes the production halving decisions), `array_set_get` (read-after-write at the same index through the real `Array.set`), `gather_step`, `compact_step`, `compact_step_cell` (one iteration of the production `Kernel.gather.go` / `compact.go`, at the U32 instance) |
| 11 Buffer contents, the full theorems (`PROOF_bits`, `PROOF_contents`; plan P1, M5) | `rd_at_wf` (`rd_at` of a well-formed array reads with the slot count 2^d), `paths_distinct` (THE distinct-paths bit-vector lemma: two indices below 2^d whose halving decisions through `Array.get`/`Array.set`'s descent agree are equal, over `Word.and / shr / sub / cmp`), `array_set_other` (a write at i leaves every other slot j below 2^d alone), `wf_array_set`, `gather_contents` (`Kernel.gather` at the U32 instance: `out[k] == src[perm[k]]` for every k < n when n <= 2^d) and `gather_keeps_perm`, `mask_not_cell` / `mask_and_cell` / `mask_or_cell` (`Kernel.map` / `Kernel.zip` slot contents: the validity combinators' truth tables slot by slot), `iota_cell` (`Kernel.iota_from`: `off + k`), `range_cell` (`Kernel.range`, the range copy behind `Column.slice` (W1f): `out[k] == a[off + k]` for every k < n when n <= 2^d; the template proof `range_tcell` is the map proof's shape with the read index `off + k`), `u32_fold_sum` / `u32_fold_keeps` (the production U32 fold with `U32.add` is the modulo-2^32 running sum of the first n cells, `FSum`), `popcount_sum` (the kept-row / valid-cell count is the sum of the mask words), `compact_contents` (`Kernel.compact_keep` at the U32 instance writes the kept rows in order at the cursor positions, `CSpec`, under the explicit precondition `CRoom`: 0/1 words and a cursor below 2^d) and `compact_keeps_mask` (data and validity stay aligned: one mask filters every buffer) |
| 12 Column cells (`PROOF_contents`) | `cell_pure` (`Column.cell(c, i) == (c, ccell(c, i))` for all five column kinds, and for a Str column both storages, Raw and Dictionary (M4: the model `scell` reads the Raw slot, or the dictionary entry of the row's code): the production cell reader is pure and reads the model `ccell`, validity then data), `head_cell` (`Column.head` keeps every cell; with `head_len` / `head_dtype` the exact prefix), `depth_for_fits` (`Kernel.depth_for(n)` gives at least n slots for n <= 2^31), `slice_cell_u32` (row k of `Column.slice(c, off, n)` is row `off + k` of c for every k below the slice's length, data and validity, on a U32 column: the exact subrange, through `range_cell`: since W1f the slice is one range copy per buffer, no iota index array and no gather) |
| 13 Evaluator typing (`PROOF_eval`, `PROOF_evalops`, `PROOF_evalrun`; plan P2, M5 part 2) | models `cdtype` / `clen` / `klen` / `skind` / `fschema` / `frame_ok` and the Type-valued `ColTy` / `ResTy` / `StkTy` / `RunTy` / `EvalTy`; purity of the readers (`len_w`, `dtype_w`, `cell_w`, `frame_height_w`, `frame_schema_w`), the P0 bridge `wf_frame_ok` (a `WFFrame` satisfies the shape facts the typing theorems assume), `get_cloned_typed` (`Frame.get_cloned` answers the frame unchanged and a copy of the column `Schema.find` names, of its dtype and h rows), `bcast_typed`, `unit_typed`; the operation laws `eval_un_typed`, `eval_bin_typed`, `eval_cast_typed` (fails exactly when `X.Cast.total` is False), `eval_try_cast_typed`, `eval_fill_typed`, `eval_when_typed`, `eval_isin_typed`, `eval_clip_typed`, `eval_strpred_typed`, `eval_agg_typed` (every operation answers a column of the dtype its typing rule in `expr.bend` gives, as long as its operand, never a failure except the strict cast); and the stack machine: `run_typed` (the postfix code `Eval.compile(e, acc)` of an expression the shared analysis `A.Expr.analyse` accepts with record (t, k, tot), run by `Eval.run` from a frame of h rows with that schema and a stack whose slots have shapes `sh`, leaves the frame unchanged and pushes one slot of dtype t and kind `skind(k)` with `klen` rows, or fails only when tot is False; by induction over the expression with the stack invariant, every Expr node), `eval_full_typed` (`Eval.full(f, e)` over a well-formed frame answers the frame unchanged and a column of the analysis' dtype with the frame's height, or a failure the analysis allowed), `eval_expr_typed` (`Eval.expr`: the same with one row for a reduction, `elen`) |
| 14 Dictionary strings (`PROOF_strs`; plan section 5 last paragraph and section 6 P1, M5 part 3) | the entry-list model `WFDictE(d, es)` (k = |es| entries fitting 2^dd slots, entry 0 `""`, every slot below k its list entry, a sound index `WFIx`: every slot empty or naming a code in range whose entry is its key); `decode_cell` (`Strs.decode` reads row i as `scell(s, i)`: decode(Dictionary) is the Raw column), `strs_gather_cells`, `strs_compact_cells` (both storages: the codes gathered / compacted read as the Raw operation's cells; the gather / compact loops of section 11 as template proofs at the String and U32 instances), `strs_clone_w` / `dict_clone_w`; `str_same_sound` / `str_same_complete` (the index's key comparison); `dict_empty_wf`; `dict_code_spec` (`Dict.code` keeps `WFDictE`, extends the entries by at most s, answers a code in range that decodes to s, and every old code keeps its entry (`Keep`), through `Dict.add` / `Dict.fit` / `Dict.room` / `Ix.seek` / `Ix.grow`); `strs_encode_cells` / `strs_encode_cell` (`Strs.encode` of a Raw column: a well-formed code array and dictionary, every row's code naming the row's string: `EncRows`; per row `scell(encode(s), i) == scell(s, i)`); `strs_raw_cell`, `column_encode_cell` / `column_decode_cell` / `column_recode_cell`, `cols_encode_cells`, `frame_encode_cells` (`DF.encode_strings` keeps the height, the names and every cell); `dict_miss_not_code`; `dict_merge_spec` (`Dict.merge`: src back, dst extended and well formed, dst's old codes keep their entries, the map re-codes every entry of src: `nthd(es2, m[c]) == dentry(src, c)`); `dict_same_sound` (`Dict.same` True only for equal entry lists); `dict_find_spec` (`Dict.find`: a miss or a sound code naming s, the dictionary back); `dict_recode_spec` (`Dict.recode`: per entry of src a miss or a code of dst naming it) |
| 15 Concatenation and the in-place kernels (`PROOF_append`, `PROOF_inplace`; plan section 6 P1, M5 part 4) | `append_cells` (`Kernel.append` = two `Kernel.copy_into` loops writing at `U32.add(off, i)`, U32 instance: a's rows below na, b's row k at na + k, the output well formed, when na + nb <= 2^d as natural numbers: `CatFits`); `strs_append_cells` (`Strs.append`, the Str storage of `Cat.col` / `concat_vertical`, both storages: two Dictionaries merge b's entries into a's and append a's codes to b's re-coded ones, any other pair decodes and appends the strings; a's cell below na, b's cell k at na + k, through `scell`); `mask_data_cell` / `mask_data_keeps_mask` (`Kernel.mask_data`, in place, U32 instance: at every pos < n the old cell where the mask word is set, z where it is 0; the mask handed back unchanged); `choose_cell` / `choose_keeps_mask` (`Kernel.choose`, in place into a, U32 instance: a's cell where the mask word is set, b's where it is 0; the mask back); `fix_cell` (`Eval.fix`, the null slots back to the default, for every column kind: Bool / U32 / I32 words, F32, Str Raw and Dictionary: `ccell` of every row is unchanged, so the reset never touches a valid slot); `fill_str_cell` (`Eval.fill` = fill_null on two Str columns, both storages: row i is a's cell where a is valid, b's cell otherwise, the Polars cell); `when_str_data` (`Eval.when.str`, the Str case of `when`: the string STORED at row i is a's where the condition mask word is set, b's where it is 0, both storages; the row's validity is not stated) |
| 16 Moves (`PROOF_moves`; v0.2 T3.1, DESIGN 16.2 rule 1, plan M_02 section 4 "projection/moves") | models `lastm` / `fcol` (the column a frame holds under a name), `hollowm` / `holed` / `holedf` (the frame with a hollow stand-in in the column's place), `nomove`, `moves_ok`; `lend_observes` (over a frame with unique names whose column named n is c: `Frame.lend(f, n) == (holedf(f, n), Done{c})`, `Frame.get_cloned(f, n) == (f, Done{c})` and `Frame.replace(holedf(f, n), n, c) == Done{f}`: the moved column IS the column the copy reproduces, and a borrow puts the frame back as it was); `mark_reads` (`Eval.mark` changes no read: the same names in the same order), `mark_moves_ok` (every `IMove{n}` it makes in move-free code is allowed, n in `dead` or `all`, and is the last read of n: no later instruction of the code and no name in `later` reads it), `compile_nomove` (`Eval.compile` emits no move), `compile_reads` (the code of e reads exactly `X.Expr.refs(e)`, in order: the list the operators pass as `later` through `Eval.refs`) |
| 17 Sort + Head (`PROOF_sorthead`; v0.2 T3.4) | the observation `robs(r, k)` (the error, or the height and per column in order its name, dtype, length and `ccell` at row k when k is a row, `SNull` past the length; `cobs` / `lobs`), `hres` (Sort then Head); `sort_head_frame` (`Sort.frame_head(f, ks, n)`, the exact full argsort then only min(n, height) rows gathered, shows at every row k what `Frame.head(Sort.frame(f, ks), n)` shows: every frame, key list, n including 0 and n past the height, errors included), `sort_head_run` (the production equivalence: `Exec.run_phys(Head{n, Sort{ks, x}}, env)`, what collect runs, shows what `Exec.run_pure` of the same plan shows (x's code, then `ISort`, then `IHead`), every plan x and env), `run_phys_obs` (the same for every plan), `collect_obs` (`run_phys(Optimize.release(p))` shows what `run_pure(p)` shows: G6 with the physical step). Inside the proof (not laws): `Column.gather` at every column kind and both Str storages as a witness (`cg_w`: the permutation back, the dtype, the length, row k the source row perm[k], from the section 11 / 14 gather theorems at U32, F32 and String) |

### 8.1 Assurance matrix (plan M_01 section 6: theorem -> production function -> assumptions -> checker)

| theorem | production function(s) it constrains | assumptions / scope | checkers |
|---|---|---|---|
| `release_run(_obs)` | `Optimize.release` (= `Opt.hmerge`, adjacent-Head merging, the whole default optimizer), `Exec.run_pure` (= `Exec.compile`, `Exec.mark`, `Exec.loop`, `Exec.step*`, `Exec.fin`), `Frame.head`, `Column.head` | NONE: every plan p (well-typed or not, every node kind, scans included) and every env (bindings are not validated by `run_pure`; `Exec.run` validates first and feeds the same env). Result equality of `E.ResT(C.Frame)`, frames included; errors included. | bend, --verdict |
| `hmerge_run`, `hmerge_keeps_sources` | `Opt.hmerge(p, n)` vs `p` with the pending limit `n` and a suffix in the hypothesis; `Exec.later` (the last-use marks) | suffixes with the same Sources that run alike; every plan | bend, --verdict |
| `hmerge_keeps_scans`, `release_keeps_scans` | `Opt.hmerge`, `Optimize.release`, `Exec.compile` (the `IScan` instructions `Exec.mat` reads and the runner's `IScan` takes from `Env.scans`) | none (all plans) | bend, --verdict |
| `head_merge_run` | the same, as the local rule, for EVERY plan x (certified or not, scans included: both sides fail alike) | none | bend, --verdict |
| `head_pass_run` | `Opt.head(p, n)` vs `p` with the pending limit `n` and a suffix in the hypothesis | `merge_only(p)`; suffixes with the same Sources that run alike | bend, --verdict |
| `head_pass_keeps_sources` | `Opt.head`, `Exec.compile`, `Exec.later` (the last-use marks) | none (all plans) | bend, --verdict |
| `frame_head_head`, `head_step` | `Frame.head`, `Cols.head`, `Column.head`, `Exec.step` | none (`U32.min` associativity from Base's Word) | bend, --verdict |
| `str_eq_refl`, `str_eq_sound` | Base `String.eq` as used by `Names.has`, `Schema.find`, `Env.take/clone`, `Exec.later`, `Opt.ren.find` | none | bend, --verdict |
| `wf_*` | `Array.new` (= `Kernel.const`, the kernels' output allocation), `Frame.empty`, `Column.head`, `Frame.head` | the P0 predicates; the other verbs' preservation is M5 (P1) | bend, --verdict |
| `array_get_pure`, `array_set_get` | Base `Array.get`, `Array.set` as every kernel calls them | none (all indices; the masking `i & (n-1)` is in the model) | bend, --verdict |
| `gather_step`, `compact_step(_cell)` | `Kernel.gather.go`, `Kernel.compact.go`, `Kernel.gather.put`, `Kernel.compact.put` | one iteration (fuel 1); U32 instance (BendTT refuses the template at a quantified type) | bend, --verdict |
| `paths_distinct`, `array_set_other`, `wf_array_set`, `rd_at_wf` | Base `Array.get`, `Array.set`, `Array.size` as every kernel calls them (the index arithmetic `i & (2^d - 1)`, `i < n/2`, `i - n/2` over Base's `Word`) | `WFArray(d, a)`; indices below `U32.shln(1, d)` (vacuous when 2^d wraps to 0, i.e. d >= 32: the row cap keeps d <= 23) | bend, --verdict |
| `gather_contents`, `gather_keeps_perm` | `Kernel.gather` = `Kernel.gather.go` + `Kernel.gather.put` (U32 instance: the word buffers of Bool/U32/I32 columns and every validity mask; the F32/String instances are the same template text, not separately stated) | `n <= 2^d` (what `Column.gather`'s `depth_for(n)` provides); indexes read through `perm` wrap as `Array.get` wraps them | bend, --verdict |
| `mask_not_cell`, `mask_and_cell`, `mask_or_cell`, `iota_cell` | `Kernel.map`, `Kernel.zip`, `Kernel.iota_from` (template loop lemmas `map_go` / `zip_go` instantiated at the mask combinators) | `n <= 2^d` | bend, --verdict |
| `u32_fold_sum`, `u32_fold_keeps`, `popcount_sum` | `Kernel.fold` with `U32.add` (`Eval.agg.w` Sum over U32, `Kernel.popcount` behind filter's kept count, `Valid.count`, `Eval.dropnull`) | none (any n; the spec `FSum` is the modulo-2^32 running sum over the first n cells; "valid cells" = the cells left after `Eval.dropnull`'s compaction, see `compact_contents`) | bend, --verdict |
| `compact_contents`, `compact_keeps_mask` | `Kernel.compact_keep` = `compact_keep.go` + `compact.put` (U32 instance), the loop behind `Column.compact`, hence `Frame.filter_mask` (filter) and `Eval.dropnull` | `CRoom(to_nat n, 0, 0, d, mask)`: every mask word is 0/1 and the write cursor stays below 2^d at each step. `Column.compact` allocates `depth_for(kept + 1)` slots, so the cursor (<= the kept count) always fits; that arithmetic ("cursor <= popcount < 2^d") is NOT yet proven, `CRoom` is the hypothesis | bend, --verdict |
| `cell_pure`, `head_cell` | `Column.cell` (= `Column.take_valid`, `Valid.get`, `Column.cell.a/b/c`, `Column.data_cell`, `Column.cell.w/f/s`, `Column.mk_w`, M4: `ST.Strs.get`, `Strs.get.r/c/d`, `Dict.get`, `Dict.get.k`), `Column.head` | none (every column, every index; the model `ccell` reads validity then data with `rd_at`) | bend, --verdict |
| `depth_for_fits` | `Kernel.depth_for` (= `depth_for.go`, fuel 32) | `n <= 2^31` (for larger n the loop runs out of fuel and answers 32, whose slot count wraps to 0; the row cap keeps n <= 2^23) | bend, --verdict |
| `range_cell` | `Kernel.range` (= `Kernel.range.go`; W1f) at the U32 instance: the data words of Bool / U32 / I32 slices, every sliced validity mask (`Valid.range`), the codes of a Dictionary slice. The F32 and String (Raw) slices run the same template loop; the template theorem `range_tcell` is generic but stated as a law at U32 only | `n <= 2^d`; the read index `off + k` is any word (`rd_at` answers what `Array.get` reads, wrapping included). Not claimed: the padding slots | bend, --verdict |
| `slice_cell_u32` | `Column.slice` (= `slice.a/b/r`, `Valid.range`, `Kernel.range`; W1f, formerly a gather by an iota index array), on `CU32` columns | `n <= 2^31`, `k < slice_len(off, n, len)`; U32 instance (Bool / I32 columns are the same word buffers and the same proof text; F32 / String need `range_tcell` at those instances) | bend, --verdict |
| `len_w`, `dtype_w`, `cell_w`, `frame_height_w`, `frame_schema_w`, `wf_frame_ok` | `Column.len`, `Column.dtype`, `Column.cell`, `Frame.height`, `Frame.schema` (= `Cols.schema`), the P0 predicates | none (every column / frame; the readers are pure and answer the models `clen` / `cdtype` / `lit_dtype` / `fheight` / `fschema`) | bend, --verdict |
| `get_cloned_typed` | `Frame.get_cloned` (= `Cols.cg.go`, `Column.clone`, `Schema.find`) | `frame_ok(h, f)` (every column h rows, unique names) and `Schema.find(fschema f, n) == Some t` | bend, --verdict |
| `eval_un_typed` .. `eval_agg_typed` (10 laws) | `Eval.un`, `Eval.bin`, `Eval.cast`, `Eval.try_cast`, `Eval.fill`, `Eval.when`, `Eval.isin`, `Eval.clip`, `Eval.strpred`, `Eval.agg` and everything they call (`Column.mk_w`, `Eval.fix`, the kernels, `Kernel.depth_for`) | the operand dtypes are accepted by the operation's rule in `expr.bend` (`Expr.type.un.ok`, `bin.ok`, `Cast.ok`, `fill`, `when.ok`, `isin.ok`, `clip.ok`, `strpred.ok`, `agg.ok`); the claims are dtype, length and totality (`ResW`): not the cells | bend, --verdict |
| `run_typed` | `Eval.compile`, `Eval.run` (= `Eval.step`, `Eval.exec`, `Eval.app1/2/3`, `Eval.do1/2/3`, `Eval.fit`, `Eval.fit_agg`, `Eval.push`, `Eval.wrap`, `Eval.unit`, `Eval.bcast`, `Frame.get_cloned`), `A.Expr.analyse` | `fschema(f) == s`, `frame_ok(h, f)`, a stack satisfying `StkTy(h, sh, stk)`, `A.Expr.analyse(e, s) == Done{Ana{t, rs, k, tot, loc}}`; every Expr node (Col, Lit, Alias, Cast, TryCast, Un, Bin, FillNull, Agg, When, IsIn, Clip, StrPred). Claims: frame unchanged, one new slot of dtype t and kind `skind(k)` with `klen` rows, failure only when tot is False. NOT claimed: cell values, that only the columns `rs` are read, the locality field `loc` | bend, --verdict |
| `eval_full_typed`, `eval_expr_typed` | `Eval.full`, `Eval.expr` (= `Eval.slot`, `Eval.slot.s/t/h`, `Eval.fin`, `Eval.mode.a/b`, `Eval.unslot`) | `WFFrame(f)` (P0) and `A.Expr.analyse(e, fschema f) == Done{..}`: the production type check `A.Ana.type` is the same analysis, so a Done answer is exactly what `Eval.filter` evaluates and, up to the moves of section 16, what `Eval.select` / `with_columns` evaluate (since T3.1 they run `Eval.slot.mv`: the same type check and `Eval.compile`'s code after `Eval.mark`; that marked code is NOT what `run_typed` is stated over, see the next row); the column has the frame's height (`Eval.full`) or `elen` (`Eval.expr`: 1 for a reduction) | bend, --verdict |
| `lend_observes`, `mark_reads`, `mark_moves_ok`, `compile_nomove`, `compile_reads` | `Frame.lend` (= `Cols.lend.go/step/k`, `Column.hollow`, `Frame.lend.k`), `Frame.get_cloned` (= `Cols.cg.go`, `Column.clone`), `Frame.replace` (= `Frame.info`, `Cols.names`, `FInfo.shape`, `Cols.replace.go/step/pick`, `Frame.replace.d`), `Eval.mark` (= `mark.i`, `mark.c`), `Eval.reads`, `Eval.compile` | lend: `frame_ok(h, f)` (unique names, every column h rows) and `fcol(f, n) == Some{c}`; mark: move-free code (what `Eval.compile` emits). NOT claimed: that the marked code computes the same stack as the unmarked one, i.e. a typing / equivalence theorem for `Eval.slot.mv` (`select`, `with_columns`, `Eval.full_mv` / `expr_mv`). The argument is the composition of these laws (a move answers the very column the copy reproduces, stand-ins keep `fschema` and `frame_ok`, and nothing reads a stand-in) plus tests and the differential; the step-by-step equivalence over `Eval.run` is open | bend, --verdict |
| `decode_cell`, `strs_gather_cells`, `strs_compact_cells`, `strs_clone_w`, `dict_clone_w` | `Strs.decode` / `Dict.decode`, `Strs.gather`, `Strs.compact`, `Strs.clone` / `Dict.clone` (= `Strs.out.r/d`, `Strs.clone.r/d`, `Dict.clone.k`, `Kernel.gather` / `Kernel.compact_keep` at the String and U32 instances), i.e. the Str case of `Column.gather.data`, `Column.compact.data`, `Column.clone.s` (since W1f `Column.slice` range copies a Raw array or a Dictionary's codes directly, `Column.slice.s`: the template loop of `range_cell`, the Str instance not separately stated) | `n <= 2^d` (gather / decode), `CRoom` (compact, as section 11); no dictionary invariant needed (codes move unchanged) | bend, --verdict |
| `str_same_sound`, `str_same_complete`, `dict_empty_wf`, `dict_code_spec` | `Str.same`, `Dict.empty`, `Dict.code` (= `Dict.code.h/k/p`, `Dict.add`, `Dict.fit`, `Dict.fit.k`, `Dict.room`, `Dict.dd`, `Dict.mix`, `Ix.seek` / `Ix.seek.go` / `Ix.look` / `Ix.id`, `Ix.grow` / `Ix.grow.go` / `Ix.move` / `Ix.move.k`), the index's `Array.set` / `Array.get` | `WFDictE(d, es)`; fewer than 2^30 entries (the row cap keeps every dictionary far below); the PROBE HYPOTHESIS `Probe(d, s)`: the hash probe for s stops at a slot that is empty or holds s (production guarantees it by the load factor <= 1/2 and the pairwise distinct entries; this termination argument is not proven: the probe's answer is taken as given and shown sound). `Str.hash` is only used as a deterministic function | bend, --verdict |
| `strs_encode_cells`, `strs_encode_cell`, `strs_raw_cell`, `column_encode_cell`, `column_decode_cell`, `column_recode_cell`, `cols_encode_cells`, `frame_encode_cells` | `Strs.encode` (= `Strs.encode.raw`, `Enc.go`, `Enc.step`, `Enc.put`, `Enc.fin` over `Dict.code` from `Dict.empty`), `Strs.raw`, `Column.encode` / `decode` / `recode`, `Cols.encode`, `Frame.encode` (= `DF.encode_strings`) | `n <= 2^d`, `n < 2^30`, the probe hypotheses along the loop (`EncProbe`: row i against the dictionary built so far); claims: the Dictionary's code array and dictionary are well formed and every row below n decodes to the Raw row (`EncRows`; per row `scell`, hence `ccell` with validity untouched) | bend, --verdict |
| `dict_miss_not_code`, `dict_merge_spec`, `dict_same_sound`, `dict_find_spec`, `dict_recode_spec` | `Dict.miss`, `Dict.merge` / `Dict.recode` (= `Dict.rc`, `Dict.rc.go/step/op/put/fin/fin2` over `Dict.code` / `Dict.find`), `Dict.same` (= `Dict.same.k/u/t/v/w/go/fin`, `Dict.size`, `Dict.tag`), `Dict.find` (= `Dict.find.k`) | `WFDictE` of the dictionary looked up; `k <= 2^dd` of the source; the probe hypotheses along the loop (`MergeProbe` also carries the entry bound at every step, `FindProbe`); `dict_same_sound` needs nothing. Claims: the map re-codes every entry of src (merge: into the extended dst whose old codes keep their entries; recode: a miss or a code of dst naming the entry); `Dict.same` True implies equal entry lists. NOT claimed: index completeness (that every entry IS found: `Dict.find` is shown sound, never complete), so a Dictionary equality that answers "not equal" on a miss is tested, not proven | bend, --verdict |
| `append_cells` | `Kernel.append` (= `Kernel.copy_into` twice, `copy_into.go`) at the U32 instance: the word buffers of Bool / U32 / I32 columns in `Cat.col`, every validity mask of `Cat.valid` (after `C.Valid.materialize`), the codes of a Dictionary in `Strs.app.m`. The F32 buffer of `Cat.col` is the same template loop, not separately stated | `CatFits(na, nb, d)`: na + nb <= 2^d as natural numbers (`Cat.join` allocates `depth_for` of the saturating height sum, so the sum never wraps in production; that allocation step is not itself a theorem). Claims: rows below na are a's, row na + k is b's row k for k < nb, the output is `WFArray(d)`. Not claimed: the padding slots, `Cat.col` / `Cat.cols` / `Cat.join` / `concat_vertical` as column or frame cell theorems | bend, --verdict |
| `strs_append_cells` | `Strs.append` (= `Strs.app.m`, `Dict.merge`, `Kernel.gather` over the merge map, `Kernel.append` at U32 and String, `Strs.decode`) | `na <= 2^da`, `nb <= 2^db`, `CatFits(na, nb, d)`, and `AppendHyp`: for two Dictionaries `WFDict` of a's dictionary, b's entry count within its slots, both code arrays in range (`CodesBelow`), and the PROBE HYPOTHESES of the merge (`MergeProbe`, as `dict_merge_spec`); nothing for the other storage pairs. Claims: `scell` of every row below na + nb (a's then b's) | bend, --verdict |
| `mask_data_cell`, `mask_data_keeps_mask` | `Kernel.mask_data` (= `mask_data.go`, in place) at the U32 instance; the template proof (`mask_data_w`) is also used at F32 and String inside `fix_cell` | `WFArray(d, a)`, `n <= 2^d`, `pos < n` (cell law); the mask law needs nothing. Claims: slot pos holds `m[pos] != 0 ? a[pos] : z`; the mask comes back unchanged | bend, --verdict |
| `choose_cell`, `choose_keeps_mask` | `Kernel.choose` (= `choose.go`, in place into a) at the U32 instance: behind `Eval.fill.t` (fill_null's data), `Eval.when.v` (when's data), `Eval.when.valid` (when's chosen mask) and the Dictionary branches through `Eval.zd.map` | `WFArray(d, a)`, `n <= 2^d`, `pos < n`; the mask law needs nothing. Claims: slot pos holds `m[pos] != 0 ? a[pos] : b[pos]`; the mask comes back unchanged | bend, --verdict |
| `fix_cell` | `Eval.fix` (= `Eval.fix.w/w2/f/f2/s/s2`, `Column.mk_w`, `Kernel.mask_data` at U32 / F32 / String, `Strs.fix`, `Strs.out.r/d`): every arithmetic / cast / clip / string-conversion result passes through it | `FixHyp(c, i)`: len <= 2^depth, i < len, the data buffer (or a Dictionary's code array) well formed. Claims: `ccell(Eval.fix(c), i) == ccell(c, i)` for every column kind and both Str storages. Not claimed: that the null slots now hold the default (the P0 invariant `WFMaskedW/T` after fix is not stated) | bend, --verdict |
| `fill_str_cell` | `Eval.fill` on two `CStr` columns (= `Eval.fill.str`, `Eval.fill.sd/sd2`, `Eval.fill.s`, `Eval.fill.t/t2`, `Kernel.choose` at U32 and String, `Kernel.mask_or`, `Dict.merge`, `Eval.zd.map`, `Strs.decode`) | `FillHyp`: n <= 2^d, i < n, a's data well formed, both mask words at i are 0/1 (`Mask01`), and for two Dictionaries `FillDictHyp` (`WFDict` of a's dictionary, b's entries within its slots, both codes at i in range, `MergeProbe`). Claims: the result is `Done` and its `ccell` at i is a's cell where a is valid, else b's (validity and string). Not claimed: fill_null over Bool / U32 / I32 / F32 columns as a cell law (same `Eval.fill.t`, kernel covered by `choose_cell` / `mask_or_cell` at U32 only) | bend, --verdict |
| `when_str_data` | `Eval.when.str` (= `Eval.when.sd/sd2`, `Eval.when.s`, `Kernel.choose` at U32 and String, `Dict.merge`, `Eval.zd.map`, `Strs.decode`) | `WhenHyp`: n <= 2^d, i < n, a's data well formed, `FillDictHyp` for two Dictionaries. Claims: the stored string at row i (`sdata`, validity ignored) is a's where m[i] != 0, else b's. Not claimed: the row's validity (`Eval.when.valid`: the chosen mask, `Kernel.popcount`, AllValid when every row is valid), the condition mask `Eval.when.c` ("true and valid"), `when` over Bool / U32 / I32 / F32 columns as a cell law | bend, --verdict |
| `sort_head_frame` | `Sort.frame_head` (= `Sort.fh.b/c/a`, `Sort.gather_head`, `Sort.gh.k`, `Sort.gcols` / `Sort.gather.k` at the cut min(n, h), `Column.gather` and below), against `Sort.frame` (= `Sort.frame.b/c/a`, `Sort.gather`) then `Frame.head`; `Sort.miss`, `Sort.argsort` and the whole T3.2 pipeline are shared by both sides, so the law does NOT depend on the sort's correctness (the order is v0.1's by construction, tested) | none (every frame, key list, n, row k). Observational (`robs`), not term equality: the bounded result's buffers are smaller than the full gather's, which `Frame.head` keeps; for a height over 2^31 (never: the row cap is 2^23) `Sort.gh.k` falls back to the full gather then head, so no `fits` hypothesis is needed | bend, --verdict |
| `sort_head_run`, `run_phys_obs`, `collect_obs` | `Exec.run_phys` (= `Exec.run_phys.h`, `Exec.sorthead/.r/.s`), what `Exec.run` (hence collect / collect_raw) executes, against `Exec.run_pure` (`Exec.compile`, `Exec.mark`, `Exec.loop`, `Exec.step*`, `Exec.fin`); `collect_obs` composes with `release_run` | none (every plan, env, row k; a malformed stack fails alike). The physical step is only taken at the ROOT (`Head{n, Sort{ks, x}}` as the whole plan); a Head over Sort deeper in a plan runs ISort then IHead | bend, --verdict |
| sections 1-5b (schema, typing, plan schema, optimizer schema level, slots) | as listed in the table above | as stated per law | bend, --verdict |

What the release chain does NOT cover, stated exactly:

- `Optimize.release` is `Opt.hmerge` (adjacent-Head merging) and nothing else since M5
  part 2 (the P3 fallback): `release_run` covers EVERY plan, so no plan is outside the
  theorem. The analysis-certified Head sink (R3) moved to `optimize_full` (`Opt.head`),
  which is opt-in and outside the guarantee; so are R2 (filter merge), R4 (pushdown) and
  R5 (projection). Their soundness is tested (regressions, the differential generator),
  not proven. Re-enabling the sink in the release optimizer needs R3 as a theorem: the
  P2 typing theorems give the dtype and height of every `Eval` result, but a sunk Head
  changes buffer depths, so `Eval.select(Frame.head(f, n), es)` equals
  `Frame.head(Eval.select(f, es), n)` only observationally (through `DF.dump` /
  `Column.cell`), which needs cell-level theorems for every `Eval` operation.
- `Exec.run_pure` is the runner after validation and scan materialisation; the
  theorem quantifies over any env, so it covers the validated env `Exec.run` hands over,
  scan frames included: since the v0.1 review (section 14 "v0.1 review: scan source
  identity") the scans' frames sit in env's unnamed scan namespace and `run_pure` runs the
  plan itself (no ScanCsv -> Source rewrite), so `release_run` speaks about scan plans
  directly, and `release_keeps_scans` proves that the optimised plan materialises the same
  scans in the same order. Still not machine-checked between `collect` and `collect_raw`:
  that `Plan.schema` and `Exec.validate` answer alike for `Optimize.release(p)` and p
  (true by inspection: `Opt.hmerge` only merges Heads and keeps every Source with its
  schema; `hmerge_keeps_sources` covers the names, not the schemas). The IO reads
  themselves (`Csv.read_with`) are outside the proof (plan M_01 section 6 "IO boundary"),
  and so is the materialisation step `Exec.mat` as a whole (it reads each scan with
  `Csv.read_with`, checks the frozen schema and hands the frames to the runner in postfix
  order). What `release_run` covers exactly, then: `Exec.run_pure(Optimize.release(p), env)
  == Exec.run_pure(p, env)` for every plan p and every env, scan plans included (through
  env's `scans` field), plus `hmerge_keeps_scans` / `release_keeps_scans` (same `IScan`
  instructions, same order). What `collect` adds around it and nothing machine-checks: the
  `Plan.schema` / `Exec.validate` agreement just named, and `Exec.mat` (plans/REVIEW_V01_FABLE.txt
  H1).
- Two typers exist. The 20 expression-typing laws of LAWS section 2 (group 2 in the table
  above) are about `X.Expr.type`, which production uses only for `group_by`; `select`,
  `with_columns` and `filter` type their expressions through `A.Expr.analyse` (the shared
  analysis), which the P2 theorems (`run_typed`, `eval_full_typed`, `eval_expr_typed`) cover
  (plans/REVIEW_V01_FABLE.txt H3). The gap is in the older laws' relevance, not in the
  soundness of the evaluator typing.
- The evaluator typing theorems (`run_typed`, `eval_full_typed`, `eval_expr_typed`)
  state dtype, height, the frame coming back unchanged and "fails only where the
  analysis says it may". They do not state cell values, that only the `refs` columns are
  read, or the locality field of the analysis record (the parts of the soundness
  statement in `src/analysis.bend`'s header that the release optimizer no longer relies
  on).

Not provable or not true as stated, recorded here instead of as open laws:

- `Plan.schema(Plan.optimize_full(p)) == Plan.schema(p)`: pushdown and
  projection rename through `Names.has` / `Opt.rename`; with `str_eq_refl` /
  `str_eq_sound` now proven the blocker is gone, but `optimize_full` is opt-in
  and outside the guarantee, so these laws are not scheduled.
- `Opt.merge` does NOT keep the schema of an ill-typed plan (the error text
  differs); hence the `Plan.schema(p) == Done{s}` hypothesis.

**Not proven, tested only (the exact list for v0.1).** Everything below runs in production and
is covered by tests (`make test`, the differential generator `make diff` in Raw and
Dictionary mode, `make diff-reduce`, the goldens of `make bench-check`), not by a law:

1. Hypotheses the string laws take instead of deriving them: the PROBE HYPOTHESIS (`Probe`,
   `EncProbe`, `MergeProbe`, `FindProbe`: the hash probe for a key stops at an empty slot or at
   the key; production guarantees it by the load factor <= 1/2 and pairwise distinct entries,
   not proven), the per-step entry bound inside `MergeProbe`, `CRoom` of `compact_contents`
   (not derived from "cursor <= popcount < 2^d", what `Column.compact`'s `depth_for(kept + 1)`
   gives), `CatFits` of `append_cells` (not derived from `Cat.join`'s allocation), and the
   connection of the P0 `WFStrs` / `WFDictCodes` of an encoded column with the finer
   `WFDictE` / `WFDict` the string laws use.
2. Dictionary index COMPLETENESS: `Dict.find` / `Dict.recode` are proven sound (a hit names
   the key), never complete (every present entry is found). So everything that answers "not
   equal" or "absent" on a miss is tested only: `Dict.same` answering False, `Eval.zd.eq.*`
   (Str `==` / `!=` over two Dictionaries), and the entries' pairwise distinctness.
3. Per-entry maps over a Dictionary: `Strs.map` / `Strs.map_p` / `Dict.map.*` / `Dict.mp.t` /
   `Dict.mm.*` (string predicates `contains_literal` / `starts_with` / `ends_with`, `len_chars`, `is_in` on
   a Str column: computed once per entry, then gathered by code).
4. Rank order of a Dictionary: `Rk.dict` (src/ranks.bend, the v0.2 rank stage: `Rl.*`, `Rw.*`,
   `Pb.*`, `Rf.*` / `Rq.*`, `Rx.*`, `Rg.*`, `Rk.*`; v0.1's Base-Map `Dict.ranks` until W2.3, now only a
   test reference in tests/lib/v01str.bend), `Sort.dict_words`, `Sort.kd*`, `Eval.zd.ord.*`, `Eval.ds.ext*`
   (Str `<` / `<=` / `>` / `>=`, sort keys over Dictionary codes, min / max).
5. Str evaluators beyond fill_null and when's storage: comparisons (items 2, 4), string
   predicates and `len_chars` (item 3), casts to and from `str`, `is_in`, and `when`'s
   validity (`Eval.when.valid`); and over every dtype, the cell values of the evaluator: the
   typing theorems (section 13) give dtype, height and totality, and `fix_cell`,
   `fill_str_cell`, `when_str_data`, the mask combinators and `u32_fold_sum` give the cells of
   those operations only. Arithmetic, comparison, cast, clip, is_in, reductions and the
   broadcast of a 1-row side have no cell law; nor do fill_null / when over Bool / U32 /
   I32 / F32 columns at the column level.
6. The CSV builders: the reader, the streaming pieces, type inference, `EncAuto` /
   `EncAutoAt` (the readers' Dictionary choice and building through `Dict.code`, i.e. the
   per-row encoder of section 14 is proven, its use inside `src/csv.bend` is not), the writer
   and every round trip; IO in general (plan section 6 "IO boundary").
7. group_by and join: the group encoders (`Grp.codes`, `Grp.enc.*`, `Grp.rank` / `Grp.prank`,
   `Grp.densify`, also behind `unique`; a Raw string key is coded by the packed flat coder
   `Hc.code.pk`, src/hcode.bend, since W2.3: `Hc.*`, with its own probe hypothesis "the probe for s stops at a
   slot that is empty or holds s", stated in the file's header, not a law, as v0.1's Base-Map
   coder had none either), Raw n_unique (`Eval.nu.str`, the same coder's entry count), the grouped scatter accumulators (the plan's "per-group
   invariant for count and U32 sum given valid group ids" was not reached), the aggregations,
   the hash join (`src/join.bend`'s own `Dict`, `Probe`, `Dense`), semi / anti, and the
   partition correctness of both. Sort: the stable LSD radix argsort and its order words
   (`Sort.*`, `Radix.*` / `WS.*` in src/radix.bend since W2.3), including stability; the order
   words of a Raw string key (`Rk.words` = `Hc.code.fnv` then the rank stage, item 4).
8. Floats: every F32 result (Neumaier sums, mean, std / var / median, describe quantiles,
   the 15.5.2 order words, casts, `F32.show` / `F32.read`). Checked against an exact or f64
   reference with the T2.3 bound (`make diff-reduce`), not proven.
9. `optimize_full`'s rewrites R2 (filter merge), R3 (the certified Head sink, `Opt.head`),
   R4 (predicate pushdown), R5 (projection pushdown) as result-preserving theorems, and the
   composition of its passes; the `refs` / locality fields of the analysis record. The
   default optimizer does not use any of them.
10. Column and frame level: `Column.gather` / `Column.compact` as cell theorems for every
   kind (section 11 proves the kernels at U32; the F32 / String instances are the same
   template text, BendTT refuses a law at a quantified cell type, and only the Str storage
   is stated at String in section 14), `Column.slice` on F32 / String columns, `Cat.col` /
   `concat_vertical` as a frame cell theorem (its buffers are `append_cells` /
   `strs_append_cells`), `filter` / `head` / `select` / `with_columns` / the table verbs as
   frame cell theorems (`Column.head` has `head_cell`; frames appear only as both sides of
   `release_run` / `frame_head_head`), and the
   preservation of the P0 well-formedness predicates by every verb other than `head`.
(Not true as stated, hence not laws at all: the two items listed just above this list.)

What IS proven of the above areas, for contrast: the code-moving kernels in both string
storages (gather, compact, clone, decode), `Dict.code` / `Strs.encode` / `Dict.merge` /
`Dict.recode` / `Dict.find` (sound) / `Dict.same` (True is sound) / `Dict.miss`,
`DF.encode_strings`, concatenation's buffers in both storages (`append_cells`,
`strs_append_cells`), `Eval.fix` for every column kind, fill_null on Str columns in both
storages, when's Str storage, and the typing of every Expr node.

Proof toolkit (verified in PROOF_*.bend; see PROOF_lib.bend's header): unfold
one step with `{==}`; `%e : P` with `e : {a == b}` rewrites a goal that is
`P[_ := b]` into `P[_ := a]` (so to replace a term X in the goal by Y, use
`e : {Y == X}` with `_` at X: flip computed-term hypotheses with `Equal.sym`
first); `Done`/`Some` injectivity via `Equal.cong` + `Result.default`/
`Maybe.default`; refute `Fail == Done`, `False == True`, `LT == EQ` etc.
through a motive and `Empty.absurd`; a value the code computes is passed to a
lemma as a PARAMETER and matched there (p08); a hypothesis that must be
rewritten moves into the goal as `H -> G`; a schema rule over an input result
is abstracted as a function parameter (`unary`); Type-kinded values (arrays,
columns, frames, runner states) are affine: a lemma takes one once, and a lemma
that rewrites one hands it back as a Sigma witness beside the equations
(`&b: Array<T> -> {.. == b} & {..}`, `col_head_w`, `head_step_w`, `size_same`,
`swap_rd`); a computed witness is taken apart only in a helper's PARAMETER,
never in a let; two codes run from ONE state by a parallel induction that
consumes the state once and carries a continuation hypothesis for the suffix
(`loop_pre`, `head_pass_run`); Word lemmas are inductions over the word length
with the tails' comparison as a parameter; template kernels are proven by
template proof defs, and a law about a template is stated at a concrete
instance when `--verdict` must accept it.


**G6 claim (final for v0.1, 2026-10-09; decided after M2, scoped after M5 part 2, buffer laws
completed in M5 part 4).** The default optimizer `Optimize.release` is adjacent-Head merging
(`Opt.hmerge`) and nothing else, and its result-equivalence theorem over the production runner
(`release_run`, `release_run_obs`, checked by `bend` and `--verdict`) holds for EVERY plan and
every environment, with no admissibility hypothesis: `Exec.run_pure(Optimize.release(p), env) ==
Exec.run_pure(p, env)`, frames and errors included, hence equal `DF.dump` text. The evaluator is
proven type-sound (`eval_full_typed`, `eval_expr_typed`, `run_typed`): over a well-formed frame,
an expression the shared analysis accepts evaluates to the frame unchanged and a column of the
predicted dtype and height, failing only where the analysis marks it fallible (a strict cast of
a fallible pair). The buffer / column / string value laws of section 6 exist as scoped in the
table above (P1: gather, compact, map / zip mask combinators, iota, the U32 fold and popcount,
head / slice / cell, append, mask_data, choose; `Eval.fix` for every column kind; fill_null and
when's storage on Str columns; the Dictionary storage's decode-preserving operations), under the
hypotheses listed in 8.1. What is tested but not proven is the numbered list above (cell values
of the evaluator in general, group_by / join / sort, CSV, floats, the opt-in `optimize_full`).
README and release notes state G6 only through the plan's release claim (plan M_01 section 0):
"a result-preserving default optimizer under documented input and runtime assumptions", with
"the default optimizer only merges adjacent Heads; `optimize_full` is tested, not proved" next
to it. The fallback's cost on the benchmark: nil for the plans as written (no q1-q6 plan has a
Head above a Select/WithColumns, tests/plan_release_bench.bend); against `optimize_full`'s
pushdown it is 4-5 ms on q1 and q5 at 1M rows and nothing elsewhere (bench/README.md
"optimize_full vs the default optimizer").


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
 - `LICENSE` (`SPDX-License-Identifier: Apache-2.0` first line; MIT until 2026-10-10), `README.md` with
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
4. **NEW-2, CSV (fixed in the M1 cleanup)**: `Csv.read` of `bench/data/sales_100000.csv` and
   `Csv.render` / `write_csv` of >= 2^15 rows overflowed the interpreter (`Csv.conv`, `Csv.rec_lines`,
   `Csv.cells`, `Csv.zip`, `Csv.zip_pre`, `List.replicate`, `String.concat` in `Csv.render.t`,
   `List.length` over records). Now: tail loops where the loop is cold (`Csv.take_rows`,
   `Csv.drop_blank`, `K.Kernel.count` for lengths, `Csv.nls`), and a 16-rows-per-call recursion on the hot
   per-cell / per-row loops (a plain accumulate-and-reverse loop cost ~30% of the native parse, and the
   rest of the write ~20%; native parse of sales_100000.csv is unchanged within 2%, the 1M-row write
   +8%). The interpreter reads the 100k file in ~2.6 s (dump FNV equal to Polars') and rewrites it
   byte for byte; csvparse.bend's walk was already a tail call. A separator String dup'd per row
   (`zip_pre(.., +pre: String)`) overflowed regardless: `Csv.zip_pre` takes the separator as a U32.
   Capacity of the interpreter is now ~500k rows per column (depth n / 16).
5. Tests: `tests/regress/NEW_1_static_checks_first.bend`, `tests/regress/NEW_2_interp_large_results.bend`
   (specs of the same names in `bench/contract/regress_expect.py`; NEW-2's expected dump summaries
   are computed there from a plain-Python join); `tests/diff/d0001.bend`, `d0002.bend` lost
   `#! xfail NEW-1`. CSV: `tests/regress/NEW_2_interp_csv_large.bend` (50,000 rows rendered, written,
   read back eager / raw / opt; spec `NEW_2_interp_csv_large` builds the CSV text and the dump in Python).

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
2. **15.5.4's quoted `std [1,2,4] = 1.5275252`, `var = 2.3333333` were the correctly rounded values**;
   the specified algorithm and Bend give 1.5275253 / 2.3333335 (1 ulp above, inside the bound). 15.5.4
   now says so (algorithm = contract); r0006 pins the algorithm's value.
3. **describe's min and max were not the 15.5.2 min/max (fixed, NEW-T23-1/2)**: `describe` of `[NaN, 1, 2]`
   answered max `NaN` and of `[0.0, -0.0]` min `0.0` (min/max and Polars 2.0.0: `2`, `-0.0`), because it read
   its extremes off the stable NaN-greatest sort. `Fmt.describe` now takes min and max from
   `Eval.agg Min/Max` (K.Kernel.fmin/fmax). Its quantile rows stay the sort's nearest rank, which IS
   Polars' `describe` (`interpolation="nearest"` is its default; checked with 2.0.0: `[1,2,3,4]` gives
   25% 2, 50% 3, 75% 3): describe's "50%" is therefore not the 15.5.4 `median` for an even count
   (2.5 for the same data); that is intended, and documented in src/fmt.bend. `std` of a constant
   column is not 0 (see IMPLEMENTING.md).
4. `Std/Var/Median` AggOps do not exist yet; the checks for them are in `reduce_ref.py`/`reduce.py` and
   switch on when `frame.bend` defines `DF.std`, `DF.var`, `DF.median`. describe's "50%" is the nearest
   rank, not the 15.5.4 median for even counts (see 3; checked as the nearest rank).

### M2 (proof feasibility: P0, name equality, Exec.run_pure, R1)

1. **Exec is factored into IO scan materialisation plus a pure runner** (plan M_01
   section 6 P2). `Exec.loop` is a pure, structural loop over the compiled code
   (`Exec.step` / `Exec.step.r` / `Exec.step.pure`); `Exec.run_code(code, env)` and
   `Exec.run_pure(p, env)` (= compile, mark, run) are the ONE physical runner, and
   the proofs of LAWS.bend section 8 quantify over `Exec.run_pure`. `Exec.run` =
   `Plan.schema`, then `Exec.validate`, then `Exec.mat` (reads every `ScanCsv` of the
   compiled code in postfix order with `Csv.read_with`, checks the frozen schema with
   the same text as before, binds the frame in env under `"#scan<k>"`), then
   `Exec.run_pure(Exec.unscan(p, 0), env)` where `Exec.unscan` replaces each `ScanCsv`
   by `Source{"#scan<k>", s}` (a Join's left scans first, as `Exec.compile` orders
   them). 4.14's "ScanCsv -> Csv.read at its position" is therefore no longer literal.
   **Superseded** by "v0.1 review: scan source identity" below: the frames go to env's
   unnamed scan namespace and the plan is not rewritten (no `"#scan<k>"`, no `unscan`).
2. **Error order with scans changed**: every scan is read before any operator runs, so
   an `IoError` / `ParseError` / frozen-schema error of a scan is reported even when an
   operator that `Exec.compile` orders earlier would have failed (before M2 the earlier
   operator's error won and the file was never read). Static (`Plan.schema`) and
   binding (`Exec.validate`) errors still come first. No existing test observed the
   old order; 15.2.8's "static error first, then bindings, then execution" still holds
   with "execution" now meaning "scans, then the pure run".
3. **Reserved names** (**withdrawn**, it was a silent wrong result: v0.1 review P1, see
   "v0.1 review: scan source identity" below): `"#scan0"`, `"#scan1"`, ... were the
   materialised scans' Source names; a user frame registered under such a name was
   shadowed by the scan during that collect (Env.add prepends). No name is reserved now.
4. **`Exec.run_pure` on a plan that still holds a `ScanCsv`** answers
   `InvalidOperation{"exec: scan_csv not materialised: <path>"}` (it cannot do IO);
   production never hits it (`Exec.unscan` runs first), and the R1 theorems cover it
   trivially (both sides fail alike). Since the v0.1 review this is the answer only when
   env's scan namespace has no frame left for the `IScan` (production fills it first).
5. **Name equality decision (P0)**: the spike CLOSED. `String.eq` reflexivity and
   soundness are proven from Base's `String.cmp` / `Char.cmp` / `Word.cmp` by
   induction over the 32-bit word (LAWS 7 `str_eq_refl`, `str_eq_sound`), so the
   runtime lookups keep `String.eq` and no local `Str.eq` exists in src. Base's
   `U32.min` is proven commutative and associative the same way (`u32_min_comm`,
   `u32_min_assoc`), which is what two Heads in a row compute.
6. **P0 predicates are Type-valued and live in LAWS.bend section 9**, not in src:
   `WFArray`, `WFWords`, `WFMaskedW/T`, `WFValidW/T`, `WFColumn`, `WFColumnH`,
   `WFCols`, `WFFrame`. What Bend cannot hide: there is no module privacy, so
   `CU32{..}`, `Frame{..}`, `ALeaf`/`ANode` can be written by any importer; building
   columns, frames or arrays directly is UNSUPPORTED and outside every law. Supported
   constructors are `Column.from_scalars`, `Csv.read*`, `Frame.from_columns`,
   `Frame.put/replace` and the verbs; of these only `Array.new` (every kernel's output
   allocation), `Frame.empty`, `Column.head` and `Frame.head` carry a proof so far (M5
   covers the rest, P1). Proofs of `WFColumn(c)` are evidence terms, not runtime checks:
   nothing in src computes them.
7. **R1 is proven as two theorems plus a corollary** (LAWS 8): the rule
   (`head_merge_run`, every plan) and the pass on the merge-only fragment
   (`head_pass_run`, hence `release_merge_only(_obs)`: `Optimize.release` preserves
   `Exec.run_pure`'s result for every well-typed plan whose Select/WithColumns are all
   Head barriers). The sink through a certified node (R3) is NOT covered; see section
   8 "What the R1 chain does NOT cover".
8. **Gather / compact contents (P1, the M2 part)**: `array_get_pure`, `array_set_get`
   and the one-step `gather_step` / `compact_step(_cell)` are proven over the real
   Array code; the full "out[i] == in[index[i]]" and subsequence theorems need the
   distinct-paths bit-vector lemma (section 8). The step laws are stated at the U32
   instance because BendTT's `--verdict` kernel refuses a template kernel applied to a
   quantified cell type ("mismatch between the TypeScript implementation and the
   formalized BendTT kernel"); the TypeScript checker accepts the generic form.
9. **PROOF.bend is split** into `PROOF_lib/schema/expr/plan/kernels/exec.bend`;
   `PROOF.bend` only imports them. `tests/proof_negative/mask_not_slots_doubled.bend`
   imports `PROOF_kernels.bend` for its lemmas; the new
   `tests/proof_negative/head_rule_outer_wins.bend` is the T5 mutation of the head rule.

### M3 table verbs (drop, rename, slice, tail, unique, concat_vertical, semi / anti)

Code: `src/table.bend` (`TV`: one static rule `<Verb>.schema` per verb, shared by
`Plan.schema` and the eager run, and one frame function `<Verb>.run` / `Concat.two`, shared
by the facade and Exec), `src/join.bend` (`Semi{}` / `Anti{}`, `Join.schema.how`,
`Join.semi`), `Kernel.append`. Plan nodes `Drop`, `Rename`, `Slice`, `Tail`, `Unique` compile
to ONE instruction `ITable{TOp}` (so a proof's Instr case split grows by one case, not five);
`Concat` to `IConcat{i}`.

1. **Concat is a chain of binary nodes, not `Concat{inputs: List<&2, Plan>}`.** A def that
   recurses through a `List<&2, Plan>` field (`f(Many{t})` after matching `Many{h <> t}`)
   passes `bend` (the TypeScript checker sees a smaller term) but `--verdict` answers
   "mismatch between the TypeScript implementation and the formalized BendTT kernel", and
   `PROOF.bend` imports plan.bend. So the node is `Concat{index: U32, left: Plan, right:
   Plan}`: `lazy_concat_vertical([p0, .., pk])` (`P.Lazy.concat`) builds `Concat{k, ..
   Concat{2, Concat{1, p0, p1}, p2} .., pk}` (`right` is input `index`, `left` holds inputs
   0 .. index-1); one plan is itself; `[]` is `Concat{0, Source{"", []}, Source{"", []}}`,
   whose schema is the static error `"concat_vertical: no inputs"` (`validate_bindings` of
   that plan alone would name the dummy source "": it is never reached through `collect`).
   `explain` prints a chain as one `CONCAT` with every input below it; a concat used as an
   input of another prints its own `CONCAT` (the index tells the two apart).
2. **Static error order of a lazy concat is input by input**: input i's own errors, then
   its schema against input 0's, then input i + 1 (postfix over the chain). An n-ary
   reading (every input's errors first, then the first differing input) is not available
   without the list node: a binary step cannot tell a later input's own error from an
   earlier mismatch. The eager facade `DF.concat_vertical(fs)` takes frames (no input
   errors), so the two agree whenever the inputs are valid; the differential generator's
   eager wrapper (`DX.e_concat_vertical`), the model (`model.concat_schema`) and the oracle
   follow the same input-by-input order. All static checks still precede every runtime
   error (15.9).
3. **Row cap of concat**: each binary step checks the saturating sum of its two heights
   (`TV.Cat.sat`, 2^32 - 1 instead of a wrap) with `Kernel.check_rows` before building
   anything, so the error names the FIRST prefix of inputs whose summed height passes 2^23
   (`[8388600, 9, 5]` reads 8388609, `[8388600, 8, 5]` 8388613). The eager `concat_vertical`
   checks every schema first, then folds the same step, so it reports the same prefix
   (tests/table_concat_cap.bend).
4. **Rename pairs are `Sigma<&2, &2, String, x => String>`**, written `("a", "b")` (alias
   `DF.RenamePair()` for annotations): 15.2.3's `List<&2, String & String>` does not
   typecheck, `A & B` is a Type ("expected Data / observed Type") and a Plan field must be
   Data. Rename's checks run in the order 15.2.3 lists them: ColumnNotFound{from} (list
   order), DuplicateColumn{from} (a from named twice), DuplicateColumn{name} (first repeated
   output name in frame order).
5. **`Plan.schema.join` takes `how`** (semi / anti answer the left fields after the same key
   checks: `J.Join.schema.how`); the proofs' `binary` lemma gained the parameter, and
   `binary_concat` / `pass_concat_rs` are its Concat copies.
6. **Optimizers**: every new node is a barrier in `Optimize.release` and in all four
   passes of `optimize_full` (merge and the head pass recurse into the inputs; pushdown
   re-wraps the pending conjuncts above the node; projection needs every input column below
   it). Semi / anti stay `Join` nodes and inherit the join's rules: projection may keep a
   right non-key column it does not need (harmless).
7. **Analysis**: the table verbs take no expressions, so `src/analysis.bend` is unchanged;
   their static rules are pure schema functions.
8. `unique` reuses group_by's key codes (`G.Grp.codes`, `G.Grp.densify` over clones of the
   key columns) and gathers every column at the groups' first rows; a frame with no
   columns keeps `min(h, 1)` rows (C24). `slice` with `start = 0` is `Frame.head` (no copy);
   otherwise every column is gathered.

### M3 expressions (when, is_in, clip, is_between, strings, std / var / median)

1. **Node shapes as frozen in 15.2.6**: `When{c, a, b}`, `IsIn{e, vals}`, `Clip{e, lo, hi}`,
   `StrPred{op, e, pat}` (`StrPredOp = Contains | StartsWith | EndsWith`), `Un{LenChars, e}`,
   `AggOp` `Std | Var | Median`, and `X.Closed = Both | Left | Right | Neither` for
   `DF.is_between_closed`. `DF.is_between(e, lo, hi)` / `is_between_closed` take EXPRESSION
   bounds (the contract left the bound type open; `DF.lit_u32(2)` etc. give the literal case) and
   build `And{Ge|Gt(e, lo), Le|Lt(e, hi)}`, so typing errors are the comparisons' (`"ge"`, `"gt"`,
   `"le"`, `"lt"`) and the explain line shows the two comparisons.
2. **Analysis (15.3.2)**: every new node is total (`When`, `IsIn`, `Clip`, `StrPred`, `LenChars`,
   and the reducers, which answer null on too few rows); kind and locality come from the operands
   (`When` joins its three), so the release optimizer sinks a Head below a Select of them
   (tests/plan_m3_exprs.bend) and treats `std/var/median` as reductions (KRed, not local: a
   barrier, B01-f). `Expr.analyse` uses first-order helpers per node (`Ana.when/isin/clip/strpred`),
   no closures, for the P2 proof.
3. **Evaluation**: `When` is a ternary stack instruction (`IWhen`; a 1-row side broadcasts like a
   binary op); both branches are evaluated over every row, so a strict `cast` that fails in the
   branch a row does not choose still fails (Polars evaluates both branches too). The literal
   parameters of is_in / clip / the string predicates ride as a Data parameter of one new template
   kernel, `K.Kernel.map_p` (kernels.bend; a template lambda cannot capture a value). is_in compares
   words: u32 / i32 bits, bool 0/1, f32 `Kernel.fword` (15.5.2), strings by `String.eq`.
4. **std / var / median share one kernel set** in eval.bend: `Eval.ssd` (fsum mean, then the fsum
   of `Eval.sqdev`), `Eval.var_of`, `Eval.med.at` (middle cell / `lo*0.5 + hi*0.5` of a sorted run).
   `Fmt.describe`'s std now IS `Eval.agg Std` (bit-identical to the old formula: same mean, same
   f32 squares, same Neumaier sum). Integers convert to f32 per cell first (`Eval.wf32`). The
   eager median sorts the valid values with one `Radix.sort` of their 15.5.2 order words (so
   eval.bend now imports sort.bend). Grouped: std / var are two scatter passes (the group mean by
   `Grp.nm`, then the squared deviations from the gathered group mean, also by `Grp.nm`), so every
   group sees exactly the eager arithmetic in row order; the grouped median is one stable radix
   sort of the rows by order word, then by `group * 2 + null flag`, after which each group's valid
   values are a sorted run starting at the exclusive prefix sum of the group sizes, read by
   `Eval.med.at`. tests/agg_std_var_median.bend and `make diff-reduce` (grp paths) check grouped
   equals eager equals the step model.
5. **Overflow in std / var follows the algorithm**: `[3e38, 3e38]` has an infinite f32 sum, so the
   mean is inf and var / std are `inf` (and `[-3e38, 3e38]` squares to inf); Polars (f64) answers
   finite values. Within 15.5.4 ("the algorithm is the contract"); the T2.3 reference classes
   `overflow` cover it.
6. **Facade**: besides the 15.2.6 builders, `DF.abs`, `DF.sqrt` (nodes existed, no facade def; the
   bench/diff DX shims are gone and tests/diff d0003/4/5/8 call `DF.abs` / `DF.sqrt`), the
   15.2.1 dtype / scalar builders `DF.t_bool .. DF.t_str` and `DF.s_null / s_bool / s_u32 / s_i32 /
   s_f32 / s_str` (needed by try_cast, is_in and clip without a src/ import; `DF.s_i32` takes a
   `D.I32`, i.e. `DF.i32(v)`'s value). Not added here: `DF.column`, `DF.schema`, `DF.height`,
   `DF.collect_show` (15.2.1; added in "M3 facade leftovers" below).
7. **Expr.show**: an is_in list shows each literal with `Expr.show.lit` (`nan`, `0`, `"a"`); a
   string pattern is shown raw inside the quotes (no escaping, as `lit("..")`).
8. **bench/diff**: the EXPRS rows and oracle functions existed from M0; `model.t_is_in` now reports
   the first offending literal in list order (null or dtype), as `Expr.type` does, and the
   generator injects a null literal into is_in / clip in invalid cases.

### M3 facade leftovers

1. **Gap check against 15.2.** Every `DF.<name>` token of section 15.2 (83 names) and every bare
   builder name in its rows was compared with the `def`s of `frame.bend`. Four had no facade def,
   all in 15.2.1, and are now added as thin wrappers (no new logic in `src/`):
   - `DF.column(t: D.DType, xs: List<&2, D.Scalar>) -> ResT(Column)` = `C.Column.from_scalars(xs, t)`.
     Its type name `DF.Column()` is added beside `DF.Frame()` so the result can be annotated.
   - `DF.schema(f: Frame) -> Frame & Schema` = `S.Frame.schema(f)`. The contract's `Schema` is the
     `Schema()` alias (Data); written `C.Frame & Schema()` it type-checks, so the signature is exact.
   - `DF.height(f: Frame) -> Frame & U32` = `C.Frame.height(f)`. Both pair results hand the frame
     back, as `Frame` is linear.
   - `DF.collect_show(p: Plan, env: Env) -> IO(String)` = `Q.Lazy.collect(p, env)`, then `show`, in a
     do block (as `write_csv.io`). Its errors are `collect`'s, rendered by `show`.
2. **No contract row needs new logic in `src/`**, and no signature is impossible in Bend, so
   nothing is substituted. `DF.schema` and `DF.height` have no error path (15.2.1 says none).
3. **Tests**: `tests/facade_m3.bend` (success and one invalid input for `column` and
   `collect_show`; success for `schema` and `height`; `height` of the empty frame is the edge case).
   Expectations were reasoned from the table format and the error texts of 15.9 before the run.

### M4 string experiment (Raw / Dictionary storage, streaming CSV reader, the default)

Plan M_01 section 5. Measurements and the per-workload table: bench/README.md "M4 string
experiment"; raw runs: bench/results/m4/*.jsonl; Bend lessons: IMPLEMENTING.md "M4".

1. **Representation**: `CStr{len, depth, valid, data: ST.Strs}` (src/strs.bend) with
   `ST.Strs = SRaw{data: Array<String>} | SDict{codes: Array<U32>, dict: ST.Dict}`, not a sixth
   Column constructor (every 5-way match in src/ and the proof files would have needed a new
   case). `Dict{k, dd, strs, b, slots, tag}`: k entries in `strs` (2^dd slots), an open-addressing
   index (FNV-1a + Fibonacci slot, linear probing, load <= 1/2) instead of the plan's
   `Map<String, U32>` (a Map lookup costs ~3x a probe and the reader codes every cell through
   it), and a fingerprint `tag`. The dtype stays `str`; codes never show (not a categorical
   dtype, not a rank, not a global id). Invariants: every valid row's code < k; entries pairwise
   distinct; the index maps each entry to its code; **entry 0 is always `""`**, so a null row
   holds code 0 and decodes to `""`, exactly the Raw invariant (an invalid slot holds the dtype
   default) and `Strs.decode` is a plain gather; null stays validity, never an entry.
2. **Tag is a fingerprint, not an identity** (deviation): Bend has no global counter, so `tag`
   is an FNV mix of the entries in code order. Equal tags are verified entry by entry
   (`Dict.same`) before two columns' codes are compared directly; otherwise the smaller
   dictionary is re-coded into the larger (`Dict.recode`; a miss is `Dict.miss()` = 2^32 - 1,
   never a code).
3. **Operations** (section 5 list): `col == lit` / `!=` codes the literal once (a 1-row Str side
   next to a Dictionary column broadcasts as a one-entry Dictionary, `Eval.fitd`, then the
   column x column path re-codes 2 entries); column x column equality as in item 2; ordering
   (sort keys, `<`/`<=`/`>`/`>=`, min / max) maps codes through `Dict.ranks` (one sort of the
   entries; Base `Map.to_list` order = code points with a prefix first = `String.is_lt`); two
   dictionaries are merged (`Dict.merge`) and the merged entries ranked once; group_by keys and
   unique use the codes (densified); join keys: both sides' dictionaries coded into one key
   space (`J.Key`), so equal values with different codes on the two sides meet (the measured
   join files are built that way); string predicates, `len_chars`, `cast` from str and `is_in`
   run once per ENTRY and gather by code (`Strs.map / map_maybe / map_p`); `when` and
   `fill_null` over two Dictionaries merge them (`Eval.when.sd`, `Eval.fill.sd`); concat merges
   explicitly (`Strs.append`: b's dictionary into a's, b's rows re-coded); a Raw x Dictionary
   pair decodes the Dictionary side. gather / filter / head / slice / clone move codes only.
   Render, dump, `Column.cell` decode (`Strs.get`).
4. **Encoding decision** (`ST.StrEnc`): `EncRaw`, `EncDict` (always), `EncAuto` (by measured
   cardinality): while reading, a column stays a Dictionary while its entries k satisfy
   `k <= max(16384, rows_so_far / 64)` (`Csv.dict_over`, checked at every cell); past it the
   column falls back to Raw at once, decoding the rows coded so far (the only rescan: of a
   prefix, at most ~16k rows for a column distinct from the start; no rescan when the
   selection is made). Threshold from the 1M-row sweep (bench/README.md): at 1 % distinct
   (10,000 values) the Dictionary parse costs nothing measurable and every operation wins
   13-55x; at 10 % (100,000) the parse costs ~30 % while group_by / sort still win; at 50 %
   and fully distinct, forced Dictionary loses on parse (-32..-50 %), `<` against a literal
   (ranking 1M entries: 36-50x slower), max over groups (3x slower), join (-15 %) and drop
   (3.5-4.5x slower), which Auto avoids by falling back. `EncAutoAt{floor, den}` is the same rule
   with other numbers (tests).
5. **Streaming reader** (src/csv.bend, src/csvparse.bend): `Csv.read_full(path, opts, ts, enc,
   chunk, cap)` reads pieces with `File.read` after a 4 KiB `File.read_at` probe for the
   piece's last LF (so no UTF-8 sequence is split; a piece without a LF doubles), parses each
   piece to records (the walk's state resumes on the next piece), and hands them to a sink:
   header / width, blank lines, ragged records, dtype count, row cap, inference over the first
   `infer_rows` records, then one typed builder per column (words, f32, Raw strings, or
   Dictionary codes coded as produced). No list of every record, no Scalar lists, no
   whole-file cons string. **Deviation: the default piece is 64 MiB (`Csv.chunk`), not 1 MiB**:
   natively, 1 MiB pieces made the 41 MB read ~3x slower (9.0 s Raw / 8.5 s Dictionary at 1 MiB
   vs 2.6 s / 1.9 s in one piece, at the time of the change; per-piece time rose from 65 to
   ~200 ms over 40 pieces: the allocator's LIFO free lists hand the next piece scattered
   memory, IMPLEMENTING.md M4). **Transient full-string materialisation that remains**
   (reported, as section 5 asks): a file under 64 MiB is read as ONE transient `String` (the
   41 MB benchmark file included), freed piece by piece as it is parsed; each field's text is a
   transient cons string (a Dictionary cell's string is dropped once coded; a Raw cell's is the
   cell). Larger files stream in 64 MiB pieces. Tests read with 1..64-byte pieces
   (tests/csv_chunks.bend) and every storage gives the 1 MiB Raw dump.
6. **Default (the gate)**: **`Csv.enc_default() = EncAuto`**: `read_csv`, `read_csv_opts`,
   `read_csv_schema`, `Csv.parse*` and `scan_csv`'s collect hold a low-cardinality str column
   as a Dictionary and a high-cardinality one as Raw. Gate (plan section 5): >= 1.5x median on
   representative low-cardinality workloads, no material memory regression, no > 15 % median
   slowdown on numeric or high-cardinality controls. Outcome (medians of 5 processes, A/B
   interleaved, 1 and 12 threads; bench/README.md has every cell, spread and machine load):
   **passed, Auto stays the default** (decided 2026-10-09 on the final measurement set).
   Low-cardinality (the sales keys, 8-64 distinct) auto vs raw at 1M: q1 8.3-8.4x, q3
   8.5-15.6x, q4 5.1-8.8x, q5 13.9-19.6x (100k 4.4-22.5x, 1k 2-4x); isolated operations on
   8 / 64 / 1,000 distinct at 1M: eq 29-31x, gather 160-200x, sort 7.8-35x, group 22-91x,
   join 8.9-33x. Memory: peak RSS auto <= raw in every sales cell (1M 1.28-1.35 GB vs
   1.31-1.42 GB raw, 1.63-1.84 GB master); five repeated group_bys +2 % over one (raw +1-7 %).
   Numeric controls: q2 pooled medians 0.90x / 1.02x at 1M (1 / 12 threads), 1.00x / 0.86x at
   100k, inside 15 % but the closest cell (a 7-12 ms query at the noise floor); q6 1.37-1.52x
   faster; numeric-keyed sort / group 2.3-3.4x faster. High-cardinality controls (fully
   distinct columns at 100k and 1M, 100k / 500k distinct at 1M): auto 0.88-1.24x of raw,
   median 1.00x, because Auto falls back to Raw (forced Dictionary would lose up to 50x on
   `<`, 4x on drop, 1.5x on the parse). Targets: 3x on q1 / q3 / q5 met; **41 MB parse under
   1.5 s not met**: 1.98 s auto at 12 threads (raw 2.46 s, master 4.28 s; 1 thread 4.38 /
   4.53 / 8.95 s). The streaming reader's effect (master -> raw) and the dictionary's (raw ->
   auto) separate: the reader parses the 41 MB file 1.98x / 1.74x faster with 18-24 % less
   peak RSS and leaves the queries unchanged; the dictionary adds 1.03x / 1.24x on that parse
   and 5-22x on the queries. Costs that remain: parsing long low-cardinality strings
   (0.70-0.94x of raw's parse at 100k, prefix_1000 at 1M 0.79x), fully distinct Raw group_by /
   sort stay slow (7.9-13 s at 1M), and a file under 64 MiB is read as one transient String
   (item 5). The table with every cell, spread and load: bench/README.md "M4 string
   experiment".
7. **Facade** (15.2.7 rows added): `DF.read_csv_enc(path, opts, dtypes, enc)` with `DF.str_auto()`
   (the default), `DF.str_raw()`, `DF.str_dict()` (type alias `DF.StrEnc()`);
   `DF.encode_strings(f, dict: Bool)` converts every str column (values unchanged);
   `DF.dict_columns(f) -> Frame & List<String>` names the Dictionary columns. Frames built from
   literals (`DF.column`, `from_columns`) and new string results of expressions start Raw;
   results computed from Dictionary columns stay Dictionaries. `scan_csv` has no storage
   argument (its collect uses the default; a lazy query over another storage reads with
   `read_csv_enc` and binds the frame with `DF.source`), so no Plan node changed.
8. **Proofs**: `LAWS.ccell`'s Str case reads `LAWS.scell` (Raw: the slot; Dictionary: the
   entry of the row's code), and `PROOF_contents` proves `ST.Strs.get` pure against it
   (`strs_get_pure`), so `cell_pure` covers both storages. `WFColumn`'s Str case names the
   storage (`WFStrs`, `WFDictCodes`). Every proof that only moves `data` (head, len, dtype,
   witnesses) was unchanged. The P2 typing laws (section 8 row 13) cover both storages since
   the merge of M5 part 2: `PROOF_eval` `strs_get_w` (the cell witness), `sclone_w` /
   `dclone_w` (clone), `fill_str_w` / `when_str_w` (with the Dictionary merge paths),
   `bcast_dict_w`, `isdict_w`; `PROOF_evalops` `aggs_*_w` / `aggdense_nu_s` (Str aggregations
   per storage) and the Str casts / is_in / predicates through `ST.Strs.map_maybe` /
   `map_p`; `PROOF_evalrun` `step2_d` / `fitd_w` (the binary step reads both operands'
   storage and broadcasts a literal as a one-entry Dictionary next to a Dictionary). Because Auto (a Dictionary for low-cardinality columns) is the
   default, plan section 5 puts the Dictionary's decode-preserving lemmas into the P1 chain
   (plan section 6 P1: "Dictionary encode/decode/remap preserve the decoded Str cells").
   Written in M5 part 3 (section 8 row 14 and the matrix; the "M5 part 3" subsection below
   says which of the functions listed here are covered and which stay tested-only). Each
   lemma says: for every row i below the length,
   `scell(op(s, ..), i)` equals the Raw operation's cell (equivalently `Strs.decode(op_dict(..))
   == op_raw(Strs.decode(..))`), under `WFStrs` (every valid code < k, entries pairwise
   distinct, the index maps each entry to its code, entry 0 is `""`), and `WFStrs` is preserved.
   **Required for P1** (the functions the kernels P1 already covers call on a Dictionary, plus
   encode / decode / remap):
   - the model: `Dict.decode` / `Strs.decode` (a gather of `strs` by `codes`: row i decodes to
     `scell(s, i)`, via `gather_contents`);
   - encode: `Strs.encode` (`Strs.encode.raw`, `Enc.put`, `Enc.step`, `Enc.go`, `Enc.fin`),
     `Dict.code` (`Dict.code.p` / `.k` / `.h`, `Dict.add`, `Dict.fit`, `Dict.room`) and the index
     (`Ix.slot`, `Ix.look`, `Ix.seek` / `Ix.seek.go`, `Ix.grow` / `Ix.grow.go`, `Ix.move` /
     `Ix.move.k`, `Str.same` sound and complete; `Str.hash` / `Str.fnv` need only determinism),
     `Dict.find`, `Dict.empty` (entry 0 = `""`);
   - decode back and the column / frame wrappers: `Strs.raw`, `Column.encode`, `Column.decode`,
     `Column.recode`, `Frame.encode`;
   - remap: `Dict.recode` (`Dict.rc`, `Dict.rc.op` / `.put` / `.step` / `.go` / `.fin` /
     `.fin2`; a miss, `Dict.miss()`, is never a code), `Dict.merge`, `Dict.same` (`Dict.same.*`:
     true implies equal entries), `Strs.append` (`Strs.app.m`) under `Cat.col` (concat);
   - the P1 kernels' Str-Dictionary case: `Strs.gather` / `Strs.compact` (codes only; under
     `Column.gather.data`, `Column.compact.data`, `Column.slice`), `Strs.clone` / `Dict.clone`
     (`Column.clone.s`), `Strs.fix` (null slots to code 0, which decodes to `""`), and
     `Strs.get` (done: `strs_get_pure`);
   - fill_null / when over two Dictionaries (P1's validity combinators): `Eval.fill.sd` /
     `Eval.fill.sd2`, `Eval.when.sd` / `Eval.when.sd2` (merge, then recode), `Eval.fix.s`.
   **Only if a later claim reaches them** (string expressions and comparisons are P2 / P3
   scope, not P1): `Strs.map` (`Dict.map.k` / `.t` / `.t2`), `Strs.map_maybe` (`Dict.mm.t` /
   `.g`), `Strs.map_p` (`Dict.mp.t` / `.t2`), `Strs.const`, `Eval.fitd`, `Eval.zd.eq.*`,
   `Eval.zd.ord*` with `Dict.ranks` (`Dict.rk.*`; rank order = `String.is_lt` order needs a
   Base `Map.to_list` order lemma), `Eval.ds.*` (min / max / first by rank), `Eval.agg.sd`,
   `Eval.isin`, `Eval.strpred.k`, `Eval.cast.s`, `Eval.zip.dd`.
   **Excluded by plan section 6** (CSV, hash-join, radix-sort and grouping partition stay
   tested, not proven): the reader's builder (`Ds.put`, `Ds.cell`, `Ds.go`, `CB.d.*`,
   `Parts.dec*`, `Csv.dict_over`), `Sort.dict_words` (`.b`), `Grp.enc.dict` / `Grp.enc.dk.*` /
   `Grp.enc.sk`, `Grp.agg.v`, `Key.enc.*` / `Join.fix`. These are covered by
   tests/strs_decode.bend, tests/csv_chunks.bend, tests/facade_m4.bend and the differential
   generator's Dictionary mode (`make diff DIFF_ARGS=--dict`).

### M5 part 3 (P1 Dictionary strings: LAWS.bend section 14, PROOF_strs.bend)

1. **Covered** (section 8 row 14, 22 laws, all under `--verdict`): the decode model and the
   code-moving kernels in both storages (`Strs.decode`, `Strs.gather`, `Strs.compact`,
   `Strs.clone` / `Dict.clone`), `Str.same`, `Dict.empty`, `Dict.code` with the whole index
   (`Ix.seek`, `Ix.grow`, `Ix.move`), `Strs.encode`, `Strs.raw`, `Column.encode` / `decode` /
   `recode`, `Cols.encode`, `Frame.encode`, `Dict.miss`, `Dict.merge`, `Dict.same`,
   `Dict.find`, `Dict.recode`. **Tested only** (of the "required for P1" list in item 8 of the
   M4 subsection): `Strs.append` under `Cat.col`, `Strs.fix`, `Eval.fix.s`, `Eval.fill.sd` /
   `.sd2`, `Eval.when.sd` / `.sd2` (section 8 "not provable or not true as stated" says why:
   their kernels `Kernel.append`, `Kernel.mask_data`, `Kernel.choose` have no content
   theorem yet; the dictionary half of fill / when, the merge with the old codes kept, is
   proven).
2. **The model**: a dictionary's entries in code order are a Data LIST `es` (`WFDictE(d, es)`:
   `to_nat(k) == |es|`, `k <= 2^dd`, `0 < k`, `nthn(es, 0) == ""`, `WFArray(strs)`, every slot
   below k its list entry, `WFIx`). The list is duplicable, so facts about every entry at once
   are Data (`Ext(es, es2)`: es2 extends es); the per-slot entry facts stay an affine forall,
   which is why `CodeW` also answers `Keep` (every old code keeps its entry): consumers
   (merge's `KeepD`, and the concat / fill / when cells once their kernels are proven) need
   the original dictionary's cells after the write consumed its `WFDictE`. `Keep` is proven
   by analysing the one production write on a second clone of the entry array
   (`PC.clone_wf`, then `set_other_w` twice: `keep_of`), the "analysed twice" technique of
   IMPLEMENTING.md M5.
3. **Hypotheses that are not derived** (deviations from a closed theorem, all stated in the
   laws): (a) the PROBE hypothesis `Probe(d, s)`: `Ix.seek` stops at a slot that is empty or
   holds s. Production guarantees it by the load factor <= 1/2 (an empty slot is always
   within the probe's fuel) and the pairwise distinct entries; proving that termination
   argument (a counting argument over the open-addressing table) is not done, so the laws
   take the probe's answer as given and show it sound. The loop laws carry it per row
   (`EncProbe`, `MergeProbe`, `FindProbe`, each threading the production's dictionary).
   (b) the entry bound below 2^30: `strs_encode_cells` derives it from `n < 2^30` along the
   loop (`Room(30n, inc i, f)`, `|es| <= to_nat(inc i)`); `dict_merge_spec` takes it per step
   inside `MergeProbe` (deriving it from the two sizes needs `U32.add` arithmetic the word
   toolkit lacks). The row cap keeps every dictionary below 2^23 + 1 entries, so both are
   vacuous in production. (c) `dict_find_spec` / `dict_recode_spec` state soundness only
   (`FoundK`: a miss or a code in range naming s), not completeness ("an entry is always
   found"), which `WFIx` does not express; completeness is what makes a miss mean "not
   equal" in `Eval.zd.eq.*` (tested).
4. **Statement shapes** (what a reader of LAWS.bend section 14 should know): the row facts
   abstract the code as a Data word with its equation (`EncRows`: `@code -> {code ==
   rdN(codes, j)} -> ...`) because `rdN(out, j)` as a live term would consume the array; the
   per-row `dentry` form is a separate law (`strs_encode_cell`). `CodeW` bounds the code both
   as a word (`c < dk(d2)`) and in the list model (`to_nat(c) < |es2|`) because the loop
   invariants live in the list model while `WFDictE` speaks in words. Laws are stated over
   the opaque `ST.Dict` with the accessors `dk`, `ddd`, `dstrs`, `dentry`; the proofs match it
   into fields at once.
5. **Mutation fixtures** (tests/proof_negative/): `encode_reuses_code.bend` (every row gets
   code 0) refused by the real `strs_encode_cells` term; `remap_wrong_slot.bend` (the merge
   map written at c + 1) refused by the real `dict_merge_spec` term.
6. **Timings**: 138 laws, `bend PROOF.bend` ~1.6 s wall / 3.1 s CPU, `--verdict` ~4.6 s.

### M5 (proof closure: P1 buffer contents; P2 / P3 not reached)

1. **What M5 delivered**: LAWS.bend section 11 and `PROOF_bits.bend` /
   `PROOF_contents.bend`: the distinct-paths lemma over the production index arithmetic
   (`paths_distinct`), `Array.set` separation on well-formed arrays (`array_set_other`,
   `wf_array_set`), and the full content theorems of the kernels `Kernel.gather`,
   `Kernel.compact_keep`, `Kernel.map` / `zip` (as the mask combinators), `Kernel.iota_from`,
   `Kernel.fold` with `U32.add` and `Kernel.popcount`; at the column level (section 12)
   `Column.cell` purity against the cell model `ccell`, `Column.head`'s cells and
   `Column.slice`'s exact subrange on U32 columns. 90 laws, `make proofs` and `make verdict`
   green; four negative fixtures. The assurance matrix (section 8.1) names the hypotheses of
   each.
2. **Deviation: the compaction theorem carries an explicit precondition.** `compact_contents`
   assumes `CRoom(to_nat n, 0, 0, d, mask)`: every mask word is 0/1 and the write cursor is
   below 2^d at every step. Production (`Column.compact`) allocates `depth_for(kept + 1)`
   slots with `kept = popcount`, which implies `CRoom` (the cursor never exceeds the kept
   count), but that arithmetic is not proven; the plan's "count = length" is `popcount_sum`
   (the kept count is the sum of the mask words) plus `CSpec` (every kept row sits at its
   cursor position), stated separately.
3. **Deviation: instances, not templates, in the laws.** The kernel laws are stated at the
   U32 instance (word buffers: Bool / U32 / I32 columns and every validity mask) because the
   BendTT kernel refuses a law applying a template kernel at a quantified cell type (as in
   M2). The proofs are template defs (`map_go`, `zip_go`, `ckeep`, `cspec_run`) and the
   F32 / String instances are the same text; `gather_go` is written at U32 only.
4. **BendTT constraints found** (both accepted by `bend PROOF.bend`, refused by `--verdict`):
   a template lambda must be spelled identically everywhere it is meant to be the same
   (`~(acc => x => U32.add(acc, x))` as in `Kernel.popcount`, not an alpha-variant), and a
   `%` rewrite whose replaced term contains a template application (`Array.set(U, out, j,
   f(x))`) is refused; the written value is carried as a variable `y` with `y == f(x)`.
   Recorded in IMPLEMENTING.md.
5. **Hypotheses the law binders had to make reusable**: `paths_distinct` takes `+hi`, `+hj`
   (the in-range facts are spent twice: for the mask identity and for the induction);
   `gather_keeps_perm` gained the `fits` hypothesis (it is derived from the same loop lemma).
6. **Not done (honest scope)**: P2 (soundness of `A.Expr.analyse`, typing soundness of
   `Eval.full`; the M3b nodes When / IsIn / Clip / StrPred / LenChars and Std / Var / Median
   therefore have no analysis lemmas yet), P3 R2–R5 and the composition theorem, the
   column-level `Column.gather` / `Column.compact` cell theorems and `Column.slice` on F32 /
   String columns, `Kernel.choose` / `mask_data` cells, the grouped scatter invariant, and
   the dictionary lemmas (M4's representation was not merged into this branch). R3 is the
   one that would widen G6, and it needs the P2 cell-level evaluator theorems first: a sunk
   Head changes buffer depths, so `Eval.select(Frame.head(f, n), es)` and
   `Frame.head(Eval.select(f, es), n)` are equal only observationally (through `DF.dump` /
   `Column.cell`), never structurally. The G6 wording stays as section 8 states it.

### M5 part 2 (P2 evaluator typing; P3 by the fallback: the release optimizer merges Heads only)

1. **Decision: P3 fallback taken.** `Optimize.release` is `Opt.hmerge` (adjacent-Head merging,
   schema-checked first) and nothing else; the analysis-certified Head sink (R3) stays in
   `Plan.optimize_full` (`Opt.head`), opt-in. `release_run` / `release_run_obs` (LAWS section 8)
   replace `release_merge_only(_obs)`: no `merge_only` hypothesis, every plan and env. The
   section 8 G6 wording is final. Cost on the benchmark: none. No q1-q6 plan has a Head above a
   Select/WithColumns (q4 = Head over Sort, a barrier for both passes), so the release optimizer,
   the previous head pass and the raw plan coincide for q1-q5 (tests/plan_release_bench.bend);
   q4's timings before / after the fallback are noise (bench/README.md). Re-enabling the sink in
   the release optimizer needs R3 as a theorem (observational commutation of `Eval.select` /
   `with_columns` with `Frame.head`, cell level), not done.
2. **What P2 delivered (LAWS section 13, 116 laws)**: stage 1 (`PROOF_eval.bend`) the models
   `cdtype` / `clen` / `klen` / `skind` / `fschema` / `frame_ok`, purity of the readers, the P0
   bridge `wf_frame_ok`, `get_cloned_typed`, `bcast_typed`, `unit_typed`; stage 2
   (`PROOF_evalops.bend`) the ten operation laws `eval_un_typed` .. `eval_agg_typed` over
   `src/eval.bend`'s operations, each case list generated from the (op, dtype) table of
   `expr.bend`'s rules (accepted cases: the production term as a live witness with its shape
   facts; refused cases refuted); stage 3 (`PROOF_evalrun.bend`, generated by
   `scripts/proofgen/gen_evalrun.py`) `run_typed` over `Eval.compile` + `Eval.run` by induction
   over the expression with the stack invariant `StkTy`, every Expr node, and the entry points
   `eval_full_typed` / `eval_expr_typed` over `Eval.full` / `Eval.expr`.
3. **Scope of the typing theorems (honest)**: dtype, height, the frame back unchanged, and
   "fails only where the analysis says it may" (tot). Not stated: cell values, that only the
   `refs` columns are read, the locality field. The analysis header's soundness statement in
   `src/analysis.bend` lists those too; they were needed only by the Head sink and the
   `optimize_full` passes, which are outside the guarantee.
4. **Deviation: the stack kind is read from the shape, not from the slot.** `StkTy` states the
   column's length as `klen(k, h)` with k the SHAPE's kind and carries `k2 == k` for the slot's
   kind separately; `Eval.do2.a` / `do3.a` test the slot kinds, so the step lemmas first rewrite
   the slot kinds to the shape kinds. The two- and three-operand steps need no case split: the
   shape test `bad` and the result length are closed terms over the three kinds once those are
   constructors, proven by the 9- / 27-case lemmas `bad2_false` / `len2` / `bad3_false` /
   `len3` and used symbolically.
5. **Dictionary strings (M4) and these lemmas.** Every section 13 lemma is over the five
   `C.Column` constructors as they are on this branch. A `Dictionary` string representation
   adds cases to `cdtype` / `clen` / `len_w` / `dtype_w` / `cell_w` / `clone_w` / `col_dup2` /
   `clen_dup` (one line each, by the kind table of the generators), to `bcast_typed` and
   `unit_typed` (the constant-column builders), to `get_cloned_typed` through `Column.clone`,
   and to the string operation laws (`eval_strpred_typed`, `eval_un_typed` LenChars,
   `eval_agg_typed` over strings, `eval_fill_typed` / `eval_when_typed` / `eval_bin_typed` on
   string operands) wherever `eval.bend` takes the dictionary path; `run_typed` and the entry
   points are representation-agnostic and need no change.
   (Done when M4 merged this branch, 2026-10-09: the Str storage is a sum type inside `CStr`,
   not a sixth constructor, so `cdtype` / `clen` / `len_w` / `dtype_w` / `col_dup2` /
   `clen_dup` / `get_cloned_typed` needed nothing; `cell_w`, `clone_w`, the constant builders
   of `bcast_typed` / `unit_typed` (a Raw constant) and the string operation laws got
   per-storage cases; and
   `run_typed` DID need one change: the binary step reads both operands' storage (`step2_d`,
   `fitd_w`). Section 14 "M4 string experiment" item 8.)
6. **Fixtures**: `tests/proof_negative/head_sink_below_select.bend` (the release pass sinking
   below every Select is refused by the `hmerge_run` term), `un_neg_wrong_dtype.bend` (Neg over
   i32 answering u32 is refused by the `eval_un_typed` case), `fit_no_broadcast.bend` (a stack
   machine `fit` that does not broadcast is refused by the `fit_w` shape lemma).

### M5 part 4 (P1: concatenation and the in-place kernels; LAWS.bend section 15)

1. **Laws at the U32 instance, proofs as templates.** `append_cells`, `mask_data_cell` and
   `choose_cell` are stated at U32 (BendTT refuses a law at a quantified cell type, as in
   section 11); the template proofs (`append_w`, `mask_data_w`, `choose_w`) are used at
   String and F32 inside `strs_append_cells`, `fix_cell` and `fill_str_cell` / `when_str_data`.
2. **Hypotheses not derived** (section 8 "Not proven" item 1): `CatFits` (na + nb <= 2^d as
   naturals; production allocates `depth_for` of `Cat.sat`'s saturating sum), `WFDict` and
   `CodesBelow` / per-row code bounds for Dictionary operands, and the probe hypotheses
   (`MergeProbe`) of the dictionary merge behind concat / fill_null / when.
3. **Scope cuts.** `when_str_data` states the stored string only; `Eval.when.valid` (the
   validity of a when row) has no cell law. fill_null and when over Bool / U32 / I32 / F32
   columns are not stated at the column level (their kernel is `choose_cell`). `Cat.col` and
   `concat_vertical` are not stated as frame cell theorems; their buffers are.
4. **In-place loops by a single-position induction** (PROOF_inplace.bend's header): the
   "every row so far" invariant of the copying kernels cannot be carried across in-place
   writes, so the loop lemma tracks one position and splits it against the write index.
5. Fixtures (added in M6): `append_right_offset.bend` (b copied from na + 1, refused by
   `append_cells`), `choose_inverted_mask.bend` (the mask test inverted, refused by
   `choose_cell`).

### M6 (release candidate)

1. **No throwaway hub publish** (user decision, plans/STATUS.md "Decisions"): the plan's
   clean-consumer step "publish to a throwaway hub name" is replaced by
   `scripts/consumer_check.sh` (a clean clone imported by relative and absolute path from a
   separate directory, native build and run of the quickstart). `bend --publish` has no dry
   run, so the hub upload itself is first exercised by the real `bend-frame@0.1.0.0` publish.
2. **CI has never run**: `.github/workflows/ci.yml` exists and `make ci` runs its gates
   locally, but the repository has no remote, so the workflow itself is untested.

### v0.1 review: scan source identity

plans/REVIEW_V01_ASTRA.txt [P1], a silent wrong result: `Exec.validate` checked the
caller's env, then `Exec.mat` prepended scan k's frame under the name `"#scan<k>"` and
`Exec.unscan` rewrote the `ScanCsv` to `Source{"#scan<k>", s}`. A user
`DF.source("#scan0", ..)` was accepted and then read the CSV's frame:
`concat_vertical([source "#scan0" x=[1], scan x=[2]])` collected `x=[2, 2]`; under any
other name `x=[1, 2]`. M2 item 3 above had documented the names as reserved, unchecked.

1. **Fix, by construction (no name-based scheme left)**: `Env` is
   `Env{frames: List<&1, Named.Frame>, scans: List<&1, C.Frame>}`. `frames` is the user's
   namespace (`Env.add`, `Env.take`, `Env.clone`, `Env.info`, so `validate_bindings`);
   `scans` holds unnamed frames, in the postfix (`Exec.compile`) order of the plan's
   `ScanCsv` nodes. `Exec.run` = `Plan.schema`, `Exec.validate` (unchanged: only names in
   `frames`), `Exec.mat` (reads every scan in postfix order, first error wins, the
   frozen-schema check as before; the frames are collected in a list, not bound), then
   `Exec.run_pure(p, Env.set_scans(env, frames))` on the plan AS IT IS. The runner's
   `IScan` takes the next frame off `scans` (`Env.scan_take`) and checks it against the
   instruction's schema with the existing `"scan_csv <path>: data schema .."` text; with
   none left it is the existing `"exec: scan_csv not materialised: <path>"`. A `Source`
   only ever reads `frames`, so a user name can never reach a scan's frame, whatever the
   name. `Exec.unscan`, `Exec.nscans` and `Exec.scan_name` are gone. No name is reserved;
   `"#scan0"` is an ordinary Source name. Nothing is rejected at the public entry points,
   so no new error text (15.9).
2. **Why not fresh names or a reserved-name check**: fresh names (skip any name in env)
   or rejecting `#scan*` at `source` / `add_source` / `validate_bindings` / `collect` would
   keep the namespaces disjoint only as long as every entry point remembers the rule; a
   separate field makes it structural. The other by-construction option, a new `Plan` or
   `Instr` constructor for materialised scans, would add a case to every proof that
   matches on `Plan` / `Instr` (LAWS 3, 4, 8). The `Env` field needs no proof change:
   no proof destructures `Env` (it is opaque in `St{env, stack}`), and `head_pass_run` /
   `hmerge_run` treat `Exec.step(IScan ..)` as an opaque step. `make proofs` / `make
   verdict` passed unchanged.
3. **What the proofs gain**: `Exec.run_pure` now runs the user's (optimised) plan itself,
   scans included, so `release_run` is no longer vacuous on scan plans (before, both sides
   failed with "not materialised" and the theorem applied only after `unscan`, an
   unproven glue step; plans/REVIEW_V01_FABLE.txt H1). New laws `hmerge_keeps_scans` /
   `release_keeps_scans` (LAWS 8, the `hmerge_keeps_sources` development over
   `Laws.scans`) prove that the optimised plan holds the same `IScan` instructions in the
   same order, so `collect` and `collect_raw` materialise the same frames. Still unproven
   glue: `Plan.schema` and `Exec.validate` agreeing on `Optimize.release(p)` and p (section 8).
4. **Contract changes** (15.7, 15.9): the `Env` type line; a "scans" row in 15.7 (a scan
   binds no name; validate_bindings neither needs nor sees scan frames); the 15.9
   "lazy error order with scans" note restated (unchanged order: static, bindings, scans
   in postfix order with the first failing one reported, then the pure run). `DF.source`,
   `DF.add_source`, `DF.empty_env`, `DF.validate_bindings`, `DF.collect*` keep their
   signatures; `DF.Env()` is the same type name.
5. **Regressions**: `tests/regress/V01_a_scan_source_identity.bend` (the repro with
   frozen and inferred scans and its control; two and three scans, one file twice, next to
   user Sources `"#scan0"` .. `"#scan2"`; equal and different schemas; scans in inner /
   left / semi / anti joins, a self-join of a scan, concat; validate_bindings and
   collect_schema of those plans; the error order; `run_pure` on a scan plan), each
   through `collect_raw` / `collect` / `collect_full` against eager. Against the previous
   commit 7 of its cases differ. `tests/regress/V01_b_scan_verbs.bend`: the IO boundary
   the review found uncovered, every lazy verb over `DF.scan_csv` (filter, select,
   with_columns, group_by, sort, head, slice, tail, unique, drop, rename, inner / left /
   semi / anti join, concat, a pipeline) against the eager verb over `DF.read_csv`.

### v0.1 review: gates, differential exit status, wording

plans/REVIEW_V01_FABLE.txt (H1-H6, notes) and plans/REVIEW_V01_ASTRA.txt (P2, sections 2-4).
Code fixes are listed in plans/STATUS.md "v0.1 review fixes (2026-10-10)"; the contract-level
consequences are these.

1. **"Correctness failures fail the build" is now true of `make ci`.** `make ci` runs, in
   order, `toolchain-check`, `check`, `runner-check`, `diff-driver-check`, `test`, `proofs`, `verdict`, `mutation-check`,
   `bench-check` (1k and 100k rows), `diff-smoke`, `consumer-check` and `coverage` (the
   operation x case matrix gate, docs/COVERAGE.md). `diff-smoke` is a
   bounded strict differential run (200 cases each in Raw and in Dictionary storage, fixed
   seeds) followed by the F32 reduction check; `diff-driver-check`
   (`bench/diff/tests/test_exit.py`) is the permanent regression that the drivers exit 1 on a
   mismatch (classified as a known defect or not), a crash, an oracle error and any reduction
   finding. Before, `run.py` without `--strict` exited 0 on a failure the shrinker labelled
   with a known-defect rule (`--strict` is now a no-op). Larger runs (`make diff N=...`,
   `make diff-reduce REDUCE_N=...`) are manual; CI size is the bounded smoke only.
2. **Benchmark correctness wording.** The goldens are Polars' output for q1, q2, q4, q5 and q6
   (q6 within rtol 5e-5 at 100k and 1M); q3's golden is the exact-rational F32 reference of
   15.5.3 (`bench/golden.py` `q3_reference`), because Polars' grouped f32 sum accumulates
   sequentially and differs by an ulp or two (tiny fixture, `inland`: Polars 96373.4141,
   reference 96373.4062). "Every result identical to Polars" was false and is not written
   anywhere now. `make bench-check` covers 1k and 100k; 1M needs `CHECK_MAX=1000000`;
   the tracked 1k golden (`bench/golden/n1000`) is regenerated by each run.
3. **CI and platform.** `.github/workflows/ci.yml` has never run (no remote); its Bend
   archive checksums and archive layout are untested (the comment that named a `flake.nix`
   was wrong: no such file exists here). macOS arm64 is the only platform ever built and
   tested.
4. **Test counting.** `make test` runs 158 test programs (files; 143 at the first release candidate); one file holds many cases.
   docs/COVERAGE.md is the operation x case matrix (774 cells: 727 covered by a named case,
   47 n/a with a stated reason, 0 missing) and the def-call report; the gate proves each
   case is accounted for and its file calls the operation, not that the case is a good one.
5. **Positioning.** v0.1 is an experimental release (plans/STATUS.md Decisions, 2026-10-10):
   R1-only default optimizer, Dictionary assurance conditional on the Probe / EncProbe
   hypotheses (index completeness not proven), the remaining proof work deferred (R2-R5,
   the grouped scatter invariant, Dictionary completeness and rank order). The plan section 0
   release claim is unchanged.

### W0 engine spikes (v0.2, plans/M_02.txt W0)
- Section 16 freezes D1-D4 and D7 from the disposable spikes under `bench/spikes/w0_engine/` (nothing in `src/`,
  `LAWS.bend` or `tests/` changed). Two revisions of the plan's assumptions, both measured: (1) chunks are born at the
  source and converted at most once per boundary, because chunking a flat 7-column frame (6.3 ms) costs more than the
  fused q1 (3.3 ms); (2) the G2 >= 3x target is proposed for q1/q2 only, with q3 >= 2x, q4 >= 1.3x, q5 >= 1.5x,
  q6 >= 2x justified by the serial fractions of section 16.8 (radix scatter passes have one owner per output array;
  F32 reductions stay one sequential pass). One open issue: the sequential F32 in-order walk over chunk leaves measured
  2.5x the flat fold with the same compiled loop (section 16.4); the fallback is costed.
### v0.2 W0 strings / reader (D5, D6; design in section 17)

Planned changes of implementation, none of the data contract (section 15 is unchanged); recorded
here so W2 / W6 do not rediscover them. Evidence: bench/spikes/w0_strings/, section 17.9.

1. **Plan revision proposed (M_02 G2)**: the CSV parse cannot reach >= 4x at 12 threads with the
   installed File API: bytes arrive as cons lists built sequentially on the IO thread, so the
   producer (~34 % of the 1-thread parse) is serial. Proposed: >= 2x end to end and >= 4x on the
   fork phase (17.8, 17.10 item 1); an Array-returning read in Base is the upstream lever.
2. **Plan revision proposed (M_02 D5 / D6 "parser-private cold types")**: no private cons parser
   types; flat packed bytes and cold scalar loop records instead (17.10 item 2).
3. **Reader pieces** (amends M4 item 5 for the W6 reader only): pieces of 256 KiB - 1 MiB, not
   64 MiB; the 64 MiB reason (allocator scatter of cons cells) does not apply to flat regions.
   15.6.4's "in pieces of up to 64 MiB" wording changes with W6; behaviour does not.
4. **String coding**: group_by / unique / n_unique / sort words / the join's string keys move from
   Base Map and `J.Dict` to the presized flat coder and the radix rank stage (17.3); codes and
   words are identical to v0.1's; the coder and ranks stay tested-only, as the code they replace.
5. **Dictionary laws**: unchanged unless W2.6 migrates `ST.Dict`'s index, in which case the
   Probe-family hypotheses are restated over the new seek (still hypotheses), never dropped.

### v0.2 T3.1 (liveness pass, moves and borrows; section 16.2 rule 1)

No change of the data contract (section 15): values, validity, names, order, F32 bits, errors and
error precedence are v0.1's (tests/eval_moves.bend: every case not using a new entry point gives the
v0.1 build's text; `make test`, `make diff-smoke`). What was implemented and where it departs from
16.2 rule 1 / 16.7 T3.1:

1. **Moves.** `Eval.mark` (a post-pass over `Eval.compile`'s postfix code, run after the static
   checks and before any data work) turns the last reference of a column the operator does not keep
   into `IMove` (`Frame.lend`: the column itself, a hollow stand-in of the same dtype and length stays
   in its place, so schemas, heights and with_columns' in-place `Frame.replace` are unchanged).
   select: every column (it consumes its input); with_columns: the inputs an output overwrites;
   group_by: `Eval.full_mv` / `Eval.expr_mv` with `later = Eval.refs(the keys / aggregations still to
   evaluate)`, for T3.3 to call inside groupby.bend (group_by itself is unchanged here: that file is
   T3.3's). Earlier references of the same column copy, so duplicates and aliases read equal columns.
2. **Borrows: only where a kernel hands the buffer back.** `unique` lends its key columns, `G.Grp.codes`
   hands them back and `Frame.replace` puts them in place (a repeated subset name copies all but its
   last reference). DEVIATION: the expression operands of filter (all input columns survive) and of
   with_columns' untouched inputs are still COPIED (`Frame.get_cloned`, commented in `Eval.filter.t` /
   `Eval.wc.b`): every Eval operation consumes its operands (`Kernel.map` / `zip` drop their
   inputs), so a borrow needs operation variants that hand the operand back. The fused kernels of W4
   (F2 zipv, F5 pred_count, F1 map_p) are where that belongs; until then q1's 8.4 MB and q2's 16.8 MB
   of predicate / with_columns copies stay (G6, copy bytes below).
3. **Sort keys** are a borrow of T3.2's (sort.bend): `Frame.lend` + `Frame.replace` with the law
   `lend_observes` are the tool; T3.1 does not touch sort.bend. **A Source not on its last use** still
   copies the whole frame (`Env.clone`, 15.7) and a self join's copy is counted (16.2 rule 3);
   narrowing that copy to the columns the consumer reads needs plan-level liveness across operators
   (and an edit of `Exec.mark` the R1 proofs are stated over): not done.
4. **head / slice then project**: a single reference now moves the parent buffer (no copy, the
   retained capacity of 16.2 rule 5); a second reference still copies the parent's FULL capacity
   (`Column.clone` is a physical copy; a logical-rows copy needs a range copy that hands its source
   back, i.e. a new kernel in kernels.bend: not done). Measured with the review's probe `bench/micro/ops.bend` (64 eager
   `select([col x])` of a 2^20-row column, native, 1 thread, 7 interleaved processes, load 13-24,
   provisional): `select` 13 ms -> 0 ms, `headselect` (after `head(1)`) 11 ms -> 0 ms (median; raw
   base 14,14,12,12,14,13,11 / 12,11,11,11,14,11,11, candidate all 0), same check lines.
5. **Proof scope.** `lend_observes` (the observation law of 16.6) and the four `Eval.mark` laws
   (section 8, group 16) are proven; the P2 theorems still cover `Eval.full` / `Eval.expr` and the
   stack machine over `Eval.compile`'s code (they checked unchanged with the new `IMove` case of
   `Eval.exec`). `select` and `with_columns` now run MARKED code (`Eval.slot.mv`), which `run_typed`
   is not stated over: their typing rests on the composition argument of the 8.1 row, not on a
   theorem (open: an equivalence of `Eval.run` over marked and unmarked code).
6. **G6 copy bytes** are measured by instrumenting the emitted C (a byte counter in the runtime's
   `blk_copy`, printed at every `IO.now` of `bench/m2/driver.bend`), not by a counter threaded through
   Bend code: threading one through eval, group_by, sort and join would change four modules' types
   (two of them other tasks' files). Exact, deterministic, 1M rows, compute phase: q1 8.39 MB, q2
   16.78 MB, q3 37.75 MB, q4 12.58 MB, q5 16.78 MB at baseline (3612482), at HEAD before T3.1 and after
   T3.1 alike (lazy q1's projection was already a move); the eager stage `select_q1` 3.15 MB -> 0. The
   W3 target (q1-q5 clone bytes -50%) therefore depends on T3.3 (group_by 33.6 MB of the 92.3) and T3.2
   (sort 12.6 MB) using these entry points, and on W4 for the 25.2 MB of filter / with_columns copies.
### v0.2 T3.2 / T3.4 (sort pipeline; Sort + Head bounded gather)

No change of the data contract (section 15): the same rows in the same stable order, the same
errors in the same order, the same F32 bits; tests/sort_head.bend, the sort / golden / groupby /
n_unique / median tests, diff-smoke and the m2 content hashes (q4 `chk` / `dump`) agree.

1. **Where the Sort + Head step lives** (M_02 W1g, section 4): in `Exec.run_phys`, at the plan's
   ROOT only (`Head{n, Sort{ks, x}}` as the whole plan, q4's shape and `sort().head(k)` collected
   lazily), not in `Exec.compile` / `Exec.mark` / `Exec.loop`. Inside `Exec.run_pure` it would have
   made `release_run` false as a term equality: `Frame.head` keeps the full buffers and lowers the
   length, the bounded gather allocates min(n, h) slots, so `Head{n, Head{m, Sort}}` and its merged
   form would no longer be equal terms. `Exec.run` (collect, collect_raw, collect_full) now runs
   `Exec.run_phys`; `Exec.run_pure` stays the proofs' runner unchanged, `Optimize.release` is
   unchanged, `release_run` and its proof are untouched. A Head over a Sort deeper in a plan still
   runs ISort then IHead (full gather). Eager `DF.sort(f).head(k)` is two separate calls and is
   unchanged (the facade composes nothing).
2. **The equivalence is observational** (LAWS section 16, `robs`): per row k, the error or the
   height and every column's name, dtype, length and cell (`ccell`, which `cell_pure` ties to
   `Column.cell`, the reader of DF.dump, show and every verb). Not stated through the DF.dump text
   itself: dump's row loop (`Column.scalars`) walks downward with `U32.sub`, whose index arithmetic
   (`to_nat(i - 1)`) the toolkit does not have (16.6 lists the same gap); robs for every k carries
   the same information.
3. **The bounded path's guard**: `Sort.gather_head` gathers min(n, h) rows when h <= 2^31
   (`Kernel.depth_for` is exact there) and otherwise the full gather then `Frame.head`; the row cap
   (2^23) makes the guard always true, and it is what lets the law hold for every frame term.
4. **`Radix.sort`'s contract**: rows past n of the answered arrays are unspecified: an already
   sorted input comes back as it is, a two-digit sort writes its second pass back into the input
   pair (v0.1 answered fresh zero-padded arrays when a pass ran). Every caller (n_unique, median,
   group_by ranks, the sort) reads rows below n only.
5. **Raw string keys still code a clone** (T3.2 brief: `Sort.str_words` / `str_codes` / `pcodes`
   and their callers stay as they are for W2; resolved by W2.3: borrowed through `Rk.words`): a `SRaw` key is cloned and coded by `Sort.words` as
   in v0.1; numeric, Bool and Dictionary keys are borrowed in place (`Sort.split` /
   `Sort.unsplit`), a Dictionary key through `Dict.ranks` and the rank lookup inside the words pass.
### v0.2 W2.4 (the join's string table)

Implementation only; the join's output (rows, order, values, validity, names, errors) is v0.1's
(tests/join_str.bend expectations were produced by the pre-W2.4 build).

1. **Amends 17.3.3 / 17.3.4 (join row)**: the probe does NOT compare a hash hit against the build
   side's representative ROW. Measured on the 1M distinct-key join (provisional, IMPLEMENTING.md
   W2.4): a lookup into `Hc.code`'s table that walks the representative cons string cost 1.25 s, of
   which ~1.1 s was that walk (a hot String costs a redirect and a cell per code point, at a random
   place: dependent misses); borrowing instead of taking it changed nothing, packing afterwards in a
   second walk cost 0.7 s more. Instead the build uses `Hc.code.pk` (src/hcode.bend, additive): the
   ONE walk of each build row hashes it, counts it and copies its code points to a flat word array
   `pk` (a repeated key's copy is overwritten), build-side hits compare flat against flat, and the
   probe (`Hc.find.pk`, sequential) compares the left string against the packed entry. Codes / ids
   are exactly `Hc.code(.., first = 0)`'s (tests/hcode_pk.bend). The table is `hs` + `ix` (entry + 1)
   instead of `hs` / `rp` / `ids`.
2. **Copy** (brief rule 2): 4 bytes per code point of each DISTINCT build key plus 12 bytes per build
   row (codes, offsets, counts), transient, made by the walk that has to read the key anyway; the
   build strings are borrowed and handed back to the right column right after the build (no longer
   held through the probe). No per-lane table, no `Dict.clone` / `Str.copy` (`Probe.fork`,
   `Probe.dd`, `J.Dict` removed). The probe is sequential (17.3.3 default); W2.5 may partition it.
3. **Assurance**: the packed coder and lookup are tested-only, as the table they replace.

### v0.2 W2.3 (wiring the flat coder and the rank stage)

Implementation only; group_by / unique / n_unique / sort / min / max / Str comparisons give v0.1's
values, validity, names, row order and errors (bench/w2/wire.sh: 8,762 frame-level content hashes over
11 key shapes x 9 sizes up to 100k (+ 300k / 1M cells) x 4 null patterns, Raw and Dictionary, equal to
the pre-W2.3 build's; tests/strwire.bend passes on both builds).

1. **Amends 17.3.4 (group_by / unique / n_unique rows)**: a Raw key is coded by `Hc.code.pk` (W2.4's
   packed coder: one walk per row hashes AND copies the code points, a hash hit compares flat words),
   not by `Hc.code(~ST.Str.hash, .., first = 1)`. Same codes: pk's ids are `Hc.code(first = 0)`'s, so
   group_by adds 1 in the pass that zeroes the null rows (`Grp.enc.p1`: `Sort.xmap` + 1, then
   `Sort.words.z`, as the Dictionary key already did); `k` = distinct + 1 as before. Measured both
   (provisional, IMPLEMENTING W2.3): equal within noise on 1M distinct short keys (median 189 vs 232 ms, ranges overlapping), pk
   ~15 % slower on distinct 45-char keys (lp 300k: 112 vs 93 ms), pk 2.2x faster on repeated keys read
   from a CSV (1M rows, 20k distinct 22-char keys: 525 vs 1,163 ms; n_unique 535 vs 2,851), because a
   hit of `Hc.code` walks the representative cons string at a scattered place (W2.4's finding).
   Cost: pk holds 4 bytes per code point of the distinct keys, presized at 8 words per row and doubled
   (peak RSS of lp_group_300k 585 vs 477 MB with `Hc.code.h`, one process each; v0.1 803 MB).
2. **Sort words of a Raw column** (`Sort.str_words`, a Raw sort key): `Rk.words` = `Hc.code.fnv` +
   the rank stage (17.3.2), unchanged from W2.2; the key is now BORROWED (`Rk.words` hands the rows
   back), which removes T3.2's item 5 exception (no `Column.clone` of a Raw key). Not moved to the
   packed coder: the rank stage reads entries through their first rows (`fr`) and UTF-8 byte lengths
   (`bl`), which `Hc.code.pk` does not answer; on repeated keys read from a CSV the hits still walk
   the representative string (open, IMPLEMENTING W2.3).
3. **`Dict.ranks` callers** (`Sort.kd`, `Sort.dict_words`, `Eval.zd.ord.m`, `Eval.ds.ext`) use
   `Rk.dict`. `ST.Dict.ranks` (Base Map) is DELETED from src/strs.bend; with `Sort.str_codes`,
   `Sort.codes.*`, `Sort.code.*`, `CS`, `Sort.pcodes`, `Sort.pmerge*`, `Sort.kbc*`, `Sort.str_fork`,
   `Sort.str_codes_par`, `Sort.ranks.*`, `Sort.str_words.b/.c` (src/sort.bend) and `Eval.nuniq*`,
   `Eval.distinct*` (the cons-list n_unique, src/eval.bend) it lives on only as the v0.1 REFERENCE of
   the differential tests, byte-identical, in tests/lib/v01str.bend.
4. **Raw n_unique** = `Hc.code.pk`'s entry count over the valid rows (`Eval.dropnull` as before) plus
   one for any null (15.2.5); `PROOF_evalops.bend`'s witness `aggdense_nu_s` names `Eval.nu.str`
   instead of `Eval.nuniq` (a witness, not a claim: no law changed).
5. **`Radix.*` and `WS` moved to src/radix.bend** (byte-identical; sort.bend, ranks.bend, eval.bend and
   groupby.bend import it) to break the ranks.bend -> sort.bend import cycle; eval.bend no longer
   imports sort.bend. No PROOF / LAWS file named them.
6. **Proof-import audit**: LAWS.bend unchanged; the Probe / EncProbe / MergeProbe / FindProbe premises
   are about `ST.Ix.seek`, untouched; `make proofs`, `make verdict`, `make mutation-check` green. The
   coder, the packed coder and the rank stage are tested-only, as the v0.1 code they replace (8.1,
   "Not proven" items 4 and 7 updated).

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
| `DF.read_csv(path)` (exists), `DF.read_csv_opts(path, opts)`, `DF.read_csv_schema(path, opts, dtypes: List<&2, D.DType>) -> IO(ResT(Frame))` | `R.Csv.read`, `R.Csv.read_with` | file read once (amended M4: in pieces of up to 64 MiB; str columns in the default storage, Auto: section 14 M4); 15.6 | `IoError{code, text}`; `ParseError{0, "malformed csv"}`; `ParseError{line, "expected <k> fields, got <g>"}`; `InvalidOperation{"csv schema: <d> dtypes for <k> columns"}`; `ParseError{line, "column <name>: cannot parse \"<text>\" as <dtype>"}`; row cap |
| `DF.read_csv_enc(path, opts, dtypes, enc: DF.StrEnc()) -> IO(ResT(Frame))` with `DF.str_auto()` (the default), `DF.str_raw()`, `DF.str_dict()`; `DF.encode_strings(f, dict: Bool) -> Frame`; `DF.dict_columns(f) -> Frame & List<&2, String>` (added M4) | `R.Csv.read_enc`; `C.Frame.encode`; `C.Column.is_dict` | the str storage: Raw (a string per row), Dictionary (a code per row, each distinct string once) or Auto (a Dictionary while the column has at most max(16384, rows / 64) distinct values, else Raw); values, dtypes, dumps and errors are the same in every storage; `encode_strings` converts every str column; `dict_columns` names the Dictionary columns in column order | as `read_csv_schema` |
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
15.5.2; the T2.2 oracle canonicalises the sign of zero for median). Worked example
`std/var [1,2,4] f32`: the correctly rounded values (exact var 7/3, std 1.5275252316..) are
`var = 2.3333333`, `std = 1.5275252`, but the algorithm above does NOT return them: `m` rounds
to 2.3333333, the squares `(x - m)^2` and their sum are f32, so it yields `var = 2.3333335` and
`std = 1.5275253` (0x3fc385f3), one ulp above, inside the error bound of 15.5.3. The algorithm is
the contract (tests/diff/r0006.bend pins it, Bend equals it bit for bit), not the correctly
rounded value. `std` of one value / empty / all-null =
null; `median [3,1,2] = 2`, `[4,1,2,3] = 2.5`, `[1,null,3,10] = 3`, `[1,NaN,3] = 3`,
`[] = null`. Result dtype f32 for u32/i32 inputs (Polars f64: documented).
`describe`'s rows are not this median: its min and max are the 15.5.2 min/max (NaN skipped, `-0.0 < 0.0`
on a tie), and its "25%", "50%", "75%" are the NEAREST-rank quantiles `sorted[round(p * (n - 1))]`
(half away from zero) of the 15.5.2-sorted valid cells, which is Polars `describe` with its default
`interpolation="nearest"` (Polars 2.0.0: `[1,2,3,4]` -> 25% 2, 50% 3, 75% 3). So for an even `n` the "50%" cell is
the upper middle value, while `DF.median` gives the interpolated `lo*0.5 + hi*0.5`.

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
columns. `collect` reads the file once (`Csv.read_with` with the frozen dtypes; amended
M4: in pieces of up to 64 MiB, not 1 MiB, see section 14 M4), strictly: a value that does not parse under the frozen dtype
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
type Env is Type:  Env{frames: List<&1, Named.Frame>, scans: List<&1, C.Frame>}
                   # frames: the user's names, unique by contract; scans: unnamed, filled by
                   # Exec.run only (v0.1 review, section 14 "v0.1 review: scan source identity")
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
| scans | a `ScanCsv` binds no name: `collect` reads every scan (after the binding checks) into env's separate, unnamed scan namespace, in postfix order, and the runner's scan takes the next frame from there. A `Source` reads only the user's frames, so no Source name (`"#scan0"` included) can ever resolve to a scan's frame, and no name is reserved. `validate_bindings` checks only Sources; a plan of scans alone validates against the empty env |
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
type errors and before any key is evaluated: `ng <= h`). `Concat` (M3): each binary step of the chain checks the saturating sum of its two heights before any column is built (section 14 "M3 table verbs" 3). See section 14 "M1 B04-i".

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
| `InvalidOperation{what}` | `"aggregation in select (v1: use group_by)"` and its `with_columns`/`filter` twins are **removed** (reductions are accepted); `"nested aggregation: <show>"`; `"group_by needs at least one key"`; `"group_by key is an aggregation: <show>"`; `"agg expects an aggregation: <show>"`; `"nested aggregation in agg: <show>"`; `"join: no key columns"`; `"join: left_on and right_on must have the same length"`; `"concat_vertical: no inputs"`; `"concat_vertical: input <i> schema [..] differs from input 0's [..]"`; `"cast <from> to <to>: row <i> holds <cell>"`; `"i32 out of range: <v>"`; `"csv schema: <d> dtypes for <k> columns"`; `"scan_csv <path>: data schema [..] differs from the plan's [..]"`; `"source <name>: data schema [..] differs from the plan's [..]"`; `"source not in env: <name>"` (replaces `"source not in env (or used twice): <name>"`); `"source bound twice in env: <name>"`; `"too many rows: <n> exceeds 8388608"`; `"exec: malformed plan (stack underflow)"`, `"exec: malformed plan (not one result)"`, `"eval: unexpected .."` (internal, unreachable from well-typed plans); `"exec: scan_csv not materialised: <path>"` (internal: `Exec.run_pure` called directly on a scan plan with no scan frame left in env; `collect` always materialises first) | |
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


**Decided after M2 (2026-10-09): lazy error order with scans.** `Exec.run` validates the plan
(`Plan.schema`, then `Exec.validate`), then reads every `ScanCsv` in plan (postfix) order, the
first failing scan's error being the result, then runs the pure runner `Exec.run_pure` (since
the v0.1 review on the plan itself, the scans' frames held in env's unnamed scan namespace;
the order is unchanged, `tests/regress/V01_a_scan_source_identity.bend` pins it). So a scan's IO, parse or frozen-schema error is reported before
any runtime operator error, even one that the old postfix interleaving would have reached
first. Eager programs read their files where the program reads them; the §15.9 admissibility
rule already exempts such multi-verb programs from eager-vs-lazy error agreement.

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
| NEW-2 | the interpreter (`bend file.bend`) overflowed the host stack on results of ~2^15 rows or more: `DF.dump` and `Column.from_scalars` recursed once per row (the native binary is fine) | 15.1, 15.8 | M1 (fixed for dump / from_scalars and CSV read / write, DESIGN.md 14) |
| V01-a | a user `Source` named `"#scan<k>"` validated and then read scan k's CSV frame (`concat([source "#scan0" x=[1], scan x=[2]])` gave `x=[2, 2]`), plans/REVIEW_V01_ASTRA.txt P1; `tests/regress/V01_a_scan_source_identity.bend` | 15.7 scans row, 15.9 scan order note | v0.1 review (fixed: scans in a separate Env namespace, section 14) |
| V01-b | no lazy-over-`scan_csv` coverage per verb (the IO / materialisation boundary), plans/REVIEW_V01_ASTRA.txt "Tests"; `tests/regress/V01_b_scan_verbs.bend` | 15.2 (every verb eager and lazy), 15.6.4 | v0.1 review (test added) |

Rows marked M0 are fixed in M0 itself (harness and tests); every other row gets an
`#! xfail <ID>` regression in M0 (eager, raw-lazy and optimised-lazy where
applicable) and loses the marker when fixed.

### M0 review (dump location)
- The §15.1 oracle lives in `src/dump.bend` (`Dump.frame`, `Dump.frame_k` which hands the frame back, `Dump.result`), not `Fmt.dump` in `src/fmt.bend`; `DF.dump(r: ResT(Frame))` and `DF.dump_frame(f)` (consumes `f`). A frame whose columns are longer than its height dumps an extra `excess` line; shorter columns print `?` cells. Both are outside the §15.1 grammar, so `bench/check.py --dump` rejects them.
- `scripts/test.sh` skips `tests/**/lib/*.bend` (helper modules imported by tests).


## 16. v0.2 performance design (engine) [W0, frozen for W3-W5]

Written by the W0 engine design lead (plans/M_02.txt W0; D1-D4 and D7 are this section's; D5/D6 belong to
the strings/reader design). Evidence: the disposable spikes under `bench/spikes/w0_engine/` (README there:
build lines, raw samples with the 1-minute load per process, emitted-C audit). Every number in this section
is PROVISIONAL: shared machine, load 17-33 during the sweeps, medians of 5 fresh processes, 1 ms clock.
The gate numbers are taken by the orchestrator on a quiet machine with the W0 harness.

### 16.0 The shape, in one paragraph

One balanced binary fork tree over a USER-DEFINED tree of owned chunks, ending in today's flat leaf
loops; fuse first, fork second; move or borrow buffers, clone only the second reference; U32 reductions
combine at the nodes, F32 reductions stay one sequential in-order pass; the chunked executor is opt-in
behind an engine flag with today's executor as the reference, and chunks are born at the source (the
reader, `from_scalars`, or an explicit conversion whose cost is charged), never rebuilt per operator.
Measured (S1): fusion alone 2.6-3x at one thread (q1 8.7 -> 3.3 ms, q2' 5.7 -> 1.9 ms); the chunk tree
costs nothing at one thread (q1 3.5, q2' 2.1); 12 threads 3.5-4.4x over the chunked one-thread time
(q1 0.8-0.9 ms, q2' 0.5-0.6 ms); grain 2^13..2^16 indistinguishable at 1M rows; building chunks for a
7-column flat frame 6.3 ms, more than the fused query, hence the boundary rule.

### 16.1 D1: owned chunks (frozen)

Type (src/chunks.bend, W5), one tree per 32-bit payload kind, monomorphic (templates would not cross the
`Type`-kinded constructors cleanly, and the leaf loops are per element type anyway):

```python
type CW is Type:                      # words: Bool / U32 / I32 payloads, validity masks, dictionary codes
  WL{n: U32, d: Nat, a: Array<U32>}   # n rows in 2^d slots (n <= 2^d); slots past n are padding, never read
  WN{rows: U32, lrows: U32, l: CW, r: CW}   # rows = lrows + rows(r); lrows = rows(l) (addressing without a second read)
type CF is Type:                      # F32 payloads: FL{n, d, a: Array<F32>} | FN{rows, lrows, l, r}
type CS is Type:                      # Raw strings: SL{n, d, a: Array<String>} | SN{..}  (Dictionary: codes in a CW, one Dict per column)
type CValid is Type:  CAllValid{} | CMask{m: CW}
type CColumn is Type: CBool{len, valid: CValid, data: CW} | CU32{..} | CI32{..} | CF32{.., data: CF} | CStr{.., data: CStrs}
type CFrame is Type:  CFrame{height: U32, cols: List<&1, CNamed>}
```

Invariants (`WFChunks`, Type-valued, smart constructors establish them, every kernel wrapper preserves
them; the spike's `laws_spike.bend` has the predicate and two of its preservation proofs):

- leaf: `n <= 2^d`, `WFArray(d, a)`; words 0/1 for Bool and masks; null slots hold the dtype default
  (the P0 invariants of section 9, per leaf);
- node: `lrows == rows(l)`, `rows == lrows + rows(r)`, no wrap (`lrows <= rows` as words; the row cap
  2^23 makes every sum of row counts wrap-free: smart constructors call `Kernel.check_rows` on the sum
  before building a node whose rows are not bounded by an existing frame);
- a frame's columns and every validity mask share the partition: the same shape, the same `n` at every
  leaf position. `WFCFrame` = equal heights, equal shapes (checked by one O(leaves) lockstep walk at the
  executor boundary, never per kernel), unique names, the zero-column convention of section 9.

Grain: leaves of `2^G` rows, `G = 14` (16K rows, 64 KB per U32 leaf; S1: grains 13..16 within noise at
1M rows, the fixed fork cost of ~0.3-0.5 ms dominates, so the grain is the memory knob, not the speed
knob). A frame of fewer than `2^G` rows is one leaf (= today's flat column exactly, so small inputs run
today's loops with no fork). Builders fold leaves into a balanced tree with a binary-counter stack
(`US.merge`: leaf i merges `tz(i+1)` times; the last leaf may be partial; a final collapse handles a
non-power-of-two leaf count). Flatten is an explicit-stack walk of `Kernel.copy_into` per leaf (0.6 ms
per 1M). Both are sequential per column and FORK ACROSS COLUMNS (independent owners).

Alignment (D1's question): columns of one frame never need alignment work because every row-changing
operator applies the same per-leaf decision to every column: filter compacts each leaf of each column
with the leaf's mask (outputs ragged, `n` per leaf, still aligned: S2 `ragged_zip`); head/slice cut the
tree (drop whole leaves, shorten the boundary leaf: O(leaves), no copy); concat is one node over the two
inputs (O(1), partitions compose: S2 `concat_zip`); literals never materialise (D3 F1) and a 1-row
aggregate broadcasts per leaf; sort/join/group_by outputs are built fresh with the output partition.
Different partitions arise only ACROSS frames (a column from another frame put into this one, horizontal
operations between frames chunked differently); then B is re-cut to A's partition by flatten + chunk-by-
partition (`UBP`, two passes, 2-3 ms per 1M column; S2 `misaligned`), once, at the frame boundary. A
lockstep walk that meets two different shapes is a bug in the engine, not a runtime path: `WFCFrame` is
checked at the boundary.

Rechunk policy: after an operator that drops rows, if `rows < leaves * 2^G / 2` (occupancy under a half)
rechunk every column of the frame: merge sibling leaves whose `n1 + n2 <= 2^G` into one leaf
(`Kernel.append`), bottom-up, forked over the tree, deciding by row counts only, so all columns take the
same shape with no shared plan (S2 `rechunk`: 64 -> 32 leaves, ~0.1 ms). Amortised bound: a rechunk copies
at most the current rows and runs only when the row count has at least halved since the frame's last
(re)chunk, so the total rechunk copying over any operator chain is at most 2x the chain's input rows.
Empty leaves (n = 0) vanish by the same merge. Never rebuild chunks per operator.

Empty frames: height 0 is one empty leaf per column (`WL{0, 0n, [0]}`, one slot: every leaf loop runs with
fuel 0 after one harmless read of slot 0); zero-column frames carry `height` with no trees (section 9).
Row-cap sums: node rows are checked at construction (above); a compaction never grows rows; concat checks
the saturating sum before building the node (as `TV.Concat.two` does today).

Compaction: per leaf, into a leaf of the SAME capacity `2^d` (not `depth_for(kept + 1)`): the legacy
branchless write lands every dropped row at the cursor `k`, and `k <= i < n <= 2^d` at every step, so
the cursor fits and no scratch slot is needed. That inequality is the `croom_of_cap` lemma (16.6); it
discharges `CRoom` at the leaf, which LAWS section 11 leaves as a hypothesis today. Ragged outputs keep
their `d`; the rechunk policy restores occupancy.

Sort/join boundary (initially): flatten the key and payload columns (one pass per column, forked across
columns), run today's flat kernels, build the outputs as chunks (one pass per column, forked across
columns); ONE conversion per boundary, every copy inside the clock (G6 reports "flatten/rebuild bytes"
per query). The F32 reduction path has its own boundary note in 16.4.

### 16.2 D2: ownership (frozen)

1. Moves at the operator level: `Exec.mark` already takes a Source on its last use. Inside an operator, a
   column referenced by expressions is MOVED out of the frame (`Frame.take`) when the operator consumes
   its input (select, filter + select, group_by, sort keys) and the column has exactly one reference in
   the operator's expression list; it is BORROWED (take, use a kernel that hands the buffer back, put back
   with `Frame.replace`) when the frame survives (with_columns, the filter's non-selected columns, a Source
   that is not on its last use); it is CLONED only for the second and later references of the same column
   within one operator (the liveness pass counts references over ALL expressions of the operator,
   including duplicates, aggregate inputs and key expressions). S4: a clone is 0.2 ms per 4 MB column, a
   take/replace is unmeasurable. The analysis is static and runs with the existing `Eval.static` checks,
   before any data work (error precedence unchanged).
2. Kernels allocate fresh outputs. In-place reuse of a dead operand measured identical to a fresh output
   (S4 `mapinplace` = `mapfresh` 0.8 ms; both loops are the same tight `spin`), so in place is used only
   where semantics want it (`mask_data`, `choose`) and never as an optimisation obligation.
3. with_columns evaluates every expression against the INPUT snapshot (borrowing), then replaces/appends;
   a self join clones the Source (today's rule) and the clone is counted.
4. Parallel lanes own disjoint leaves; a read-only input several lanes need (a permutation, gids, a
   dictionary) is cloned once per split point and the bytes are counted (S3: 2 perm clones per node). No
   `+` Array shared across lanes; no `Array.fork`.
5. Retained capacity: head/slice keep the parent leaves (as today); the rechunk policy bounds padding after
   drops; G6 reports copied bytes and retained-vs-logical rows per query (W1h, extended to chunk/flatten
   bytes in W5).

### 16.3 D3: fusion peepholes (the whole list; each carries a law in W4)

| id | peephole (Eval.compile / exec) | kernel | law (G5) |
|---|---|---|---|
| F1 | `Bin{op, e, Lit}` / `Bin{op, Lit, e}`: the literal as a scalar parameter, no broadcast array | `Kernel.map_p` instance | map_p cell = f(lit, a[k]) (template proof `map_cell`'s shape) |
| F2 | null-propagating arithmetic/comparison zip with validity: `out = both valid ? f(a, b) : default`, `vout = va & vb`, one loop (replaces vand + zip + fix) | new `Kernel.zipv` (4 inputs, 2 outputs; AllValid sides as a 1-slot ones array) | `zipv_cell`: value and validity slot by slot (`mask_and_cell` + zip cell + `fix_cell`) |
| F3 | a TOTAL cast feeding arithmetic (u32/i32/bool -> f32, bool -> u32/i32): the cast inside the zip template | the F2 kernel with a composed template | the cast's total-pair law composed (15.5.5) |
| F4 | `fill_null(e, lit)`: lit == dtype default: validity := AllValid, payload untouched (the null-slot invariant); other lit: one masked map with a scalar | none / `Kernel.map_p` + mask | `fix_cell` (slots are the default) + a validity law: it is NOT a no-op |
| F5 | filter predicate: mask AND kept count in one loop; written in place into a dead Bool operand when the predicate's leaf is a Col (else fresh) | new `Kernel.pred_count` | `popcount_sum` + the mask cell laws |
| F6 | compaction of k aligned columns with one mask in one loop (k <= 4 per loop by arity; chained) | new `Kernel.compact3/4` | `compact_contents` per column (same mask, same cursor) |
| F7 | Kleene and/or, floor_div/mod, strict casts: NOT fused (separate rules; W1d's `R{v, ok}` unboxed record replaces the per-row `Maybe`) | existing | existing; strict-cast row-major error precedence kept by evaluating fallible fragments as their own pass |
| F8 | `Select(plain cols, Filter(p, x))` at the exec level: compact only the selected columns | F5 + F6 | `filter_select_run`: production equivalence against `Exec.run_pure` of the two nodes |
| F9 | with_columns of k expressions: one tree walk evaluating all k per leaf (fusing the walks, not the loops) | tree congruence | congruence (16.6) |

Rules: fuse only total row-wise fragments; a fallible fragment (strict cast, str parse) keeps its own pass
and its row index; no reassociation, no FMA, F32 rounding points as written; `R{value, valid}` unboxing
is verified in the C (S1/S4: single-constructor records ride in registers, `spin_33`), not assumed.

### 16.4 D4: reductions (frozen)

- U32 modular sum, count, popcount: per-leaf fold, `U32.add` at the nodes (S3: 0.7 -> 0.2 ms at 12
  threads; law: `u32_fold_sum` per leaf + associativity). U32/I32 min/max: per-leaf fold, lawful combine
  at the node (associative, commutative, first-appearance irrelevant for words). F32 min/max: combine with
  `Kernel.fmin/fmax` only after the law that the 15.5.2 policy (NaN skipped, -0.0/0.0 tie) is associative
  and commutative; until then sequential.
- F32 sum/mean/std/var: ONE sequential pass in ascending row order, eager and grouped (15.5.3 unchanged).
  Over chunks that is an explicit-stack in-order leaf walk carrying `NS{s, c}` (S3 `fsum_leafwalk`).
  OPEN ISSUE: the walk measured 2.5x the flat fold (4.7 vs 1.9 ms per 1M) with the SAME compiled loop,
  at every grain including one leaf, in either run order; the C shows no per-row difference. W5 re-measures
  in situ; the fallback is to reduce F32 columns from a flattened copy (one 0.6 ms pass) or to keep F32
  reduction inputs single-leaf, both inside the clock.
- Forks across reductions: independent aggregates of one group_by run 2x2 balanced (each lane with its own
  gids clone), the columns of `describe` in halves, the columns of a gather in a balanced column tree
  (perm cloned per node). Aggregate INPUTS are evaluated sequentially first (errors in expression order),
  then the scatters fork (they cannot fail): error ordering preserved. Hot/skewed groups stay serial by
  construction (no per-group lanes in v0.2).

### 16.5 D7: the engine selector and the representation boundary (frozen)

- `Exec.run_with(engine, p, env)`, `engine: Engine = Reference{} | Chunked{grain: Nat}`; `Exec.run` =
  `Reference` until W8 flips the default (a separate commit from removal; the reference stays as the
  pinned oracle through v0.2). `bench/main.bend` reads `BF_ENGINE=chunked` and reports the engine in its
  JSON; the differential driver runs both engines on every case (G1).
- The boundary: `CFrame` exists only inside `src/cexec.bend` (the chunked runner: the same postfix code,
  `Exec.compile`/`Exec.mark` unchanged, a second step function over `CFrame`). Sources are converted at
  `ISource`/`IScan` (`CFrame.of_frame`: one pass per column, forked across columns, the bytes counted and
  the time INSIDE the clock) and the result converted back at the end (`CFrame.to_frame`). In W6 the
  reader produces leaves directly and `DF.dump`/`collect` accept a `CFrame` through the facade, which
  removes both conversions for scan_csv plans; for env-bound flat frames the conversion stays and is
  reported as "preparation" (G6) next to the compute number. No optimizer change: the chunked runner
  consumes the same plans (`release_run` keeps holding for `Exec.run_pure`; the chunked runner gets its own
  differential evidence, not a proof, in v0.2).
- Sort, join, unique, n_unique run today's flat code behind the boundary note of 16.1; group_by runs
  chunked for codes/count/max and flat (serial) for the F32 scatters.

### 16.6 Proof obligations (G5) and leaf-lemma reuse

Proven in the spike (`bench/spikes/w0_engine/laws_spike.bend`, bend and --verdict; a wrong claim is refused):
`cmap_shape` (the chunked map keeps counts and shape) and `cmap_leafwise` (the chunked map is the flat map
leaf by leaf, a node congruence whose leaf lemma is PROOF_contents' `map_cell`, 8 lines). Obligations for
W5, with the reusable leaf lemmas and the budget (lines of proof, estimated from the spike and from the
M5 proofs' sizes):

| obligation | leaf lemma reused | new work | budget |
|---|---|---|---|
| `WFChunks` / `WFCFrame`, smart constructors, preservation by every wrapper | `wf_new`, `wf_array_set` | the two predicates, one bundled induction per wrapper (counts come back with the shape: a live child goes to ONE lemma) | 30-60 each |
| flatten / of_frame bridge: logical cells (offset form `rdN(o, U32.add(off, k))`, Nat `CatFits`, no subtraction) | `append_cells`, `copy_into_w` (PROOF_append) | one offset lemma per leaf position, by induction over the tree | 150-250 |
| map / zip / zipv / map_p congruence per instance | `mask_not_cell`, `mask_and_cell`, `mask_or_cell`, `map_cell`/zip templates | one `Leafwise` predicate per kernel, 8-15 lines each | 10-20 each |
| per-leaf compaction (F5/F6) | `compact_contents`, `compact_keeps_mask`, `popcount_sum` | `croom_of_cap` (0/1 words and n <= 2^d give `CRoom`: the cursor k <= i < n, invariant by induction) + `CompactLeafwise` congruence | 80-150 + 20 |
| rechunk | `append_cells` | congruence + counts | 40-80 |
| reductions | `u32_fold_sum`, `popcount_sum` | `U32.add` associativity at nodes (trivial); min/max combine laws (U32 trivial; F32 fmin/fmax assoc/comm under 15.5.2: new, 100-200) | 20 / 100-200 |
| gather by leaf (join/sort outputs) | `gather_contents` (leaf-local index arrays) | congruence | 20 |
| fused kernels (16.3) | the composed cell laws | one content law per kernel variant | 30-80 each |
| `filter_select_run` (F8) | `release_run`'s style | production equivalence over `Exec.run_pure` | 100-200 |
| moves (16.2): take/replace observes as get_cloned | `get_cloned_typed`, `cell_pure` | an observation lemma over `Frame.take`/`Frame.replace` | 60-120 |
| mutation controls | `scripts/mutation_check.sh` | one patch per new kernel/bridge | tests |

Not needed if the congruence form is used: `sub_lt_of_lt_add` (subtraction-addressed cells; stated open in
the spike as the measured gap of the `ccell` model: 60-150 lines of new word arithmetic, the toolkit has
`B.cmp_nat_u`/`B.le_nat_u`/`PST.lt_nat_of_u`/`B.add_sub` but no `to_nat` of `U32.add`/`U32.sub`).

### 16.7 Work breakdown (single-agent tasks; tier)

W3 ownership and sort (~3 days):
- T3.1 [opus] liveness analysis and moves/borrows in Eval/Exec (16.2 rule 1), the observation law, copy-byte
  counters (G6), diff + tests (duplicate references, self join, with_columns snapshot).
- T3.2 [sonnet] sort pipeline: words built reading the column in place, no identity xmap / iota gather,
  one read pass for vary + sortedness + all histograms, two ping-pong buffers, sorted-skip; tests + bench.
- T3.3 [sonnet] group_by: move dead aggregation inputs, drop the single-key constant combine + second
  densify after checking sparse ids/nulls/first appearance; tests.
- T3.4 [sonnet kernel + opus law] Sort+Head bounded gather (W1g) with its equivalence law.
W4 fusion (~4 days):
- T4.1 [opus] kernels `zipv`, `pred_count`, `compact3/4`, `R{v, ok}` variants + content laws + mutation
  patches.
- T4.2 [sonnet] Eval.compile peepholes F1/F3/F4 and the F5/F6 wiring; tests with competing errors in
  different rows/operands; diff. [opus review for error precedence.]
- T4.3 [opus] F8 exec shortcut + `filter_select_run`.
W5 chunks (~6 days):
- T5.1 [opus] `src/chunks.bend`: types, WFChunks, builders, flatten, rechunk, lockstep walkers,
  smart constructors; the shape/bridge/`croom_of_cap` laws.
- T5.2 [sonnet kernels + opus laws] chunked wrappers for map/zip/zipv/pred_count/compactN/gather/fold/
  the F32 walk; `Leafwise` laws; the in-situ F32 walk measurement (16.4 open issue) with the fallback.
- T5.3 [opus] `src/cexec.bend` chunked runner behind `Engine`, boundary conversions forked across columns,
  G1 old/new differential across thread/grain counts, boundary-row tests (rows around 2^G, selectivities
  0/1/50/100%, many tiny chunks, empty frames).
- T5.4 [sonnet] coarse forks: describe columns, 2x2 aggregates, column-tree gathers; bench cells.
- T5.5 [sonnet] `bench/m2` harness cells for chunk/flatten bytes and per-phase times (G6).

### 16.8 G2 / G3 thresholds per query (proposed at W0; the orchestrator freezes them on a quiet machine)

Serial fractions from the code and the spikes (1M rows, after W3/W4, the chunked engine, inputs already
chunked; Amdahl at 12 threads = 1 / (s + (1 - s) / 12)):

| query | forkable stages | serial stages | s | Amdahl(12) | G2 proposed (12 vs 1 thr) | G3 1-thread (ms) |
|---|---|---|---|---|---|---|
| q1 | fused predicate+count, 3-column compaction per leaf | fork iteration (~0.4 ms), result assembly | ~0.1 | 5x | **>= 3x** (measured 3.5-4.4x) | <= 3 (keep; 3.3 under load) |
| q2 | one fused 4-input loop per leaf | fork iteration | ~0.15 | 4.6x | **>= 3x** (measured 3.4-4x) | <= 3 (keep; 1.9-2.1) |
| q3 | q2 loop, region codes/densify per leaf, count, max | two F32 Neumaier scatters (1.3 ms each, run as 2 lanes: critical path 1.3), the 8-row sort | ~0.3 (0.5 if the walk anomaly stands) | 2.6x (1.7x) | **>= 2x**; 3x aspirational, conditional on the F32 walk | <= 12 (keep, conditional on W3) |
| q4 | key words per leaf (3 passes), per-leaf histograms, the 10-row gather | every radix scatter pass (one owner per output array: ~8 passes after digit skipping, 8-10 ms) | ~0.75 | 1.3x | **>= 1.3x**; >= 2x only with a partitioned parallel sort (serial top-digit partition into owned buckets, sorted in parallel, concatenated as a tree), proposed for W5 only if T5.1-T5.3 land early | <= 20 (keep, conditional on W3's argsort <= 15) |
| q5 | the code probe per leaf (a gather), the 7 output gathers across columns, category codes + U32 sum | the build (64 rows), the CSR count/offset pass, the row-cap check | ~0.45 | 2x | **>= 1.5x** | no > 10% regression (keep) |
| q6 | the 4 columns in parallel (2x2) | each column's own F32 passes and its full sort are serial per column | bounded by the heaviest column | <= 4x | **>= 2x** | <= 60 (keep; W1c) |

The G3 one-thread numbers stay as the plan's aspirational values, now with the measured support above;
q3/q4 are conditional on W3 landing first. Every compute number is reported next to its preparation
(chunk build / flatten bytes and time) and end-to-end (G6); a flat env-bound Source pays the conversion
inside the end-to-end number, a chunked scan does not. Small-input/control medians within 10% as planned
(a frame under 2^G rows is one leaf running today's loops).

### 16.9 Risks and open issues

1. The F32 in-order leaf walk (16.4): unexplained 2.5x; re-measure in situ (T5.2); fallback costed.
2. Conversion cost at the boundary: 0.8-0.9 ms per 1M-row column to chunk, 0.6 ms to flatten; forked
   across columns; charged. The G2 ratio is measured on chunked inputs; the end-to-end number carries the
   conversion for flat Sources.
3. All W0 ratios were taken at load 17-33; the 12-thread cells could not have 12 free cores. The fused
   one-thread numbers are robust (variance < 10%), the thread ratios are lower bounds.
4. The fork tree's fixed cost (~0.3-0.5 ms per iteration) caps 12-thread gains for operators under ~2 ms
   of work; fusion before forking (W4 before W5) is load-bearing, not optional.
5. Forking across 7 gathers and across 4 aggregates showed no gain on the loaded machine; the design keeps
   these coarse forks but does not count on them for G2.
## 17. v0.2 performance design (strings and reader)

Work package W0 of plans/M_02.txt, design decisions **D5 (strings)** and **D6 (reader)**. The
engine decisions D1-D4 are section 16 (written in parallel; not edited here). Section 15 (the
v0.1 data contract) does not change: every rule below produces the same values, validity,
names, row order, dictionary codes, errors and error precedence as v0.1.

Evidence: disposable spikes in `bench/spikes/w0_strings/` (its README: build and run lines,
tools; raw samples in `results/*.jsonl`, one record per process with the load before and
after). **Every number here is PROVISIONAL**: the machine was shared (1-minute load mostly
11-20 during the campaigns, spikes to 100-280 from other agents; each table gives the load range
of its samples), medians of 5 fresh interleaved processes, Bend 2.0.36 native, Apple M2 Pro.
Gate numbers are the orchestrator's (quiet machine, bench/m2/). Every spike run was checked
against the v0.1 code by a checksum of its output (same first-appearance codes, same sort
words, same cells, validity, dictionary codes and dictionary size).

### 17.1 Platform facts measured in W0 (they constrain both designs)

1. **The File API returns cons lists only.** Base 2.0.36 has `File.read(f, max) -> String`
   (bytes decoded by the runtime's `io_str`: an invalid byte becomes U+FFFD and the byte is read
   again), `File.read_bytes(f, max)` and `File.read_at(f, off, max) -> List<&2, U32>` (one cell
   per byte; `read_at` is `pread`: the position does not move), `File.size`, `File.open/close`.
   No read into an `Array`, no mmap, no streaming primitive other than repeated reads.
2. **IO is sequential.** The syscall runs on an IO helper thread, but the result's cons cells are
   built (`io_list`, `io_str`) on the single IO event-loop thread, and `IO.fork` / `IO.spawn` are
   green threads on that loop. Several handles on one file are possible (one `File.open` each,
   each affine and threaded) but buy nothing: list construction serialises. **Parallel work
   exists only inside pure parallel lets**: "a producer of owned pieces" is a sequential IO loop
   and the parse forks after it.
3. **Hotness is decided per constructor over the program's reachable code.** In every program
   importing frame.bend, `String` (SCon, Chr), `List` (Con), `Some`, `CsvCell`, `CsvRec` and ~200
   more constructors are hot (`tools/hot.py build/rd_frame.c`): every constructed field is
   `rfc_seal`ed (one extra heap cell) and every read goes through the redirect (`term_peek`: one
   more dependent load; `ctr_take`: an atomic and a free). Private single-constructor loop records
   (the spike's 17-field tokenizer state `TK`, `PK`, `LW`, `LS`, ...) stay cold in the integrated
   program and are passed unboxed in registers (spin arguments; no allocation per row). So
   **cold private loop state survives integration; private cold cons types do not help, because
   their input arrives as hot String / List from the File API.** In situ (T4, 41 MB, 1 thread,
   load 12-13):

   | probe | cold build | inside a frame.bend program |
   |---|---|---|
   | File.read_at 1 MiB pieces, only count the bytes (the API floor) | 117 ms | 273 ms |
   | the producer of 17.4.1 (read_at + pack + lexical scan) | 197 ms | 334 ms |
   | today's parser: File.read of the whole file + H.step (records of cells, no columns) | 361 ms | 889 ms |

   The review's "2x hot tax" on the parser is confirmed (2.5x here). The new reader has exactly
   one hot boundary, the byte list of one piece, charged to the producer.
4. **Freeing cons strings is expensive and is timed where the last owner drops them**: 1M short
   strings ~0.2 s, 1M 41-char strings ~0.7 s (the first T1-T3 campaign, results/superseded/,
   dropped the input rows inside the timed region). A field bound by a `match` and never used is
   dropped AT the match, before a later `IO.now()`: benchmarks keep inputs alive past the clock,
   kernels hand string arrays back instead of dropping a consumed copy (rule 2 of the brief).
5. **Walking cons strings**: hashing 1M strings laid out in allocation order costs 2-4 ns per
   code point; the same data as a flat UTF-8 buffer 0.2-0.6 ns (T6). Scattered strings (built
   between other allocations) walk slower; a coder probe costs 80-130 ns per short key (T1).
6. **f32**: `F32.read` is C `strtof` on the text (correctly rounded; accepts `nan`, `inf`,
   exponents, a sign; rejects hex); `F32` is C `float` and the emitted division is one float
   division.

### 17.2 Summary of the evidence (tables in 17.9)

- **Coder (T1)**: the flat coder codes 1M distinct short keys in 129 ms against 20.4 s for
  today's Map coder (158x), 1M 41-char shared-prefix keys in 308 ms against 87 s (283x); skewed
  71x, low-cardinality 7x, all-equal 6x. Per-row time grows at most 1.6x from 100k to 1M rows
  (cache), never superlinearly. Codes identical to `Sort.str_codes` on every shape.
- **Ranks (T2)**: on 1M distinct keys, ranks after coding take 370 ms (radix refinement) against
  1,152 ms (merge sort over a flat code-point buffer) and 7,052 ms (Base Map over the distinct
  entries); today's `Sort.str_words` takes 23 s. Words identical on every shape.
- **Parallel coding (T3)**: owned hash partitions reproduce the sequential codes exactly and give
  2.8x (distinct) / 3.7x (41-char prefix) at 12 threads on 1M rows; skewed and all-equal keys
  gain little (the hot keys' lane) and lose at 1 thread.
- **Reader (T5)**: the piece reader parses the 41 MB sales file (explicit schema, Dictionary
  strings) in 987 ms at 1 thread and 472 ms at 12 (443 with 256 KiB pieces), RSS 266-310 MB,
  against 5,538 / 2,276 ms and 1,227-1,245 MB for today's reader; the cells, validity and
  dictionary codes are identical. The serial producer is 334-356 ms of it (34 %).
- **Adversarial boundaries (T5b)**: 30 adversarial files x 15 piece sizes (1 byte .. 1 MiB):
  identical values, codes and errors to today's reader except two header-step cases the spike
  does not implement (17.4.1).

### 17.3 D5 strings

#### 17.3.1 The distinct-key coder (replaces `Sort.str_codes`, `str_codes_par`, `pcodes`, `pmerge`, `kbc`)

    Hc.code(~hash: String -> U32, +n: U32, +d: Nat, +first: U32, a: Array<String>)
      -> HC{next, a, hs, rp, ids, codes, fr}      # a comes back untouched

- **Table**: three `Array<U32>` of 2^b slots, `b = ceil(log2(max(2n, 2)))`, at most 24 (the row
  cap 2^23 gives 2n <= 2^24): `hs[j]` the key's hash, `rp[j]` its first row + 1 (0 = empty),
  `ids[j]` its id. **No string is stored in the table**: the rows stay in `a`, borrowed and handed
  back. Load <= 1/2 for any input (every row distinct at worst): presized once, never grown,
  never rehashed.
- **Hash**: FNV-1a over the code points (`ST.Str.hash`, the function `ST.Dict` uses), passed as
  the `~hash` template so a test can instantiate a constant hash (every probe collides) and
  exercise the comparison path. Slot = the top b bits of `h * 2654435769`; linear probing.
- **Equality**: a probe compares the stored hash first and walks the strings only on a hash hit
  (the representative row `rp[j] - 1` against the current row: a tail-recursive, borrowed
  code-point walk with early exit). A hash match never decides equality.
- **Ids**: first appearance, starting at `first` (group_by 1, unique / ranks 0): identical to
  `Sort.str_codes` (T1). `fr[id - first]` = the entry's first row: the entries, for ranks, and
  for a parallel remap.
- **Probe exhaustion**: fuel 2^b; unreachable, because an empty slot exists while distinct keys
  <= n <= 2^(b-1). On fuel exhaustion the probe answers the slot it stopped at, exactly like
  `ST.Ix.seek`; correctness then rests on the same kind of hypothesis as `LAWS.Probe` (the probe
  stops at an empty slot or at the key), stated for this table and not proven (tested-only, 17.6).
- **Empty / null**: `""` is a key like any other. A Raw null slot holds `""` (v0.1 invariant), so
  null rows get the code of `""` and consumers apply validity afterwards as today (`Grp.zero`
  zeroes null rows' codes; `Sort.words.z` their words; n_unique counts the distinct codes of the
  VALID rows plus one if any null, 15.2.5: a `""` coded only from null rows is not a value).
  n = 0 answers `next = first` and touches no slot.
- **Cost** (T1, 1 thread): 80-130 ns per row for short keys, ~310 ns for 41-char keys (7.6 ns
  per code point); per-row growth 100k -> 1M at most 1.6x. Memory: 12 bytes x 2^b (24 MB at 1M
  rows) + 4n (codes) + 4n (first rows), transient.

#### 17.3.2 Lexical ranks (never first-appearance ids as sort words)

First-appearance ids are not an order. Sorting by a string column, string min / max and `<`
between dictionaries need the RANK of each distinct entry in code-point order with a prefix first
(Base `Map.to_list` order = `String.is_lt`), mapped back by one gather:
`rank[id] = position of entry id among the entries`, `word[row] = rank[code[row]]`.

1. **Pack** the k entries once into big-endian U32 words of UTF-8 bytes (4 bytes per word, word
   offset and byte length per entry). UTF-8 byte order is code-point order, so comparing words
   compares strings. W2 computes the byte length in the coder's hash walk (the spike walks each
   entry twice: the pack is 60-75 % of the stage, T2). **Fallback**: a code point above U+10FFFF
   (a `Chr` can hold any U32) has no order-preserving 4-byte form; the packer then switches the
   column to one code point per word (same algorithm).
2. **Radix refinement**: round r stable-sorts every entry by
   `(group, word 2r, word 2r + 1, min(bytes left, 8))` with four `Radix.sort` calls (LSD: last key
   first; digits that never vary are skipped), then splits the groups (group = equal keys so far,
   id = its first position). The last key puts a string before its extensions even when they
   continue with U+0000 (padding and NUL compare equal, the remaining length does not). Distinct
   entries end in singleton groups after `ceil((LCP + 1) / 8)` rounds (LCP: the longest common
   prefix of two entries, in bytes); the loop stops at the first round with no tie.
3. `rank[perm[p]] = p` (one scatter), the words by one gather.

**Decision: radix refinement** (T2: 3.1-3.2x faster than the merge sort, 19-25x faster than Base
Map over the same entries, identical words on every shape). Left to W2 if measured worthwhile:
re-sort only the tied entries each round (long shared prefixes re-sort every entry 6 times today).
Plugs into `Sort.str_words` (Raw: coder, then ranks) and `ST.Dict.ranks` (Dictionary: the entries
are already distinct: ranks only), hence every `Dict.ranks` caller (`Eval.zd.ord.w` comparisons
between dictionaries, `Eval.ds.ext.r` min / max). No rank cache in v0.2 (no invalidation story;
the stage is O(k x rounds) per request).

#### 17.3.3 Probe ownership (the parallel question)

- **Sequential borrowed coder / probe (DEFAULT)**: one table; the rows (and, for a join, the
  build side's rows) borrowed and handed back; no copy; deterministic by construction.
- **Per-worker copies: rejected** above 4096 slots (today's `Probe.levels` bound, kept). A lane
  needs the representative STRINGS, not only the three flat arrays: a deep copy (`Str.copy`,
  today's `Dict.clone`) walks and allocates every key per lane (1.4 s of the 5.1 s distinct-key
  join, Fable); a shallow `Array.clone(String)` shares every key (an atomic per read in every
  lane, and a hot type). `Array.fork` is never used.
- **Owned hash partitions (the approved parallel architecture, demonstrated in probe.bend)**:
  hashes by one balanced fork over the rows' ANode spine (it copies the pointer blocks down and
  up; included in the timings, 11-39 ms at 12 threads, small next to the string walks: the one
  measured exception to brief rule 3, for string arrays only); partition id = top L bits of
  `h * 2246822519` (independent of the table's slot bits); one stable `Radix.sort` groups the rows
  by partition, in row order inside each; each partition's rows are MOVED (`Array.swap`) into its
  own arrays (strings, hashes, global rows); ONE fork over the partition tree codes each
  partition with its own presized table; the global first-appearance order comes back from the
  entries' first rows by one flat scan over the rows (deterministic, independent of completion
  order); codes are scattered to row order and the strings moved back. Nothing is copied or
  shared. Skew: a hot key's rows land in one lane (T3 skew / equal: 1.2x at 12 threads, and
  skew loses 1.8x at 1 thread).

**Decision for v0.2**: group_by / unique / n_unique / str_words code **sequentially, borrowed**;
the join probes **sequentially, borrowed** (17.8: the G3 cells are met without parallelism).
W2.5 may enable owned partitions for n >= 2^18 rows and >= 4 threads, never at 1 thread, if the
gate machine confirms >= 1.5x at 12 threads on 1M distinct keys and no skew regression above
10 %; its serial phases (partition move-out, remap, move-back) are inside the measurement.
`Probe.fork`'s per-lane `Dict.clone` disappears with W1a.

#### 17.3.4 Integration points (W2)

| consumer | v0.1 | v0.2 |
|---|---|---|
| group_by Raw key (`Grp.enc.str`, `Grp.enc.strk`) | `Sort.str_codes_par(n, d, 1, a)` (Map, 8 blocks, sequential re-insert merge) | `Hc.code(~ST.Str.hash, n, d, 1, a)`; identical codes; `Grp.zero` unchanged |
| unique / n_unique Raw | same coder / list sort | `Hc.code`; n_unique = distinct codes of the valid rows + 1 if any null (15.2.5) |
| sort by Raw (`Sort.str_words`) | coder + `Map.to_list` ranks | `Hc.code` + 17.3.2 |
| order on a Dictionary (`ST.Dict.ranks`) | Map over the entries | 17.3.2 over the entries |
| join Raw key (`Key.enc.sb` / `sp`) | `J.Dict` (SSlot strings) + `Probe.fork` with `Dict.clone` per lane | a flat table over the right column (ids = first appearance on the right), sequential borrowed probe of the left; miss / null = DEAD as today |
| join Dictionary key (`Key.ids`) | `J.Dict` over the right entries | the same flat table over the entries |
| `ST.Dict`'s index (`Ix`: `Array<SSlot{String, id}>`, grown by doubling) | unchanged by W2.1-W2.5 | optional W2.6: flat `hs` / `ids` arrays presized when the entry count is known (the reader's merge, 17.4.7) |

**Dictionary laws stay conditional.** `LAWS.Probe`, `EncProbe`, `MergeProbe` and `FindProbe` are
hypotheses about `ST.Ix.seek`. If W2 leaves `ST.Dict`'s index alone, LAWS.bend does not change.
If W2.6 migrates it, the hypothesis is RESTATED over the new seek (same shape: "the probe for s
stops at a slot that is empty or holds s"), still a hypothesis, and `dict_code_spec`,
`strs_encode_cells`, the merge / recode / find laws keep their statements; no obligation
disappears by omission (G5). The coder, the rank stage and the join's string table are
tested-only, as the code they replace (v0.1 has no content theorem for `Sort.str_codes`,
`Sort.str_words` or the join's string table), and are listed so in the assurance matrix.

### 17.4 D6 reader

#### 17.4.1 Pipeline

    header step (sequential: the reference logic on a bounded prefix)
      -> producer (IO, sequential): read_at pieces -> packed bytes + lexical scan -> regions
      -> ONE balanced fork over the regions; per region: tokenizer -> typed column loops ->
         per-region string coders -> entry decoding
      -> combine (sequential, region order): error summary, dictionary merge, remap, row cap,
         concatenation into the frame's columns (or the engine's chunk leaves, 17.5)

1. **Header step**: v0.1's prefix logic (it exists for `scan_csv`, 15.6.4): leading blank lines
   (has_header), the header record and its names, the width k, the dtype-count check of an
   explicit schema, headerless names `column_i` (width of the first non-blank record), empty
   file / header only (no region parsed), inference over the first `infer_rows` records
   (17.4.5). It answers the byte offset where the data starts and the physical line there; the
   producer starts at that offset. (The spike only skips the first non-blank record of the first
   non-empty region: its two adversarial misses, `lead_blank` and `empty`, are this step.)
2. **Producer** (`Rd.*`): `File.read_at(f, off, P)` pieces; each piece's byte list is walked ONCE
   (`Pk.go`), packing 4 bytes per U32 word (little endian) into the current region and running
   the lexical scan in the same walk: quote parity, LF count, the last record terminator (an LF at
   even parity). A region ends after the piece's last terminator; the bytes after it are
   replayed into the next region (a copy of at most one record). A piece with no terminator (a
   record longer than a piece) leaves the region open and it grows (doubling capacity; the spike
   re-replays, quadratic only for multi-piece records). Each region records its first physical
   line and its terminator count, an upper bound of its rows that sizes its builders (never the
   piece size). **P = 256 KiB - 1 MiB** (T5: 4 MiB leaves 10 regions for 12 threads; 256 KiB is
   the fastest at 12). v0.1's 64 MiB default (14 M4 item 5: the allocator scattered the CONS cells
   of consecutive pieces) does not apply to flat regions. Serial cost: 330-350 ms per 41 MB in a
   frame.bend program, of which ~270 ms is the File API floor (17.1.3).
3. **Fork**: regions -> leaves in file order -> a balanced tree by pairing (`Rt.top`; never
   1-vs-rest) -> `a b = Ln.tree(l) Ln.tree(r)`. Everything a lane touches is its own (region
   bytes, field arrays, builders, string table); the schema list is the only shared value.
4. **Lane**: tokenizer (17.4.3), one flat loop per column (17.4.4), the region's string entries
   decoded once each (UTF-8 with `io_str`'s rules).
5. **Combine**: 17.4.6, 17.4.7.

#### 17.4.2 Global record boundaries

The producer scans sequentially, so every region starts at a globally valid record boundary and
no lane guesses its start state. Argument (the reader is tested-only; this is the reasoning the
tests check): the hub parser is inside a quoted field exactly in mode ME. Before the first
rejecting byte q, every `"` either opens a quoted field (MS -> ME), closes or half-escapes one
(ME -> MQ) or completes a doubled quote (MQ -> ME); each flips the quote parity, and ME holds
exactly at odd parity (MS, MB, MSC, MBC, MQ, MQC at even). Hence an LF ends a record iff the
parity before it is even, up to q. Every cut before q is a true record boundary, so the lane whose
region contains q starts at a true boundary, parses as the sequential parser does and rejects at
q; well-formed input makes no lane reject; an input that ends in ME has odd final parity and its
last lane rejects at the end. Cuts after q may be wrong, which is harmless: malformed quoting
outranks every other error (17.4.6). CRLF split across pieces, `""` at a piece edge, a UTF-8
sequence split across pieces and records longer than a piece need no special case (bytes are
carried; cuts are at ASCII LF bytes). **Associative lexical-state summaries are not needed**: the
producer is sequential anyway (17.1.2). If a parallel producer ever exists (an Array-returning
read), each piece summarises its parity and its last LF at even and at odd local parity (plus LF
counts) and the summaries are prefix-composed in piece order.

#### 17.4.3 Tokenizer

One flat loop over the region's words, 4 bytes per word, each byte one transition of the modes
MS / MB / ME / MQ / MQC (field start, bare, in quotes, after a quote, CR after a closing quote) on
the classes LF / CR / separator / quote / other. A bare field keeps its CRs and drops one CR right
before the LF or the end of input that ends it (exactly the hub's CR-holding modes MSC / MBC); a CR
after a closing quote must be followed by LF. Output per region: field start / end / flags
(quoted, holds a doubled quote) at slot `r * k + c` in three flat `Array<U32>`, each kept
record's physical line, the first ragged record (line, width), a reject flag. A blank record (one
empty unquoted field) is skipped when k > 1 and kept as a null row when k = 1; LFs inside quotes
count toward physical lines. No allocation per byte: the state record is passed in registers
(C: `spin_296` -> `spin_289` -> `spin_274` in build/rd_frame.c, only `blk_read` / `blk_write`).
Cost: ~0.4 s per 41 MB at 1 thread (9.6 ns per byte; the kernel W6 should tighten: the state has
17 fields and each byte is a non-inlined call).

#### 17.4.4 Typed column loops (no CsvCell, no per-field String, no reverse / trim lists)

Per column one flat loop over the region's records reading `[start, end)` from the packed bytes,
trimming ASCII `Char.is_space` bytes (9-13, 32: the same set on bytes as on code points):
- **u32**: `acc' = acc * 10 + (b - 48)`, ok while `acc' / 10 == acc`: U32.read's own test, so every
  non-digit byte (a UTF-8 byte >= 0x80 too) fails exactly as its code point does. Empty -> null.
- **i32**: an optional `-`, then the u32 rule and `I32.read`'s bounds (W6.2).
- **f32**: fast path `[+-]digits[.digits]` with mantissa M <= 2^24 and at most 10 fraction digits:
  `F32.div(U32.to_f32(M), 10^fd)` is ONE correctly rounded division of two exact f32 values
  (Clinger), the value `strtof` returns (negative zero by `F32.neg`). Anything else (exponents,
  `nan`, `inf`, long mantissas, escaped quoted fields) decodes the field and calls `F32.read`.
  Bit-equal to `F32.read` on 20,000 random fast-path decimals and every edge of tools/adv.py.
- **bool**: exactly `true` / `True` -> 1, `false` / `False` -> 0 after trimming.
- **str**: a per-region coder keyed on byte RANGES (FNV-1a over the content bytes, a doubled quote
  read as one; bytes compared on a hash hit); validity = quoted or non-empty (15.6.1); the
  region's entries = each entry's first content, decoded once. Two different byte sequences can
  decode to the same string (invalid UTF-8 -> U+FFFD), so region codes are never exposed: the
  merge (17.4.7) codes decoded strings.
- the first bad cell per column per region: its row; its line from the region's lines and its
  text decoded from the region's bytes inside the lane (no second read).
Cost per column at 1 thread (T5 phases): u32 ~11 ms, bool ~20 ms, f32 ~45 ms, Dictionary str
~65-70 ms per 1M rows.

#### 17.4.5 Inference, schemas, headerless, empty input (contracts kept)

- explicit schema: no inference; the dtype count is checked against the header width in the
  header step, before any region is read.
- `infer_rows = N > 0` (default 100): the header step infers from the first N records with the
  reference code (`Csv.infer.col` on a bounded prefix, as scan_csv), freezes the dtypes, and the
  regions parse strictly: a later value that does not fit is that column's bad cell
  (`ParseError` at its line), as 15.6.3 requires.
- `infer_rows = 0` (all rows decide): two passes over the packed regions (in memory: no second
  read). Pass 1 per lane, per column: `has_value` and the four "every cell fits" flags (u32, i32,
  f32, bool) with the same field rules; AND (has_value: OR) over lanes is order-free;
  `Csv.pick` decides; pass 2 parses typed. Cost: one more tokenizer + classify pass, forked.
- headerless, empty file, header only, blank lines before the header: the header step, exactly
  15.6.2; the producer starts after it.

#### 17.4.6 Error precedence (15.6's order, combined in region order, never completion order)

1. malformed quoting anywhere: some lane rejected (or the final parity is odd);
2. no data records: the empty frame, or the dtype-count error (header step);
3. the first ragged record in file order (the first region, in order, that saw one);
4. the dtype count (header step);
5. the row cap: the total rows (sum over regions) checked before the combined columns are
   allocated (region parts are bounded by their region, not by the cap);
6. the first column in column order holding a bad cell, at its first such row (the first region
   with one for that column), with its line and text.
tools/adv.py checks 1, 3 and 6 and their competition (malformed after ragged, an earlier bad
cell in a later column) at 15 piece sizes.

#### 17.4.7 Dictionary merge, storage choice, Raw

- Per Str column, regions in order: each region's entries, in its local first-appearance order,
  are coded into ONE `ST.Dict` starting from `Dict.empty()` (`""` = code 0) by `ST.Dict.code`
  (a `Dict.merge` of the region's entries); `map[local id] = global code`; the region's codes are
  remapped by one gather. The global codes are the column's first-appearance order, i.e. v0.1's
  codes exactly (identical checksums including codes and dictionary size). Serial cost: entries
  x regions probes (2.6k for the sales file: 18-24 ms of merge + concatenation for 7 x 1M cells).
- **High-cardinality columns**: read as a 1M-distinct Dictionary column (`id` as str), the merge
  is 629-681 ms serial (T5: 1M `Dict.code` calls into an index that grows by doubling). W6.3 must
  (a) decide EncAuto's fallback per region BEFORE decoding entries (a region whose distinct count
  already exceeds the threshold makes the column Raw: rows decoded in the lanes, no merge) and
  (b) presize the global coder for the forced-Dictionary case (W2.6 or the flat coder of 17.3.1
  over the entries, then `Dict` built once from the entries and their codes).
- EncAuto (v0.1: `k > max(16384, rows / 64)` falls back to Raw at that cell): the decision is
  computable after the regions: entry e with global code c_e first appears at global row r_e =
  region row offset + local first row; the column falls back iff some entry has
  `c_e + 1 > max(floor, (r_e + 1) / den)`. W6 replicates the rule exactly (storage is not data,
  but tests and bench/README compare storages).
- Raw (EncRaw, or the fallback): each lane decodes one String per row of its region (parallel);
  a fallback decided after the merge decodes `entries[code]` per row (a gather of shared
  strings). Raw stays the expensive storage (24 bytes per code point, hot).

#### 17.4.8 Memory

Peak RSS for the 41 MB file: 266 MB at 1 thread, 306-310 MB at 12 (v0.1: 1,227-1,245 MB), with a
1M-distinct str column 449-488 MB. Budget: 1 byte per file byte packed (regions freed by their
lanes) + per region in flight 3 words per field + the builders + the output columns + decoded
entries. The producer holds one piece's byte list at a time (P x ~24 bytes hot).

### 17.5 Chunk hand-off (with section 16)

The combine step is where the engine's chunk leaves (16, D1) are built: region parts are row
ranges in file order, so leaves are cut by row count (the D1 grain) from the region parts with
one copy, no flat intermediate. Until D1 freezes, W6 concatenates into v0.1's flat columns (the
spike: 18-24 ms for 7 columns x 1M rows plus the dictionary merge).

### 17.6 Proof and test obligations

- **Assurance status**: coder, rank stage, the join's string table, producer, tokenizer, typed
  loops and merge are TESTED-ONLY, as the v0.1 code they replace (Sort.str_codes, Sort.str_words,
  the join's table, csv.bend, csvparse.bend), and listed so in the assurance matrix. The kernels
  they reuse keep their laws (`Kernel.gather`, `Kernel.copy_into`; `Radix.sort` is tested-only
  today). LAWS.bend changes only if W2.6 migrates `ST.Dict`'s index (17.3.4: hypotheses restated,
  never dropped; `make proofs` and `make verdict` re-run). Every PR that touches files imported
  by PROOF*.bend runs `make verdict`.
- **D5 tests (W2)**: differential against the pinned v0.1 coder (codes) and v0.1
  `Sort.str_words` / `Dict.ranks` (words) on distinct / 41-char shared prefix / skewed /
  all-equal / low-cardinality / Unicode keys (NUL, the 1-4 byte UTF-8 boundaries, U+10FFFF,
  prefixes of each other; the spike's `uni` shape) at sizes 0, 1, 2^k +- 1 and 1M; forced
  collisions (the coder instantiated with a constant `~hash`, and a fixture of real FNV-1a 32-bit
  collisions); null rows; group_by / unique / sort / join outputs equal to v0.1 on the
  differential suite (Raw and Dictionary, joinstress).
- **D6 tests (W6)**: tools/adv.py promoted into the differential harness (bench/diff): every case
  x piece sizes 1 .. 2^20 against the reference reader, comparing typed values, validity, names,
  codes, errors and lines; a random CSV generator (quoting, CR / LF mixes, UTF-8 and invalid
  bytes, blank lines, ragged and malformed mutations, competing errors in different rows,
  columns and regions); f32 fast path vs `F32.read` (random decimals, bit-equal); UTF-8 decoding
  byte for byte vs `File.read` of the same bytes; every 15.6 row (inference prefix vs a later
  conflicting value, infer_rows = 0, explicit schemas, headerless, empty, header only, blank lines
  before the header); the B02 regressions; EncAuto's storage decision equal to v0.1's.
- **Performance probes**: the spikes (or their successors under bench/micro/) are W2 / W6's
  before / after probes; G6 instrumentation reports producer, fork and combine phases and RSS.

### 17.7 Work breakdown (W2 strings, W6 reader)

Tiers: **opus** for cross-module integration and anything touching proofs, contracts or error
precedence; **sonnet** for one kernel with its tests.

| task | tier | scope | done when |
|---|---|---|---|
| W2.1 coder | sonnet | `Hc.code` (template hash, first rows, entry byte lengths from the hash walk) in src/strs.bend or a new src/hcode.bend; 17.6 D5 tests | differential green on every shape incl. forced collisions; 17.8 coder cells |
| W2.2 ranks | sonnet | the rank stage (packing with the > U+10FFFF fallback; radix refinement) | words equal to v0.1 `Sort.str_words` / `Dict.ranks` on every shape |
| W2.3 wiring | opus | group_by, unique, n_unique Raw, `Sort.str_words`, `Dict.ranks` callers; delete `pcodes` / `pmerge` / `kbc` / `str_codes_par` after the differential; proof-import audit (`make proofs`, `make verdict`); assurance matrix | make ci and diff-smoke green; G3 distinct-string cells |
| W2.4 join | opus | the join's flat string table (Raw and Dictionary keys), sequential borrowed probe; `Probe.fork` / `Dict.clone` removed (after W1a); joinstress, duplicates, nulls, misses, collisions | distinct-key join G3 cell; joinstress differential green |
| W2.5 partitions (optional) | sonnet | owned-hash-partition coder behind the 17.3.3 threshold | >= 1.5x at 12 threads on 1M distinct keys on the gate machine, no skew regression > 10 % |
| W2.6 Dict index (optional) | opus | `ST.Dict`'s index on flat arrays, presized from a known entry count; `LAWS.Probe` restated over the new seek | `make proofs` / `make verdict` green, no law dropped |
| W6.1 producer | sonnet | read_at pieces, pack + scan in one walk, regions with carries (doubling growth), lines, terminator counts | region starts equal the reference parser's record starts on every adversarial case x piece size |
| W6.2 lane | sonnet | tokenizer, typed loops (u32, i32, f32 fast / slow, bool, str coder), entry decoding, first bad (line, text) | field-level differential vs csvparse + Csv conversions; f32 and UTF-8 bit tests |
| W6.3 integration | opus | header step, inference (prefix, two-pass), explicit / headerless / empty, error precedence, row cap, dictionary merge + EncAuto rule + per-region early fallback, Raw, scan_csv collect, chunk hand-off with 16 | tests/csv*, B02 regressions, CSV diff with piece sizes and competing errors green; G3 / G4 parse cells |
| W6.4 fuzz harness | sonnet | random CSV generator + the adversarial cases in bench/diff, both readers, typed comparison | 10,000 cases x piece sizes clean |
| W6.5 close | opus | G2 / G3 / G4 parse measurement on the gate machine; DESIGN 14, IMPLEMENTING, bench README; the v0.1 reader kept as the reference per D7 | gate report |

### 17.8 Proposed G2 / G3 / G4 thresholds (strings and reader)

Measured values PROVISIONAL (17.9); thresholds leave 1.5-3x headroom for the gate machine and
for what the spikes leave out (null handling, i32, inference prefix, EncAuto, hand-back).

| cell (1 thread unless noted) | M_02 | spike | proposed | justification |
|---|---|---|---|---|
| coder, 1M distinct short keys | (in <= 2 s) | 129 ms | <= 0.4 s | 3x: integration adds validity and the hand-back |
| coder growth 100k -> 1M, every shape | report per row and byte | <= 1.6x per row | per-row time at 1M <= 2x that at 100k | cache only; no superlinear step left |
| distinct-string group_by / unique, 1M | <= 2 s | coder 129 ms + v0.1 remainder (~0.9 s: 5 % of 17-18 s) | <= 1.5 s | as measured, plus margin |
| sort words of a distinct Raw string column, 1M | | 515 ms (coder + ranks) | <= 1.0 s | 2x |
| distinct-key join 1M x 1M | <= 2 s | not measured end to end | <= 2 s (keep) | v0.1 5.1 s minus 1.4 s copy (W1a) minus the Map / clone walks |
| 41 MB parse | <= 2 s | 987 ms | <= 1.5 s | header step, i32, inference prefix, EncAuto still to add |
| 41 MB parse, 12 threads | <= 0.6 s | 472 ms (443 at 256 KiB pieces) | <= 0.6 s (keep) | the serial producer is ~0.34 s of it |
| parse scaling 12 vs 1 (G2) | >= 4x | 2.1x end to end; 5.5x on the fork phase | **revise: >= 2x end to end and >= 4x on the fork phase** | serial fraction 34 % (producer): even infinite threads give < 3x (M_02 G2's own rule) |
| read of a 1M-distinct str column (sales with `id` as str) | | 1,731 / 1,163 ms (1 / 12 threads; merge 629 ms serial) | <= 1.5 s / <= 0.8 s | after 17.4.7 (a) / (b) remove most of the serial merge |
| parse peak RSS (share of G4) | (<= 600 MB whole workload) | 266 / 306-310 MB | <= 400 MB at 1-12 threads | leaves >= 200 MB of G4 to the engine |

### 17.9 Measurements (PROVISIONAL; raw samples: bench/spikes/w0_strings/results/)

**T1 coder (1 thread): ms = coding only (rows alive past the clock); ns/row and ns/char of the new coder**

| shape | n | k | chars/row | new ms | old ms | speedup | new ns/row | new ns/char | load | codes equal |
|---|---|---|---|---|---|---|---|---|---|---|
| distinct | 100000 | 100000 | 10.7 | 8 | 895 | 112x | 80 | 7.4 | 11-37 | yes |
| distinct | 300000 | 300000 | 10.7 | 35 | 3463 | 99x | 117 | 10.9 | 11-128 | yes |
| distinct | 1000000 | 1000000 | 10.7 | 129 | 20355 | 158x | 129 | 12.0 | 10-221 | yes |
| prefix | 100000 | 100000 | 40.7 | 23 | 5113 | 222x | 230 | 5.6 | 11-37 | yes |
| prefix | 300000 | 300000 | 40.7 | 73 | 16245 | 223x | 243 | 6.0 | 12-196 | yes |
| prefix | 1000000 | 1000000 | 40.7 | 308 | 87214 | 283x | 308 | 7.6 | 11-162 | yes |
| skew | 100000 | 50008 | 7.4 | 8 | 394 | 49x | 80 | 10.9 | 11-128 | yes |
| skew | 300000 | 150008 | 7.4 | 32 | 1574 | 49x | 107 | 14.5 | 11-237 | yes |
| skew | 1000000 | 500008 | 7.4 | 118 | 8372 | 71x | 118 | 16.0 | 13-41 | yes |
| equal | 100000 | 1 | 28.0 | 12 | 68 | 6x | 120 | 4.3 | 11-128 | yes |
| equal | 300000 | 1 | 28.0 | 37 | 209 | 6x | 123 | 4.4 | 11-237 | yes |
| equal | 1000000 | 1 | 28.0 | 117 | 685 | 6x | 117 | 4.2 | 11-37 | yes |
| low | 100000 | 1000 | 3.9 | 8 | 67 | 8x | 80 | 20.6 | 11-128 | yes |
| low | 300000 | 1000 | 3.9 | 27 | 179 | 7x | 90 | 23.1 | 11-221 | yes |
| low | 1000000 | 1000 | 3.9 | 84 | 584 | 7x | 84 | 21.6 | 11-37 | yes |
| uni | 100000 | 5016 | 3.6 | 8 | 167 | 21x | 80 | 22.5 | 11-128 | yes |
| uni | 300000 | 5016 | 3.6 | 27 | 316 | 12x | 90 | 25.3 | 11-221 | yes |
| uni | 1000000 | 5016 | 3.6 | 84 | 990 | 12x | 84 | 23.7 | 11-37 | yes |

Load: the range of the samples' 1-minute load (other agents' jobs spiked it; medians are robust). The `old` times include nothing but coding; `codes equal` = identical checksums of the code arrays.

**T2 lexical ranks (1 thread), ms: total (coder + stage) and the stage's parts**

| shape | n | k | rrad total (code/pack/sort/rank) | rounds | rnew total (flat/sort) | rmap total (map) | rold | load | words equal |
|---|---|---|---|---|---|---|---|---|---|
| distinct | 100000 | 100000 | 38 (9/20/8/0) | 2 | 62 (22/32) | 389 (379) | 1070 | 13-86 | yes |
| distinct | 300000 | 300000 | 137 (32/60/27/1) | 2 | 281 (61/184) | 1551 (1523) | - | 13-86 | yes |
| distinct | 1000000 | 1000000 | 515 (133/220/147/3) | 2 | 1281 (194/958) | 7185 (7052) | 22979 | 12-264 | yes |
| prefix | 100000 | 100000 | 107 (22/74/14/0) | 6 | 215 (72/126) | 1909 (1888) | 5245 | 13-86 | yes |
| prefix | 300000 | 300000 | 379 (81/222/56/1) | 6 | 881 (279/479) | 5935 (5837) | - | 13-155 | yes |
| prefix | 1000000 | 1000000 | 1254 (314/719/237/2) | 6 | 3194 (884/2102) | 24431 (24107) | - | 16-237 | yes |
| skew | 100000 | 50008 | 25 (8/11/2/0) | 1 | 35 (10/16) | 154 (142) | 443 | 13-86 | yes |
| skew | 300000 | 150008 | 76 (33/31/12/0) | 2 | 113 (28/51) | 573 (539) | - | 12-282 | yes |
| skew | 1000000 | 500008 | 263 (119/101/43/1) | 2 | 587 (98/360) | 2888 (2748) | - | 18-144 | yes |
| low | 100000 | 1000 | 8 (8/0/0/0) | 1 | 8 (0/0) | 9 (1) | 74 | 13-86 | yes |
| low | 300000 | 1000 | 27 (26/0/0/0) | 1 | 26 (0/0) | 27 (1) | - | 12-264 | yes |
| low | 1000000 | 1000 | 93 (92/0/1/1) | 1 | 88 (0/0) | 94 (2) | - | 18-144 | yes |
| uni | 100000 | 5016 | 9 (8/0/1/0) | 2 | 9 (0/1) | 17 (8) | 182 | 13-86 | yes |
| uni | 300000 | 5016 | 28 (27/0/1/0) | 2 | 29 (0/1) | 36 (9) | - | 12-264 | yes |
| uni | 1000000 | 5016 | 98 (95/1/1/1) | 2 | 95 (0/1) | 97 (9) | - | 18-134 | yes |

`rold` is today's `Sort.str_words` and also frees its input rows inside the call (it drops the strings it was handed); the other modes keep them alive. `words equal` = identical sort words in all four modes.

**T3 parallel coding, owned hash partitions vs sequential borrowed (1M rows), ms**

| shape | seq (1 thr) | part L, threads | total | hash | partition+move | lanes | remap+assemble | load | codes equal |
|---|---|---|---|---|---|---|---|---|---|
| distinct | 138 | L=0, 1 thr | 132 | 24 | 7 | 92 | 7 | 11-15 | yes |
| distinct | 138 | L=4, 1 thr | 93 | 31 | 15 | 34 | 11 | 11-15 | yes |
| distinct | 138 | L=4, 4 thr | 48 | 13 | 14 | 12 | 11 | 11-15 | yes |
| distinct | 138 | L=4, 12 thr | 49 | 11 | 14 | 11 | 12 | 12-15 | yes |
| distinct | 138 | L=6, 12 thr | 58 | 11 | 20 | 9 | 17 | 12-15 | yes |
| prefix | 284 | L=0, 1 thr | 283 | 169 | 9 | 102 | 8 | 11-15 | yes |
| prefix | 284 | L=4, 1 thr | 234 | 170 | 16 | 36 | 11 | 11-14 | yes |
| prefix | 284 | L=4, 4 thr | 100 | 62 | 16 | 13 | 12 | 12-14 | yes |
| prefix | 284 | L=4, 12 thr | 77 | 39 | 14 | 12 | 12 | 12-14 | yes |
| prefix | 284 | L=6, 12 thr | 77 | 29 | 23 | 9 | 19 | 12-14 | yes |
| skew | 123 | L=0, 1 thr | 132 | 20 | 7 | 96 | 7 | 12-15 | yes |
| skew | 123 | L=4, 1 thr | 223 | 23 | 15 | 173 | 12 | 11-15 | yes |
| skew | 123 | L=4, 4 thr | 116 | 11 | 13 | 80 | 12 | 11-15 | yes |
| skew | 123 | L=4, 12 thr | 106 | 10 | 14 | 71 | 12 | 11-15 | yes |
| skew | 123 | L=6, 12 thr | 104 | 11 | 20 | 58 | 16 | 11-15 | yes |
| equal | 120 | L=0, 1 thr | 124 | 39 | 6 | 74 | 5 | 11-15 | yes |
| equal | 120 | L=4, 1 thr | 131 | 43 | 8 | 74 | 5 | 11-15 | yes |
| equal | 120 | L=4, 4 thr | 104 | 17 | 8 | 73 | 5 | 11-15 | yes |
| equal | 120 | L=4, 12 thr | 102 | 14 | 8 | 73 | 6 | 11-15 | yes |
| equal | 120 | L=6, 12 thr | 100 | 13 | 8 | 74 | 5 | 11-15 | yes |

seq = the sequential borrowed coder in the same program. `hash` includes the ANode split/rebuild copies of the pointer blocks.

**T4 hot-type tax in situ (41 MB), ms**

| probe | ms | read | parse | max RSS MB | load |
|---|---|---|---|---|---|
| hs_solo --threads 1 | 361 | 132 | 229 | 805 | 12-13 |
| rd_frame --threads 1 sales_1000000.csv 0 hstep | 889 | 268 | 623 | 1188 | 12-12 |
| pk_cold --threads 1 | 197 | - | - | 181 | 12-12 |
| rd_frame --threads 1 sales_1000000.csv 1048576 pack | 334 | - | - | 188 | 12-12 |
| cnt_cold | 117 | - | - | 20 | 12-12 |
| cnt_hot | 273 | - | - | 29 | 12-12 |

cold builds: hs_solo (imports only csvparse.bend), pk_cold / cnt_cold (no List shared); hot: rd_frame (imports frame.bend), cnt_hot (one owned second use of a List).

**T5 reader scaling (41 MB, 1M rows), ms**

| command | total | producer (read) | fork (lanes) | merge | max RSS MB | user s | load | chk |
|---|---|---|---|---|---|---|---|---|
| rd_frame --threads 1 F 1048576 spike | 987 | 339 | 627 | 21 | 266 | 0.93 | 12-18 | 3590274662 |
| rd_frame --threads 4 F 1048576 spike | 537 | 328 | 189 | 20 | 278 | 0.96 | 12-18 | 3590274662 |
| rd_frame --threads 12 F 1048576 spike | 472 | 338 | 113 | 18 | 306 | 1.02 | 13-18 | 3590274662 |
| rd_frame --threads 12 F 262144 spike | 443 | 330 | 85 | 22 | 310 | 1.02 | 13-18 | 3590274662 |
| rd_frame --threads 12 F 4194304 spike | 528 | 353 | 166 | 16 | 460 | 1.00 | 13-18 | 3590274662 |
| rd_frame --threads 1 F 4194304 spike | 1024 | 356 | 635 | 22 | 396 | 0.94 | 13-18 | 3590274662 |
| rd_solo --threads 1 F 1048576 spike | 1034 | 365 | 641 | 23 | 266 | 0.96 | 13-18 | 3590274662 |
| rd_solo --threads 12 F 1048576 spike | 498 | 361 | 112 | 20 | 306 | 1.03 | 13-18 | 3590274662 |
| rd_frame --threads 1 F 1048576 ref | 5538 | 5538 | - | - | 1227 | 4.47 | 13-18 | 3590274662 |
| rd_frame --threads 12 F 1048576 ref | 2276 | 2276 | - | - | 1245 | 4.75 | 12-18 | 3590274662 |
| rd_frame --threads 1 F 1048576 hstep | 844 | 261 | - | - | 1188 | 1.47 | 13-18 | 1000001 |
| rd_frame --threads 1 F 1048576 spike SSSUFFB | 1731 | 355 | 741 | 629 | 449 | 2.13 | 13-18 | 3551339577 |
| rd_frame --threads 12 F 1048576 spike SSSUFFB | 1163 | 348 | 132 | 681 | 488 | 2.24 | 13-18 | 3551339577 |
| rd_frame --threads 1 F 1048576 ref SSSUFFB | 5235 | 5235 | - | - | 1236 | 4.43 | 13-18 | 244979450 |

F = bench/data/sales_1000000.csv (41.2 MB, 1M rows); the spike reads with the explicit schema `USSUFFB` (Dictionary strings), `ref` is today's `Csv.read_with` with the same schema (EncAuto default); equal chk = identical cells, validity, codes and dictionary sizes. `SSSUFFB` reads `id` as a 1M-distinct str column (ref: EncAuto falls back to Raw, so its chk differs by construction).

**T5 reader phase decomposition (1 thread), ms**

| command | total | producer (read) | fork (lanes) | merge | max RSS MB | user s | load | chk |
|---|---|---|---|---|---|---|---|---|
| rd_frame --threads 1 F 1048576 spike ------- | 748 | 343 | 396 | 0 | 197 | 0.70 | 15-17 | 1088006010 |
| rd_frame --threads 1 F 1048576 spike U------ | 749 | 344 | 407 | 3 | 206 | 0.71 | 15-17 | 114751354 |
| rd_frame --threads 1 F 1048576 spike ----F-- | 797 | 352 | 441 | 3 | 206 | 0.73 | 15-17 | 3603036329 |
| rd_frame --threads 1 F 1048576 spike -S----- | 824 | 338 | 461 | 4 | 207 | 0.76 | 15-17 | 572181243 |
| rd_frame --threads 1 F 1048576 spike --S---- | 820 | 332 | 467 | 4 | 207 | 0.77 | 15-16 | 228599724 |
| rd_frame --threads 1 F 1048576 spike ------B | 765 | 348 | 416 | 3 | 206 | 0.71 | 15-16 | 2162188621 |
| rd_frame --threads 1 F 1048576 spike USSUFFB | 1045 | 351 | 655 | 21 | 262 | 0.95 | 15-16 | 3590274662 |
| rd_frame --threads 1 F 1048576 pack | 326 | - | - | - | 188 | 0.30 | 15-16 | 42193279 |

A dash skips that column's loop: the fork time of a column = its row minus the tokenizer-only row (`-------`).

**T5b adversarial boundaries** (tools/adv.py, results/t5_adv.jsonl): 30 files (quoted newlines in every
record with LF and CRLF; CR soup in bare fields, lone CR, `\r\r\n`, a final CR without LF; 2- to
4-byte UTF-8 in typed and str columns; records longer than 100 pieces; blank lines with k = 1 and
k > 1; no final newline; invalid UTF-8 bytes that decode to the same U+FFFD; malformed quoting
early, late, after a closing quote, unclosed at the end, CR then quote, malformed after a ragged
record; ragged short and long; a ragged record after a bad cell; bad cells competing across
columns and rows; f32 edges and 20,000 random fast-path decimals; u32 edges, overflow, `+5`; bool
spellings; escaped quoted numbers; quote runs of every length straddling piece edges) x 15 piece
sizes (1, 2, 3, 4, 5, 7, 8, 13, 16, 31, 64, 97, 256, 4096, 1 MiB bytes): spike = reference on 28
files x 15 sizes; the 2 exceptions are header-step cases the spike does not implement (17.4.1):
`lead_blank` (blank lines before the header, piece sizes <= 7) and `empty` (the dtype-count
check of an empty file).)

**T6 hashing every row: cons String vs flat UTF-8 buffer (1 thread), ms**

| shape | n | code points | flat words | cons hash | flat hash | flat build | cons ns per code point | flat ns per code point | load |
|---|---|---|---|---|---|---|---|---|---|
| distinct | 1000000 | 10741299 | 2997670 | 23 | 2 | 210 | 2.1 | 0.19 | 11-12 |
| prefix | 1000000 | 40741299 | 10767147 | 169 | 7 | 740 | 4.1 | 0.17 | 12-12 |
| low | 1000000 | 3890004 | 1000000 | 9 | 1 | 63 | 2.3 | 0.26 | 12-13 |
| uni | 1000000 | 3550444 | 1927869 | 9 | 2 | 81 | 2.5 | 0.56 | 12-13 |

1M rows (the 100k rows are below the 1 ms clock for the flat hash). Per code point; `flat build` (two walks of each cons string) is what converting an existing cons column costs.

### 17.10 M_02 assumptions that did not hold, and the revisions

1. **"Read the file in pieces with File.read_at and fork over them" (Fable P3) holds only
   halfway.** Pieces can be read, but only sequentially, and their bytes arrive as hot cons lists
   built on the IO thread: in a real program the producer is a serial ~0.33 s per 41 MB (floor
   ~0.27 s to build and walk the lists). Revision: a sequential producer that does the lexical
   scan in the same walk; G2's parse target becomes >= 2x end to end and >= 4x on the fork phase
   (17.8). The lever beyond that is upstream: a Base primitive reading into a U32 buffer (e.g.
   `File.read_words(f, off, max) -> Array<U32>`) would remove most of the serial 0.33 s. Recorded
   as a toolchain request, not assumed.
2. **"Parser-private cold types" (D5 / D6)**: private loop RECORDS do stay cold in the integrated
   program; private cons CHAR / CELL types would not, because their input is the File API's hot
   String / List. Revision: no cons parser; flat packed bytes, cold scalar records, one hot
   boundary per piece, charged to the producer.
3. **Associative lexical-state summaries** are unnecessary with a sequential producer (17.4.2);
   kept as the documented option for a future parallel producer.
4. **The 64 MiB default piece** (v0.1, 14 M4) was a cons-list allocator effect; flat regions run
   as fast with 1 MiB / 256 KiB pieces at 1 thread and need them for 12-thread balance.
5. **A parallel coder is not needed for G3**: the sequential flat coder meets the distinct-key
   cells by a wide margin; owned partitions are approved and optional (W2.5).
6. **W7 (flat string storage)**: 17.11.

### 17.11 Flat string storage sizing (input to W7)

Per row of a Raw string column (T6 and the T1 RSS): a hot cons `String` costs ~24 bytes per code
point (16-byte cell + the seal's redirect cell) + 8 bytes for the row slot: ~270 bytes for an
11-character key, ~1 KB for a 41-character one. A flat buffer (UTF-8 bytes packed 4 per word +
a 4-byte offset and a 4-byte length per row) costs bytes + 8: ~19 / ~49 bytes (14-20x smaller).
A Dictionary costs 4 bytes per row + its entries (cons) + its index. Hashing every row: 2.1-4.1
ns per code point on cons strings laid out in order (slower when scattered), 0.2-0.6 ns per code
point flat (T6: 23 vs 2 ms for 1M short keys, 169 vs 7 ms for 1M 41-char keys); building the flat
form from cons strings costs 210 / 740 ms (two walks), i.e. a flat column pays only if it is
produced directly (by the reader, from its packed bytes) and never converted back per operation.
Every string operation of the API (predicates, `len_chars`, casts, render, dump, `Column.cell`,
the String values the facade returns) and the proof model (`LAWS.scell`) work on cons `String`, so
a third storage needs a decode at each of those boundaries or byte-level re-implementations, plus
a third case in the storage proofs (M4 chose a sum type to avoid a sixth Column constructor).
**Recommendation**: do not schedule W7 in v0.2 unless the gate shows a Raw-string cell (parse of a
high-cardinality column, RSS) outside 17.8 after W2 / W6; the distinct-key cells are met with the
coder alone. If scheduled, scope it to "reader-produced flat Raw columns, decoded at the API
boundary", measured against the per-region Raw decode of 17.4.7.
