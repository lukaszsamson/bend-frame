# p21: every type definition DESIGN.md quotes, plus the public signatures
# as open laws (stubs), in one file, so `--check-only` validates the shapes
# before implementation. Open laws are reported as TODOs: the expected
# result is "N TODOs found" with NO type error above it. Kernel templates
# cannot be stubbed (a law takes no ~ parameter), so they carry bodies.
#   ~/.bend/bin/bend probes/p21_design_sigs.bend --check-only
import Base

# ---- src/dtype.bend ---------------------------------------------------------

type DType is Data:
  TBool{}
  TU32{}
  TI32{}
  TF32{}
  TStr{}

type I32 is Data:
  I32{bits: U32}

# a scalar value: a literal in an expression, a cell read out of a column
type Scalar is Data:
  SNull{}
  SBool{b: Bool}
  SU32{v: U32}
  SI32{v: I32}
  SF32{v: F32}
  SStr{s: String}

law DType.eq:
  for a: DType
  for b: DType
  Bool

law DType.show:
  for t: DType
  String

law Scalar.dtype:
  for s: Scalar
  Maybe<&2, DType>

law Scalar.show:
  for s: Scalar
  String

# ---- src/err.bend -----------------------------------------------------------

type Err is Data:
  ColumnNotFound{name: String}
  DuplicateColumn{name: String}
  TypeMismatch{op: String, want: String, got: String}
  ShapeMismatch{want: U32, got: U32}
  ParseError{line: U32, text: String}
  InvalidOperation{what: String}
  IoError{code: U32, text: String}

# Data-kinded results (scalars, schemas, plans) and Type-kinded ones (columns, frames)
def Res(-A: Data) -> Data:
  Result<&2, &2, Err, A>

def ResT(-A: Type) -> Type:
  Result<&2, &1, Err, A>

law Err.show:
  for e: Err
  String

# ---- src/column.bend --------------------------------------------------------

# validity as 0/1 words, one per row, so it is also what comparisons yield
type Valid is Type:
  AllValid{}
  Mask{m: Array<U32>}

# len rows live in an array of 2^depth slots (len <= 2^depth); Bool and I32
# share the U32 word buffer (0/1 words; two's complement bits)
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

law Column.len:
  for c: Column
  Column & U32

law Column.dtype:
  for c: Column
  Column & DType

law Column.cell:
  for c: Column
  for +i: U32
  Column & Scalar

law Column.from_scalars:
  for xs: List<&2, Scalar>
  for t: DType
  ResT(Column)

law Column.head:
  for c: Column
  for +n: U32
  Column

law Column.clone:
  for c: Column
  Column & Column

law Column.gather:
  for c: Column
  for perm: Array<U32>
  for +n: U32
  Column & Array<U32>

law Column.compact:
  for c: Column
  for mask: Array<U32>
  for +kept: U32
  Column & Array<U32>

law Frame.height:
  for f: Frame
  Frame & U32

law Frame.names:
  for f: Frame
  Frame & List<&2, String>

law Frame.take:
  for f: Frame
  for +name: String
  Frame & Maybe<&1, Column>

law Frame.put:
  for f: Frame
  for name: String
  for c: Column
  ResT(Frame)

law Frame.from_columns:
  for cols: List<&1, Named>
  ResT(Frame)

# ---- src/schema.bend --------------------------------------------------------

type Field is Data:
  Field{name: String, dtype: DType}

law Schema.find:
  for s: List<&2, Field>
  for +name: String
  Maybe<&2, DType>

law Schema.project:
  for names: List<&2, String>
  for +s: List<&2, Field>
  Res(List<&2, Field>)

law Schema.with:
  for s: List<&2, Field>
  for f: Field
  List<&2, Field>

law Frame.schema:
  for f: Frame
  Frame & List<&2, Field>

# ---- src/expr.bend ----------------------------------------------------------

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

# the output name: the alias, else the leftmost column, else "literal"
law Expr.name:
  for e: Expr
  String

# strict typing against a schema: no implicit casts
law Expr.type:
  for e: Expr
  for +s: List<&2, Field>
  Res(DType)

law Expr.refs:
  for e: Expr
  List<&2, String>

law Expr.is_agg:
  for e: Expr
  Bool

# ---- src/eval.bend ----------------------------------------------------------

# evaluate one expression over a frame: the frame comes back untouched
# (referenced columns are cloned), the result is a column of Frame.height
# rows, or of one row for an aggregation
law Eval.expr:
  for f: Frame
  for e: Expr
  Frame & ResT(Column)

law Eval.scalar:
  for e: Expr
  Res(Scalar)

# ---- src/sort.bend / groupby.bend / join.bend --------------------------------

type SortKey is Data:
  SortKey{name: String, descending: Bool, nulls_last: Bool}

type JoinHow is Data:
  Inner{}
  Left{}

law Sort.argsort:
  for f: Frame
  for keys: List<&2, SortKey>
  Frame & ResT(Array<U32>)

law Sort.frame:
  for f: Frame
  for keys: List<&2, SortKey>
  ResT(Frame)

law GroupBy.run:
  for f: Frame
  for keys: List<&2, Expr>
  for aggs: List<&2, Expr>
  for +maintain_order: Bool
  ResT(Frame)

law Join.run:
  for +how: JoinHow
  for left: Frame
  for right: Frame
  for left_on: List<&2, String>
  for right_on: List<&2, String>
  ResT(Frame)

# ---- src/plan.bend ----------------------------------------------------------

type CsvOpts is Data:
  CsvOpts{sep: Char, has_header: Bool, infer_rows: U32}

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

# the output schema with no data: strict early errors
law Plan.schema:
  for p: Plan
  Res(List<&2, Field>)

# predicate and projection pushdown; filter merging
law Plan.optimize:
  for p: Plan
  Plan

# the frames a plan's Source nodes name
type Env is Type:
  Env{frames: List<&1, Named.Frame>}

type Named.Frame is Type:
  NF{name: String, frame: Frame}

# ---- src/exec.bend ----------------------------------------------------------

law Exec.run:
  for p: Plan
  for env: Env
  IO(ResT(Frame))

# ---- src/csv.bend -----------------------------------------------------------

law Csv.read:
  for path: String
  for opts: CsvOpts
  IO(ResT(Frame))

law Csv.parse:
  for text: String
  for opts: CsvOpts
  ResT(Frame)

law Csv.write:
  for f: Frame
  for path: String
  IO(Frame & Result<&1, &1, (U32 & String), Unit>)

law Csv.render:
  for f: Frame
  for prec: Maybe<&2, U32>
  Frame & String

# ---- src/fmt.bend -----------------------------------------------------------

law Fmt.show:
  for f: Frame
  Frame & String

law Fmt.describe:
  for f: Frame
  Frame & ResT(Frame)

# ---- src/kernels.bend (templates must carry bodies) -------------------------

# the least depth d with 2^d >= n (n >= 1); the exit test rides as a parameter
def Kernel.depth_for.go(f: Nat, +n: U32, +d: Nat, fits: Bool) -> Nat:
  match f fits:
    case _ True{}:
      d
    case 0n False{}:
      d
    case 1n+p False{}:
      Kernel.depth_for.go(p, n, 1n+d, U32.is_le(n, U32.shln(1, 1n+d)))

def Kernel.depth_for(+n: U32) -> Nat:
  Kernel.depth_for.go(32n, n, 0n, U32.is_le(n, 1))

# out[i] = f(a[i]) for i < n, consuming a; r is the NEXT read (a, a[i])
def Kernel.map.go(~T: Data, ~U: Data, ~f: T -> U, n: Nat, +i: U32, out: Array<U>, r: Array<T> & T) -> Array<U>:
  match n:
    case 0n:
      out
    case 1n+p:
      (a, x) = r
      +j = U32.inc(i)
      Kernel.map.go(~T, ~U, ~f, p, j, Array.set(U, out, i, f(x)), Array.get(T, a, j))

def Kernel.map(~T: Data, ~U: Data, ~f: T -> U, +n: U32, +d: Nat, a: Array<T>, +z: U) -> Array<U>:
  Kernel.map.go(~T, ~U, ~f, U32.to_nat(n), 0, Array.new(U, d, z), Array.get(T, a, 0))

# out[i] = f(a[i], b[i]); ra, rb are the next reads
def Kernel.zip.go(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, n: Nat, +i: U32, out: Array<V>, ra: Array<T> & T, rb: Array<U> & U) -> Array<V>:
  match n:
    case 0n:
      out
    case 1n+p:
      (a, x) = ra
      (b, y) = rb
      +j = U32.inc(i)
      Kernel.zip.go(~T, ~U, ~V, ~f, p, j, Array.set(V, out, i, f(x, y)), Array.get(T, a, j), Array.get(U, b, j))

def Kernel.zip(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +n: U32, +d: Nat, a: Array<T>, b: Array<U>, +z: V) -> Array<V>:
  Kernel.zip.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, Array.new(V, d, z), Array.get(T, a, 0), Array.get(U, b, 0))

# acc = f(acc, a[i]) over i < n; the array comes back
def Kernel.fold.go(~T: Data, ~A: Data, ~f: A -> T -> A, n: Nat, +i: U32, acc: A, r: Array<T> & T) -> Array<T> & A:
  match n:
    case 0n:
      (a, x) = r
      (a, acc)
    case 1n+p:
      (a, x) = r
      +j = U32.inc(i)
      Kernel.fold.go(~T, ~A, ~f, p, j, f(acc, x), Array.get(T, a, j))

def Kernel.fold(~T: Data, ~A: Data, ~f: A -> T -> A, +n: U32, a: Array<T>, z: A) -> Array<T> & A:
  Kernel.fold.go(~T, ~A, ~f, U32.to_nat(n), 0, z, Array.get(T, a, 0))

# branch-free compaction: out[k] = a[i], k += mask[i]; answers (out, k)
def Kernel.compact.put(~T: Data, out: Array<T>, +k: U32, r: Array<T> & T) -> Array<T> & Array<T>:
  (a, x) = r
  (a, Array.set(T, out, k, x))

def Kernel.compact.go(~T: Data, n: Nat, +i: U32, +k: U32, ao: Array<T> & Array<T>, mi: Array<U32> & U32) -> Array<T> & U32:
  match n:
    case 0n:
      (a, out) = ao
      (out, k)
    case 1n+p:
      (a, out) = ao
      (mask, bit) = mi
      +j = U32.inc(i)
      Kernel.compact.go(~T, p, j, U32.add(k, bit), Kernel.compact.put(~T, out, k, Array.get(T, a, i)), Array.get(U32, mask, j))

def Kernel.compact(~T: Data, +n: U32, +d: Nat, a: Array<T>, mask: Array<U32>, +z: T) -> Array<T> & U32:
  Kernel.compact.go(~T, U32.to_nat(n), 0, 0, (a, Array.new(T, d, z)), Array.get(U32, mask, 0))

# out[j] = src[perm[j]] for j < n; answers (out, perm)
def Kernel.gather.put(~T: Data, out: Array<T>, +j: U32, r: Array<T> & T) -> Array<T> & Array<T>:
  (src, x) = r
  (src, Array.set(T, out, j, x))

def Kernel.gather.go(~T: Data, n: Nat, +j: U32, so: Array<T> & Array<T>, r: Array<U32> & U32) -> Array<T> & Array<U32>:
  match n:
    case 0n:
      (src, out) = so
      (perm, i) = r
      (out, perm)
    case 1n+p:
      (src, out) = so
      (perm, i) = r
      +j2 = U32.inc(j)
      Kernel.gather.go(~T, p, j2, Kernel.gather.put(~T, out, j, Array.get(T, src, i)), Array.get(U32, perm, j2))

def Kernel.gather(~T: Data, +n: U32, +d: Nat, src: Array<T>, perm: Array<U32>, +z: T) -> Array<T> & Array<U32>:
  Kernel.gather.go(~T, U32.to_nat(n), 0, (src, Array.new(T, d, z)), Array.get(U32, perm, 0))

# acc[g[i]] = f(acc[g[i]], v[i]) for i < n: the scatter behind group_by
def Kernel.scatter.put(~T: Data, ~A: Data, ~f: A -> T -> A, +g: U32, x: T, r: Array<A> & A) -> Array<A>:
  (acc, old) = r
  Array.set(A, acc, g, f(old, x))

def Kernel.scatter.go(~T: Data, ~A: Data, ~f: A -> T -> A, n: Nat, +i: U32, acc: Array<A>, rg: Array<U32> & U32, rv: Array<T> & T) -> Array<A>:
  match n:
    case 0n:
      acc
    case 1n+p:
      (gs, +g) = rg
      (vs, x) = rv
      +j = U32.inc(i)
      Kernel.scatter.go(~T, ~A, ~f, p, j, Kernel.scatter.put(~T, ~A, ~f, g, x, Array.get(A, acc, g)), Array.get(U32, gs, j), Array.get(T, vs, j))

def Kernel.scatter(~T: Data, ~A: Data, ~f: A -> T -> A, +n: U32, gids: Array<U32>, vals: Array<T>, acc: Array<A>) -> Array<A>:
  Kernel.scatter.go(~T, ~A, ~f, U32.to_nat(n), 0, acc, Array.get(U32, gids, 0), Array.get(T, vals, 0))

# a list into a fresh array of 2^depth_for(n) slots padded with z
def Kernel.fill.go(~T: Data, xs: List<&2, T>, +i: U32, a: Array<T>) -> Array<T>:
  match xs:
    case Nil{}:
      a
    case h <> t:
      Kernel.fill.go(~T, t, U32.inc(i), Array.set(T, a, i, h))

def Kernel.from_list(~T: Data, +xs: List<&2, T>, +z: T) -> U32 & Array<T>:
  +n = U32.from_nat(List.length(&2, T, xs))
  (n, Kernel.fill.go(~T, xs, 0, Array.new(T, Kernel.depth_for(U32.max(n, 1)), z)))

# a smoke test of the kernels that carry bodies
def smoke(r: U32 & Array<F32>) -> String:
  (n, a) = r
  List.show(~&1, ~F32, ~(x => F32.show(x)), Array.to_list(~F32, Kernel.map(~F32, ~F32, ~(x => F32.mul(x, 2.0)), n, 2n, a, 0.0)))

def main() -> IO(Unit):
  IO.print(smoke(Kernel.from_list(~F32, [1.0, 2.0, 3.0], 0.0)))
