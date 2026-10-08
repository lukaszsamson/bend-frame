# frame.bend -- the public facade: one import for users.
#
#   import ./frame.bend as DF            (examples/ and tests/ write ./../frame.bend)
#
# Each def is a thin wrapper over src/*.bend (DESIGN.md 4.15); the few with a
# match only pass an error through or split a pair. The names read as
# DF.<name>: DF.col("qty"), DF.filter(f, pred), DF.collect(p, env).
#
# Conventions:
#  - Eager verbs take a Frame and answer ResT(Frame): an error is a value,
#    matched with `match r: case Fail{e}: .. case Done{f}: ..`. DF.show takes
#    such a result and prints the table or the error.
#  - Lazy verbs (lazy_*) build a Plan; nothing runs until DF.collect(p, env).
#    DF.collect_schema and DF.explain work on the plan alone.
#  - Types are not re-exported (Bend imports carry only the file's own defs).
#    Annotations name them through the aliases in the types section below
#    (DF.Frame(), DF.ResT(..), DF.Plan(), ...). DF.cast takes a D.DType from
#    src/dtype.bend; DF.cast_f32 and DF.cast_u32 cover the common casts.
#  - Helpers that take a pair (Frame & X) and answer X are named `<verb>.<x>`
#    and sit above their user.
import Base
import ./src/dtype.bend as D
import ./src/err.bend as E
import ./src/column.bend as C
import ./src/schema.bend as S
import ./src/expr.bend as X
import ./src/eval.bend as V
import ./src/sort.bend as O
import ./src/groupby.bend as G
import ./src/join.bend as J
import ./src/csv.bend as R
import ./src/fmt.bend as F
import ./src/plan.bend as P
import ./src/exec.bend as Q
import ./src/dump.bend as Y

# ---- types ----------------------------------------------------------------------------
# Imports carry no types, so annotations name them through these aliases:
# `r : DF.ResT(DF.Frame()) <- DF.read_csv(path)` (a do-block bind needs its type).
# A Frame, Expr or Plan is a call: DF.Frame(), DF.Expr(), DF.Plan().

def Frame() -> Type:
  C.Frame

def Expr() -> Data:
  X.Expr

def SortKey() -> Data:
  O.SortKey

def Plan() -> Data:
  P.Plan

def Env() -> Type:
  P.Env

def ResT(-A: Type) -> Type:
  E.ResT(A)

def Res(-A: Data) -> Data:
  E.Res(A)

def Err() -> Data:
  E.Err

def Schema() -> Data:
  List<&2, S.Field>

def CsvOpts() -> Data:
  R.CsvOpts

def CsvWriteOpts() -> Data:
  R.CsvWriteOpts

# ---- columns and literals -------------------------------------------------------------

def col(name: String) -> X.Expr:
  X.Col{name}

def lit_u32(v: U32) -> X.Expr:
  X.Lit{D.SU32{v}}

# the i32 literal v for v < 2^31; a larger v builds `cast(lit_u32(v), i32)`, a strict cast that
# fails when evaluated ("cast u32 to i32: row 0 holds <v>"): no silent wrap (DESIGN.md 15.2.1 D:)
def lit_i32(+v: U32) -> X.Expr:
  Bool.pick(X.Expr, U32.is_lt(v, 2147483648), X.Lit{D.SI32{D.I32{v}}}, X.Cast{X.Lit{D.SU32{v}}, D.TI32{}})

# -v for v <= 2^31 (lit_i32_neg(2147483648) is MIN); a larger v builds the negation of the
# failing cast above
def lit_i32_neg(+v: U32) -> X.Expr:
  Bool.pick(X.Expr, U32.is_le(v, 2147483648), X.Lit{D.SI32{D.I32.neg(D.I32{v})}}, X.Un{X.Neg{}, X.Cast{X.Lit{D.SU32{v}}, D.TI32{}}})

# a checked i32 value: v < 2^31, else InvalidOperation{"i32 out of range: <v>"} (D.I32.checked);
# D.I32.from_bits(w) is the explicit, unchecked reinterpretation
def i32(v: U32) -> E.Res(D.I32):
  D.I32.checked(v)

# -v as a checked i32: v <= 2^31
def i32_neg(v: U32) -> E.Res(D.I32):
  D.I32.checked_neg(v)

# the null literal of dtype t
def lit_null(t: D.DType) -> X.Expr:
  X.Cast{X.Lit{D.SNull{}}, t}

def lit_f32(v: F32) -> X.Expr:
  X.Lit{D.SF32{v}}

def lit_str(s: String) -> X.Expr:
  X.Lit{D.SStr{s}}

def lit_bool(b: Bool) -> X.Expr:
  X.Lit{D.SBool{b}}

def alias(e: X.Expr, name: String) -> X.Expr:
  X.Alias{e, name}

# strict (DESIGN.md 15.5.5): the first valid cell that does not convert is
# InvalidOperation{"cast <from> to <to>: row <i> holds <cell>"}
def cast(e: X.Expr, t: D.DType) -> X.Expr:
  X.Cast{e, t}

# the same conversion with failing cells set to null (never an error at run time)
def try_cast(e: X.Expr, t: D.DType) -> X.Expr:
  X.TryCast{e, t}

def cast_f32(e: X.Expr) -> X.Expr:
  X.Cast{e, D.TF32{}}

def cast_u32(e: X.Expr) -> X.Expr:
  X.Cast{e, D.TU32{}}

# ---- operators ----------------------------------------------------------------------------

def add(a: X.Expr, b: X.Expr) -> X.Expr:
  X.Bin{X.Add{}, a, b}

def sub(a: X.Expr, b: X.Expr) -> X.Expr:
  X.Bin{X.Sub{}, a, b}

def mul(a: X.Expr, b: X.Expr) -> X.Expr:
  X.Bin{X.Mul{}, a, b}

# f32 / f32 only (IEEE: x/0 = +-inf); cast integers to f32 first
def div(a: X.Expr, b: X.Expr) -> X.Expr:
  X.Bin{X.Div{}, a, b}

# u32 // u32, i32 // i32: floor toward -inf; null for a zero divisor and for i32 MIN // -1
def floor_div(a: X.Expr, b: X.Expr) -> X.Expr:
  X.Bin{X.FloorDiv{}, a, b}

# u32 % u32, i32 % i32: the result has the divisor's sign (consistent with floor_div); null
# for a zero divisor
def mod(a: X.Expr, b: X.Expr) -> X.Expr:
  X.Bin{X.Mod{}, a, b}


def eq(a: X.Expr, b: X.Expr) -> X.Expr:
  X.Bin{X.Eq{}, a, b}

def ne(a: X.Expr, b: X.Expr) -> X.Expr:
  X.Bin{X.Ne{}, a, b}

def lt(a: X.Expr, b: X.Expr) -> X.Expr:
  X.Bin{X.Lt{}, a, b}

def le(a: X.Expr, b: X.Expr) -> X.Expr:
  X.Bin{X.Le{}, a, b}

def gt(a: X.Expr, b: X.Expr) -> X.Expr:
  X.Bin{X.Gt{}, a, b}

def ge(a: X.Expr, b: X.Expr) -> X.Expr:
  X.Bin{X.Ge{}, a, b}

# Kleene logic: false & null = false, true | null = true
def and(a: X.Expr, b: X.Expr) -> X.Expr:
  X.Bin{X.And{}, a, b}

def or(a: X.Expr, b: X.Expr) -> X.Expr:
  X.Bin{X.Or{}, a, b}

def not(e: X.Expr) -> X.Expr:
  X.Un{X.Not{}, e}

def neg(e: X.Expr) -> X.Expr:
  X.Un{X.Neg{}, e}

def is_null(e: X.Expr) -> X.Expr:
  X.Un{X.IsNull{}, e}

def is_not_null(e: X.Expr) -> X.Expr:
  X.Un{X.IsNotNull{}, e}

def fill_null(e: X.Expr, v: X.Expr) -> X.Expr:
  X.FillNull{e, v}

# ---- aggregations: group_by aggs, and global reductions anywhere in select /
# with_columns / filter, eager and lazy (DESIGN.md 15.2.5, 15.4) ------------------------

def sum(e: X.Expr) -> X.Expr:
  X.Agg{X.Sum{}, e}

def mean(e: X.Expr) -> X.Expr:
  X.Agg{X.Mean{}, e}

def min(e: X.Expr) -> X.Expr:
  X.Agg{X.Min{}, e}

def max(e: X.Expr) -> X.Expr:
  X.Agg{X.Max{}, e}

# non-null values
def count(e: X.Expr) -> X.Expr:
  X.Agg{X.Count{}, e}

# rows in the group (pl.len())
def len() -> X.Expr:
  X.Agg{X.Len{}, X.Lit{D.SU32{1}}}

def first(e: X.Expr) -> X.Expr:
  X.Agg{X.First{}, e}

def last(e: X.Expr) -> X.Expr:
  X.Agg{X.Last{}, e}

def n_unique(e: X.Expr) -> X.Expr:
  X.Agg{X.NUnique{}, e}

# ---- sort keys -------------------------------------------------------------------------

def sort_key(name: String, descending: Bool, nulls_last: Bool) -> O.SortKey:
  O.SortKey{name, descending, nulls_last}

# ascending, nulls first (Polars default)
def asc(name: String) -> O.SortKey:
  O.SortKey{name, False{}, False{}}

# descending, nulls first (Polars default)
def desc(name: String) -> O.SortKey:
  O.SortKey{name, True{}, False{}}

# ---- frames -----------------------------------------------------------------------------

def named(name: String, c: C.Column) -> C.Named:
  C.Named{name, c}

def from_columns(cols: List<&1, C.Named>) -> E.ResT(C.Frame):
  C.Frame.from_columns(cols)

# CSV options: separator, has_header, rows that decide each column's dtype (0 = all)
# (DESIGN.md 15.6.3). `read_csv` and `scan_csv` use (',', True, 100).
def csv_opts(sep: Char, has_header: Bool, infer_rows: U32) -> R.CsvOpts:
  R.CsvOpts{sep, has_header, infer_rows}

# the whole file is read once; dtypes are inferred
def read_csv(path: String) -> IO(E.ResT(C.Frame)):
  R.Csv.read(path, R.Csv.default())

def read_csv_opts(path: String, opts: R.CsvOpts) -> IO(E.ResT(C.Frame)):
  R.Csv.read(path, opts)

# explicit dtypes by column position (the header gives the names); a cell that does not
# parse is a ParseError, a wrong count an InvalidOperation; [] infers
def read_csv_schema(path: String, opts: R.CsvOpts, dtypes: List<&2, D.DType>) -> IO(E.ResT(C.Frame)):
  R.Csv.read_with(path, opts, dtypes)

# helper: the table of a (frame & text) pair
def show.s(x: C.Frame & String) -> String:
  (f, s) = x
  s

# the table, or the error text
def show(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      show.s(F.Fmt.show(f))

# the typed oracle text of a result (DESIGN.md 15.1): every dtype, name, validity
# and F32 bit pattern, or the error line; consumes r
def dump(r: E.ResT(C.Frame)) -> String:
  Y.Dump.result(r)

# the same for a Frame that is not wrapped in a result
def dump_frame(f: C.Frame) -> String:
  Y.Dump.frame(f)

# helper: the result of a (frame & result) pair
def describe.r(x: C.Frame & E.ResT(C.Frame)) -> E.ResT(C.Frame):
  (f, r) = x
  r

# Polars-style summary statistics (a stub until the describe milestone: it
# answers an InvalidOperation error); an error in r passes through
def describe(r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      describe.r(F.Fmt.describe(f))

# the write's result as the frame, or the IoError that stopped it
def write_csv.res(f: C.Frame, w: Result<&1, &1, U32 & String, Unit>) -> E.ResT(C.Frame):
  match w:
    case Done{u}:
      Done{f}
    case Fail{(code, msg)}:
      Fail{E.IoError{code, msg}}

# helper: the result of a (frame & write result) pair
def write_csv.r(x: C.Frame & Result<&1, &1, U32 & String, Unit>) -> E.ResT(C.Frame):
  (f, w) = x
  write_csv.res(f, w)

def write_csv.io(f: C.Frame, path: String, w: R.CsvWriteOpts) -> IO(E.ResT(C.Frame)):
  do IO<E.ResT(C.Frame)>:
    x : C.Frame & Result<&1, &1, U32 & String, Unit> <- R.Csv.write_with(f, path, w)
    return write_csv.r(x)

# CSV write options: separator, header line or not, F32 decimals (None: shortest digits)
def write_opts(sep: Char, include_header: Bool, float_precision: Maybe<&2, U32>) -> R.CsvWriteOpts:
  R.CsvWriteOpts{sep, include_header, float_precision}

# writes the frame as CSV with the options (DESIGN.md 15.6.3) and answers the same frame,
# or the write's error; an error in r passes through
def write_csv_opts(r: E.ResT(C.Frame), path: String, w: R.CsvWriteOpts) -> IO(E.ResT(C.Frame)):
  match r:
    case Fail{e}:
      IO.pure(E.ResT(C.Frame), Fail{e})
    case Done{f}:
      write_csv.io(f, path, w)

# writes the frame as CSV (',' separator, header, F32 shortest digits) and answers the
# same frame, or the write's error; an error in r passes through
def write_csv(r: E.ResT(C.Frame), path: String) -> IO(E.ResT(C.Frame)):
  write_csv_opts(r, path, R.Csv.write_default())

# ---- eager verbs (Frame -> ResT(Frame)) ----------------------------------------------

def select(f: C.Frame, exprs: List<&2, X.Expr>) -> E.ResT(C.Frame):
  V.Eval.select(f, exprs)

def with_columns(f: C.Frame, exprs: List<&2, X.Expr>) -> E.ResT(C.Frame):
  V.Eval.with_columns(f, exprs)

def filter(f: C.Frame, pred: X.Expr) -> E.ResT(C.Frame):
  V.Eval.filter(f, pred)

def sort(f: C.Frame, keys: List<&2, O.SortKey>) -> E.ResT(C.Frame):
  O.Sort.frame(f, keys)

# aggregates each group; output in first-appearance order (v1 ignores the
# flag and always orders this way, DESIGN.md 14 M5)
def group_by(f: C.Frame, keys: List<&2, X.Expr>, aggs: List<&2, X.Expr>) -> E.ResT(C.Frame):
  G.GroupBy.run(f, keys, aggs, True{})

def head(f: C.Frame, n: U32) -> E.ResT(C.Frame):
  Done{C.Frame.head(f, n)}

def inner_join(left: C.Frame, right: C.Frame, left_on: List<&2, String>, right_on: List<&2, String>) -> E.ResT(C.Frame):
  J.Join.run(J.Inner{}, left, right, left_on, right_on)

def left_join(left: C.Frame, right: C.Frame, left_on: List<&2, String>, right_on: List<&2, String>) -> E.ResT(C.Frame):
  J.Join.run(J.Left{}, left, right, left_on, right_on)

# ---- lazy: sources and plan builders --------------------------------------------------

def empty_env() -> P.Env:
  P.Env.empty()

# a lazy frame: the environment that holds it, and a Source plan naming it
def source(name: String, f: C.Frame) -> P.Env & P.Plan:
  P.Lazy.source(name, f)

# one more named frame in an env (several sources in one plan, DESIGN.md 15.2.2):
# the env holding it and the Source plan Source{name, schema of f}. A name bound
# twice is reported by validate_bindings / collect, not here.
def add_source(env: P.Env, name: String, f: C.Frame) -> P.Env & P.Plan:
  P.Env.add(env, name, f)

# the bindings a plan needs, checked without running it (DESIGN.md 15.7): every
# name bound once in env, every Source of p present with its schema. Hands env
# back untouched; the error texts are collect's.
def validate_bindings(p: P.Plan, env: P.Env) -> P.Env & E.Res(Unit):
  Q.Exec.validate(p, env)

# an O(n) deep copy (same height, names, order and cells)
def clone(f: C.Frame) -> C.Frame & C.Frame:
  C.Frame.clone(f)

# and_then: k runs on the frame; an error passes through
def then(r: E.ResT(C.Frame), k: C.Frame -> E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      k(f)

# and_then into IO (write_csv, collect chains); an error passes through
def then_io(r: E.ResT(C.Frame), k: C.Frame -> IO(E.ResT(C.Frame))) -> IO(E.ResT(C.Frame)):
  match r:
    case Fail{e}:
      IO.pure(E.ResT(C.Frame), Fail{e})
    case Done{f}:
      k(f)

# reads a bounded prefix of a CSV file now (header and the first infer_rows rows, 64 KiB
# chunks) to freeze the schema; the whole file is read once, at collect (DESIGN.md 15.6.4)
def scan_csv(path: String) -> IO(E.Res(P.Plan)):
  P.Lazy.scan_csv(path, R.Csv.default())

def scan_csv_opts(path: String, opts: R.CsvOpts) -> IO(E.Res(P.Plan)):
  P.Lazy.scan_csv(path, opts)

# a scan with a given schema: pure, no inference and no IO until collect, which checks the
# file's header against the schema's names and reads the cells strictly as its dtypes
def scan_csv_schema(path: String, opts: R.CsvOpts, schema: List<&2, S.Field>) -> P.Plan:
  P.ScanCsv{path, opts, schema}

def lazy_select(p: P.Plan, exprs: List<&2, X.Expr>) -> P.Plan:
  P.Select{exprs, p}

def lazy_with_columns(p: P.Plan, exprs: List<&2, X.Expr>) -> P.Plan:
  P.WithColumns{exprs, p}

def lazy_filter(p: P.Plan, pred: X.Expr) -> P.Plan:
  P.Filter{pred, p}

def lazy_sort(p: P.Plan, keys: List<&2, O.SortKey>) -> P.Plan:
  P.Sort{keys, p}

def lazy_group_by(p: P.Plan, keys: List<&2, X.Expr>, aggs: List<&2, X.Expr>) -> P.Plan:
  P.GroupBy{keys, aggs, True{}, p}

def lazy_head(p: P.Plan, n: U32) -> P.Plan:
  P.Head{n, p}

def lazy_inner_join(left: P.Plan, right: P.Plan, left_on: List<&2, String>, right_on: List<&2, String>) -> P.Plan:
  P.Join{J.Inner{}, left_on, right_on, left, right}

def lazy_left_join(left: P.Plan, right: P.Plan, left_on: List<&2, String>, right_on: List<&2, String>) -> P.Plan:
  P.Join{J.Left{}, left_on, right_on, left, right}

# ---- lazy: inspect and run ------------------------------------------------------------

# the output schema, with no data read (strict: a type error is an Err value)
def collect_schema(p: P.Plan) -> E.Res(List<&2, S.Field>):
  P.Plan.schema(p)

# an error as text
def err_show(e: E.Err) -> String:
  E.Err.show(e)

# a schema as text ("a:u32, b:f32"), or the error that stopped it
def schema_show(r: E.Res(List<&2, S.Field>)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{s}:
      S.Schema.show(s)

# the plan as an indented tree, one node per line
def explain(p: P.Plan) -> String:
  P.Plan.explain(p)

# the plan collect runs (DESIGN.md 15.2.8): only the certified rewrites (Head
# merging; a Head sinks only below a Select/WithColumns the analysis certifies
# height preserving)
def optimize(p: P.Plan) -> P.Plan:
  P.Optimize.release(p)

# every rewrite (filter merge, pushdown, head, projection), opt-in, outside the
# release guarantee
def optimize_full(p: P.Plan) -> P.Plan:
  P.Plan.optimize_full(p)

# optimise (DF.optimize), then execute: the frame, or the first error (the
# plan's schema error, then a binding error, then IO / data errors)
def collect(p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  Q.Lazy.collect(p, env)

# execute the plan as written (no rewrite)
def collect_raw(p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  Q.Exec.run(p, env)

# execute after DF.optimize_full
def collect_full(p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  Q.Lazy.collect_full(p, env)
