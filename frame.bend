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

# ---- columns and literals -------------------------------------------------------------

def col(name: String) -> X.Expr:
  X.Col{name}

def lit_u32(v: U32) -> X.Expr:
  X.Lit{D.SU32{v}}

# non-negative only (the bit pattern must be < 2^31); see lit_i32_neg
def lit_i32(v: U32) -> X.Expr:
  X.Lit{D.SI32{D.I32{v}}}

# -v
def lit_i32_neg(v: U32) -> X.Expr:
  X.Lit{D.SI32{D.I32.neg(D.I32{v})}}

def lit_f32(v: F32) -> X.Expr:
  X.Lit{D.SF32{v}}

def lit_str(s: String) -> X.Expr:
  X.Lit{D.SStr{s}}

def lit_bool(b: Bool) -> X.Expr:
  X.Lit{D.SBool{b}}

def alias(e: X.Expr, name: String) -> X.Expr:
  X.Alias{e, name}

def cast(e: X.Expr, t: D.DType) -> X.Expr:
  X.Cast{e, t}

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

def div(a: X.Expr, b: X.Expr) -> X.Expr:
  X.Bin{X.Div{}, a, b}

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

# ---- aggregations (inside group_by only; see DESIGN.md 4.13) ------------------------

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

def read_csv(path: String) -> IO(E.ResT(C.Frame)):
  R.Csv.read(path, R.Csv.default())

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

def write_csv.io(f: C.Frame, path: String) -> IO(E.ResT(C.Frame)):
  do IO<E.ResT(C.Frame)>:
    x : C.Frame & Result<&1, &1, U32 & String, Unit> <- R.Csv.write(f, path)
    return write_csv.r(x)

# writes the frame as CSV (F32 shortest digits) and answers the same frame, or
# the write's error; an error in r passes through
def write_csv(r: E.ResT(C.Frame), path: String) -> IO(E.ResT(C.Frame)):
  match r:
    case Fail{e}:
      IO.pure(E.ResT(C.Frame), Fail{e})
    case Done{f}:
      write_csv.io(f, path)

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

# reads the header and a sample of a CSV file now; the rows are read at collect
def scan_csv(path: String) -> IO(E.Res(P.Plan)):
  P.Lazy.scan_csv(path, R.Csv.default())

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

# the same plan after the rewrites (filter merge, pushdown, head merge, projection)
def optimize(p: P.Plan) -> P.Plan:
  P.Plan.optimize(p)

# optimise, then execute: the frame, or the first error
def collect(p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  Q.Lazy.collect(p, env)
