# src/plan.bend -- the lazy Plan (Polars LazyFrame), Env, Plan.schema
# (collect_schema), Plan.optimize, Plan.explain, Lazy.scan_csv. DESIGN.md 4.13.
#
# A Plan is pure Data: a tree of operators over named in-memory frames
# (`Source`, the frames live in an `Env`) or CSV files (`ScanCsv`). Nothing
# here touches column data; `src/exec.bend` runs a plan.
#
# Plan.schema (collect_schema) is strict and data-free, and agrees with the
# eager verbs of eval.bend on every plan it accepts. Expressions are typed by
# the shared analysis (A.Ana.type = the dtype of A.Expr.analyse, src/analysis.bend),
# the same function Eval's type check uses:
#   - Select: each expression typed against the input schema (first error in
#     list order), then DuplicateColumn on repeated output names
#     (Schema.project.chk, the same check Schema.project uses, so a Select of
#     plain Cols IS Schema.project of the names).
#   - WithColumns: every expression sees the INPUT schema (Polars); type
#     errors in list order, then DuplicateColumn; then Schema.with in order.
#   - Filter: the predicate's type error, else TypeMismatch{"filter", "bool",
#     got}.
#   - Global reductions are accepted in Select/WithColumns/Filter, as eagerly
#     (DESIGN.md 15.2.5, 15.4: B04-a); a reduction over a reduction is the
#     analysis' "nested aggregation" error. Row preservation is therefore not
#     "no Agg node" any more: the optimizer asks the analysis (Ana.preserving,
#     Ana.rowwise_total).
#   - Sort: every key must exist (ColumnNotFound), schema unchanged.
#   - GroupBy: G.Grp.validate (groupby.bend, what GroupBy.run checks): type
#     errors (keys, then aggs), >= 1 key, keys non-aggregate, each agg an
#     `Agg{op, e}` under at most Aliases with a non-aggregate `e`; output
#     keys then aggs; DuplicateColumn last.
#   - Join: J.Join.schema (join.bend, what Join.run checks): >= 1 key pair,
#     equal lengths, keys exist, key dtypes equal (TypeMismatch{"join", left,
#     right}); output = left fields, then right non-key fields, a right name
#     that clashes with ANY left name gets the suffix `_right`;
#     DuplicateColumn last.
#   - Head: input schema.
#   - Drop / Rename / Slice / Tail / Unique / Concat (M3): the static rules of src/table.bend
#     (TV.Drop.schema, TV.Rename.schema, TV.Unique.schema, TV.Concat.schema; slice and tail keep
#     the input schema). Concat{i, l, r} is one step of a left-nested chain (Lazy.concat): l's
#     errors, r's, then r (input i) against l's schema (input 0's); i = 0 is the empty list.
#     Join{Semi/Anti}: the join's key checks, then the left fields (J.Join.schema.how).
#   - ScanCsv/Source: their declared schema. `Lazy.scan_csv` fills
#     ScanCsv.schema at plan-build time from the header + the first
#     `infer_rows` rows (Csv.infer), so Plan.schema stays pure; Exec reads
#     the file with exactly those dtypes (strict) and checks the names.
#
# Optimizers (DESIGN.md 15.2.8). Both run only on plans whose schema resolves
# (an ill-typed plan comes back unchanged, so the schema is kept trivially on
# errors).
#   Optimize.release (DF.optimize, used by collect): the proven fragment, exactly
#     Opt.hmerge: Head{n, Head{m, x}} -> Head{min n m, x}, and nothing else. Every
#     other node is a barrier, Select / WithColumns included whatever the analysis
#     says of them (M5 part 2 decision, DESIGN.md 8 / 14: the analysis-certified
#     Head sink, R3, is not proven, so it moved to optimize_full). The theorem
#     `release_run` (LAWS.bend 8) covers every plan and every env.
#   Plan.optimize_full (DF.optimize_full, opt-in, outside the guarantee): four
#     structural passes, in this order:
#   1. Opt.merge  Filter{p, Filter{q, x}} -> Filter{q & p, x}; applied only
#                 when every Filter predicate of the plan is total and no
#                 reduction (Opt.merge_safe), since merging evaluates the outer
#                 predicate on rows the inner one removed.
#   2. Opt.push   predicate pushdown: predicates are split into conjuncts and
#                 sunk through Select (when every column they read is a plain
#                 `Col`/`Alias{Col}` output; renamed back through the alias),
#                 WithColumns (when they read no column it produces) and Sort;
#                 never through Head, GroupBy, Join. Only total, reduction-free
#                 predicates move, and only through Select/WithColumns whose
#                 expressions are total and reduction-free (and, for Select,
#                 height preserving: some KRow); every other Filter/node is a
#                 barrier. Conjuncts that cannot move stay where they are
#                 (re-joined with `&`).
#   3. Opt.head   Head merging as Opt.hmerge, plus the Head sink below a
#                 Select/WithColumns the analysis certifies as height preserving
#                 (Opt.sinks = Ana.preserving: a non-empty list of KRow, total,
#                 local expressions). Literal-only, reduction, mixed, empty and
#                 fallible (strict cast) nodes are barriers (B01-a, B01-f,
#                 B04-j); so is every other node, the M3 table verbs included
#                 (no rewrite moves anything across Drop, Rename, Slice, Tail,
#                 Unique, Concat or a semi / anti Join, in either optimizer).
#   4. Opt.proj   projection pushdown: the names needed above each node; a
#                 `Select{[Col ..]}` of the needed columns (source order) is
#                 inserted directly over a Source/ScanCsv when it narrows it
#                 (not when the parent is already a plain-Col Select).
#
# Idioms (DESIGN.md section 9): helpers above callers; match only on params;
# pairs taken apart in a helper's parameter; `+` on every reused binder.
import Base
import ./dtype.bend as D
import ./err.bend as E
import ./column.bend as C
import ./schema.bend as S
import ./expr.bend as X
import ./analysis.bend as A
import ./csv.bend as V
import ./sort.bend as O
import ./join.bend as J
import ./groupby.bend as G
import ./table.bend as TV

type Plan is Data:
  ScanCsv{path: String, opts: V.CsvOpts, schema: List<&2, S.Field>}
  Source{name: String, schema: List<&2, S.Field>}
  Select{exprs: List<&2, X.Expr>, input: Plan}
  WithColumns{exprs: List<&2, X.Expr>, input: Plan}
  Filter{pred: X.Expr, input: Plan}
  Sort{keys: List<&2, O.SortKey>, input: Plan}
  GroupBy{keys: List<&2, X.Expr>, aggs: List<&2, X.Expr>, maintain_order: Bool, input: Plan}
  Join{how: J.JoinHow, left_on: List<&2, String>, right_on: List<&2, String>, left: Plan, right: Plan}
  Head{n: U32, input: Plan}
  Drop{names: List<&2, String>, input: Plan}
  Rename{pairs: List<&2, Sigma<&2, &2, String, x => String>>, input: Plan}
  Slice{offset: U32, len: U32, input: Plan}
  Tail{n: U32, input: Plan}
  Unique{subset: List<&2, String>, input: Plan}
  Concat{index: U32, left: Plan, right: Plan}

# the frames a plan's Source nodes name
type Named.Frame is Type:
  NF{name: String, frame: C.Frame}

type Env is Type:
  Env{frames: List<&1, Named.Frame>}

# a rename through a Select: output name `out` is the input column `src`
type Ren is Data:
  Ren{out: String, src: String}

# what an Env binds under a name (Env.info): the frame's schema
type Bind is Data:
  Bind{name: String, schema: List<&2, S.Field>}

# ---- Plan.schema ------------------------------------------------------------------

# one output field: the expression's dtype (the shared analysis), or its error
def Plan.field.k(t: E.Res(D.DType), n: String) -> E.Res(S.Field):
  match t:
    case Fail{e}:
      Fail{e}
    case Done{d}:
      Done{S.Field{n, d}}

def Plan.field(+e: X.Expr, +s: List<&2, S.Field>) -> E.Res(S.Field):
  Plan.field.k(A.Ana.type(e, s), X.Expr.name(e))

# cons a field result onto the rest: the earlier (outer) error wins
def Plan.fields.put(f: E.Res(S.Field), r: E.Res(List<&2, S.Field>)) -> E.Res(List<&2, S.Field>):
  match f r:
    case Fail{e} _:
      Fail{e}
    case Done{x} Fail{e}:
      Fail{e}
    case Done{x} Done{xs}:
      Done{x <> xs}

# the fields of expressions over one input schema, first error in list order
# (no duplicate check: Schema.project.chk does it after)
def Plan.fields(es: List<&2, X.Expr>, +s: List<&2, S.Field>) -> E.Res(List<&2, S.Field>):
  match es:
    case Nil{}:
      Done{Nil{}}
    case e <> t:
      Plan.fields.put(Plan.field(e, s), Plan.fields(t, s))

def Plan.schema.select(es: List<&2, X.Expr>, r: E.Res(List<&2, S.Field>)) -> E.Res(List<&2, S.Field>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{s}:
      S.Schema.project.chk(Plan.fields(es, s))

# Schema.with each output field in order
def Plan.with_all(fs: List<&2, S.Field>, s: List<&2, S.Field>) -> List<&2, S.Field>:
  match fs:
    case Nil{}:
      s
    case f <> t:
      Plan.with_all(t, S.Schema.with(s, f))

def Plan.schema.wc.k(r: E.Res(List<&2, S.Field>), s: List<&2, S.Field>) -> E.Res(List<&2, S.Field>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{fs}:
      Done{Plan.with_all(fs, s)}

def Plan.schema.wc(es: List<&2, X.Expr>, r: E.Res(List<&2, S.Field>)) -> E.Res(List<&2, S.Field>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+s}:
      Plan.schema.wc.k(S.Schema.project.chk(Plan.fields(es, s)), s)

def Plan.schema.filter.k(t: E.Res(D.DType), s: List<&2, S.Field>) -> E.Res(List<&2, S.Field>):
  match t:
    case Fail{e}:
      Fail{e}
    case Done{D.TBool{}}:
      Done{s}
    case Done{other}:
      Fail{E.TypeMismatch{"filter", "bool", D.DType.show(other)}}

def Plan.schema.filter(+e: X.Expr, r: E.Res(List<&2, S.Field>)) -> E.Res(List<&2, S.Field>):
  match r:
    case Fail{err}:
      Fail{err}
    case Done{+s}:
      Plan.schema.filter.k(A.Ana.type(e, s), s)

def Plan.sort.miss.k(has: Bool, n: String, rest: Maybe<&2, E.Err>) -> Maybe<&2, E.Err>:
  match has:
    case True{}:
      rest
    case False{}:
      Some{E.ColumnNotFound{n}}

# the first sort key that is not a column of s
def Plan.sort.miss(ks: List<&2, O.SortKey>, +s: List<&2, S.Field>) -> Maybe<&2, E.Err>:
  match ks:
    case Nil{}:
      None{}
    case O.SortKey{+n, d, nl} <> t:
      Plan.sort.miss.k(S.Schema.has(s, n), n, Plan.sort.miss(t, s))

def Plan.schema.sort.k(m: Maybe<&2, E.Err>, s: List<&2, S.Field>) -> E.Res(List<&2, S.Field>):
  match m:
    case Some{e}:
      Fail{e}
    case None{}:
      Done{s}

def Plan.schema.sort(ks: List<&2, O.SortKey>, r: E.Res(List<&2, S.Field>)) -> E.Res(List<&2, S.Field>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+s}:
      Plan.schema.sort.k(Plan.sort.miss(ks, s), s)

# the fields of already validated expressions
def Plan.tfields.put(n: String, t: E.Res(D.DType), rest: List<&2, S.Field>) -> List<&2, S.Field>:
  match t:
    case Fail{e}:
      rest
    case Done{d}:
      S.Field{n, d} <> rest

def Plan.tfields(es: List<&2, X.Expr>, +s: List<&2, S.Field>) -> List<&2, S.Field>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> t:
      Plan.tfields.put(X.Expr.name(e), X.Expr.type(e, s), Plan.tfields(t, s))

def Plan.schema.gb.k(m: Maybe<&2, E.Err>, keys: List<&2, X.Expr>, aggs: List<&2, X.Expr>, +s: List<&2, S.Field>) -> E.Res(List<&2, S.Field>):
  match m:
    case Some{e}:
      Fail{e}
    case None{}:
      S.Schema.project.chk(Done{Plan.tfields(List.append(&2, X.Expr, keys, aggs), s)})

# Grp.validate (src/groupby.bend) is the check GroupBy.run makes: type errors
# (keys, then aggs), >= 1 key, no aggregation in a key, every agg an
# `Agg{op, e}` under Aliases with a non-aggregate `e`; then DuplicateColumn
def Plan.schema.gb(+keys: List<&2, X.Expr>, +aggs: List<&2, X.Expr>, r: E.Res(List<&2, S.Field>)) -> E.Res(List<&2, S.Field>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+s}:
      Plan.schema.gb.k(G.Grp.validate(keys, aggs, s), keys, aggs, s)

# Join.schema (src/join.bend) is the single definition Join.run checks too
def Plan.schema.join(how: J.JoinHow, lo: List<&2, String>, ro: List<&2, String>, rl: E.Res(List<&2, S.Field>), rr: E.Res(List<&2, S.Field>)) -> E.Res(List<&2, S.Field>):
  match rl rr:
    case Fail{e} _:
      Fail{e}
    case Done{x} Fail{e}:
      Fail{e}
    case Done{ls} Done{rs}:
      J.Join.schema.how(how, ls, rs, lo, ro)

# the M3 table verbs: one static rule each over the input's schema (src/table.bend), a Fail of
# the input passing through
def Plan.schema.drop(ns: List<&2, String>, r: E.Res(List<&2, S.Field>)) -> E.Res(List<&2, S.Field>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{s}:
      TV.Drop.schema(ns, s)

def Plan.schema.rename(ps: List<&2, Sigma<&2, &2, String, x => String>>, r: E.Res(List<&2, S.Field>)) -> E.Res(List<&2, S.Field>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{s}:
      TV.Rename.schema(ps, s)

def Plan.schema.slice(o: U32, l: U32, r: E.Res(List<&2, S.Field>)) -> E.Res(List<&2, S.Field>):
  r

def Plan.schema.tail(n: U32, r: E.Res(List<&2, S.Field>)) -> E.Res(List<&2, S.Field>):
  r

def Plan.schema.unique(ss: List<&2, String>, r: E.Res(List<&2, S.Field>)) -> E.Res(List<&2, S.Field>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{s}:
      TV.Unique.schema(ss, s)

# Concat{i, l, r}: the left inputs' errors, then the right input's, then input i's schema
# against input 0's (TV.Concat.schema; i = 0 is the empty input list)
def Plan.schema.concat(i: U32, rl: E.Res(List<&2, S.Field>), rr: E.Res(List<&2, S.Field>)) -> E.Res(List<&2, S.Field>):
  match rl rr:
    case Fail{e} _:
      Fail{e}
    case Done{x} Fail{e}:
      Fail{e}
    case Done{ls} Done{rs}:
      TV.Concat.schema(i, ls, rs)

# the output schema with no data (Polars collect_schema), strict early errors
def Plan.schema(p: Plan) -> E.Res(List<&2, S.Field>):
  match p:
    case ScanCsv{path, opts, s}:
      Done{s}
    case Source{n, s}:
      Done{s}
    case Select{es, x}:
      Plan.schema.select(es, Plan.schema(x))
    case WithColumns{es, x}:
      Plan.schema.wc(es, Plan.schema(x))
    case Filter{e, x}:
      Plan.schema.filter(e, Plan.schema(x))
    case Sort{ks, x}:
      Plan.schema.sort(ks, Plan.schema(x))
    case GroupBy{ks, as, mo, x}:
      Plan.schema.gb(ks, as, Plan.schema(x))
    case Join{how, lo, ro, l, r}:
      Plan.schema.join(how, lo, ro, Plan.schema(l), Plan.schema(r))
    case Head{n, x}:
      Plan.schema(x)
    case Drop{ns, x}:
      Plan.schema.drop(ns, Plan.schema(x))
    case Rename{ps, x}:
      Plan.schema.rename(ps, Plan.schema(x))
    case Slice{o, l, x}:
      Plan.schema.slice(o, l, Plan.schema(x))
    case Tail{n, x}:
      Plan.schema.tail(n, Plan.schema(x))
    case Unique{ss, x}:
      Plan.schema.unique(ss, Plan.schema(x))
    case Concat{i, l, r}:
      Plan.schema.concat(i, Plan.schema(l), Plan.schema(r))

# ---- Plan.optimize: shared helpers -------------------------------------------------------

def Opt.all_in(xs: List<&2, String>, +ns: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Bool.and(C.Names.has(ns, x), Opt.all_in(t, ns))

def Opt.any_in(xs: List<&2, String>, +ns: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(C.Names.has(ns, x), Opt.any_in(t, ns))

def Opt.names(es: List<&2, X.Expr>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case e <> t:
      X.Expr.name(e) <> Opt.names(t)

# every column the expressions read, prepended to acc
def Opt.refs(es: List<&2, X.Expr>, acc: List<&2, String>) -> List<&2, String>:
  match es:
    case Nil{}:
      acc
    case e <> t:
      X.Expr.refs.go(e, Opt.refs(t, acc))

# ---- the analysis' certificates over a node's input schema (an input whose schema
# does not resolve certifies nothing) --------------------------------------------------

# Head may sink below Select/WithColumns{es}: non-empty, every expression KRow and total
def Opt.sinks(+es: List<&2, X.Expr>, r: E.Res(List<&2, S.Field>)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{+s}:
      A.Ana.preserving(es, s)

# a predicate that may see more rows than its Filter gives it: total, no reduction
def Opt.pred_ok(+e: X.Expr, r: E.Res(List<&2, S.Field>)) -> Bool:
  match r:
    case Fail{err}:
      False{}
    case Done{+s}:
      A.Ana.rowwise_total(e, s)

# a row filter commutes with Select{es}: height preserving, total, no reduction
def Opt.sel_ok(+es: List<&2, X.Expr>, r: E.Res(List<&2, S.Field>)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{+s}:
      A.Ana.rowwise_select(es, s)

# a row filter commutes with WithColumns{es}: total, no reduction
def Opt.wc_ok(+es: List<&2, X.Expr>, r: E.Res(List<&2, S.Field>)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{+s}:
      A.Ana.rowwise_with(es, s)

# ---- pass 1: filter merging ---------------------------------------------------------------

# Filter{e, x} where x is already merged: a Filter directly below absorbs e
def Opt.merge.f(e: X.Expr, x: Plan) -> Plan:
  match x:
    case Filter{q, y}:
      Filter{X.Bin{X.And{}, q, e}, y}
    case other:
      Filter{e, other}

def Opt.merge(p: Plan) -> Plan:
  match p:
    case ScanCsv{path, o, s}:
      ScanCsv{path, o, s}
    case Source{n, s}:
      Source{n, s}
    case Select{es, x}:
      Select{es, Opt.merge(x)}
    case WithColumns{es, x}:
      WithColumns{es, Opt.merge(x)}
    case Filter{e, x}:
      Opt.merge.f(e, Opt.merge(x))
    case Sort{ks, x}:
      Sort{ks, Opt.merge(x)}
    case GroupBy{ks, as, mo, x}:
      GroupBy{ks, as, mo, Opt.merge(x)}
    case Join{how, lo, ro, l, r}:
      Join{how, lo, ro, Opt.merge(l), Opt.merge(r)}
    case Head{n, x}:
      Head{n, Opt.merge(x)}
    case Drop{ns, x}:
      Drop{ns, Opt.merge(x)}
    case Rename{ps, x}:
      Rename{ps, Opt.merge(x)}
    case Slice{o, l, x}:
      Slice{o, l, Opt.merge(x)}
    case Tail{n, x}:
      Tail{n, Opt.merge(x)}
    case Unique{ss, x}:
      Unique{ss, Opt.merge(x)}
    case Concat{i, l, r}:
      Concat{i, Opt.merge(l), Opt.merge(r)}

# every Filter predicate of the plan is total and no reduction (over its input's
# schema): only then may Opt.merge evaluate an outer predicate on rows an inner one
# removed
def Opt.fsafe(p: Plan) -> Bool:
  match p:
    case ScanCsv{path, o, s}:
      True{}
    case Source{n, s}:
      True{}
    case Select{es, x}:
      Opt.fsafe(x)
    case WithColumns{es, x}:
      Opt.fsafe(x)
    case Filter{+e, +x}:
      Bool.and(Opt.pred_ok(e, Plan.schema(x)), Opt.fsafe(x))
    case Sort{ks, x}:
      Opt.fsafe(x)
    case GroupBy{ks, as, mo, x}:
      Opt.fsafe(x)
    case Join{how, lo, ro, l, r}:
      Bool.and(Opt.fsafe(l), Opt.fsafe(r))
    case Head{n, x}:
      Opt.fsafe(x)
    case Drop{ns, x}:
      Opt.fsafe(x)
    case Rename{ps, x}:
      Opt.fsafe(x)
    case Slice{o, l, x}:
      Opt.fsafe(x)
    case Tail{n, x}:
      Opt.fsafe(x)
    case Unique{ss, x}:
      Opt.fsafe(x)
    case Concat{i, l, r}:
      Bool.and(Opt.fsafe(l), Opt.fsafe(r))

def Opt.merge_if(ok: Bool, p: Plan) -> Plan:
  match ok:
    case True{}:
      Opt.merge(p)
    case False{}:
      p

# ---- pass 2: predicate pushdown -------------------------------------------------------------

# the conjuncts of a predicate, left to right, prepended to acc
def Opt.conj(e: X.Expr, acc: List<&2, X.Expr>) -> List<&2, X.Expr>:
  match e:
    case X.Bin{X.And{}, a, b}:
      Opt.conj(a, Opt.conj(b, acc))
    case other:
      other <> acc

def Opt.and_fold(ps: List<&2, X.Expr>, acc: X.Expr) -> X.Expr:
  match ps:
    case Nil{}:
      acc
    case q <> t:
      Opt.and_fold(t, X.Bin{X.And{}, acc, q})

# the pending conjuncts as one Filter over x (none: x itself)
def Opt.wrap(ps: List<&2, X.Expr>, x: Plan) -> Plan:
  match ps:
    case Nil{}:
      x
    case p <> t:
      Filter{Opt.and_fold(t, p), x}

# the input column behind a plain projection (`Col`, `Alias{Col}`), if any
def Opt.plain(e: X.Expr) -> Maybe<&2, String>:
  match e:
    case X.Col{n}:
      Some{n}
    case X.Alias{e2, n}:
      Opt.plain(e2)
    case _:
      None{}

def Opt.rens.k(m: Maybe<&2, String>, out: String, rest: List<&2, Ren>) -> List<&2, Ren>:
  match m:
    case Some{c}:
      Ren{out, c} <> rest
    case None{}:
      rest

# the plain projections of a Select, output name -> input column
def Opt.rens(es: List<&2, X.Expr>) -> List<&2, Ren>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> t:
      Opt.rens.k(Opt.plain(e), X.Expr.name(e), Opt.rens(t))

def Opt.rens.outs(rs: List<&2, Ren>) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case Ren{o, c} <> t:
      o <> Opt.rens.outs(t)

def Opt.ren.find(rs: List<&2, Ren>, +n: String) -> String:
  match rs:
    case Nil{}:
      n
    case Ren{+o, c} <> t:
      Bool.pick(String, String.eq(o, n), c, Opt.ren.find(t, n))

# rewrite the column names of an expression through a Select's renames
def Opt.rename(e: X.Expr, +rs: List<&2, Ren>) -> X.Expr:
  match e:
    case X.Col{n}:
      X.Col{Opt.ren.find(rs, n)}
    case X.Lit{v}:
      X.Lit{v}
    case X.Alias{e2, n}:
      X.Alias{Opt.rename(e2, rs), n}
    case X.Cast{e2, t}:
      X.Cast{Opt.rename(e2, rs), t}
    case X.TryCast{e2, t}:
      X.TryCast{Opt.rename(e2, rs), t}
    case X.Un{op, e2}:
      X.Un{op, Opt.rename(e2, rs)}
    case X.Bin{op, a, b}:
      X.Bin{op, Opt.rename(a, rs), Opt.rename(b, rs)}
    case X.FillNull{e2, v}:
      X.FillNull{Opt.rename(e2, rs), Opt.rename(v, rs)}
    case X.Agg{op, e2}:
      X.Agg{op, Opt.rename(e2, rs)}
    case X.When{c, a, b}:
      X.When{Opt.rename(c, rs), Opt.rename(a, rs), Opt.rename(b, rs)}
    case X.IsIn{e2, vs}:
      X.IsIn{Opt.rename(e2, rs), vs}
    case X.Clip{e2, lo, hi}:
      X.Clip{Opt.rename(e2, rs), lo, hi}
    case X.StrPred{op, e2, p}:
      X.StrPred{op, Opt.rename(e2, rs), p}

def Opt.keep.k(moves: Bool, p: X.Expr, rest: List<&2, X.Expr>) -> List<&2, X.Expr>:
  match moves:
    case True{}:
      rest
    case False{}:
      p <> rest

def Opt.move.k(moves: Bool, p: X.Expr, rest: List<&2, X.Expr>) -> List<&2, X.Expr>:
  match moves:
    case True{}:
      p <> rest
    case False{}:
      rest

# through a Select: a conjunct moves when it reads only plain projections
def Opt.sel.keep(ps: List<&2, X.Expr>, +outs: List<&2, String>) -> List<&2, X.Expr>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> t:
      Opt.keep.k(Opt.all_in(X.Expr.refs(p), outs), p, Opt.sel.keep(t, outs))

def Opt.sel.move(ps: List<&2, X.Expr>, +rs: List<&2, Ren>) -> List<&2, X.Expr>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> t:
      Opt.move.k(Opt.all_in(X.Expr.refs(p), Opt.rens.outs(rs)), Opt.rename(p, rs), Opt.sel.move(t, rs))

# through a WithColumns: a conjunct moves when it reads no produced name
def Opt.wc.keep(ps: List<&2, X.Expr>, +ns: List<&2, String>) -> List<&2, X.Expr>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> t:
      Opt.move.k(Opt.any_in(X.Expr.refs(p), ns), p, Opt.wc.keep(t, ns))

def Opt.wc.move(ps: List<&2, X.Expr>, +ns: List<&2, String>) -> List<&2, X.Expr>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> t:
      Opt.keep.k(Opt.any_in(X.Expr.refs(p), ns), p, Opt.wc.move(t, ns))

# what moves below a node: the movable conjuncts when the node allows it, else none
def Opt.gate(ok: Bool, ps: List<&2, X.Expr>) -> List<&2, X.Expr>:
  match ok:
    case True{}:
      ps
    case False{}:
      Nil{}

# what stays above a node: the unmovable conjuncts when the node allows moving, else all
def Opt.hold(ok: Bool, ps: List<&2, X.Expr>, kept: List<&2, X.Expr>) -> List<&2, X.Expr>:
  match ok:
    case True{}:
      kept
    case False{}:
      ps

# a Filter whose predicate may not move (fallible or a reduction) stays, with the
# pending conjuncts above it; a movable one joins them
def Opt.push.f(ok: Bool, e: X.Expr, ps: List<&2, X.Expr>, inner: Plan) -> Plan:
  match ok:
    case True{}:
      inner
    case False{}:
      Opt.wrap(ps, Filter{e, inner})

# sink the pending conjuncts `ps` (to be applied on top of p) as deep as they go
def Opt.push(p: Plan, +ps: List<&2, X.Expr>) -> Plan:
  match p:
    case ScanCsv{path, o, s}:
      Opt.wrap(ps, ScanCsv{path, o, s})
    case Source{n, s}:
      Opt.wrap(ps, Source{n, s})
    case Select{+es, +x}:
      +ok = Opt.sel_ok(es, Plan.schema(x))
      Opt.wrap(Opt.hold(ok, ps, Opt.sel.keep(ps, Opt.rens.outs(Opt.rens(es)))), Select{es, Opt.push(x, Opt.gate(ok, Opt.sel.move(ps, Opt.rens(es))))})
    case WithColumns{+es, +x}:
      +ok = Opt.wc_ok(es, Plan.schema(x))
      Opt.wrap(Opt.hold(ok, ps, Opt.wc.keep(ps, Opt.names(es))), WithColumns{es, Opt.push(x, Opt.gate(ok, Opt.wc.move(ps, Opt.names(es))))})
    case Filter{+e, +x}:
      +ok = Opt.pred_ok(e, Plan.schema(x))
      Opt.push.f(ok, e, ps, Opt.push(x, Opt.gate(ok, Opt.conj(e, ps))))
    case Sort{ks, x}:
      Sort{ks, Opt.push(x, ps)}
    case GroupBy{ks, as, mo, x}:
      Opt.wrap(ps, GroupBy{ks, as, mo, Opt.push(x, Nil{})})
    case Join{how, lo, ro, l, r}:
      Opt.wrap(ps, Join{how, lo, ro, Opt.push(l, Nil{}), Opt.push(r, Nil{})})
    case Head{n, x}:
      Opt.wrap(ps, Head{n, Opt.push(x, Nil{})})
    case Drop{ns, x}:
      Opt.wrap(ps, Drop{ns, Opt.push(x, Nil{})})
    case Rename{rs, x}:
      Opt.wrap(ps, Rename{rs, Opt.push(x, Nil{})})
    case Slice{o, l, x}:
      Opt.wrap(ps, Slice{o, l, Opt.push(x, Nil{})})
    case Tail{n, x}:
      Opt.wrap(ps, Tail{n, Opt.push(x, Nil{})})
    case Unique{ss, x}:
      Opt.wrap(ps, Unique{ss, Opt.push(x, Nil{})})
    case Concat{i, l, r}:
      Opt.wrap(ps, Concat{i, Opt.push(l, Nil{}), Opt.push(r, Nil{})})

# ---- pass 3: Head merging / pushdown ---------------------------------------------------------

def Opt.hmin(+m: U32, n: Maybe<&2, U32>) -> U32:
  match n:
    case None{}:
      m
    case Some{k}:
      U32.min(m, k)

def Opt.hwrap(n: Maybe<&2, U32>, x: Plan) -> Plan:
  match n:
    case None{}:
      x
    case Some{k}:
      Head{k, x}

# the limit that moves below a certified node (all of it, or none)
def Opt.hpass(ok: Bool, n: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match ok:
    case True{}:
      n
    case False{}:
      None{}

# the limit that stays above it
def Opt.hstop(ok: Bool, n: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match ok:
    case True{}:
      None{}
    case False{}:
      n

# sink the pending row limit `n` (to be applied on top of p): below a
# Select/WithColumns only when the analysis certifies it height preserving
# (Opt.sinks); every other node keeps the limit above it. optimize_full only
# (the sink is tested, not proven); Optimize.release uses Opt.hmerge
def Opt.head(p: Plan, +n: Maybe<&2, U32>) -> Plan:
  match p:
    case ScanCsv{path, o, s}:
      Opt.hwrap(n, ScanCsv{path, o, s})
    case Source{nm, s}:
      Opt.hwrap(n, Source{nm, s})
    case Select{+es, +x}:
      +ok = Opt.sinks(es, Plan.schema(x))
      Opt.hwrap(Opt.hstop(ok, n), Select{es, Opt.head(x, Opt.hpass(ok, n))})
    case WithColumns{+es, +x}:
      +ok = Opt.sinks(es, Plan.schema(x))
      Opt.hwrap(Opt.hstop(ok, n), WithColumns{es, Opt.head(x, Opt.hpass(ok, n))})
    case Filter{e, x}:
      Opt.hwrap(n, Filter{e, Opt.head(x, None{})})
    case Sort{ks, x}:
      Opt.hwrap(n, Sort{ks, Opt.head(x, None{})})
    case GroupBy{ks, as, mo, x}:
      Opt.hwrap(n, GroupBy{ks, as, mo, Opt.head(x, None{})})
    case Join{how, lo, ro, l, r}:
      Opt.hwrap(n, Join{how, lo, ro, Opt.head(l, None{}), Opt.head(r, None{})})
    case Head{m, x}:
      Opt.head(x, Some{Opt.hmin(m, n)})
    case Drop{ns, x}:
      Opt.hwrap(n, Drop{ns, Opt.head(x, None{})})
    case Rename{ps, x}:
      Opt.hwrap(n, Rename{ps, Opt.head(x, None{})})
    case Slice{o, l, x}:
      Opt.hwrap(n, Slice{o, l, Opt.head(x, None{})})
    case Tail{m, x}:
      Opt.hwrap(n, Tail{m, Opt.head(x, None{})})
    case Unique{ss, x}:
      Opt.hwrap(n, Unique{ss, Opt.head(x, None{})})
    case Concat{i, l, r}:
      Opt.hwrap(n, Concat{i, Opt.head(l, None{}), Opt.head(r, None{})})

# ---- the release optimizer's head pass: Head merging only -----------------------------------

# the pending row limit `n` (to be applied on top of p) merges with a Head directly
# below it (Head{n, Head{m, x}} -> Head{min n m, x}) and stays above every other
# node, Select / WithColumns included whatever the analysis says of them: the
# certified Head sink is Opt.head, optimize_full only (DESIGN.md 8, 14 "M5 part 2").
# Proven result preserving for every plan and env (LAWS.bend 8, hmerge_run /
# release_run, against Exec.run_pure)
def Opt.hmerge(p: Plan, n: Maybe<&2, U32>) -> Plan:
  match p:
    case ScanCsv{path, o, s}:
      Opt.hwrap(n, ScanCsv{path, o, s})
    case Source{nm, s}:
      Opt.hwrap(n, Source{nm, s})
    case Select{es, x}:
      Opt.hwrap(n, Select{es, Opt.hmerge(x, None{})})
    case WithColumns{es, x}:
      Opt.hwrap(n, WithColumns{es, Opt.hmerge(x, None{})})
    case Filter{e, x}:
      Opt.hwrap(n, Filter{e, Opt.hmerge(x, None{})})
    case Sort{ks, x}:
      Opt.hwrap(n, Sort{ks, Opt.hmerge(x, None{})})
    case GroupBy{ks, as, mo, x}:
      Opt.hwrap(n, GroupBy{ks, as, mo, Opt.hmerge(x, None{})})
    case Join{how, lo, ro, l, r}:
      Opt.hwrap(n, Join{how, lo, ro, Opt.hmerge(l, None{}), Opt.hmerge(r, None{})})
    case Head{m, x}:
      Opt.hmerge(x, Some{Opt.hmin(m, n)})
    case Drop{ns, x}:
      Opt.hwrap(n, Drop{ns, Opt.hmerge(x, None{})})
    case Rename{ps, x}:
      Opt.hwrap(n, Rename{ps, Opt.hmerge(x, None{})})
    case Slice{o, l, x}:
      Opt.hwrap(n, Slice{o, l, Opt.hmerge(x, None{})})
    case Tail{m, x}:
      Opt.hwrap(n, Tail{m, Opt.hmerge(x, None{})})
    case Unique{ss, x}:
      Opt.hwrap(n, Unique{ss, Opt.hmerge(x, None{})})
    case Concat{i, l, r}:
      Opt.hwrap(n, Concat{i, Opt.hmerge(l, None{}), Opt.hmerge(r, None{})})

# ---- pass 4: projection pushdown ------------------------------------------------------------

def Opt.sch(r: E.Res(List<&2, S.Field>)) -> List<&2, S.Field>:
  match r:
    case Fail{e}:
      Nil{}
    case Done{s}:
      s

def Opt.is_col(e: X.Expr) -> Bool:
  match e:
    case X.Col{n}:
      True{}
    case _:
      False{}

def Opt.all_cols(es: List<&2, X.Expr>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case e <> t:
      Bool.and(Opt.is_col(e), Opt.all_cols(t))

def Opt.key_names(ks: List<&2, O.SortKey>, acc: List<&2, String>) -> List<&2, String>:
  match ks:
    case Nil{}:
      acc
    case O.SortKey{n, d, nl} <> t:
      n <> Opt.key_names(t, acc)

def Opt.cols(fs: List<&2, S.Field>) -> List<&2, X.Expr>:
  match fs:
    case Nil{}:
      Nil{}
    case S.Field{n, t} <> rest:
      X.Col{n} <> Opt.cols(rest)

def Opt.fkeep.k(keep: Bool, f: S.Field, rest: List<&2, S.Field>) -> List<&2, S.Field>:
  match keep:
    case True{}:
      f <> rest
    case False{}:
      rest

# the fields of s whose names are needed, in s order
def Opt.fkeep(s: List<&2, S.Field>, +need: List<&2, String>) -> List<&2, S.Field>:
  match s:
    case Nil{}:
      Nil{}
    case S.Field{+n, t} <> rest:
      Opt.fkeep.k(C.Names.has(need, n), S.Field{n, t}, Opt.fkeep(rest, need))

def Opt.first(s: List<&2, S.Field>) -> List<&2, S.Field>:
  match s:
    case Nil{}:
      Nil{}
    case f <> t:
      f <> Nil{}

def Opt.proj.ins(fewer: Bool, kept: List<&2, S.Field>, p: Plan) -> Plan:
  match fewer:
    case True{}:
      Select{Opt.cols(kept), p}
    case False{}:
      p

def Opt.proj.k(+kept: List<&2, S.Field>, +s: List<&2, S.Field>, p: Plan) -> Plan:
  Opt.proj.ins(Nat.is_lt(List.length(&2, S.Field, kept), List.length(&2, S.Field, s)), kept, p)

# keep at least one column, so the height survives (a Select of literals only)
def Opt.proj.ne(kept: List<&2, S.Field>, +s: List<&2, S.Field>, p: Plan) -> Plan:
  match kept:
    case Nil{}:
      Opt.proj.k(Opt.first(s), s, p)
    case f <> t:
      Opt.proj.k(f <> t, s, p)

# a leaf: narrow it with a Select of the needed columns, unless the nearest
# ancestor above any Heads is already a plain-Col Select (`top`)
def Opt.proj.src(top: Bool, +need: List<&2, String>, +s: List<&2, S.Field>, p: Plan) -> Plan:
  match top:
    case True{}:
      p
    case False{}:
      Opt.proj.ne(Opt.fkeep(s, need), s, p)

def Opt.need.l.k(keep: Bool, n: String, rest: List<&2, String>) -> List<&2, String>:
  match keep:
    case True{}:
      n <> rest
    case False{}:
      rest

# a join's left columns to keep: needed above, keys, and every column a right
# non-key column clashes with (so the `_right` suffixes do not change)
def Opt.need.l(ls: List<&2, S.Field>, +need: List<&2, String>, +lo: List<&2, String>, +rnk: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case S.Field{+n, t} <> rest:
      Opt.need.l.k(Bool.or(Bool.or(C.Names.has(need, n), C.Names.has(lo, n)), C.Names.has(rnk, n)), n, Opt.need.l(rest, need, lo, rnk))

# a join's right non-key column names
def Opt.need.nk(rs: List<&2, S.Field>, +ro: List<&2, String>) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case S.Field{+n, t} <> rest:
      Opt.need.l.k(Bool.not(C.Names.has(ro, n)), n, Opt.need.nk(rest, ro))

def Opt.out_name(clash: Bool, +n: String) -> String:
  Bool.pick(String, clash, n ++ "_right", n)

# a join's right columns to keep: keys, and those whose OUTPUT name is needed
def Opt.need.r(rs: List<&2, S.Field>, +need: List<&2, String>, +ro: List<&2, String>, +lnames: List<&2, String>) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case S.Field{+n, t} <> rest:
      Opt.need.l.k(Bool.or(C.Names.has(ro, n), C.Names.has(need, Opt.out_name(C.Names.has(lnames, n), n))), n, Opt.need.r(rest, need, ro, lnames))

# need: the output names of p used above it
def Opt.proj(p: Plan, +need: List<&2, String>, top: Bool) -> Plan:
  match p:
    case ScanCsv{path, o, +s}:
      Opt.proj.src(top, need, s, ScanCsv{path, o, s})
    case Source{n, +s}:
      Opt.proj.src(top, need, s, Source{n, s})
    case Select{+es, x}:
      Select{es, Opt.proj(x, Opt.refs(es, Nil{}), Opt.all_cols(es))}
    case WithColumns{+es, x}:
      WithColumns{es, Opt.proj(x, Opt.refs(es, need), False{})}
    case Filter{+e, x}:
      Filter{e, Opt.proj(x, X.Expr.refs.go(e, need), False{})}
    case Sort{+ks, x}:
      Sort{ks, Opt.proj(x, Opt.key_names(ks, need), False{})}
    case GroupBy{+ks, +as, mo, x}:
      GroupBy{ks, as, mo, Opt.proj(x, Opt.refs(ks, Opt.refs(as, Nil{})), False{})}
    case Join{how, +lo, +ro, +l, +r}:
      Join{how, lo, ro, Opt.proj(l, Opt.need.l(Opt.sch(Plan.schema(l)), need, lo, Opt.need.nk(Opt.sch(Plan.schema(r)), ro)), False{}), Opt.proj(r, Opt.need.r(Opt.sch(Plan.schema(r)), need, ro, S.Schema.names(Opt.sch(Plan.schema(l)))), False{})}
    case Head{n, x}:
      Head{n, Opt.proj(x, need, top)}
    case Drop{ns, +x}:
      Drop{ns, Opt.proj(x, S.Schema.names(Opt.sch(Plan.schema(x))), False{})}
    case Rename{ps, +x}:
      Rename{ps, Opt.proj(x, S.Schema.names(Opt.sch(Plan.schema(x))), False{})}
    case Slice{o, l, +x}:
      Slice{o, l, Opt.proj(x, S.Schema.names(Opt.sch(Plan.schema(x))), False{})}
    case Tail{n, +x}:
      Tail{n, Opt.proj(x, S.Schema.names(Opt.sch(Plan.schema(x))), False{})}
    case Unique{ss, +x}:
      Unique{ss, Opt.proj(x, S.Schema.names(Opt.sch(Plan.schema(x))), False{})}
    case Concat{i, +l, +r}:
      Concat{i, Opt.proj(l, S.Schema.names(Opt.sch(Plan.schema(l))), False{}), Opt.proj(r, S.Schema.names(Opt.sch(Plan.schema(r))), False{})}

# ---- Optimize.release / Plan.optimize_full ------------------------------------------------------

def Optimize.release.k(r: E.Res(List<&2, S.Field>), p: Plan) -> Plan:
  match r:
    case Fail{e}:
      p
    case Done{s}:
      Opt.hmerge(p, None{})

# the default optimizer (DF.optimize, collect): only the proven rewrite
# (DESIGN.md 15.2.8, 8): adjacent Head merging (Opt.hmerge). An ill-typed plan
# comes back unchanged. `release_run` (LAWS.bend 8): Exec.run_pure gives the same
# result for Optimize.release(p) and p, for every plan p and every env.
def Optimize.release(+p: Plan) -> Plan:
  Optimize.release.k(Plan.schema(p), p)

def Plan.optimize_full.k(r: E.Res(List<&2, S.Field>), +p: Plan) -> Plan:
  match r:
    case Fail{e}:
      p
    case Done{s}:
      Opt.proj(Opt.head(Opt.push(Opt.merge_if(Opt.fsafe(p), p), Nil{}), None{}), S.Schema.names(s), False{})

# the four passes (filter merge, pushdown, head, projection), opt-in
# (DF.optimize_full, DF.collect_full), outside the release guarantee; an
# ill-typed plan comes back unchanged
def Plan.optimize_full(+p: Plan) -> Plan:
  Plan.optimize_full.k(Plan.schema(p), p)

# every Source name of a plan in postfix order (Exec's order), with repeats,
# prepended to acc (DESIGN.md 15.7)
def Plan.sources(p: Plan, acc: List<&2, String>) -> List<&2, String>:
  match p:
    case ScanCsv{path, o, s}:
      acc
    case Source{n, s}:
      n <> acc
    case Select{es, x}:
      Plan.sources(x, acc)
    case WithColumns{es, x}:
      Plan.sources(x, acc)
    case Filter{e, x}:
      Plan.sources(x, acc)
    case Sort{ks, x}:
      Plan.sources(x, acc)
    case GroupBy{ks, as, mo, x}:
      Plan.sources(x, acc)
    case Join{how, lo, ro, l, r}:
      Plan.sources(l, Plan.sources(r, acc))
    case Head{n, x}:
      Plan.sources(x, acc)
    case Drop{ns, x}:
      Plan.sources(x, acc)
    case Rename{ps, x}:
      Plan.sources(x, acc)
    case Slice{o, l, x}:
      Plan.sources(x, acc)
    case Tail{n, x}:
      Plan.sources(x, acc)
    case Unique{ss, x}:
      Plan.sources(x, acc)
    case Concat{i, l, r}:
      Plan.sources(l, Plan.sources(r, acc))

# ---- Plan.explain ----------------------------------------------------------------------------------

def Plan.exprs.go(es: List<&2, X.Expr>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case e <> t:
      X.Expr.show(e) <> Plan.exprs.go(t)

def Plan.exprs.show(es: List<&2, X.Expr>) -> String:
  "[" ++ String.join(Plan.exprs.go(es), ", ") ++ "]"

def Plan.keys.go(ks: List<&2, O.SortKey>) -> List<&2, String>:
  match ks:
    case Nil{}:
      Nil{}
    case O.SortKey{n, d, nl} <> t:
      ("col(\"" ++ n ++ "\")" ++ Bool.pick(String, d, " desc", "") ++ Bool.pick(String, nl, " nulls_last", "")) <> Plan.keys.go(t)

def Plan.on.go(lo: List<&2, String>, ro: List<&2, String>) -> List<&2, String>:
  match lo ro:
    case l <> lt r <> rt:
      (l ++ " = " ++ r) <> Plan.on.go(lt, rt)
    case _ _:
      Nil{}

def Plan.how.show(h: J.JoinHow) -> String:
  match h:
    case J.Inner{}:
      "INNER"
    case J.Left{}:
      "LEFT"
    case J.Semi{}:
      "SEMI"
    case J.Anti{}:
      "ANTI"

def Plan.strs.show(ns: List<&2, String>) -> String:
  "[" ++ String.join(ns, ", ") ++ "]"

def Plan.ren.go(ps: List<&2, Sigma<&2, &2, String, x => String>>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case (a, b) <> t:
      (a ++ " -> " ++ b) <> Plan.ren.go(t)

# the indentation of a Concat's inputs: one level deeper, except in a chain continuation (the
# left input of a Concat{i >= 2} is Concat{i - 1}: its inputs sit with the outer node's)
def Plan.lines.cind(cont: Bool, +ind: String) -> String:
  Bool.pick(String, cont, ind, ind ++ "  ")

# one line per node, children indented by two spaces, prepended to acc. `cont` marks the left
# input of a Concat chain (Plan.lines.cind): it prints no CONCAT header of its own, so a chain
# reads as ONE `CONCAT` with every input below it
def Plan.lines(p: Plan, +ind: String, +cont: Bool, +acc: List<&2, String>) -> List<&2, String>:
  match p:
    case ScanCsv{path, o, s}:
      (ind ++ "SCAN CSV " ++ path ++ " [" ++ S.Schema.show(s) ++ "]") <> acc
    case Source{n, s}:
      (ind ++ "SOURCE " ++ n ++ " [" ++ S.Schema.show(s) ++ "]") <> acc
    case Select{es, x}:
      (ind ++ "SELECT " ++ Plan.exprs.show(es)) <> Plan.lines(x, ind ++ "  ", False{}, acc)
    case WithColumns{es, x}:
      (ind ++ "WITH_COLUMNS " ++ Plan.exprs.show(es)) <> Plan.lines(x, ind ++ "  ", False{}, acc)
    case Filter{e, x}:
      (ind ++ "FILTER " ++ X.Expr.show(e)) <> Plan.lines(x, ind ++ "  ", False{}, acc)
    case Sort{ks, x}:
      (ind ++ "SORT BY [" ++ String.join(Plan.keys.go(ks), ", ") ++ "]") <> Plan.lines(x, ind ++ "  ", False{}, acc)
    case GroupBy{ks, as, mo, x}:
      (ind ++ "GROUP_BY " ++ Plan.exprs.show(ks) ++ " AGG " ++ Plan.exprs.show(as) ++ Bool.pick(String, mo, " MAINTAIN_ORDER", "")) <> Plan.lines(x, ind ++ "  ", False{}, acc)
    case Join{how, lo, ro, l, r}:
      +ind2 = ind ++ "  "
      (ind ++ Plan.how.show(how) ++ " JOIN ON [" ++ String.join(Plan.on.go(lo, ro), ", ") ++ "]") <> Plan.lines(l, ind2, False{}, Plan.lines(r, ind2, False{}, acc))
    case Head{n, x}:
      (ind ++ "HEAD " ++ U32.show(n)) <> Plan.lines(x, ind ++ "  ", False{}, acc)
    case Drop{ns, x}:
      (ind ++ "DROP " ++ Plan.strs.show(ns)) <> Plan.lines(x, ind ++ "  ", False{}, acc)
    case Rename{ps, x}:
      (ind ++ "RENAME [" ++ String.join(Plan.ren.go(ps), ", ") ++ "]") <> Plan.lines(x, ind ++ "  ", False{}, acc)
    case Slice{o, l, x}:
      (ind ++ "SLICE " ++ U32.show(o) ++ " " ++ U32.show(l)) <> Plan.lines(x, ind ++ "  ", False{}, acc)
    case Tail{n, x}:
      (ind ++ "TAIL " ++ U32.show(n)) <> Plan.lines(x, ind ++ "  ", False{}, acc)
    case Unique{ss, x}:
      (ind ++ "UNIQUE " ++ Plan.strs.show(ss)) <> Plan.lines(x, ind ++ "  ", False{}, acc)
    case Concat{+i, l, r}:
      +ind2 = Plan.lines.cind(cont, ind)
      +body = Bool.pick(List<&2, String>, U32.is_zero(i), acc, Plan.lines(l, ind2, U32.is_gt(i, 1), Plan.lines(r, ind2, False{}, acc)))
      Bool.pick(List<&2, String>, cont, body, (ind ++ "CONCAT") <> body)

# the plan as an indented tree (Polars `explain()`), one node per line
def Plan.explain(p: Plan) -> String:
  String.join(Plan.lines(p, "", False{}, Nil{}), "\n")

# ---- Env -------------------------------------------------------------------------------------------

def Env.empty() -> Env:
  Env{Nil{}}

def Env.add.k(+name: String, fs: List<&1, Named.Frame>, r: C.Frame & List<&2, S.Field>) -> Env & Plan:
  (f, s) = r
  (Env{NF{name, f} <> fs}, Source{name, s})

# register a frame under a name; answers the Source plan that reads it
def Env.add(env: Env, +name: String, f: C.Frame) -> Env & Plan:
  match env:
    case Env{fs}:
      Env.add.k(name, fs, S.Frame.schema(f))

# a one-frame environment and its Source (Polars `df.lazy()`)
def Lazy.source(+name: String, f: C.Frame) -> Env & Plan:
  Env.add(Env.empty(), name, f)

def Lazy.concat.go(ps: List<&2, Plan>, acc: Plan, +i: U32) -> Plan:
  match ps:
    case Nil{}:
      acc
    case p <> t:
      Lazy.concat.go(t, Concat{i, acc, p}, U32.inc(i))

# concat_vertical of plans (DESIGN.md 15.2.4, 14 "M3 table verbs"): [p0, p1, .., pk] is the
# left-nested chain Concat{k, .. Concat{2, Concat{1, p0, p1}, p2} .., pk} of binary nodes
# (Concat{i, l, r}: r is input i); one plan is itself; [] is Concat{0, ..} over two empty
# Sources, whose schema is the static error "concat_vertical: no inputs"
def Lazy.concat(ps: List<&2, Plan>) -> Plan:
  match ps:
    case Nil{}:
      Concat{0, Source{"", Nil{}}, Source{"", Nil{}}}
    case p <> t:
      Lazy.concat.go(t, p, 1)

def Env.take.hit.k(f: C.Frame, r: List<&1, Named.Frame> & Maybe<&1, C.Frame>) -> List<&1, Named.Frame> & Maybe<&1, C.Frame>:
  (rest, m) = r
  (rest, Some{f})

def Env.take.hit(nf: Named.Frame, r: List<&1, Named.Frame> & Maybe<&1, C.Frame>) -> List<&1, Named.Frame> & Maybe<&1, C.Frame>:
  match nf:
    case NF{n, f}:
      Env.take.hit.k(f, r)

def Env.take.miss(nf: Named.Frame, r: List<&1, Named.Frame> & Maybe<&1, C.Frame>) -> List<&1, Named.Frame> & Maybe<&1, C.Frame>:
  (rest, m) = r
  (nf <> rest, m)

def Env.take.k(r: List<&1, Named.Frame> & Maybe<&1, C.Frame>) -> Env & Maybe<&1, C.Frame>:
  (fs, m) = r
  (Env{fs}, m)

# a later (older) frame of the same name is dropped when an earlier one hits:
# Env names are meant to be unique (Env.add prepends)
def Env.take.pick(hit: Bool, nf: Named.Frame, r: List<&1, Named.Frame> & Maybe<&1, C.Frame>) -> List<&1, Named.Frame> & Maybe<&1, C.Frame>:
  match hit:
    case True{}:
      Env.take.hit(nf, r)
    case False{}:
      Env.take.miss(nf, r)

def Env.take.go(fs: List<&1, Named.Frame>, +name: String) -> List<&1, Named.Frame> & Maybe<&1, C.Frame>:
  match fs:
    case Nil{}:
      (Nil{}, None{})
    case NF{+n, f} <> t:
      Env.take.pick(String.eq(n, name), NF{n, f}, Env.take.go(t, name))

# remove the first frame of that name (a frame is consumed by one Source)
def Env.take(env: Env, +name: String) -> Env & Maybe<&1, C.Frame>:
  match env:
    case Env{fs}:
      Env.take.k(Env.take.go(fs, name))

def Env.clone.k(+n: String, cc: C.Frame & C.Frame, r: List<&1, Named.Frame> & Maybe<&1, C.Frame>) -> List<&1, Named.Frame> & Maybe<&1, C.Frame>:
  (a, b) = cc
  (rest, m) = r
  (NF{n, a} <> rest, Some{b})

def Env.clone.pick(hit: Bool, +n: String, f: C.Frame, r: List<&1, Named.Frame> & Maybe<&1, C.Frame>) -> List<&1, Named.Frame> & Maybe<&1, C.Frame>:
  match hit:
    case True{}:
      Env.clone.k(n, C.Frame.clone(f), r)
    case False{}:
      (rest, m) = r
      (NF{n, f} <> rest, m)

def Env.clone.go(fs: List<&1, Named.Frame>, +name: String) -> List<&1, Named.Frame> & Maybe<&1, C.Frame>:
  match fs:
    case Nil{}:
      (Nil{}, None{})
    case NF{+n, f} <> t:
      Env.clone.pick(String.eq(n, name), n, f, Env.clone.go(t, name))

# a copy of the first frame of that name (Frame.clone, column order kept); the
# frame stays in env (a Source used again later, DESIGN.md 15.7)
def Env.clone(env: Env, +name: String) -> Env & Maybe<&1, C.Frame>:
  match env:
    case Env{fs}:
      Env.take.k(Env.clone.go(fs, name))

def Env.info.k(+n: String, r: C.Frame & List<&2, S.Field>, rest: List<&1, Named.Frame> & List<&2, Bind>) -> List<&1, Named.Frame> & List<&2, Bind>:
  (f, s) = r
  (fs, bs) = rest
  (NF{n, f} <> fs, Bind{n, s} <> bs)

def Env.info.go(fs: List<&1, Named.Frame>) -> List<&1, Named.Frame> & List<&2, Bind>:
  match fs:
    case Nil{}:
      (Nil{}, Nil{})
    case NF{+n, f} <> t:
      Env.info.k(n, S.Frame.schema(f), Env.info.go(t))

def Env.info.fin(r: List<&1, Named.Frame> & List<&2, Bind>) -> Env & List<&2, Bind>:
  (fs, bs) = r
  (Env{fs}, bs)

# the name and schema of every frame, in env order; env comes back untouched
def Env.info(env: Env) -> Env & List<&2, Bind>:
  match env:
    case Env{fs}:
      Env.info.fin(Env.info.go(fs))

# ---- Lazy.scan_csv: the schema from the header + the first infer_rows rows ----------------------

def Lazy.fields(cs: List<&2, V.CsvField>) -> List<&2, S.Field>:
  match cs:
    case Nil{}:
      Nil{}
    case V.CsvField{n, t} <> rest:
      S.Field{n, t} <> Lazy.fields(rest)

def Lazy.scan.plan(path: String, opts: V.CsvOpts, r: E.Res(List<&2, V.CsvField>)) -> E.Res(Plan):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{cs}:
      Done{ScanCsv{path, opts, Lazy.fields(cs)}}

# Polars scan_csv: reads a bounded prefix of the file (Csv.scan_fields, DESIGN.md 15.6.4:
# 64 KiB chunks until infer_rows + 1 line ends outside quotes) to infer the schema; no
# column is built and the rest of the file is not read. The data is read at collect (Exec).
# IoError and ParseError are values.
def Lazy.scan_csv(+path: String, +opts: V.CsvOpts) -> IO(E.Res(Plan)):
  do IO<E.Res(Plan)>:
    r : E.Res(List<&2, V.CsvField>) <- V.Csv.scan_fields(path, opts)
    return Lazy.scan.plan(path, opts, r)
