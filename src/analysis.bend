# src/analysis.bend -- the shared expression analysis (DESIGN.md 15.3.2, plan P2):
# `Expr.analyse(e, s)` answers the record Ana{dtype, refs, kind, total, local}
# of an expression over a schema, or its first typing error. ONE function serves
#   - Eval (eager): the type check of every expression and select's height rule,
#   - Plan.schema (lazy, collect_schema): the dtype of every output field and
#     of a filter predicate,
#   - the optimizer (plan.bend): the height-preservation certificate behind
#     Opt.head and the totality / locality barrier for filter merge and pushdown.
# It lives in its own module (not expr.bend) so expr.bend's per-node typing rules
# (`Expr.type.col/lit/cast/un.ok/bin.ok/fill/agg.ok`) stay the single place a
# dtype rule is written: the analysis calls them on its sub-records' dtypes.
#
# Kinds (15.3.2): KRow = one value per input row (height h); KScalar = built from
# literals only (1 row, broadcastable, height-independent); KRed = a reduction of
# the input (1 row, computed over all h rows). Join: KRow wins, then KRed, else
# KScalar. An aggregation over a KRed operand is the error
# InvalidOperation{"nested aggregation: <Expr.show>"} (checked before the
# reducer's own dtype rule).
#
# Totality (15.3.2 note i, 15.5.5): `total = True{}` means Eval of the node over a
# well-formed frame never answers Fail whatever the data. It is syntactic and
# conservative: only `Cast` of a fallible pair (Ana.cast_total) is non-total; the
# typed null literal `Cast{Lit{SNull}, t}` is total.
#
# Locality (field `local`, an addition to the 15.3.2 record, DESIGN.md 14 "M1
# B01/B04"): `local = True{}` means no reduction occurs anywhere in e, so row i
# of the result depends on row i of the input only (and a KScalar on nothing).
# KRow alone does not give that: `x - mean(x)` is KRow (h rows) but every row
# reads all h rows, so a Head sunk below it, or a filter merged into or pushed
# below it, would change its values (tests/regress/B01_f "head2-over-centered").
#
# Soundness statement (proof is plan P2, milestones M2/M5; not proven here):
#   for a well-formed frame f with Frame.schema(f) = s and
#   Expr.analyse(e, s) = Done{Ana{t, rs, k, tot, loc}}:
#     Eval.full(f, e) answers (f', Done{c}) with Column.dtype(c) = t and
#     Column.len(c) = h, and Eval.expr(f, e) answers a column of dtype t whose
#     length is h when k = KRow, 1 when k is KScalar or KRed, whenever tot holds;
#     when tot does not hold the same conclusions hold for every Done answer and a
#     Fail is one of the 15.5.5 cast errors; f' = f; Eval reads only the columns
#     named in rs; when loc holds, row i of Eval.full(f, e) is row 0 of
#     Eval.full(row i of f, e) (and k is not KRed). (By induction over
#     Eval.compile's postfix code with the stack invariant "slot i carries the
#     record of its subexpression": KRow <-> KFull, KScalar <-> KLit,
#     KRed <-> KAgg.)
#   Consequences the optimizer relies on (15.4 rule): a Select/WithColumns whose
#   list is non-empty and whose records are all KRow, total and local commutes
#   with Head (Ana.preserving); a predicate whose record is total and local may be
#   evaluated over more rows than its Filter receives (Ana.rowwise_total); a row
#   filter commutes with a Select/WithColumns of total, local expressions that
#   keeps the height (Ana.rowwise_select / Ana.rowwise_with).
#
# Idioms (DESIGN.md section 9): helpers above callers; match only on params;
# a recursive def makes its recursive calls in the argument list of a helper.
import Base
import ./dtype.bend as D
import ./err.bend as E
import ./schema.bend as S
import ./expr.bend as X

# ("Kind" is a Bend keyword)
type AKind is Data:
  KRow{}
  KScalar{}
  KRed{}

type Ana is Data:
  Ana{dtype: D.DType, refs: List<&2, String>, kind: AKind, total: Bool, local: Bool}

# ---- kinds --------------------------------------------------------------------------

def AKind.join(a: AKind, b: AKind) -> AKind:
  match a b:
    case KRow{} _:
      KRow{}
    case _ KRow{}:
      KRow{}
    case KRed{} _:
      KRed{}
    case _ KRed{}:
      KRed{}
    case _ _:
      KScalar{}

def AKind.is_row(k: AKind) -> Bool:
  match k:
    case KRow{}:
      True{}
    case _:
      False{}

# ---- per-node rules -------------------------------------------------------------------

# the record of a node from its dtype rule's answer and its other fields
def Ana.mk(t: E.Res(D.DType), rs: List<&2, String>, k: AKind, tot: Bool, loc: Bool) -> E.Res(Ana):
  match t:
    case Fail{e}:
      Fail{e}
    case Done{d}:
      Done{Ana{d, rs, k, tot, loc}}

# DESIGN.md 15.5.5: a cast pair is total when no valid cell can fail. Pairs the
# cast table refuses (Cast.ok) never get here.
def Ana.cast_total(from: D.DType, to: D.DType) -> Bool:
  match from to:
    case D.TBool{} _:
      True{}
    case D.TU32{} D.TI32{}:
      False{}
    case D.TU32{} _:
      True{}
    case D.TI32{} D.TU32{}:
      False{}
    case D.TI32{} _:
      True{}
    case D.TF32{} D.TF32{}:
      True{}
    case D.TF32{} D.TStr{}:
      True{}
    case D.TF32{} _:
      False{}
    case D.TStr{} D.TStr{}:
      True{}
    case D.TStr{} _:
      False{}

def Ana.col(+n: String, t: Maybe<&2, D.DType>) -> E.Res(Ana):
  Ana.mk(X.Expr.type.col(n, t), n <> Nil{}, KRow{}, True{}, True{})

def Ana.lit(v: D.Scalar) -> E.Res(Ana):
  Ana.mk(X.Expr.type.lit(D.Scalar.dtype(v)), Nil{}, KScalar{}, True{}, True{})

def Ana.cast.k(+to: D.DType, a: Ana) -> E.Res(Ana):
  match a:
    case Ana{+t, rs, k, tot, loc}:
      Ana.mk(X.Expr.type.cast(False{}, to, Done{t}), rs, k, Bool.and(tot, Ana.cast_total(t, to)), loc)

# the typed null literal Cast{Lit{SNull}, to} is a total scalar of dtype `to`
def Ana.cast(nl: Bool, +to: D.DType, r: E.Res(Ana)) -> E.Res(Ana):
  match nl r:
    case True{} _:
      Done{Ana{to, Nil{}, KScalar{}, True{}, True{}}}
    case False{} Fail{e}:
      Fail{e}
    case False{} Done{a}:
      Ana.cast.k(to, a)

def Ana.un.k(op: X.UnOp, a: Ana) -> E.Res(Ana):
  match a:
    case Ana{t, rs, k, tot, loc}:
      Ana.mk(X.Expr.type.un.ok(op, t), rs, k, tot, loc)

def Ana.un(op: X.UnOp, r: E.Res(Ana)) -> E.Res(Ana):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{a}:
      Ana.un.k(op, a)

def Ana.bin.k(op: X.BinOp, a: Ana, b: Ana) -> E.Res(Ana):
  match a b:
    case Ana{ta, ra, ka, xa, la} Ana{tb, rb, kb, xb, lb}:
      Ana.mk(X.Expr.type.bin.ok(op, ta, tb), List.append(&2, String, ra, rb), AKind.join(ka, kb), Bool.and(xa, xb), Bool.and(la, lb))

# the left operand's error wins
def Ana.bin(op: X.BinOp, ra: E.Res(Ana), rb: E.Res(Ana)) -> E.Res(Ana):
  match ra rb:
    case Fail{e} _:
      Fail{e}
    case Done{a} Fail{e}:
      Fail{e}
    case Done{a} Done{b}:
      Ana.bin.k(op, a, b)

def Ana.fill.k(a: Ana, b: Ana) -> E.Res(Ana):
  match a b:
    case Ana{ta, ra, ka, xa, la} Ana{tb, rb, kb, xb, lb}:
      Ana.mk(X.Expr.type.fill(Done{ta}, Done{tb}), List.append(&2, String, ra, rb), AKind.join(ka, kb), Bool.and(xa, xb), Bool.and(la, lb))

def Ana.fill(ra: E.Res(Ana), rb: E.Res(Ana)) -> E.Res(Ana):
  match ra rb:
    case Fail{e} _:
      Fail{e}
    case Done{a} Fail{e}:
      Fail{e}
    case Done{a} Done{b}:
      Ana.fill.k(a, b)

# a reducer over a KRed operand is a nested aggregation; otherwise a KRed of the
# reducer's dtype, as total as its operand, never local
def Ana.agg.k(k: AKind, +op: X.AggOp, +e: X.Expr, t: D.DType, rs: List<&2, String>, tot: Bool) -> E.Res(Ana):
  match k:
    case KRed{}:
      Fail{E.InvalidOperation{"nested aggregation: " ++ X.Expr.show(X.Agg{op, e})}}
    case _:
      Ana.mk(X.Expr.type.agg.ok(op, t), rs, KRed{}, tot, False{})

def Ana.agg.a(+op: X.AggOp, +e: X.Expr, a: Ana) -> E.Res(Ana):
  match a:
    case Ana{t, rs, k, tot, loc}:
      Ana.agg.k(k, op, e, t, rs, tot)

def Ana.agg(+op: X.AggOp, +e: X.Expr, r: E.Res(Ana)) -> E.Res(Ana):
  match r:
    case Fail{err}:
      Fail{err}
    case Done{a}:
      Ana.agg.a(op, e, a)

# ---- the analysis ---------------------------------------------------------------------

# the dtype / refs / kind / totality / locality of e over schema s, or the first
# typing error (left to right, innermost first; Expr.type's errors and texts)
def Expr.analyse(e: X.Expr, +s: List<&2, S.Field>) -> E.Res(Ana):
  match e:
    case X.Col{+n}:
      Ana.col(n, S.Schema.find(s, n))
    case X.Lit{v}:
      Ana.lit(v)
    case X.Alias{e2, n}:
      Expr.analyse(e2, s)
    case X.Cast{+e2, +to}:
      Ana.cast(X.Expr.is_null_lit(e2), to, Expr.analyse(e2, s))
    case X.Un{op, e2}:
      Ana.un(op, Expr.analyse(e2, s))
    case X.Bin{op, a, b}:
      Ana.bin(op, Expr.analyse(a, s), Expr.analyse(b, s))
    case X.FillNull{e2, v}:
      Ana.fill(Expr.analyse(e2, s), Expr.analyse(v, s))
    case X.Agg{+op, +e2}:
      Ana.agg(op, e2, Expr.analyse(e2, s))

# ---- projections ------------------------------------------------------------------------

def Ana.dtype(a: Ana) -> D.DType:
  match a:
    case Ana{t, rs, k, tot, loc}:
      t

def Ana.kind(a: Ana) -> AKind:
  match a:
    case Ana{t, rs, k, tot, loc}:
      k

# total and local: the expression may see rows its node would not give it
def Ana.safe(a: Ana) -> Bool:
  match a:
    case Ana{t, rs, k, tot, loc}:
      Bool.and(tot, loc)

def Ana.type.k(r: E.Res(Ana)) -> E.Res(D.DType):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{a}:
      Done{Ana.dtype(a)}

# the dtype of e over s (what Plan.schema and Eval's type check use)
def Ana.type(e: X.Expr, +s: List<&2, S.Field>) -> E.Res(D.DType):
  Ana.type.k(Expr.analyse(e, s))

def Ana.list.put(r: E.Res(Ana), rest: E.Res(List<&2, Ana>)) -> E.Res(List<&2, Ana>):
  match r rest:
    case Fail{e} _:
      Fail{e}
    case Done{a} Fail{e}:
      Fail{e}
    case Done{a} Done{xs}:
      Done{a <> xs}

# the records of a list of expressions, the first error in list order
def Ana.list(es: List<&2, X.Expr>, +s: List<&2, S.Field>) -> E.Res(List<&2, Ana>):
  match es:
    case Nil{}:
      Done{Nil{}}
    case e <> t:
      Ana.list.put(Expr.analyse(e, s), Ana.list(t, s))

def Ana.any_row(xs: List<&2, Ana>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case a <> t:
      Bool.or(AKind.is_row(Ana.kind(a)), Ana.any_row(t))

def Ana.all_row_safe(xs: List<&2, Ana>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +a <> t:
      Bool.and(Bool.and(AKind.is_row(Ana.kind(a)), Ana.safe(a)), Ana.all_row_safe(t))

def Ana.all_safe(xs: List<&2, Ana>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case a <> t:
      Bool.and(Ana.safe(a), Ana.all_safe(t))

def Ana.rows.k(r: E.Res(List<&2, Ana>)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{xs}:
      Ana.any_row(xs)

# select's height rule (15.4): h when some expression is KRow, else 1 (an
# ill-typed list answers False; its error is reported by the type check)
def Ana.rows(es: List<&2, X.Expr>, +s: List<&2, S.Field>) -> Bool:
  Ana.rows.k(Ana.list(es, s))

def Ana.preserving.k(r: E.Res(List<&2, Ana>)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{Nil{}}:
      False{}
    case Done{+xs}:
      Ana.all_row_safe(xs)

# the height certificate (15.4 rule, P2): the list is non-empty and every
# expression is KRow (it reads a column), total and local. Such a
# Select/WithColumns keeps the input's height and commutes with Head.
def Ana.preserving(es: List<&2, X.Expr>, +s: List<&2, S.Field>) -> Bool:
  Ana.preserving.k(Ana.list(es, s))

def Ana.rowwise.k(row: Bool, r: E.Res(List<&2, Ana>)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{xs}:
      Bool.and(row, Ana.all_safe(xs))

# a Select whose output height is the input's (some KRow) and whose expressions
# are all total and local: a row filter commutes with it
def Ana.rowwise_select(+es: List<&2, X.Expr>, +s: List<&2, S.Field>) -> Bool:
  Ana.rowwise.k(Ana.rows(es, s), Ana.list(es, s))

# the same for WithColumns (its height is always the input's)
def Ana.rowwise_with(es: List<&2, X.Expr>, +s: List<&2, S.Field>) -> Bool:
  Ana.rowwise.k(True{}, Ana.list(es, s))

def Ana.rowwise_total.k(r: E.Res(Ana)) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{a}:
      Ana.safe(a)

# a predicate that is total and local (hence no reduction): evaluating it over a
# superset of its rows (filter merge, pushdown) neither changes its values nor
# can fail
def Ana.rowwise_total(e: X.Expr, +s: List<&2, S.Field>) -> Bool:
  Ana.rowwise_total.k(Expr.analyse(e, s))
