# src/expr.bend -- UnOp/BinOp/AggOp/Expr and the data-free analyses over them:
# Expr.name / Expr.type (strict typing) / Expr.refs / Expr.is_agg, plus
# Expr.show and Expr.split_agg. DESIGN.md 4.6.
# Idioms (DESIGN.md section 9): helpers above callers; a recursive def makes
# every recursive call in the argument list of a non-recursive helper above it.
import Base
import ./dtype.bend as D
import ./err.bend as E
import ./schema.bend as S

type UnOp is Data:
  Neg{}
  Not{}
  IsNull{}
  IsNotNull{}
  Abs{}
  Sqrt{}
  LenChars{}

type BinOp is Data:
  Add{}
  Sub{}
  Mul{}
  Div{}
  FloorDiv{}
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
  Std{}
  Var{}
  Median{}

# the literal string predicates (DESIGN.md 15.2.6): case-sensitive, code-point equality
type StrPredOp is Data:
  Contains{}
  StartsWith{}
  EndsWith{}

# which bounds of is_between are inclusive (DF.is_between_closed; sugar, no Expr node)
type Closed is Data:
  Both{}
  Left{}
  Right{}
  Neither{}

type Expr is Data:
  Col{name: String}
  Lit{v: D.Scalar}
  Alias{e: Expr, name: String}
  Cast{e: Expr, to: D.DType}
  TryCast{e: Expr, to: D.DType}
  Un{op: UnOp, e: Expr}
  Bin{op: BinOp, a: Expr, b: Expr}
  FillNull{e: Expr, v: Expr}
  Agg{op: AggOp, e: Expr}
  When{c: Expr, a: Expr, b: Expr}
  IsIn{e: Expr, vals: List<&2, D.Scalar>}
  Clip{e: Expr, lo: D.Scalar, hi: D.Scalar}
  StrPred{op: StrPredOp, e: Expr, pat: String}

# an aggregation at the root of an expression, under at most aliases
type AggSplit is Data:
  AggSplit{op: AggOp, e: Expr}

# ---- op names (lowercase; used in TypeMismatch.op and Expr.show) ------------------

def UnOp.name(op: UnOp) -> String:
  match op:
    case Neg{}:
      "neg"
    case Not{}:
      "not"
    case IsNull{}:
      "is_null"
    case IsNotNull{}:
      "is_not_null"
    case Abs{}:
      "abs"
    case Sqrt{}:
      "sqrt"
    case LenChars{}:
      "len_chars"

def BinOp.name(op: BinOp) -> String:
  match op:
    case Add{}:
      "add"
    case Sub{}:
      "sub"
    case Mul{}:
      "mul"
    case Div{}:
      "div"
    case FloorDiv{}:
      "floor_div"
    case Mod{}:
      "mod"
    case Eq{}:
      "eq"
    case Ne{}:
      "ne"
    case Lt{}:
      "lt"
    case Le{}:
      "le"
    case Gt{}:
      "gt"
    case Ge{}:
      "ge"
    case And{}:
      "and"
    case Or{}:
      "or"

def BinOp.symbol(op: BinOp) -> String:
  match op:
    case Add{}:
      "+"
    case Sub{}:
      "-"
    case Mul{}:
      "*"
    case Div{}:
      "/"
    case FloorDiv{}:
      "//"
    case Mod{}:
      "%"
    case Eq{}:
      "=="
    case Ne{}:
      "!="
    case Lt{}:
      "<"
    case Le{}:
      "<="
    case Gt{}:
      ">"
    case Ge{}:
      ">="
    case And{}:
      "&"
    case Or{}:
      "|"

def AggOp.name(op: AggOp) -> String:
  match op:
    case Sum{}:
      "sum"
    case Mean{}:
      "mean"
    case Min{}:
      "min"
    case Max{}:
      "max"
    case Count{}:
      "count"
    case Len{}:
      "len"
    case First{}:
      "first"
    case Last{}:
      "last"
    case NUnique{}:
      "n_unique"
    case Std{}:
      "std"
    case Var{}:
      "var"
    case Median{}:
      "median"

def StrPredOp.name(op: StrPredOp) -> String:
  match op:
    case Contains{}:
      "contains_literal"
    case StartsWith{}:
      "starts_with"
    case EndsWith{}:
      "ends_with"

# ---- Expr.name / refs / is_agg -----------------------------------------------------

# the leftmost name: an Alias names its subtree, a Col names itself
def Expr.lname(e: Expr) -> Maybe<&2, String>:
  match e:
    case Col{n}:
      Some{n}
    case Lit{v}:
      None{}
    case Alias{e2, n}:
      Some{n}
    case Cast{e2, t}:
      Expr.lname(e2)
    case TryCast{e2, t}:
      Expr.lname(e2)
    case Un{op, e2}:
      Expr.lname(e2)
    case Bin{op, a, b}:
      Maybe.or(&2, String, Expr.lname(a), Expr.lname(b))
    case FillNull{e2, v}:
      Maybe.or(&2, String, Expr.lname(e2), Expr.lname(v))
    case Agg{op, e2}:
      Expr.lname(e2)
    case When{c, a, b}:
      Expr.lname(a)
    case IsIn{e2, vs}:
      Expr.lname(e2)
    case Clip{e2, lo, hi}:
      Expr.lname(e2)
    case StrPred{op, e2, p}:
      Expr.lname(e2)

# the output column name: the Alias name, else the leftmost Col, else "literal"
def Expr.name(e: Expr) -> String:
  Maybe.default(&2, String, Expr.lname(e), "literal")

def Expr.refs.go(e: Expr, acc: List<&2, String>) -> List<&2, String>:
  match e:
    case Col{n}:
      n <> acc
    case Lit{v}:
      acc
    case Alias{e2, n}:
      Expr.refs.go(e2, acc)
    case Cast{e2, t}:
      Expr.refs.go(e2, acc)
    case TryCast{e2, t}:
      Expr.refs.go(e2, acc)
    case Un{op, e2}:
      Expr.refs.go(e2, acc)
    case Bin{op, a, b}:
      Expr.refs.go(a, Expr.refs.go(b, acc))
    case FillNull{e2, v}:
      Expr.refs.go(e2, Expr.refs.go(v, acc))
    case Agg{op, e2}:
      Expr.refs.go(e2, acc)
    case When{c, a, b}:
      Expr.refs.go(c, Expr.refs.go(a, Expr.refs.go(b, acc)))
    case IsIn{e2, vs}:
      Expr.refs.go(e2, acc)
    case Clip{e2, lo, hi}:
      Expr.refs.go(e2, acc)
    case StrPred{op, e2, p}:
      Expr.refs.go(e2, acc)

# the column names an expression reads, left to right, with duplicates
def Expr.refs(e: Expr) -> List<&2, String>:
  Expr.refs.go(e, Nil{})

# does an aggregation occur anywhere in the expression?
def Expr.is_agg(e: Expr) -> Bool:
  match e:
    case Col{n}:
      False{}
    case Lit{v}:
      False{}
    case Alias{e2, n}:
      Expr.is_agg(e2)
    case Cast{e2, t}:
      Expr.is_agg(e2)
    case TryCast{e2, t}:
      Expr.is_agg(e2)
    case Un{op, e2}:
      Expr.is_agg(e2)
    case Bin{op, a, b}:
      Bool.or(Expr.is_agg(a), Expr.is_agg(b))
    case FillNull{e2, v}:
      Bool.or(Expr.is_agg(e2), Expr.is_agg(v))
    case Agg{op, e2}:
      True{}
    case When{c, a, b}:
      Bool.or(Expr.is_agg(c), Bool.or(Expr.is_agg(a), Expr.is_agg(b)))
    case IsIn{e2, vs}:
      Expr.is_agg(e2)
    case Clip{e2, lo, hi}:
      Expr.is_agg(e2)
    case StrPred{op, e2, p}:
      Expr.is_agg(e2)

# `Agg{op, e}` at the root, possibly under Alias nodes (group_by's input form);
# None for anything else. The output name is still Expr.name of the whole.
def Expr.split_agg(e: Expr) -> Maybe<&2, AggSplit>:
  match e:
    case Alias{e2, n}:
      Expr.split_agg(e2)
    case Agg{op, e2}:
      Some{AggSplit{op, e2}}
    case _:
      None{}

# ---- Expr.type: strict typing (DESIGN.md 4.6 table) ----------------------------------

def DType.is_num(t: D.DType) -> Bool:
  match t:
    case D.TU32{}:
      True{}
    case D.TI32{}:
      True{}
    case D.TF32{}:
      True{}
    case _:
      False{}

def DType.is_int(t: D.DType) -> Bool:
  match t:
    case D.TU32{}:
      True{}
    case D.TI32{}:
      True{}
    case _:
      False{}

def DType.is_bool(t: D.DType) -> Bool:
  match t:
    case D.TBool{}:
      True{}
    case _:
      False{}

# the explicit cast table: T->T; U32<->I32; U32/I32/Bool->F32; F32->U32/I32;
# Bool->U32/I32; anything->Str; Str->anything. Which pairs can fail at run time is
# Cast.total (cast errors, try_cast nulls; DESIGN.md 15.5.5)
def Cast.ok(from: D.DType, to: D.DType) -> Bool:
  match from to:
    case D.TBool{} D.TBool{}:
      True{}
    case D.TBool{} _:
      True{}
    case D.TU32{} D.TBool{}:
      False{}
    case D.TU32{} _:
      True{}
    case D.TI32{} D.TBool{}:
      False{}
    case D.TI32{} _:
      True{}
    case D.TF32{} D.TBool{}:
      False{}
    case D.TF32{} _:
      True{}
    case D.TStr{} _:
      True{}

# a pair whose conversion never fails (DESIGN.md 15.5.5): T -> T; u32 / i32 / bool -> f32;
# bool -> u32 / i32; anything -> str. u32 <-> i32, f32 -> u32 / i32 and str -> anything
# else are fallible: cast errors on the first failing valid cell, try_cast nulls it.
def Cast.total(from: D.DType, to: D.DType) -> Bool:
  match from to:
    case _ D.TStr{}:
      True{}
    case D.TBool{} _:
      True{}
    case D.TU32{} D.TU32{}:
      True{}
    case D.TU32{} D.TF32{}:
      True{}
    case D.TI32{} D.TI32{}:
      True{}
    case D.TI32{} D.TF32{}:
      True{}
    case D.TF32{} D.TF32{}:
      True{}
    case _ _:
      False{}

# r when ok, else the error
def Expr.chk(ok: Bool, e: E.Err, r: E.Res(D.DType)) -> E.Res(D.DType):
  match ok:
    case True{}:
      r
    case False{}:
      Fail{e}

def Expr.type.col(n: String, t: Maybe<&2, D.DType>) -> E.Res(D.DType):
  match t:
    case Some{t2}:
      Done{t2}
    case None{}:
      Fail{E.ColumnNotFound{n}}

def Expr.type.lit(t: Maybe<&2, D.DType>) -> E.Res(D.DType):
  match t:
    case Some{t2}:
      Done{t2}
    case None{}:
      Fail{E.TypeMismatch{"lit", "a typed literal", "null"}}

def Expr.is_null_lit(e: Expr) -> Bool:
  match e:
    case Lit{D.SNull{}}:
      True{}
    case _:
      False{}

# Cast{Lit{SNull}, to} is the typed null literal: it has type `to`
def Expr.type.cast(null_lit: Bool, +to: D.DType, r: E.Res(D.DType)) -> E.Res(D.DType):
  match null_lit r:
    case True{} _:
      Done{to}
    case False{} Fail{e}:
      Fail{e}
    case False{} Done{+t}:
      Expr.chk(Cast.ok(t, to), E.TypeMismatch{"cast", "castable to " ++ D.DType.show(to), D.DType.show(t)}, Done{to})

# TryCast: Cast.ok's table under the name "try_cast"; TryCast{Lit{SNull}, to} is a typed null
def Expr.type.trycast(null_lit: Bool, +to: D.DType, r: E.Res(D.DType)) -> E.Res(D.DType):
  match null_lit r:
    case True{} _:
      Done{to}
    case False{} Fail{e}:
      Fail{e}
    case False{} Done{+t}:
      Expr.chk(Cast.ok(t, to), E.TypeMismatch{"try_cast", "castable to " ++ D.DType.show(to), D.DType.show(t)}, Done{to})

def Expr.type.un.ok(op: UnOp, +t: D.DType) -> E.Res(D.DType):
  match op:
    case Neg{}:
      Expr.chk(Bool.or(D.DType.eq(t, D.TI32{}), D.DType.eq(t, D.TF32{})), E.TypeMismatch{"neg", "i32 or f32", D.DType.show(t)}, Done{t})
    case Not{}:
      Expr.chk(DType.is_bool(t), E.TypeMismatch{"not", "bool", D.DType.show(t)}, Done{t})
    case IsNull{}:
      Done{D.TBool{}}
    case IsNotNull{}:
      Done{D.TBool{}}
    case Abs{}:
      Expr.chk(Bool.or(D.DType.eq(t, D.TI32{}), D.DType.eq(t, D.TF32{})), E.TypeMismatch{"abs", "i32 or f32", D.DType.show(t)}, Done{t})
    case Sqrt{}:
      Expr.chk(D.DType.eq(t, D.TF32{}), E.TypeMismatch{"sqrt", "f32", D.DType.show(t)}, Done{t})
    case LenChars{}:
      Expr.chk(D.DType.eq(t, D.TStr{}), E.TypeMismatch{"len_chars", "str", D.DType.show(t)}, Done{D.TU32{}})

def Expr.type.un(op: UnOp, r: E.Res(D.DType)) -> E.Res(D.DType):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      Expr.type.un.ok(op, t)

# arithmetic: a numeric left operand, the same dtype on the right
def Expr.type.arith(+name: String, +a: D.DType, +b: D.DType) -> E.Res(D.DType):
  Expr.chk(DType.is_num(a), E.TypeMismatch{name, "numeric", D.DType.show(a)}, Expr.chk(D.DType.eq(a, b), E.TypeMismatch{name, D.DType.show(a), D.DType.show(b)}, Done{a}))

def Expr.type.bin.ok(op: BinOp, +a: D.DType, +b: D.DType) -> E.Res(D.DType):
  match op:
    case Mod{}:
      Expr.chk(DType.is_int(a), E.TypeMismatch{"mod", "u32 or i32", D.DType.show(a)}, Expr.chk(D.DType.eq(a, b), E.TypeMismatch{"mod", D.DType.show(a), D.DType.show(b)}, Done{a}))
    case Add{}:
      Expr.type.arith("add", a, b)
    case Sub{}:
      Expr.type.arith("sub", a, b)
    case Mul{}:
      Expr.type.arith("mul", a, b)
    case Div{}:
      Expr.chk(D.DType.eq(a, D.TF32{}), E.TypeMismatch{"div", "f32", D.DType.show(a)}, Expr.chk(D.DType.eq(b, D.TF32{}), E.TypeMismatch{"div", "f32", D.DType.show(b)}, Done{D.TF32{}}))
    case FloorDiv{}:
      Expr.chk(DType.is_int(a), E.TypeMismatch{"floor_div", "u32 or i32", D.DType.show(a)}, Expr.chk(D.DType.eq(a, b), E.TypeMismatch{"floor_div", D.DType.show(a), D.DType.show(b)}, Done{a}))
    case And{}:
      Expr.chk(DType.is_bool(a), E.TypeMismatch{"and", "bool", D.DType.show(a)}, Expr.chk(DType.is_bool(b), E.TypeMismatch{"and", "bool", D.DType.show(b)}, Done{D.TBool{}}))
    case Or{}:
      Expr.chk(DType.is_bool(a), E.TypeMismatch{"or", "bool", D.DType.show(a)}, Expr.chk(DType.is_bool(b), E.TypeMismatch{"or", "bool", D.DType.show(b)}, Done{D.TBool{}}))
    case +cmp:
      Expr.chk(D.DType.eq(a, b), E.TypeMismatch{BinOp.name(cmp), D.DType.show(a), D.DType.show(b)}, Done{D.TBool{}})

# the left operand's error wins
def Expr.type.bin(op: BinOp, ra: E.Res(D.DType), rb: E.Res(D.DType)) -> E.Res(D.DType):
  match ra rb:
    case Fail{e} _:
      Fail{e}
    case Done{a} Fail{e}:
      Fail{e}
    case Done{a} Done{b}:
      Expr.type.bin.ok(op, a, b)

def Expr.type.fill(ra: E.Res(D.DType), rb: E.Res(D.DType)) -> E.Res(D.DType):
  match ra rb:
    case Fail{e} _:
      Fail{e}
    case Done{a} Fail{e}:
      Fail{e}
    case Done{+a} Done{+b}:
      Expr.chk(D.DType.eq(a, b), E.TypeMismatch{"fill_null", D.DType.show(a), D.DType.show(b)}, Done{a})

def Expr.type.agg.ok(op: AggOp, +t: D.DType) -> E.Res(D.DType):
  match op:
    case Sum{}:
      Expr.chk(DType.is_num(t), E.TypeMismatch{"sum", "numeric", D.DType.show(t)}, Done{t})
    case Mean{}:
      Expr.chk(DType.is_num(t), E.TypeMismatch{"mean", "numeric", D.DType.show(t)}, Done{D.TF32{}})
    case Min{}:
      Done{t}
    case Max{}:
      Done{t}
    case Count{}:
      Done{D.TU32{}}
    case Len{}:
      Done{D.TU32{}}
    case NUnique{}:
      Done{D.TU32{}}
    case First{}:
      Done{t}
    case Last{}:
      Done{t}
    case Std{}:
      Expr.chk(DType.is_num(t), E.TypeMismatch{"std", "numeric", D.DType.show(t)}, Done{D.TF32{}})
    case Var{}:
      Expr.chk(DType.is_num(t), E.TypeMismatch{"var", "numeric", D.DType.show(t)}, Done{D.TF32{}})
    case Median{}:
      Expr.chk(DType.is_num(t), E.TypeMismatch{"median", "numeric", D.DType.show(t)}, Done{D.TF32{}})

def Expr.type.agg(op: AggOp, r: E.Res(D.DType)) -> E.Res(D.DType):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      Expr.type.agg.ok(op, t)

# when(c).then(a).otherwise(b): c bool, a and b the same dtype (DESIGN.md 15.3.1)
def Expr.type.when.ok(+c: D.DType, +a: D.DType, +b: D.DType) -> E.Res(D.DType):
  Expr.chk(DType.is_bool(c), E.TypeMismatch{"when", "bool", D.DType.show(c)}, Expr.chk(D.DType.eq(a, b), E.TypeMismatch{"when", D.DType.show(a), D.DType.show(b)}, Done{a}))

# the first operand error, left to right (c, then a, then b)
def Expr.type.when(rc: E.Res(D.DType), ra: E.Res(D.DType), rb: E.Res(D.DType)) -> E.Res(D.DType):
  match rc ra rb:
    case Fail{e} _ _:
      Fail{e}
    case Done{c} Fail{e} _:
      Fail{e}
    case Done{c} Done{a} Fail{e}:
      Fail{e}
    case Done{c} Done{a} Done{b}:
      Expr.type.when.ok(c, a, b)

# a literal of dtype t: None when it is, else the TypeMismatch{op, <t>, <its dtype or "null">}
def Expr.lit_of.k(+op: String, +t: D.DType, m: Maybe<&2, D.DType>) -> Maybe<&2, E.Err>:
  match m:
    case None{}:
      Some{E.TypeMismatch{op, D.DType.show(t), "null"}}
    case Some{+u}:
      Bool.pick(Maybe<&2, E.Err>, D.DType.eq(t, u), None{}, Some{E.TypeMismatch{op, D.DType.show(t), D.DType.show(u)}})

def Expr.lit_of(+op: String, +t: D.DType, v: D.Scalar) -> Maybe<&2, E.Err>:
  Expr.lit_of.k(op, t, D.Scalar.dtype(v))

def Expr.or_done(m: Maybe<&2, E.Err>, r: E.Res(D.DType)) -> E.Res(D.DType):
  match m:
    case Some{e}:
      Fail{e}
    case None{}:
      r

# is_in: every scalar of the list has the operand's dtype (the first offending one is
# reported; an SNull is refused as "null"); the result is bool
def Expr.type.isin.ok(vs: List<&2, D.Scalar>, +t: D.DType) -> E.Res(D.DType):
  match vs:
    case Nil{}:
      Done{D.TBool{}}
    case v <> rest:
      Expr.or_done(Expr.lit_of("is_in", t, v), Expr.type.isin.ok(rest, t))

def Expr.type.isin(vs: List<&2, D.Scalar>, r: E.Res(D.DType)) -> E.Res(D.DType):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      Expr.type.isin.ok(vs, t)

# clip: a numeric operand, then lo, then hi of its dtype; the result keeps the dtype
def Expr.type.clip.ok(lo: D.Scalar, hi: D.Scalar, +t: D.DType) -> E.Res(D.DType):
  Expr.chk(DType.is_num(t), E.TypeMismatch{"clip", "numeric", D.DType.show(t)}, Expr.or_done(Expr.lit_of("clip", t, lo), Expr.or_done(Expr.lit_of("clip", t, hi), Done{t})))

def Expr.type.clip(lo: D.Scalar, hi: D.Scalar, r: E.Res(D.DType)) -> E.Res(D.DType):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      Expr.type.clip.ok(lo, hi, t)

# contains_literal / starts_with / ends_with: str -> bool
def Expr.type.strpred.ok(op: StrPredOp, +t: D.DType) -> E.Res(D.DType):
  Expr.chk(D.DType.eq(t, D.TStr{}), E.TypeMismatch{StrPredOp.name(op), "str", D.DType.show(t)}, Done{D.TBool{}})

def Expr.type.strpred(op: StrPredOp, r: E.Res(D.DType)) -> E.Res(D.DType):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{t}:
      Expr.type.strpred.ok(op, t)

# the dtype of an expression over a schema, or the first violated rule
# (TypeMismatch{op, want, got} / ColumnNotFound), left to right
def Expr.type(e: Expr, +s: List<&2, S.Field>) -> E.Res(D.DType):
  match e:
    case Col{+n}:
      Expr.type.col(n, S.Schema.find(s, n))
    case Lit{v}:
      Expr.type.lit(D.Scalar.dtype(v))
    case Alias{e2, n}:
      Expr.type(e2, s)
    case Cast{+e2, to}:
      Expr.type.cast(Expr.is_null_lit(e2), to, Expr.type(e2, s))
    case TryCast{+e2, to}:
      Expr.type.trycast(Expr.is_null_lit(e2), to, Expr.type(e2, s))
    case Un{op, e2}:
      Expr.type.un(op, Expr.type(e2, s))
    case Bin{op, a, b}:
      Expr.type.bin(op, Expr.type(a, s), Expr.type(b, s))
    case FillNull{e2, v}:
      Expr.type.fill(Expr.type(e2, s), Expr.type(v, s))
    case Agg{op, e2}:
      Expr.type.agg(op, Expr.type(e2, s))
    case When{c, a, b}:
      Expr.type.when(Expr.type(c, s), Expr.type(a, s), Expr.type(b, s))
    case IsIn{e2, vs}:
      Expr.type.isin(vs, Expr.type(e2, s))
    case Clip{e2, lo, hi}:
      Expr.type.clip(lo, hi, Expr.type(e2, s))
    case StrPred{op, e2, p}:
      Expr.type.strpred(op, Expr.type(e2, s))

# ---- Expr.show (Polars-like, for explain and tests) ------------------------------------

def Expr.show.lit(v: D.Scalar) -> String:
  match v:
    case D.SStr{s}:
      "\"" ++ s ++ "\""
    case other:
      D.Scalar.show(other)

# literals separated by ", " (is_in's list)
def Expr.show.lits(vs: List<&2, D.Scalar>) -> String:
  match vs:
    case Nil{}:
      ""
    case v <> Nil{}:
      Expr.show.lit(v)
    case v <> rest:
      Expr.show.lit(v) ++ ", " ++ Expr.show.lits(rest)

def Expr.show(e: Expr) -> String:
  match e:
    case Col{n}:
      "col(\"" ++ n ++ "\")"
    case Lit{v}:
      "lit(" ++ Expr.show.lit(v) ++ ")"
    case Alias{e2, n}:
      Expr.show(e2) ++ ".alias(\"" ++ n ++ "\")"
    case Cast{e2, t}:
      Expr.show(e2) ++ ".cast(" ++ D.DType.show(t) ++ ")"
    case TryCast{e2, t}:
      Expr.show(e2) ++ ".try_cast(" ++ D.DType.show(t) ++ ")"

    case Un{LenChars{}, e2}:
      Expr.show(e2) ++ ".str.len_chars()"
    case Un{op, e2}:
      Expr.show(e2) ++ "." ++ UnOp.name(op) ++ "()"
    case Bin{op, a, b}:
      "(" ++ Expr.show(a) ++ " " ++ BinOp.symbol(op) ++ " " ++ Expr.show(b) ++ ")"
    case FillNull{e2, v}:
      Expr.show(e2) ++ ".fill_null(" ++ Expr.show(v) ++ ")"
    case Agg{op, e2}:
      Expr.show(e2) ++ "." ++ AggOp.name(op) ++ "()"
    case When{c, a, b}:
      "when(" ++ Expr.show(c) ++ ").then(" ++ Expr.show(a) ++ ").otherwise(" ++ Expr.show(b) ++ ")"
    case IsIn{e2, vs}:
      Expr.show(e2) ++ ".is_in([" ++ Expr.show.lits(vs) ++ "])"
    case Clip{e2, lo, hi}:
      Expr.show(e2) ++ ".clip(" ++ Expr.show.lit(lo) ++ ", " ++ Expr.show.lit(hi) ++ ")"
    case StrPred{op, e2, p}:
      Expr.show(e2) ++ ".str." ++ StrPredOp.name(op) ++ "(\"" ++ p ++ "\")"
