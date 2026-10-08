# PROOF_expr.bend -- proofs of LAWS.bend section 2 (expression typing).
import Base
import ./src/dtype.bend as D
import ./src/err.bend as E
import ./src/kernels.bend as K
import ./src/column.bend as C
import ./src/schema.bend as S
import ./src/expr.bend as X
import ./src/analysis.bend as A
import ./src/sort.bend as O
import ./src/plan.bend as P
import ./LAWS.bend as Laws
import ./PROOF_lib.bend as L

# =====================================================================================
# 2. Expression typing
# =====================================================================================

def Laws.dtype_eq_refl(t):
  match t:
    case D.TBool{}:
      {==}
    case D.TU32{}:
      {==}
    case D.TI32{}:
      {==}
    case D.TF32{}:
      {==}
    case D.TStr{}:
      {==}

def Laws.alias_name(e, n):
  {==}

def Laws.col_name(n):
  {==}

def Laws.alias_type(e, s, n):
  {==}

def Laws.alias_is_agg(e, n):
  {==}

def Laws.agg_is_agg(op, e):
  {==}

def Laws.col_refs(n):
  {==}

def Laws.lit_type(v, s, t, d):
  %Equal.sym(Maybe<&2, D.DType>, D.Scalar.dtype(v), Some{t}, d) : {X.Expr.type.lit(_) == Done{t} : E.Res(D.DType)}
  {==}

def Laws.col_type(n, s, t, f):
  %Equal.sym(Maybe<&2, D.DType>, S.Schema.find(s, n), Some{t}, f) : {X.Expr.type.col(n, _) == Done{t} : E.Res(D.DType)}
  {==}

# a comparison of two equal dtypes checks: DType.eq(t, t) is True
def cmp_ok(op: X.BinOp, +t: D.DType, cmp: {Laws.is_cmp(op) == True{} : Bool}) -> {X.Expr.type.bin.ok(op, t, t) == Done{D.TBool{}} : E.Res(D.DType)}:
  match op:
    case X.Eq{}:
      %Equal.sym(Bool, D.DType.eq(t, t), True{}, Laws.dtype_eq_refl(t)) : {X.Expr.chk(_, E.TypeMismatch{X.BinOp.name(X.Eq{}), D.DType.show(t), D.DType.show(t)}, Done{D.TBool{}}) == Done{D.TBool{}} : E.Res(D.DType)}
      {==}
    case X.Ne{}:
      %Equal.sym(Bool, D.DType.eq(t, t), True{}, Laws.dtype_eq_refl(t)) : {X.Expr.chk(_, E.TypeMismatch{X.BinOp.name(X.Ne{}), D.DType.show(t), D.DType.show(t)}, Done{D.TBool{}}) == Done{D.TBool{}} : E.Res(D.DType)}
      {==}
    case X.Lt{}:
      %Equal.sym(Bool, D.DType.eq(t, t), True{}, Laws.dtype_eq_refl(t)) : {X.Expr.chk(_, E.TypeMismatch{X.BinOp.name(X.Lt{}), D.DType.show(t), D.DType.show(t)}, Done{D.TBool{}}) == Done{D.TBool{}} : E.Res(D.DType)}
      {==}
    case X.Le{}:
      %Equal.sym(Bool, D.DType.eq(t, t), True{}, Laws.dtype_eq_refl(t)) : {X.Expr.chk(_, E.TypeMismatch{X.BinOp.name(X.Le{}), D.DType.show(t), D.DType.show(t)}, Done{D.TBool{}}) == Done{D.TBool{}} : E.Res(D.DType)}
      {==}
    case X.Gt{}:
      %Equal.sym(Bool, D.DType.eq(t, t), True{}, Laws.dtype_eq_refl(t)) : {X.Expr.chk(_, E.TypeMismatch{X.BinOp.name(X.Gt{}), D.DType.show(t), D.DType.show(t)}, Done{D.TBool{}}) == Done{D.TBool{}} : E.Res(D.DType)}
      {==}
    case X.Ge{}:
      %Equal.sym(Bool, D.DType.eq(t, t), True{}, Laws.dtype_eq_refl(t)) : {X.Expr.chk(_, E.TypeMismatch{X.BinOp.name(X.Ge{}), D.DType.show(t), D.DType.show(t)}, Done{D.TBool{}}) == Done{D.TBool{}} : E.Res(D.DType)}
      {==}
    case X.Add{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Add{}, t, t) == Done{D.TBool{}} : E.Res(D.DType)}, L.false_true(cmp))
    case X.Sub{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Sub{}, t, t) == Done{D.TBool{}} : E.Res(D.DType)}, L.false_true(cmp))
    case X.Mul{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Mul{}, t, t) == Done{D.TBool{}} : E.Res(D.DType)}, L.false_true(cmp))
    case X.Div{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Div{}, t, t) == Done{D.TBool{}} : E.Res(D.DType)}, L.false_true(cmp))
    case X.FloorDiv{}:
      Empty.absurd({X.Expr.type.bin.ok(X.FloorDiv{}, t, t) == Done{D.TBool{}} : E.Res(D.DType)}, L.false_true(cmp))
    case X.Mod{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Mod{}, t, t) == Done{D.TBool{}} : E.Res(D.DType)}, L.false_true(cmp))
    case X.And{}:
      Empty.absurd({X.Expr.type.bin.ok(X.And{}, t, t) == Done{D.TBool{}} : E.Res(D.DType)}, L.false_true(cmp))
    case X.Or{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Or{}, t, t) == Done{D.TBool{}} : E.Res(D.DType)}, L.false_true(cmp))

def Laws.cmp_type_bool(op, a, b, s, t, cmp, ta, tb):
  %Equal.sym(E.Res(D.DType), X.Expr.type(a, s), Done{t}, ta) : {X.Expr.type.bin(op, _, X.Expr.type(b, s)) == Done{D.TBool{}} : E.Res(D.DType)}
  %Equal.sym(E.Res(D.DType), X.Expr.type(b, s), Done{t}, tb) : {X.Expr.type.bin(op, Done{t}, _) == Done{D.TBool{}} : E.Res(D.DType)}
  cmp_ok(op, t, cmp)

# arithmetic over one numeric dtype: is_num(t) then DType.eq(t, t) both check
def arith_ok(+name: String, +t: D.DType, num: {X.DType.is_num(t) == True{} : Bool}) -> {X.Expr.type.arith(name, t, t) == Done{t} : E.Res(D.DType)}:
  %Equal.sym(Bool, X.DType.is_num(t), True{}, num) : {X.Expr.chk(_, E.TypeMismatch{name, "numeric", D.DType.show(t)}, X.Expr.chk(D.DType.eq(t, t), E.TypeMismatch{name, D.DType.show(t), D.DType.show(t)}, Done{t})) == Done{t} : E.Res(D.DType)}
  %Equal.sym(Bool, D.DType.eq(t, t), True{}, Laws.dtype_eq_refl(t)) : {X.Expr.chk(_, E.TypeMismatch{name, D.DType.show(t), D.DType.show(t)}, Done{t}) == Done{t} : E.Res(D.DType)}
  {==}

def arith_op_ok(op: X.BinOp, +t: D.DType, ar: {Laws.is_arith(op) == True{} : Bool}, num: {X.DType.is_num(t) == True{} : Bool}) -> {X.Expr.type.bin.ok(op, t, t) == Done{t} : E.Res(D.DType)}:
  match op:
    case X.Add{}:
      arith_ok("add", t, num)
    case X.Sub{}:
      arith_ok("sub", t, num)
    case X.Mul{}:
      arith_ok("mul", t, num)
    case X.Div{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Div{}, t, t) == Done{t} : E.Res(D.DType)}, L.false_true(ar))
    case X.FloorDiv{}:
      Empty.absurd({X.Expr.type.bin.ok(X.FloorDiv{}, t, t) == Done{t} : E.Res(D.DType)}, L.false_true(ar))
    case X.Mod{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Mod{}, t, t) == Done{t} : E.Res(D.DType)}, L.false_true(ar))
    case X.Eq{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Eq{}, t, t) == Done{t} : E.Res(D.DType)}, L.false_true(ar))
    case X.Ne{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Ne{}, t, t) == Done{t} : E.Res(D.DType)}, L.false_true(ar))
    case X.Lt{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Lt{}, t, t) == Done{t} : E.Res(D.DType)}, L.false_true(ar))
    case X.Le{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Le{}, t, t) == Done{t} : E.Res(D.DType)}, L.false_true(ar))
    case X.Gt{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Gt{}, t, t) == Done{t} : E.Res(D.DType)}, L.false_true(ar))
    case X.Ge{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Ge{}, t, t) == Done{t} : E.Res(D.DType)}, L.false_true(ar))
    case X.And{}:
      Empty.absurd({X.Expr.type.bin.ok(X.And{}, t, t) == Done{t} : E.Res(D.DType)}, L.false_true(ar))
    case X.Or{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Or{}, t, t) == Done{t} : E.Res(D.DType)}, L.false_true(ar))

def Laws.arith_type(op, a, b, s, t, ar, num, ta, tb):
  %Equal.sym(E.Res(D.DType), X.Expr.type(a, s), Done{t}, ta) : {X.Expr.type.bin(op, _, X.Expr.type(b, s)) == Done{t} : E.Res(D.DType)}
  %Equal.sym(E.Res(D.DType), X.Expr.type(b, s), Done{t}, tb) : {X.Expr.type.bin(op, Done{t}, _) == Done{t} : E.Res(D.DType)}
  arith_op_ok(op, t, ar, num)

def Laws.mod_type(a, b, s, t, int, ta, tb):
  %Equal.sym(E.Res(D.DType), X.Expr.type(a, s), Done{t}, ta) : {X.Expr.type.bin(X.Mod{}, _, X.Expr.type(b, s)) == Done{t} : E.Res(D.DType)}
  %Equal.sym(E.Res(D.DType), X.Expr.type(b, s), Done{t}, tb) : {X.Expr.type.bin(X.Mod{}, Done{t}, _) == Done{t} : E.Res(D.DType)}
  %Equal.sym(Bool, X.DType.is_int(t), True{}, int) : {X.Expr.chk(_, E.TypeMismatch{"mod", "u32 or i32", D.DType.show(t)}, X.Expr.chk(D.DType.eq(t, t), E.TypeMismatch{"mod", D.DType.show(t), D.DType.show(t)}, Done{t})) == Done{t} : E.Res(D.DType)}
  %Equal.sym(Bool, D.DType.eq(t, t), True{}, Laws.dtype_eq_refl(t)) : {X.Expr.chk(_, E.TypeMismatch{"mod", D.DType.show(t), D.DType.show(t)}, Done{t}) == Done{t} : E.Res(D.DType)}
  {==}

def logic_ok(op: X.BinOp, lg: {Laws.is_logic(op) == True{} : Bool}) -> {X.Expr.type.bin.ok(op, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}:
  match op:
    case X.And{}:
      {==}
    case X.Or{}:
      {==}
    case X.Add{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Add{}, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}, L.false_true(lg))
    case X.Sub{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Sub{}, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}, L.false_true(lg))
    case X.Mul{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Mul{}, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}, L.false_true(lg))
    case X.Div{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Div{}, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}, L.false_true(lg))
    case X.FloorDiv{}:
      Empty.absurd({X.Expr.type.bin.ok(X.FloorDiv{}, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}, L.false_true(lg))
    case X.Mod{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Mod{}, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}, L.false_true(lg))
    case X.Eq{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Eq{}, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}, L.false_true(lg))
    case X.Ne{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Ne{}, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}, L.false_true(lg))
    case X.Lt{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Lt{}, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}, L.false_true(lg))
    case X.Le{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Le{}, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}, L.false_true(lg))
    case X.Gt{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Gt{}, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}, L.false_true(lg))
    case X.Ge{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Ge{}, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}, L.false_true(lg))

def Laws.logic_type(op, a, b, s, lg, ta, tb):
  %Equal.sym(E.Res(D.DType), X.Expr.type(a, s), Done{D.TBool{}}, ta) : {X.Expr.type.bin(op, _, X.Expr.type(b, s)) == Done{D.TBool{}} : E.Res(D.DType)}
  %Equal.sym(E.Res(D.DType), X.Expr.type(b, s), Done{D.TBool{}}, tb) : {X.Expr.type.bin(op, Done{D.TBool{}}, _) == Done{D.TBool{}} : E.Res(D.DType)}
  logic_ok(op, lg)

# the null literal is typed by the target; anything else by the cast table
def cast_ok(nl: Bool, +to: D.DType, +t: D.DType, ok: {X.Cast.ok(t, to) == True{} : Bool}) -> {X.Expr.type.cast(nl, to, Done{t}) == Done{to} : E.Res(D.DType)}:
  match nl:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, X.Cast.ok(t, to), True{}, ok) : {X.Expr.chk(_, E.TypeMismatch{"cast", "castable to " ++ D.DType.show(to), D.DType.show(t)}, Done{to}) == Done{to} : E.Res(D.DType)}
      {==}

def Laws.cast_type(e, s, t, to, ta, ok):
  %Equal.sym(E.Res(D.DType), X.Expr.type(e, s), Done{t}, ta) : {X.Expr.type.cast(X.Expr.is_null_lit(e), to, _) == Done{to} : E.Res(D.DType)}
  cast_ok(X.Expr.is_null_lit(e), to, t, ok)

def Laws.is_null_type(e, s, t, ta):
  %Equal.sym(E.Res(D.DType), X.Expr.type(e, s), Done{t}, ta) : {X.Expr.type.un(X.IsNull{}, _) == Done{D.TBool{}} : E.Res(D.DType)}
  {==}

def Laws.is_not_null_type(e, s, t, ta):
  %Equal.sym(E.Res(D.DType), X.Expr.type(e, s), Done{t}, ta) : {X.Expr.type.un(X.IsNotNull{}, _) == Done{D.TBool{}} : E.Res(D.DType)}
  {==}

def counting_ok(op: X.AggOp, -t: D.DType, cnt: {Laws.is_counting(op) == True{} : Bool}) -> {X.Expr.type.agg.ok(op, t) == Done{D.TU32{}} : E.Res(D.DType)}:
  match op:
    case X.Count{}:
      {==}
    case X.Len{}:
      {==}
    case X.NUnique{}:
      {==}
    case X.Sum{}:
      Empty.absurd({X.Expr.type.agg.ok(X.Sum{}, t) == Done{D.TU32{}} : E.Res(D.DType)}, L.false_true(cnt))
    case X.Mean{}:
      Empty.absurd({X.Expr.type.agg.ok(X.Mean{}, t) == Done{D.TU32{}} : E.Res(D.DType)}, L.false_true(cnt))
    case X.Min{}:
      Empty.absurd({X.Expr.type.agg.ok(X.Min{}, t) == Done{D.TU32{}} : E.Res(D.DType)}, L.false_true(cnt))
    case X.Max{}:
      Empty.absurd({X.Expr.type.agg.ok(X.Max{}, t) == Done{D.TU32{}} : E.Res(D.DType)}, L.false_true(cnt))
    case X.First{}:
      Empty.absurd({X.Expr.type.agg.ok(X.First{}, t) == Done{D.TU32{}} : E.Res(D.DType)}, L.false_true(cnt))
    case X.Last{}:
      Empty.absurd({X.Expr.type.agg.ok(X.Last{}, t) == Done{D.TU32{}} : E.Res(D.DType)}, L.false_true(cnt))

def Laws.counting_type(op, e, s, t, cnt, ta):
  %Equal.sym(E.Res(D.DType), X.Expr.type(e, s), Done{t}, ta) : {X.Expr.type.agg(op, _) == Done{D.TU32{}} : E.Res(D.DType)}
  counting_ok(op, t, cnt)

def keeping_ok(op: X.AggOp, -t: D.DType, kp: {Laws.keeps_dtype(op) == True{} : Bool}) -> {X.Expr.type.agg.ok(op, t) == Done{t} : E.Res(D.DType)}:
  match op:
    case X.Min{}:
      {==}
    case X.Max{}:
      {==}
    case X.First{}:
      {==}
    case X.Last{}:
      {==}
    case X.Sum{}:
      Empty.absurd({X.Expr.type.agg.ok(X.Sum{}, t) == Done{t} : E.Res(D.DType)}, L.false_true(kp))
    case X.Mean{}:
      Empty.absurd({X.Expr.type.agg.ok(X.Mean{}, t) == Done{t} : E.Res(D.DType)}, L.false_true(kp))
    case X.Count{}:
      Empty.absurd({X.Expr.type.agg.ok(X.Count{}, t) == Done{t} : E.Res(D.DType)}, L.false_true(kp))
    case X.Len{}:
      Empty.absurd({X.Expr.type.agg.ok(X.Len{}, t) == Done{t} : E.Res(D.DType)}, L.false_true(kp))
    case X.NUnique{}:
      Empty.absurd({X.Expr.type.agg.ok(X.NUnique{}, t) == Done{t} : E.Res(D.DType)}, L.false_true(kp))

def Laws.keeping_agg_type(op, e, s, t, kp, ta):
  %Equal.sym(E.Res(D.DType), X.Expr.type(e, s), Done{t}, ta) : {X.Expr.type.agg(op, _) == Done{t} : E.Res(D.DType)}
  keeping_ok(op, t, kp)

def Laws.sum_type(e, s, t, num, ta):
  %Equal.sym(E.Res(D.DType), X.Expr.type(e, s), Done{t}, ta) : {X.Expr.type.agg(X.Sum{}, _) == Done{t} : E.Res(D.DType)}
  %Equal.sym(Bool, X.DType.is_num(t), True{}, num) : {X.Expr.chk(_, E.TypeMismatch{"sum", "numeric", D.DType.show(t)}, Done{t}) == Done{t} : E.Res(D.DType)}
  {==}

def Laws.mean_type(e, s, t, num, ta):
  %Equal.sym(E.Res(D.DType), X.Expr.type(e, s), Done{t}, ta) : {X.Expr.type.agg(X.Mean{}, _) == Done{D.TF32{}} : E.Res(D.DType)}
  %Equal.sym(Bool, X.DType.is_num(t), True{}, num) : {X.Expr.chk(_, E.TypeMismatch{"mean", "numeric", D.DType.show(t)}, Done{D.TF32{}}) == Done{D.TF32{}} : E.Res(D.DType)}
  {==}
