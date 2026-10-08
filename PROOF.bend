# PROOF.bend -- the proofs of LAWS.bend. Each `law x` there is proven by a
# `def Laws.x` here; the lemmas above it are the proof's own helpers.
#
# Toolkit (DESIGN.md section 8, probes p08/p20): a goal that both sides compute
# to is `{==}`; `%e : P` rewrites the goal with `e : {a == b : T}` (P is the
# goal with `_` marking b, and becomes P with a there), so a hypothesis
# `h : {f(p) == Done{s}}` is flipped with Equal.sym before it replaces f(p);
# `Done` is injective through Equal.cong + Result.default; `Fail == Done` and
# `False == True` are refuted through a motive (Fail/False -> Unit, Done/True
# -> Empty) and Empty.absurd; a value the code computes (a dtype lookup, a
# sub-plan's schema) is passed to a lemma as a PARAMETER and matched there; a
# hypothesis that must be rewritten moves into the goal as a function type
# (`H -> G`), is rewritten there, and is taken back with `h => ...`.
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

# ---- toolkit --------------------------------------------------------------------

# Done is injective: the payload, read back through a default
def done_inj(-A: Data, -xs: A, -ys: A, e: {Done{xs} == Done{ys} : E.Res(A)}) -> {xs == ys : A}:
  Equal.cong(E.Res(A), A, r => Result.default(&2, &2, E.Err, A, r, xs), Done{xs}, Done{ys}, e)

# the motive that refutes Fail == Done
def res_disc(-A: Data, r: E.Res(A)) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{x}:
      Empty

def fail_done(-A: Data, -e: E.Err, -x: A, h: {Fail{e} == Done{x} : E.Res(A)}) -> Empty:
  %h : res_disc(A, _)
  Unit{}

# the motive that refutes False == True
def bool_disc(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def false_true(h: {False{} == True{} : Bool}) -> Empty:
  %h : bool_disc(_)
  Unit{}

# the motive that refutes True == False
def bool_disc_t(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def true_false(h: {True{} == False{} : Bool}) -> Empty:
  %h : bool_disc_t(_)
  Unit{}

# Bool.not(b) == True gives b == False
def not_true(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, false_true(h))
    case False{}:
      {==}

# both True gives Bool.and True
def and_true(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

# Bool.and(a, b) == True gives both
def and_left(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def and_right(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, false_true(h))

# =====================================================================================
# 1. Schema operations
# =====================================================================================

def Laws.project_nil(s):
  {==}

# Schema.project.chk(r) == Done{out} needs r == Done{out}: the duplicate check
# only ever turns a Done into a Fail
def chk_dup_inv(d: Maybe<&2, String>, -fs: List<&2, S.Field>, -out: List<&2, S.Field>, h: {S.Schema.project.dup(d, fs) == Done{out} : E.Res(List<&2, S.Field>)}) -> {Done{fs} == Done{out} : E.Res(List<&2, S.Field>)}:
  match d:
    case Some{n}:
      Empty.absurd({Done{fs} == Done{out} : E.Res(List<&2, S.Field>)}, fail_done(List<&2, S.Field>, E.DuplicateColumn{n}, out, h))
    case None{}:
      h

def chk_inv(r: E.Res(List<&2, S.Field>), -out: List<&2, S.Field>, h: {S.Schema.project.chk(r) == Done{out} : E.Res(List<&2, S.Field>)}) -> {r == Done{out} : E.Res(List<&2, S.Field>)}:
  match r:
    case Fail{e}:
      Empty.absurd({Fail{e} == Done{out} : E.Res(List<&2, S.Field>)}, fail_done(List<&2, S.Field>, e, out, h))
    case Done{+fs}:
      chk_dup_inv(C.Names.dup(S.Schema.names(fs), Nil{}, None{}), fs, out, h)

# one step of Schema.project.go: the head's lookup t and the tail's result r
# are parameters; ih is the induction hypothesis for the tail
def project_step(-n: String, -rest: List<&2, String>, t: Maybe<&2, D.DType>, r: E.Res(List<&2, S.Field>), -out: List<&2, S.Field>,
  ok: {S.Schema.project.put(n, t, r) == Done{out} : E.Res(List<&2, S.Field>)},
  ih: @o: List<&2, S.Field> -> {r == Done{o} : E.Res(List<&2, S.Field>)} -> {List.length(&2, S.Field, o) == List.length(&2, String, rest) : Nat})
  -> {List.length(&2, S.Field, out) == 1n+List.length(&2, String, rest) : Nat}:
  match t r:
    case Some{d} Done{+fs}:
      %done_inj(List<&2, S.Field>, S.Field{n, d} <> fs, out, ok) : {List.length(&2, S.Field, _) == 1n+List.length(&2, String, rest) : Nat}
      %ih(fs, {==}) : {1n+List.length(&2, S.Field, fs) == 1n+_ : Nat}
      {==}
    case Some{d} Fail{e}:
      Empty.absurd({List.length(&2, S.Field, out) == 1n+List.length(&2, String, rest) : Nat}, fail_done(List<&2, S.Field>, e, out, ok))
    case None{} Done{fs}:
      Empty.absurd({List.length(&2, S.Field, out) == 1n+List.length(&2, String, rest) : Nat}, fail_done(List<&2, S.Field>, E.ColumnNotFound{n}, out, ok))
    case None{} Fail{e}:
      Empty.absurd({List.length(&2, S.Field, out) == 1n+List.length(&2, String, rest) : Nat}, fail_done(List<&2, S.Field>, E.ColumnNotFound{n}, out, ok))

def project_go_length(names: List<&2, String>, +s: List<&2, S.Field>, -out: List<&2, S.Field>, ok: {S.Schema.project.go(names, s) == Done{out} : E.Res(List<&2, S.Field>)}) -> {List.length(&2, S.Field, out) == List.length(&2, String, names) : Nat}:
  match names:
    case Nil{}:
      %done_inj(List<&2, S.Field>, Nil{}, out, ok) : {List.length(&2, S.Field, _) == 0n : Nat}
      {==}
    case +n <> +rest:
      project_step(n, rest, S.Schema.find(s, n), S.Schema.project.go(rest, s), out, ok, o => e => project_go_length(rest, s, o, e))

def Laws.project_length(names, s, out, ok):
  project_go_length(names, s, out, chk_inv(S.Schema.project.go(names, s), out, ok))

# the same induction for the names: one field per name, in request order
def names_step(-n: String, -rest: List<&2, String>, t: Maybe<&2, D.DType>, r: E.Res(List<&2, S.Field>), -out: List<&2, S.Field>,
  ok: {S.Schema.project.put(n, t, r) == Done{out} : E.Res(List<&2, S.Field>)},
  ih: @o: List<&2, S.Field> -> {r == Done{o} : E.Res(List<&2, S.Field>)} -> {S.Schema.names(o) == rest : List<&2, String>})
  -> {S.Schema.names(out) == n <> rest : List<&2, String>}:
  match t r:
    case Some{d} Done{+fs}:
      %done_inj(List<&2, S.Field>, S.Field{n, d} <> fs, out, ok) : {S.Schema.names(_) == n <> rest : List<&2, String>}
      %ih(fs, {==}) : {n <> S.Schema.names(fs) == n <> _ : List<&2, String>}
      {==}
    case Some{d} Fail{e}:
      Empty.absurd({S.Schema.names(out) == n <> rest : List<&2, String>}, fail_done(List<&2, S.Field>, e, out, ok))
    case None{} Done{fs}:
      Empty.absurd({S.Schema.names(out) == n <> rest : List<&2, String>}, fail_done(List<&2, S.Field>, E.ColumnNotFound{n}, out, ok))
    case None{} Fail{e}:
      Empty.absurd({S.Schema.names(out) == n <> rest : List<&2, String>}, fail_done(List<&2, S.Field>, E.ColumnNotFound{n}, out, ok))

def project_go_names(names: List<&2, String>, +s: List<&2, S.Field>, -out: List<&2, S.Field>, ok: {S.Schema.project.go(names, s) == Done{out} : E.Res(List<&2, S.Field>)}) -> {S.Schema.names(out) == names : List<&2, String>}:
  match names:
    case Nil{}:
      %done_inj(List<&2, S.Field>, Nil{}, out, ok) : {S.Schema.names(_) == Nil{} : List<&2, String>}
      {==}
    case +n <> +rest:
      names_step(n, rest, S.Schema.find(s, n), S.Schema.project.go(rest, s), out, ok, o => e => project_go_names(rest, s, o, e))

def Laws.project_names(names, s, out, ok):
  project_go_names(names, s, out, chk_inv(S.Schema.project.go(names, s), out, ok))

# replacing in place keeps the length, whatever the hit test says per field
def with_go_length(s: List<&2, S.Field>, -n: String, -f: S.Field) -> {List.length(&2, S.Field, S.Schema.with.go(s, n, f)) == List.length(&2, S.Field, s) : Nat}:
  match s:
    case Nil{}:
      {==}
    case S.Field{k, t} <> rest:
      %with_go_length(rest, n, f) : {1n+List.length(&2, S.Field, S.Schema.with.go(rest, n, f)) == 1n+_ : Nat}
      {==}

def Laws.with_existing_keeps_width(s, n, t, has):
  %Equal.sym(Bool, S.Schema.has(s, n), True{}, has) : {List.length(&2, S.Field, S.Schema.with.fin(_, s, n, S.Field{n, t})) == List.length(&2, S.Field, s) : Nat}
  with_go_length(s, n, S.Field{n, t})

def Laws.with_new_appends(s, n, t, has):
  %Equal.sym(Bool, S.Schema.has(s, n), False{}, has) : {S.Schema.with.fin(_, s, n, S.Field{n, t}) == List.append(&2, S.Field, s, S.Field{n, t} <> Nil{}) : List<&2, S.Field>}
  {==}

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
      Empty.absurd({X.Expr.type.bin.ok(X.Add{}, t, t) == Done{D.TBool{}} : E.Res(D.DType)}, false_true(cmp))
    case X.Sub{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Sub{}, t, t) == Done{D.TBool{}} : E.Res(D.DType)}, false_true(cmp))
    case X.Mul{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Mul{}, t, t) == Done{D.TBool{}} : E.Res(D.DType)}, false_true(cmp))
    case X.Div{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Div{}, t, t) == Done{D.TBool{}} : E.Res(D.DType)}, false_true(cmp))
    case X.FloorDiv{}:
      Empty.absurd({X.Expr.type.bin.ok(X.FloorDiv{}, t, t) == Done{D.TBool{}} : E.Res(D.DType)}, false_true(cmp))
    case X.Mod{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Mod{}, t, t) == Done{D.TBool{}} : E.Res(D.DType)}, false_true(cmp))
    case X.And{}:
      Empty.absurd({X.Expr.type.bin.ok(X.And{}, t, t) == Done{D.TBool{}} : E.Res(D.DType)}, false_true(cmp))
    case X.Or{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Or{}, t, t) == Done{D.TBool{}} : E.Res(D.DType)}, false_true(cmp))

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
      Empty.absurd({X.Expr.type.bin.ok(X.Div{}, t, t) == Done{t} : E.Res(D.DType)}, false_true(ar))
    case X.FloorDiv{}:
      Empty.absurd({X.Expr.type.bin.ok(X.FloorDiv{}, t, t) == Done{t} : E.Res(D.DType)}, false_true(ar))
    case X.Mod{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Mod{}, t, t) == Done{t} : E.Res(D.DType)}, false_true(ar))
    case X.Eq{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Eq{}, t, t) == Done{t} : E.Res(D.DType)}, false_true(ar))
    case X.Ne{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Ne{}, t, t) == Done{t} : E.Res(D.DType)}, false_true(ar))
    case X.Lt{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Lt{}, t, t) == Done{t} : E.Res(D.DType)}, false_true(ar))
    case X.Le{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Le{}, t, t) == Done{t} : E.Res(D.DType)}, false_true(ar))
    case X.Gt{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Gt{}, t, t) == Done{t} : E.Res(D.DType)}, false_true(ar))
    case X.Ge{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Ge{}, t, t) == Done{t} : E.Res(D.DType)}, false_true(ar))
    case X.And{}:
      Empty.absurd({X.Expr.type.bin.ok(X.And{}, t, t) == Done{t} : E.Res(D.DType)}, false_true(ar))
    case X.Or{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Or{}, t, t) == Done{t} : E.Res(D.DType)}, false_true(ar))

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
      Empty.absurd({X.Expr.type.bin.ok(X.Add{}, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}, false_true(lg))
    case X.Sub{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Sub{}, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}, false_true(lg))
    case X.Mul{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Mul{}, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}, false_true(lg))
    case X.Div{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Div{}, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}, false_true(lg))
    case X.FloorDiv{}:
      Empty.absurd({X.Expr.type.bin.ok(X.FloorDiv{}, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}, false_true(lg))
    case X.Mod{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Mod{}, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}, false_true(lg))
    case X.Eq{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Eq{}, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}, false_true(lg))
    case X.Ne{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Ne{}, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}, false_true(lg))
    case X.Lt{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Lt{}, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}, false_true(lg))
    case X.Le{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Le{}, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}, false_true(lg))
    case X.Gt{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Gt{}, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}, false_true(lg))
    case X.Ge{}:
      Empty.absurd({X.Expr.type.bin.ok(X.Ge{}, D.TBool{}, D.TBool{}) == Done{D.TBool{}} : E.Res(D.DType)}, false_true(lg))

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
      Empty.absurd({X.Expr.type.agg.ok(X.Sum{}, t) == Done{D.TU32{}} : E.Res(D.DType)}, false_true(cnt))
    case X.Mean{}:
      Empty.absurd({X.Expr.type.agg.ok(X.Mean{}, t) == Done{D.TU32{}} : E.Res(D.DType)}, false_true(cnt))
    case X.Min{}:
      Empty.absurd({X.Expr.type.agg.ok(X.Min{}, t) == Done{D.TU32{}} : E.Res(D.DType)}, false_true(cnt))
    case X.Max{}:
      Empty.absurd({X.Expr.type.agg.ok(X.Max{}, t) == Done{D.TU32{}} : E.Res(D.DType)}, false_true(cnt))
    case X.First{}:
      Empty.absurd({X.Expr.type.agg.ok(X.First{}, t) == Done{D.TU32{}} : E.Res(D.DType)}, false_true(cnt))
    case X.Last{}:
      Empty.absurd({X.Expr.type.agg.ok(X.Last{}, t) == Done{D.TU32{}} : E.Res(D.DType)}, false_true(cnt))

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
      Empty.absurd({X.Expr.type.agg.ok(X.Sum{}, t) == Done{t} : E.Res(D.DType)}, false_true(kp))
    case X.Mean{}:
      Empty.absurd({X.Expr.type.agg.ok(X.Mean{}, t) == Done{t} : E.Res(D.DType)}, false_true(kp))
    case X.Count{}:
      Empty.absurd({X.Expr.type.agg.ok(X.Count{}, t) == Done{t} : E.Res(D.DType)}, false_true(kp))
    case X.Len{}:
      Empty.absurd({X.Expr.type.agg.ok(X.Len{}, t) == Done{t} : E.Res(D.DType)}, false_true(kp))
    case X.NUnique{}:
      Empty.absurd({X.Expr.type.agg.ok(X.NUnique{}, t) == Done{t} : E.Res(D.DType)}, false_true(kp))

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

# =====================================================================================
# 3. Plan schema inference
# =====================================================================================

def Laws.source_schema(n, s):
  {==}

def Laws.head_keeps_schema(p, n):
  {==}

def Laws.filter_keeps_schema(p, s, e, ok, t):
  %Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(p), Done{s}, ok) : {P.Plan.schema.filter(e, _) == Done{s} : E.Res(List<&2, S.Field>)}
  %Equal.sym(E.Res(D.DType), A.Ana.type(e, s), Done{D.TBool{}}, t) : {P.Plan.schema.filter.k(_, s) == Done{s} : E.Res(List<&2, S.Field>)}
  {==}

# Plan.schema.filter.k(t, s) == Done{out} forces t = bool, out = s
def filter_inv(t: E.Res(D.DType), -s: List<&2, S.Field>, -out: List<&2, S.Field>, h: {P.Plan.schema.filter.k(t, s) == Done{out} : E.Res(List<&2, S.Field>)}) -> {out == s : List<&2, S.Field>}:
  match t:
    case Fail{e}:
      Empty.absurd({out == s : List<&2, S.Field>}, fail_done(List<&2, S.Field>, e, out, h))
    case Done{D.TBool{}}:
      Equal.sym(List<&2, S.Field>, s, out, done_inj(List<&2, S.Field>, s, out, h))
    case Done{D.TU32{}}:
      Empty.absurd({out == s : List<&2, S.Field>}, fail_done(List<&2, S.Field>, E.TypeMismatch{"filter", "bool", "u32"}, out, h))
    case Done{D.TI32{}}:
      Empty.absurd({out == s : List<&2, S.Field>}, fail_done(List<&2, S.Field>, E.TypeMismatch{"filter", "bool", "i32"}, out, h))
    case Done{D.TF32{}}:
      Empty.absurd({out == s : List<&2, S.Field>}, fail_done(List<&2, S.Field>, E.TypeMismatch{"filter", "bool", "f32"}, out, h))
    case Done{D.TStr{}}:
      Empty.absurd({out == s : List<&2, S.Field>}, fail_done(List<&2, S.Field>, E.TypeMismatch{"filter", "bool", "str"}, out, h))

# the hypothesis about Filter{e, p} is rewritten inside the goal (as H -> G)
def filter_is_input(-p: P.Plan, +s: List<&2, S.Field>, +e: X.Expr, -out: List<&2, S.Field>, ok: {P.Plan.schema(p) == Done{s} : E.Res(List<&2, S.Field>)}) -> {P.Plan.schema(P.Filter{e, p}) == Done{out} : E.Res(List<&2, S.Field>)} -> {out == s : List<&2, S.Field>}:
  %Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(p), Done{s}, ok) : {P.Plan.schema.filter(e, _) == Done{out} : E.Res(List<&2, S.Field>)} -> {out == s : List<&2, S.Field>}
  h => filter_inv(A.Ana.type(e, s), s, out, h)

def Laws.filter_schema_is_input(p, s, e, out, ok, h):
  filter_is_input(p, s, e, out, ok)(h)

# keys_exist(ks, s) == True makes Plan.sort.miss(ks, s) == None
def keys_miss(ks: List<&2, O.SortKey>, +s: List<&2, S.Field>, +keys: {Laws.keys_exist(ks, s) == True{} : Bool}) -> {P.Plan.sort.miss(ks, s) == None{} : Maybe<&2, E.Err>}:
  match ks:
    case Nil{}:
      {==}
    case O.SortKey{+n, d, nl} <> +t:
      %Equal.sym(Bool, S.Schema.has(s, n), True{}, and_left(S.Schema.has(s, n), Laws.keys_exist(t, s), keys)) : {P.Plan.sort.miss.k(_, n, P.Plan.sort.miss(t, s)) == None{} : Maybe<&2, E.Err>}
      keys_miss(t, s, and_right(S.Schema.has(s, n), Laws.keys_exist(t, s), keys))

def Laws.sort_keeps_schema(p, s, ks, ok, keys):
  %Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(p), Done{s}, ok) : {P.Plan.schema.sort(ks, _) == Done{s} : E.Res(List<&2, S.Field>)}
  %Equal.sym(Maybe<&2, E.Err>, P.Plan.sort.miss(ks, s), None{}, keys_miss(ks, s, keys)) : {P.Plan.schema.sort.k(_, s) == Done{s} : E.Res(List<&2, S.Field>)}
  {==}

def sort_inv(m: Maybe<&2, E.Err>, -s: List<&2, S.Field>, -out: List<&2, S.Field>, h: {P.Plan.schema.sort.k(m, s) == Done{out} : E.Res(List<&2, S.Field>)}) -> {out == s : List<&2, S.Field>}:
  match m:
    case Some{e}:
      Empty.absurd({out == s : List<&2, S.Field>}, fail_done(List<&2, S.Field>, e, out, h))
    case None{}:
      Equal.sym(List<&2, S.Field>, s, out, done_inj(List<&2, S.Field>, s, out, h))

def sort_is_input(-p: P.Plan, +s: List<&2, S.Field>, +ks: List<&2, O.SortKey>, -out: List<&2, S.Field>, ok: {P.Plan.schema(p) == Done{s} : E.Res(List<&2, S.Field>)}) -> {P.Plan.schema(P.Sort{ks, p}) == Done{out} : E.Res(List<&2, S.Field>)} -> {out == s : List<&2, S.Field>}:
  %Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(p), Done{s}, ok) : {P.Plan.schema.sort(ks, _) == Done{out} : E.Res(List<&2, S.Field>)} -> {out == s : List<&2, S.Field>}
  h => sort_inv(P.Plan.sort.miss(ks, s), s, out, h)

def Laws.sort_schema_is_input(p, s, ks, out, ok, h):
  sort_is_input(p, s, ks, out, ok)(h)

# one Col field of a Select is one step of Schema.project.go: the lookup t
# and the tail r are parameters
def fields_cols_step(-n: String, t: Maybe<&2, D.DType>, r: E.Res(List<&2, S.Field>)) -> {P.Plan.fields.put(P.Plan.field.k(A.Ana.type.k(A.Ana.col(n, t)), n), r) == S.Schema.project.put(n, t, r) : E.Res(List<&2, S.Field>)}:
  match t r:
    case None{} Fail{e}:
      {==}
    case None{} Done{fs}:
      {==}
    case Some{d} Fail{e}:
      {==}
    case Some{d} Done{fs}:
      {==}

def fields_cols(names: List<&2, String>, +s: List<&2, S.Field>) -> {P.Plan.fields(Laws.cols(names), s) == S.Schema.project.go(names, s) : E.Res(List<&2, S.Field>)}:
  match names:
    case Nil{}:
      {==}
    case +n <> +rest:
      %fields_cols(rest, s) : {P.Plan.fields.put(P.Plan.field(X.Col{n}, s), P.Plan.fields(Laws.cols(rest), s)) == S.Schema.project.put(n, S.Schema.find(s, n), _) : E.Res(List<&2, S.Field>)}
      fields_cols_step(n, S.Schema.find(s, n), P.Plan.fields(Laws.cols(rest), s))

def Laws.select_cols_is_project(p, s, names, ok):
  %Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(p), Done{s}, ok) : {P.Plan.schema.select(Laws.cols(names), _) == S.Schema.project(names, s) : E.Res(List<&2, S.Field>)}
  %fields_cols(names, s) : {S.Schema.project.chk(P.Plan.fields(Laws.cols(names), s)) == S.Schema.project.chk(_) : E.Res(List<&2, S.Field>)}
  {==}

def Laws.select_cols_names(p, s, names, out, ok, h):
  Laws.project_names(names, s, out, Equal.trans(E.Res(List<&2, S.Field>), S.Schema.project(names, s), P.Plan.schema(P.Select{Laws.cols(names), p}), Done{out}, Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(P.Select{Laws.cols(names), p}), S.Schema.project(names, s), Laws.select_cols_is_project(p, s, names, ok)), h))

# with_columns of one field whose name s has: the hit test is rewritten to
# True inside the goal, then the in-place replacement keeps the length
def wc_has(+n: String, -d: D.DType, +s: List<&2, S.Field>, -out: List<&2, S.Field>, has: {S.Schema.has(s, n) == True{} : Bool}) -> {Done{S.Schema.with.fin(S.Schema.has(s, n), s, n, S.Field{n, d})} == Done{out} : E.Res(List<&2, S.Field>)} -> {List.length(&2, S.Field, out) == List.length(&2, S.Field, s) : Nat}:
  %Equal.sym(Bool, S.Schema.has(s, n), True{}, has) : {Done{S.Schema.with.fin(_, s, n, S.Field{n, d})} == Done{out} : E.Res(List<&2, S.Field>)} -> {List.length(&2, S.Field, out) == List.length(&2, S.Field, s) : Nat}
  h =>
    %done_inj(List<&2, S.Field>, S.Schema.with.go(s, n, S.Field{n, d}), out, h) : {List.length(&2, S.Field, _) == List.length(&2, S.Field, s) : Nat}
    with_go_length(s, n, S.Field{n, d})

# the typed field of the one expression: t its type (the shared analysis)
def wc_inv(t: E.Res(D.DType), +n: String, +s: List<&2, S.Field>, -out: List<&2, S.Field>, has: {S.Schema.has(s, n) == True{} : Bool},
  h: {P.Plan.schema.wc.k(S.Schema.project.chk(P.Plan.fields.put(P.Plan.field.k(t, n), Done{Nil{}})), s) == Done{out} : E.Res(List<&2, S.Field>)})
  -> {List.length(&2, S.Field, out) == List.length(&2, S.Field, s) : Nat}:
  match t:
    case Fail{e}:
      Empty.absurd({List.length(&2, S.Field, out) == List.length(&2, S.Field, s) : Nat}, fail_done(List<&2, S.Field>, e, out, h))
    case Done{d}:
      wc_has(n, d, s, out, has)(h)

def wc_width(-p: P.Plan, +s: List<&2, S.Field>, +e: X.Expr, -out: List<&2, S.Field>, ok: {P.Plan.schema(p) == Done{s} : E.Res(List<&2, S.Field>)}, has: {S.Schema.has(s, X.Expr.name(e)) == True{} : Bool}) -> {P.Plan.schema(P.WithColumns{e <> Nil{}, p}) == Done{out} : E.Res(List<&2, S.Field>)} -> {List.length(&2, S.Field, out) == List.length(&2, S.Field, s) : Nat}:
  %Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(p), Done{s}, ok) : {P.Plan.schema.wc(e <> Nil{}, _) == Done{out} : E.Res(List<&2, S.Field>)} -> {List.length(&2, S.Field, out) == List.length(&2, S.Field, s) : Nat}
  h => wc_inv(A.Ana.type(e, s), X.Expr.name(e), s, out, has, h)

def Laws.with_column_keeps_width(p, s, e, out, ok, has, h):
  wc_width(p, s, e, out, ok, has)(h)

# =====================================================================================
# 4. Optimizer passes
# =====================================================================================

# a pending Head over x has x's schema
def hwrap_schema(n: Maybe<&2, U32>, -x: P.Plan) -> {P.Plan.schema(P.Opt.hwrap(n, x)) == P.Plan.schema(x) : E.Res(List<&2, S.Field>)}:
  match n:
    case None{}:
      {==}
    case Some{k}:
      {==}

def Laws.head_pass_keeps_schema(p, n):
  match p:
    case P.ScanCsv{path, o, s}:
      hwrap_schema(n, P.ScanCsv{path, o, s})
    case P.Source{nm, s}:
      hwrap_schema(n, P.Source{nm, s})
    case P.Select{+es, +x}:
      %Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(P.Opt.hwrap(P.Opt.hstop(P.Opt.sinks(es, P.Plan.schema(x)), n), P.Select{es, P.Opt.head(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n))})), P.Plan.schema(P.Select{es, P.Opt.head(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n))}), hwrap_schema(P.Opt.hstop(P.Opt.sinks(es, P.Plan.schema(x)), n), P.Select{es, P.Opt.head(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n))})) : {_ == P.Plan.schema.select(es, P.Plan.schema(x)) : E.Res(List<&2, S.Field>)}
      %Laws.head_pass_keeps_schema(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n)) : {P.Plan.schema.select(es, P.Plan.schema(P.Opt.head(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n)))) == P.Plan.schema.select(es, _) : E.Res(List<&2, S.Field>)}
      {==}
    case P.WithColumns{+es, +x}:
      %Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(P.Opt.hwrap(P.Opt.hstop(P.Opt.sinks(es, P.Plan.schema(x)), n), P.WithColumns{es, P.Opt.head(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n))})), P.Plan.schema(P.WithColumns{es, P.Opt.head(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n))}), hwrap_schema(P.Opt.hstop(P.Opt.sinks(es, P.Plan.schema(x)), n), P.WithColumns{es, P.Opt.head(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n))})) : {_ == P.Plan.schema.wc(es, P.Plan.schema(x)) : E.Res(List<&2, S.Field>)}
      %Laws.head_pass_keeps_schema(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n)) : {P.Plan.schema.wc(es, P.Plan.schema(P.Opt.head(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n)))) == P.Plan.schema.wc(es, _) : E.Res(List<&2, S.Field>)}
      {==}
    case P.Filter{e, +x}:
      %Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(P.Opt.hwrap(n, P.Filter{e, P.Opt.head(x, None{})})), P.Plan.schema(P.Filter{e, P.Opt.head(x, None{})}), hwrap_schema(n, P.Filter{e, P.Opt.head(x, None{})})) : {_ == P.Plan.schema.filter(e, P.Plan.schema(x)) : E.Res(List<&2, S.Field>)}
      %Laws.head_pass_keeps_schema(x, None{}) : {P.Plan.schema.filter(e, P.Plan.schema(P.Opt.head(x, None{}))) == P.Plan.schema.filter(e, _) : E.Res(List<&2, S.Field>)}
      {==}
    case P.Sort{ks, +x}:
      %Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(P.Opt.hwrap(n, P.Sort{ks, P.Opt.head(x, None{})})), P.Plan.schema(P.Sort{ks, P.Opt.head(x, None{})}), hwrap_schema(n, P.Sort{ks, P.Opt.head(x, None{})})) : {_ == P.Plan.schema.sort(ks, P.Plan.schema(x)) : E.Res(List<&2, S.Field>)}
      %Laws.head_pass_keeps_schema(x, None{}) : {P.Plan.schema.sort(ks, P.Plan.schema(P.Opt.head(x, None{}))) == P.Plan.schema.sort(ks, _) : E.Res(List<&2, S.Field>)}
      {==}
    case P.GroupBy{ks, ags, mo, +x}:
      %Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(P.Opt.hwrap(n, P.GroupBy{ks, ags, mo, P.Opt.head(x, None{})})), P.Plan.schema(P.GroupBy{ks, ags, mo, P.Opt.head(x, None{})}), hwrap_schema(n, P.GroupBy{ks, ags, mo, P.Opt.head(x, None{})})) : {_ == P.Plan.schema.gb(ks, ags, P.Plan.schema(x)) : E.Res(List<&2, S.Field>)}
      %Laws.head_pass_keeps_schema(x, None{}) : {P.Plan.schema.gb(ks, ags, P.Plan.schema(P.Opt.head(x, None{}))) == P.Plan.schema.gb(ks, ags, _) : E.Res(List<&2, S.Field>)}
      {==}
    case P.Join{how, lo, ro, +l, +r}:
      %Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(P.Opt.hwrap(n, P.Join{how, lo, ro, P.Opt.head(l, None{}), P.Opt.head(r, None{})})), P.Plan.schema(P.Join{how, lo, ro, P.Opt.head(l, None{}), P.Opt.head(r, None{})}), hwrap_schema(n, P.Join{how, lo, ro, P.Opt.head(l, None{}), P.Opt.head(r, None{})})) : {_ == P.Plan.schema.join(lo, ro, P.Plan.schema(l), P.Plan.schema(r)) : E.Res(List<&2, S.Field>)}
      %Laws.head_pass_keeps_schema(l, None{}) : {P.Plan.schema.join(lo, ro, P.Plan.schema(P.Opt.head(l, None{})), P.Plan.schema(P.Opt.head(r, None{}))) == P.Plan.schema.join(lo, ro, _, P.Plan.schema(r)) : E.Res(List<&2, S.Field>)}
      %Laws.head_pass_keeps_schema(r, None{}) : {P.Plan.schema.join(lo, ro, P.Plan.schema(P.Opt.head(l, None{})), P.Plan.schema(P.Opt.head(r, None{}))) == P.Plan.schema.join(lo, ro, P.Plan.schema(P.Opt.head(l, None{})), _) : E.Res(List<&2, S.Field>)}
      {==}
    case P.Head{m, x}:
      Laws.head_pass_keeps_schema(x, Some{P.Opt.hmin(m, n)})

# a schema rule f over its input's result: a Fail passes through, so a Done
# output has a Done input; when the rewritten input resolves to the same
# schema (ih), so does the output
def unary(-f: E.Res(List<&2, S.Field>) -> E.Res(List<&2, S.Field>), fails: @e: E.Err -> {f(Fail{e}) == Fail{e} : E.Res(List<&2, S.Field>)}, r1: E.Res(List<&2, S.Field>), -r2: E.Res(List<&2, S.Field>), -s: List<&2, S.Field>,
  h: {f(r1) == Done{s} : E.Res(List<&2, S.Field>)},
  ih: @o: List<&2, S.Field> -> {r1 == Done{o} : E.Res(List<&2, S.Field>)} -> {r2 == Done{o} : E.Res(List<&2, S.Field>)})
  -> {f(r2) == Done{s} : E.Res(List<&2, S.Field>)}:
  match r1:
    case Fail{e}:
      Empty.absurd({f(r2) == Done{s} : E.Res(List<&2, S.Field>)}, fail_done(List<&2, S.Field>, e, s, Equal.trans(E.Res(List<&2, S.Field>), Fail{e}, f(Fail{e}), Done{s}, Equal.sym(E.Res(List<&2, S.Field>), f(Fail{e}), Fail{e}, fails(e)), h)))
    case Done{s1}:
      %Equal.sym(E.Res(List<&2, S.Field>), r2, Done{s1}, ih(s1, {==})) : {f(_) == Done{s} : E.Res(List<&2, S.Field>)}
      h

# the join rule over both inputs
def binary(lo: List<&2, String>, ro: List<&2, String>, rl: E.Res(List<&2, S.Field>), rr: E.Res(List<&2, S.Field>), -rl2: E.Res(List<&2, S.Field>), -rr2: E.Res(List<&2, S.Field>), -s: List<&2, S.Field>,
  h: {P.Plan.schema.join(lo, ro, rl, rr) == Done{s} : E.Res(List<&2, S.Field>)},
  ihl: @o: List<&2, S.Field> -> {rl == Done{o} : E.Res(List<&2, S.Field>)} -> {rl2 == Done{o} : E.Res(List<&2, S.Field>)},
  ihr: @o: List<&2, S.Field> -> {rr == Done{o} : E.Res(List<&2, S.Field>)} -> {rr2 == Done{o} : E.Res(List<&2, S.Field>)})
  -> {P.Plan.schema.join(lo, ro, rl2, rr2) == Done{s} : E.Res(List<&2, S.Field>)}:
  match rl rr:
    case Fail{e} _:
      Empty.absurd({P.Plan.schema.join(lo, ro, rl2, rr2) == Done{s} : E.Res(List<&2, S.Field>)}, fail_done(List<&2, S.Field>, e, s, h))
    case Done{a} Fail{e}:
      Empty.absurd({P.Plan.schema.join(lo, ro, rl2, rr2) == Done{s} : E.Res(List<&2, S.Field>)}, fail_done(List<&2, S.Field>, e, s, h))
    case Done{a} Done{b}:
      %Equal.sym(E.Res(List<&2, S.Field>), rl2, Done{a}, ihl(a, {==})) : {P.Plan.schema.join(lo, ro, _, rr2) == Done{s} : E.Res(List<&2, S.Field>)}
      %Equal.sym(E.Res(List<&2, S.Field>), rr2, Done{b}, ihr(b, {==})) : {P.Plan.schema.join(lo, ro, Done{a}, _) == Done{s} : E.Res(List<&2, S.Field>)}
      h

# a bool e over s0 after a bool q (its record rs, k, tot, loc): `q & e` is bool
# over s0 too. re is e's analysis.
def and_e(re: E.Res(A.Ana), -rs: List<&2, String>, -k: A.AKind, -tot: Bool, -loc: Bool, -s0: List<&2, S.Field>, -s: List<&2, S.Field>, h: {P.Plan.schema.filter.k(A.Ana.type.k(re), s0) == Done{s} : E.Res(List<&2, S.Field>)}) -> {P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, Done{A.Ana{D.TBool{}, rs, k, tot, loc}}, re)), s0) == Done{s} : E.Res(List<&2, S.Field>)}:
  match re:
    case Fail{e}:
      Empty.absurd({P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, Done{A.Ana{D.TBool{}, rs, k, tot, loc}}, Fail{e})), s0) == Done{s} : E.Res(List<&2, S.Field>)}, fail_done(List<&2, S.Field>, e, s, h))
    case Done{A.Ana{D.TBool{}, rs2, k2, tot2, loc2}}:
      h
    case Done{A.Ana{D.TU32{}, rs2, k2, tot2, loc2}}:
      Empty.absurd({P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, Done{A.Ana{D.TBool{}, rs, k, tot, loc}}, Done{A.Ana{D.TU32{}, rs2, k2, tot2, loc2}})), s0) == Done{s} : E.Res(List<&2, S.Field>)}, fail_done(List<&2, S.Field>, E.TypeMismatch{"filter", "bool", "u32"}, s, h))
    case Done{A.Ana{D.TI32{}, rs2, k2, tot2, loc2}}:
      Empty.absurd({P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, Done{A.Ana{D.TBool{}, rs, k, tot, loc}}, Done{A.Ana{D.TI32{}, rs2, k2, tot2, loc2}})), s0) == Done{s} : E.Res(List<&2, S.Field>)}, fail_done(List<&2, S.Field>, E.TypeMismatch{"filter", "bool", "i32"}, s, h))
    case Done{A.Ana{D.TF32{}, rs2, k2, tot2, loc2}}:
      Empty.absurd({P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, Done{A.Ana{D.TBool{}, rs, k, tot, loc}}, Done{A.Ana{D.TF32{}, rs2, k2, tot2, loc2}})), s0) == Done{s} : E.Res(List<&2, S.Field>)}, fail_done(List<&2, S.Field>, E.TypeMismatch{"filter", "bool", "f32"}, s, h))
    case Done{A.Ana{D.TStr{}, rs2, k2, tot2, loc2}}:
      Empty.absurd({P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, Done{A.Ana{D.TBool{}, rs, k, tot, loc}}, Done{A.Ana{D.TStr{}, rs2, k2, tot2, loc2}})), s0) == Done{s} : E.Res(List<&2, S.Field>)}, fail_done(List<&2, S.Field>, E.TypeMismatch{"filter", "bool", "str"}, s, h))

# the inner filter q over s0 resolved to s1 (h1); the outer e over s1 to s (H).
# rq is q's analysis over s0.
def and_q(rq: E.Res(A.Ana), +s0: List<&2, S.Field>, -s1: List<&2, S.Field>, -s: List<&2, S.Field>, +e: X.Expr, h1: {P.Plan.schema.filter.k(A.Ana.type.k(rq), s0) == Done{s1} : E.Res(List<&2, S.Field>)})
  -> {P.Plan.schema.filter.k(A.Ana.type.k(A.Expr.analyse(e, s1)), s1) == Done{s} : E.Res(List<&2, S.Field>)} -> {P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, rq, A.Expr.analyse(e, s0))), s0) == Done{s} : E.Res(List<&2, S.Field>)}:
  match rq:
    case Fail{err}:
      Empty.absurd({P.Plan.schema.filter.k(A.Ana.type.k(A.Expr.analyse(e, s1)), s1) == Done{s} : E.Res(List<&2, S.Field>)} -> {P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, Fail{err}, A.Expr.analyse(e, s0))), s0) == Done{s} : E.Res(List<&2, S.Field>)}, fail_done(List<&2, S.Field>, err, s1, h1))
    case Done{A.Ana{D.TBool{}, rs, k, tot, loc}}:
      %done_inj(List<&2, S.Field>, s0, s1, h1) : {P.Plan.schema.filter.k(A.Ana.type.k(A.Expr.analyse(e, _)), _) == Done{s} : E.Res(List<&2, S.Field>)} -> {P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, Done{A.Ana{D.TBool{}, rs, k, tot, loc}}, A.Expr.analyse(e, s0))), s0) == Done{s} : E.Res(List<&2, S.Field>)}
      h => and_e(A.Expr.analyse(e, s0), rs, k, tot, loc, s0, s, h)
    case Done{A.Ana{D.TU32{}, rs, k, tot, loc}}:
      Empty.absurd({P.Plan.schema.filter.k(A.Ana.type.k(A.Expr.analyse(e, s1)), s1) == Done{s} : E.Res(List<&2, S.Field>)} -> {P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, Done{A.Ana{D.TU32{}, rs, k, tot, loc}}, A.Expr.analyse(e, s0))), s0) == Done{s} : E.Res(List<&2, S.Field>)}, fail_done(List<&2, S.Field>, E.TypeMismatch{"filter", "bool", "u32"}, s1, h1))
    case Done{A.Ana{D.TI32{}, rs, k, tot, loc}}:
      Empty.absurd({P.Plan.schema.filter.k(A.Ana.type.k(A.Expr.analyse(e, s1)), s1) == Done{s} : E.Res(List<&2, S.Field>)} -> {P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, Done{A.Ana{D.TI32{}, rs, k, tot, loc}}, A.Expr.analyse(e, s0))), s0) == Done{s} : E.Res(List<&2, S.Field>)}, fail_done(List<&2, S.Field>, E.TypeMismatch{"filter", "bool", "i32"}, s1, h1))
    case Done{A.Ana{D.TF32{}, rs, k, tot, loc}}:
      Empty.absurd({P.Plan.schema.filter.k(A.Ana.type.k(A.Expr.analyse(e, s1)), s1) == Done{s} : E.Res(List<&2, S.Field>)} -> {P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, Done{A.Ana{D.TF32{}, rs, k, tot, loc}}, A.Expr.analyse(e, s0))), s0) == Done{s} : E.Res(List<&2, S.Field>)}, fail_done(List<&2, S.Field>, E.TypeMismatch{"filter", "bool", "f32"}, s1, h1))
    case Done{A.Ana{D.TStr{}, rs, k, tot, loc}}:
      Empty.absurd({P.Plan.schema.filter.k(A.Ana.type.k(A.Expr.analyse(e, s1)), s1) == Done{s} : E.Res(List<&2, S.Field>)} -> {P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, Done{A.Ana{D.TStr{}, rs, k, tot, loc}}, A.Expr.analyse(e, s0))), s0) == Done{s} : E.Res(List<&2, S.Field>)}, fail_done(List<&2, S.Field>, E.TypeMismatch{"filter", "bool", "str"}, s1, h1))

# Filter{e, Filter{q, z}} resolving to s makes Filter{q & e, z} resolve to s;
# r is z's schema
def and_filter(+q: X.Expr, +e: X.Expr, r: E.Res(List<&2, S.Field>), -s1: List<&2, S.Field>, -s: List<&2, S.Field>,
  h1: {P.Plan.schema.filter(q, r) == Done{s1} : E.Res(List<&2, S.Field>)},
  h: {P.Plan.schema.filter(e, Done{s1}) == Done{s} : E.Res(List<&2, S.Field>)})
  -> {P.Plan.schema.filter(X.Bin{X.And{}, q, e}, r) == Done{s} : E.Res(List<&2, S.Field>)}:
  match r:
    case Fail{err}:
      Empty.absurd({P.Plan.schema.filter(X.Bin{X.And{}, q, e}, Fail{err}) == Done{s} : E.Res(List<&2, S.Field>)}, fail_done(List<&2, S.Field>, err, s1, h1))
    case Done{+s0}:
      and_q(A.Expr.analyse(q, s0), s0, s1, s, e, h1)(h)

# Filter{e, y} resolves to s when y resolves to s1 and e over s1 to s
def filter_over(+e: X.Expr, -y: P.Plan, -s1: List<&2, S.Field>, -s: List<&2, S.Field>, iy: {P.Plan.schema(y) == Done{s1} : E.Res(List<&2, S.Field>)}, h: {P.Plan.schema.filter(e, Done{s1}) == Done{s} : E.Res(List<&2, S.Field>)}) -> {P.Plan.schema(P.Filter{e, y}) == Done{s} : E.Res(List<&2, S.Field>)}:
  %Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(y), Done{s1}, iy) : {P.Plan.schema.filter(e, _) == Done{s} : E.Res(List<&2, S.Field>)}
  h

# Opt.merge.f(e, y) where y is the merged input: r1 is the unmerged input's
# schema, ih says the merged input y resolves to whatever r1 resolved to
def filter_merge(+e: X.Expr, r1: E.Res(List<&2, S.Field>), y: P.Plan, -s: List<&2, S.Field>,
  h: {P.Plan.schema.filter(e, r1) == Done{s} : E.Res(List<&2, S.Field>)},
  ih: @o: List<&2, S.Field> -> {r1 == Done{o} : E.Res(List<&2, S.Field>)} -> {P.Plan.schema(y) == Done{o} : E.Res(List<&2, S.Field>)})
  -> {P.Plan.schema(P.Opt.merge.f(e, y)) == Done{s} : E.Res(List<&2, S.Field>)}:
  match r1 y:
    case Fail{err} _:
      Empty.absurd({P.Plan.schema(P.Opt.merge.f(e, y)) == Done{s} : E.Res(List<&2, S.Field>)}, fail_done(List<&2, S.Field>, err, s, h))
    case Done{s1} P.Filter{q, z}:
      and_filter(q, e, P.Plan.schema(z), s1, s, ih(s1, {==}), h)
    case Done{s1} P.ScanCsv{path, o, sc}:
      filter_over(e, P.ScanCsv{path, o, sc}, s1, s, ih(s1, {==}), h)
    case Done{s1} P.Source{nm, sc}:
      filter_over(e, P.Source{nm, sc}, s1, s, ih(s1, {==}), h)
    case Done{s1} P.Select{es, x}:
      filter_over(e, P.Select{es, x}, s1, s, ih(s1, {==}), h)
    case Done{s1} P.WithColumns{es, x}:
      filter_over(e, P.WithColumns{es, x}, s1, s, ih(s1, {==}), h)
    case Done{s1} P.Sort{ks, x}:
      filter_over(e, P.Sort{ks, x}, s1, s, ih(s1, {==}), h)
    case Done{s1} P.GroupBy{ks, ags, mo, x}:
      filter_over(e, P.GroupBy{ks, ags, mo, x}, s1, s, ih(s1, {==}), h)
    case Done{s1} P.Join{how, lo, ro, l, r}:
      filter_over(e, P.Join{how, lo, ro, l, r}, s1, s, ih(s1, {==}), h)
    case Done{s1} P.Head{m, x}:
      filter_over(e, P.Head{m, x}, s1, s, ih(s1, {==}), h)

def Laws.merge_pass_keeps_schema(p, s, ok):
  match p:
    case P.ScanCsv{path, o, sc}:
      ok
    case P.Source{nm, sc}:
      ok
    case P.Select{+es, +x}:
      unary(r => P.Plan.schema.select(es, r), e => {==}, P.Plan.schema(x), P.Plan.schema(P.Opt.merge(x)), s, ok, o => h => Laws.merge_pass_keeps_schema(x, o, h))
    case P.WithColumns{+es, +x}:
      unary(r => P.Plan.schema.wc(es, r), e => {==}, P.Plan.schema(x), P.Plan.schema(P.Opt.merge(x)), s, ok, o => h => Laws.merge_pass_keeps_schema(x, o, h))
    case P.Filter{+e, +x}:
      filter_merge(e, P.Plan.schema(x), P.Opt.merge(x), s, ok, o => h => Laws.merge_pass_keeps_schema(x, o, h))
    case P.Sort{+ks, +x}:
      unary(r => P.Plan.schema.sort(ks, r), e => {==}, P.Plan.schema(x), P.Plan.schema(P.Opt.merge(x)), s, ok, o => h => Laws.merge_pass_keeps_schema(x, o, h))
    case P.GroupBy{+ks, +ags, mo, +x}:
      unary(r => P.Plan.schema.gb(ks, ags, r), e => {==}, P.Plan.schema(x), P.Plan.schema(P.Opt.merge(x)), s, ok, o => h => Laws.merge_pass_keeps_schema(x, o, h))
    case P.Join{how, +lo, +ro, +l, +r}:
      binary(lo, ro, P.Plan.schema(l), P.Plan.schema(r), P.Plan.schema(P.Opt.merge(l)), P.Plan.schema(P.Opt.merge(r)), s, ok, o => h => Laws.merge_pass_keeps_schema(l, o, h), o => h => Laws.merge_pass_keeps_schema(r, o, h))
    case P.Head{m, x}:
      Laws.merge_pass_keeps_schema(x, s, ok)

def Laws.merge_head_keeps_schema(p, s, n, ok):
  %Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(P.Opt.head(P.Opt.merge(p), n)), P.Plan.schema(P.Opt.merge(p)), Laws.head_pass_keeps_schema(P.Opt.merge(p), n)) : {_ == Done{s} : E.Res(List<&2, S.Field>)}
  Laws.merge_pass_keeps_schema(p, s, ok)

# Opt.merge.f keeps "no adjacent filters": absorbing e into a Filter below
# leaves that Filter's input alone; over anything else it adds one Filter
def mergef_naf(-e: X.Expr, y: P.Plan, h: {Laws.no_adjacent_filters(y) == True{} : Bool}) -> {Laws.no_adjacent_filters(P.Opt.merge.f(e, y)) == True{} : Bool}:
  match y:
    case P.Filter{q, z}:
      h
    case P.ScanCsv{path, o, sc}:
      h
    case P.Source{nm, sc}:
      h
    case P.Select{es, x}:
      h
    case P.WithColumns{es, x}:
      h
    case P.Sort{ks, x}:
      h
    case P.GroupBy{ks, ags, mo, x}:
      h
    case P.Join{how, lo, ro, l, r}:
      h
    case P.Head{m, x}:
      h

def Laws.merge_pass_merges(p):
  match p:
    case P.ScanCsv{path, o, sc}:
      {==}
    case P.Source{nm, sc}:
      {==}
    case P.Select{es, x}:
      Laws.merge_pass_merges(x)
    case P.WithColumns{es, x}:
      Laws.merge_pass_merges(x)
    case P.Filter{e, +x}:
      mergef_naf(e, P.Opt.merge(x), Laws.merge_pass_merges(x))
    case P.Sort{ks, x}:
      Laws.merge_pass_merges(x)
    case P.GroupBy{ks, ags, mo, x}:
      Laws.merge_pass_merges(x)
    case P.Join{how, lo, ro, +l, +r}:
      and_true(Laws.no_adjacent_filters(P.Opt.merge(l)), Laws.no_adjacent_filters(P.Opt.merge(r)), Laws.merge_pass_merges(l), Laws.merge_pass_merges(r))
    case P.Head{m, x}:
      Laws.merge_pass_merges(x)

# over a non-Filter input, Opt.merge.f just rebuilds the Filter
def mergef_plain(-e: X.Expr, y: P.Plan, nf: {Laws.is_filter(y) == False{} : Bool}) -> {P.Opt.merge.f(e, y) == P.Filter{e, y} : P.Plan}:
  match y:
    case P.Filter{q, z}:
      Empty.absurd({P.Opt.merge.f(e, P.Filter{q, z}) == P.Filter{e, P.Filter{q, z}} : P.Plan}, true_false(nf))
    case P.ScanCsv{path, o, sc}:
      {==}
    case P.Source{nm, sc}:
      {==}
    case P.Select{es, x}:
      {==}
    case P.WithColumns{es, x}:
      {==}
    case P.Sort{ks, x}:
      {==}
    case P.GroupBy{ks, ags, mo, x}:
      {==}
    case P.Join{how, lo, ro, l, r}:
      {==}
    case P.Head{m, x}:
      {==}

def Laws.merge_fixed_point(p, h):
  match p:
    case P.ScanCsv{path, o, sc}:
      {==}
    case P.Source{nm, sc}:
      {==}
    case P.Select{es, x}:
      %Laws.merge_fixed_point(x, h) : {P.Select{es, P.Opt.merge(x)} == P.Select{es, _} : P.Plan}
      {==}
    case P.WithColumns{es, x}:
      %Laws.merge_fixed_point(x, h) : {P.WithColumns{es, P.Opt.merge(x)} == P.WithColumns{es, _} : P.Plan}
      {==}
    case P.Filter{e, +x}:
      %Equal.sym(P.Plan, P.Opt.merge(x), x, Laws.merge_fixed_point(x, and_right(Bool.not(Laws.is_filter(x)), Laws.no_adjacent_filters(x), h))) : {P.Opt.merge.f(e, _) == P.Filter{e, x} : P.Plan}
      mergef_plain(e, x, not_true(Laws.is_filter(x), and_left(Bool.not(Laws.is_filter(x)), Laws.no_adjacent_filters(x), h)))
    case P.Sort{ks, x}:
      %Laws.merge_fixed_point(x, h) : {P.Sort{ks, P.Opt.merge(x)} == P.Sort{ks, _} : P.Plan}
      {==}
    case P.GroupBy{ks, ags, mo, x}:
      %Laws.merge_fixed_point(x, h) : {P.GroupBy{ks, ags, mo, P.Opt.merge(x)} == P.GroupBy{ks, ags, mo, _} : P.Plan}
      {==}
    case P.Join{how, lo, ro, +l, +r}:
      %Laws.merge_fixed_point(l, and_left(Laws.no_adjacent_filters(l), Laws.no_adjacent_filters(r), h)) : {P.Join{how, lo, ro, P.Opt.merge(l), P.Opt.merge(r)} == P.Join{how, lo, ro, _, r} : P.Plan}
      %Laws.merge_fixed_point(r, and_right(Laws.no_adjacent_filters(l), Laws.no_adjacent_filters(r), h)) : {P.Join{how, lo, ro, P.Opt.merge(l), P.Opt.merge(r)} == P.Join{how, lo, ro, P.Opt.merge(l), _} : P.Plan}
      {==}
    case P.Head{m, x}:
      %Laws.merge_fixed_point(x, h) : {P.Head{m, P.Opt.merge(x)} == P.Head{m, _} : P.Plan}
      {==}

def Laws.merge_idempotent(p):
  Laws.merge_fixed_point(P.Opt.merge(p), Laws.merge_pass_merges(p))

# a pending Head over a non-Head x with no adjacent heads has none either
def hwrap_nah(n: Maybe<&2, U32>, -x: P.Plan, nh: {Laws.is_head(x) == False{} : Bool}, h: {Laws.no_adjacent_heads(x) == True{} : Bool}) -> {Laws.no_adjacent_heads(P.Opt.hwrap(n, x)) == True{} : Bool}:
  match n:
    case None{}:
      h
    case Some{k}:
      %Equal.sym(Bool, Laws.is_head(x), False{}, nh) : {Bool.and(Bool.not(_), Laws.no_adjacent_heads(x)) == True{} : Bool}
      h

def Laws.head_pass_merges(p, n):
  match p:
    case P.ScanCsv{path, o, sc}:
      hwrap_nah(n, P.ScanCsv{path, o, sc}, {==}, {==})
    case P.Source{nm, sc}:
      hwrap_nah(n, P.Source{nm, sc}, {==}, {==})
    case P.Select{+es, +x}:
      hwrap_nah(P.Opt.hstop(P.Opt.sinks(es, P.Plan.schema(x)), n), P.Select{es, P.Opt.head(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n))}, {==}, Laws.head_pass_merges(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n)))
    case P.WithColumns{+es, +x}:
      hwrap_nah(P.Opt.hstop(P.Opt.sinks(es, P.Plan.schema(x)), n), P.WithColumns{es, P.Opt.head(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n))}, {==}, Laws.head_pass_merges(x, P.Opt.hpass(P.Opt.sinks(es, P.Plan.schema(x)), n)))
    case P.Filter{e, +x}:
      hwrap_nah(n, P.Filter{e, P.Opt.head(x, None{})}, {==}, Laws.head_pass_merges(x, None{}))
    case P.Sort{ks, +x}:
      hwrap_nah(n, P.Sort{ks, P.Opt.head(x, None{})}, {==}, Laws.head_pass_merges(x, None{}))
    case P.GroupBy{ks, ags, mo, +x}:
      hwrap_nah(n, P.GroupBy{ks, ags, mo, P.Opt.head(x, None{})}, {==}, Laws.head_pass_merges(x, None{}))
    case P.Join{how, lo, ro, +l, +r}:
      hwrap_nah(n, P.Join{how, lo, ro, P.Opt.head(l, None{}), P.Opt.head(r, None{})}, {==}, and_true(Laws.no_adjacent_heads(P.Opt.head(l, None{})), Laws.no_adjacent_heads(P.Opt.head(r, None{})), Laws.head_pass_merges(l, None{}), Laws.head_pass_merges(r, None{})))
    case P.Head{m, x}:
      Laws.head_pass_merges(x, Some{P.Opt.hmin(m, n)})

# =====================================================================================
# 5. Columns
# =====================================================================================

def Laws.head_len(c, n):
  match c:
    case C.CBool{len, depth, valid, data}:
      {==}
    case C.CU32{len, depth, valid, data}:
      {==}
    case C.CI32{len, depth, valid, data}:
      {==}
    case C.CF32{len, depth, valid, data}:
      {==}
    case C.CStr{len, depth, valid, data}:
      {==}

def Laws.head_dtype(c, n):
  match c:
    case C.CBool{len, depth, valid, data}:
      {==}
    case C.CU32{len, depth, valid, data}:
      {==}
    case C.CI32{len, depth, valid, data}:
      {==}
    case C.CF32{len, depth, valid, data}:
      {==}
    case C.CStr{len, depth, valid, data}:
      {==}

# =====================================================================================
# 5b. Kernels: array shape. Arrays are affine, so every lemma that rewrites one
# hands the rewritten array back as a witness (&b: Array<T> -> ...) beside
# the equation about it.
# =====================================================================================

# Array.size(xs) = (b, n) lifted to the node: size.node rebuilds ANode{b, ys}
def size_node(-T: Type, -xs: Array<T>, ys: Array<T>, w: &b: Array<T> -> &n: U32 -> {Array.size(T, xs) == (b, n) : Array<T> & U32} & {Laws.slots(T, b) == n : U32} & {Laws.slots(T, xs) == n : U32})
  -> &b2: Array<T> -> &n2: U32 -> {Array.size(T, ANode{xs, ys}) == (b2, n2) : Array<T> & U32} & {Laws.slots(T, b2) == n2 : U32} & {Laws.slots(T, ANode{xs, ys}) == n2 : U32}:
  (b, n0, eq, sl, sa) = w
  +n = n0
  (ANode{b, ys}, U32.shl(n), (%Equal.sym(Array<T> & U32, Array.size(T, xs), (b, n), eq) : {Array.size.node(T, ys, _) == (ANode{b, ys}, U32.shl(n)) : Array<T> & U32}; {==}), (%sl : {U32.shl(Laws.slots(T, b)) == U32.shl(_) : U32}; {==}), (%sa : {U32.shl(Laws.slots(T, xs)) == U32.shl(_) : U32}; {==}))

# Array.size(a) is (b, n): b is a handed back live, n the slots of both
def size_is(-T: Type, a: Array<T>) -> &b: Array<T> -> &n: U32 -> {Array.size(T, a) == (b, n) : Array<T> & U32} & {Laws.slots(T, b) == n : U32} & {Laws.slots(T, a) == n : U32}:
  match a:
    case ALeaf{x}:
      (ALeaf{x}, 1, {==}, {==}, {==})
    case ANode{xs, ys}:
      size_node(T, xs, ys, size_is(T, xs))

# the swap of the left half lifted to the node
def swap_lo(-T: Type, -xs: Array<T>, ys: Array<T>, -n: U32, -i: U32, -v: T, w: &c: Array<T> -> &o: T -> {Array.swap.go(T, xs, n, i, v, U32.is_lt(i, U32.shr(n))) == (c, o) : Array<T> & T} & {Laws.slots(T, c) == Laws.slots(T, xs) : U32})
  -> &c2: Array<T> -> &o2: T -> {Array.swap.lo(T, ys, Array.swap.go(T, xs, n, i, v, U32.is_lt(i, U32.shr(n)))) == (c2, o2) : Array<T> & T} & {Laws.slots(T, c2) == Laws.slots(T, ANode{xs, ys}) : U32}:
  (c, o, eq, sl) = w
  (ANode{c, ys}, o, (%Equal.sym(Array<T> & T, Array.swap.go(T, xs, n, i, v, U32.is_lt(i, U32.shr(n))), (c, o), eq) : {Array.swap.lo(T, ys, _) == (ANode{c, ys}, o) : Array<T> & T}; {==}), (%sl : {U32.shl(Laws.slots(T, c)) == U32.shl(_) : U32}; {==}))

# the swap of the right half lifted to the node (the slots are the left half's)
def swap_hi(-T: Type, xs: Array<T>, -ys: Array<T>, -n: U32, -j: U32, -v: T, w: &c: Array<T> -> &o: T -> {Array.swap.go(T, ys, n, j, v, U32.is_lt(j, U32.shr(n))) == (c, o) : Array<T> & T} & {Laws.slots(T, c) == Laws.slots(T, ys) : U32})
  -> &c2: Array<T> -> &o2: T -> {Array.swap.hi(T, xs, Array.swap.go(T, ys, n, j, v, U32.is_lt(j, U32.shr(n)))) == (c2, o2) : Array<T> & T} & {Laws.slots(T, c2) == Laws.slots(T, ANode{xs, ys}) : U32}:
  (c, o, eq, sl) = w
  (ANode{xs, c}, o, (%Equal.sym(Array<T> & T, Array.swap.go(T, ys, n, j, v, U32.is_lt(j, U32.shr(n))), (c, o), eq) : {Array.swap.hi(T, xs, _) == (ANode{xs, c}, o) : Array<T> & T}; {==}), {==})

# Array.swap.go answers (c, o) with c of a's slots
def swap_ex(-T: Type, a: Array<T>, +n: U32, +i: U32, v: T, z: Bool) -> &c: Array<T> -> &o: T -> {Array.swap.go(T, a, n, i, v, z) == (c, o) : Array<T> & T} & {Laws.slots(T, c) == Laws.slots(T, a) : U32}:
  match a z:
    case ALeaf{x} _:
      (ALeaf{v}, x, {==}, {==})
    case ANode{xs, ys} True{}:
      swap_lo(T, xs, ys, U32.shr(n), i, v, swap_ex(T, xs, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n)))))
    case ANode{xs, ys} False{}:
      swap_hi(T, xs, ys, U32.shr(n), U32.sub(i, U32.shr(n)), v, swap_ex(T, ys, U32.shr(n), U32.sub(i, U32.shr(n)), v, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))))

# Array.set(out, i, v) = set.fin(swap.at(i, v, size(out))): the size step (eq1)
# then the swap step (w) give the written array c, with out's slots k
def set_swap(-T: Type, -out: Array<T>, -b1: Array<T>, -n: U32, -i: U32, -v: T, -k: U32,
  eq1: {Array.size(T, out) == (b1, n) : Array<T> & U32}, sl1: {Laws.slots(T, b1) == n : U32}, sa1: {Laws.slots(T, out) == n : U32}, hk: {Laws.slots(T, out) == k : U32},
  w: &c: Array<T> -> &o: T -> {Array.swap.go(T, b1, n, U32.and(i, U32.sub(n, 1)), v, U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))) == (c, o) : Array<T> & T} & {Laws.slots(T, c) == Laws.slots(T, b1) : U32})
  -> &b: Array<T> -> {Array.set(T, out, i, v) == b : Array<T>} & {Laws.slots(T, b) == k : U32}:
  (c, o, eq2, sl2) = w
  (c, (%Equal.sym(Array<T> & U32, Array.size(T, out), (b1, n), eq1) : {Array.set.fin(T, Array.swap.at(T, i, v, _)) == c : Array<T>}; %Equal.sym(Array<T> & T, Array.swap.go(T, b1, n, U32.and(i, U32.sub(n, 1)), v, U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))), (c, o), eq2) : {Array.set.fin(T, _) == c : Array<T>}; {==}), (%hk : {Laws.slots(T, c) == _ : U32}; %Equal.sym(U32, Laws.slots(T, out), n, sa1) : {Laws.slots(T, c) == _ : U32}; %sl1 : {Laws.slots(T, c) == _ : U32}; sl2))

def set_size(-T: Type, -out: Array<T>, +i: U32, v: T, -k: U32, hk: {Laws.slots(T, out) == k : U32}, w: &b1: Array<T> -> &n: U32 -> {Array.size(T, out) == (b1, n) : Array<T> & U32} & {Laws.slots(T, b1) == n : U32} & {Laws.slots(T, out) == n : U32})
  -> &b: Array<T> -> {Array.set(T, out, i, v) == b : Array<T>} & {Laws.slots(T, b) == k : U32}:
  (b1, n0, eq1, sl1, sa1) = w
  +n = n0
  set_swap(T, out, b1, n, i, v, k, eq1, sl1, sa1, hk, swap_ex(T, b1, n, U32.and(i, U32.sub(n, 1)), v, U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))))

# Array.set keeps the slots: the written array is handed back live
def set_ex(-T: Type, out: Array<T>, +i: U32, v: T, -k: U32, hk: {Laws.slots(T, out) == k : U32}) -> &b: Array<T> -> {Array.set(T, out, i, v) == b : Array<T>} & {Laws.slots(T, b) == k : U32}:
  set_size(T, out, i, v, k, hk, size_is(T, out))

# one step of Kernel.map.go: the written array b replaces Array.set(out, i, f(x))
# and the induction hypothesis ih runs the remaining fuel over it
def map_step(~T: Data, ~U: Data, ~f: T -> U, -p: Nat, -j: U32, -out: Array<U>, -i: U32, -x: T, -k: U32, r2: Array<T> & T,
  w: &b: Array<U> -> {Array.set(U, out, i, f(x)) == b : Array<U>} & {Laws.slots(U, b) == k : U32},
  ih: @b: Array<U> -> @r: Array<T> & T -> {Laws.slots(U, b) == k : U32} -> {Laws.slots(U, K.Kernel.map.go(~T, ~U, ~f, p, j, b, r)) == k : U32})
  -> {Laws.slots(U, K.Kernel.map.go(~T, ~U, ~f, p, j, Array.set(U, out, i, f(x)), r2)) == k : U32}:
  (b, eq, sl) = w
  %Equal.sym(Array<U>, Array.set(U, out, i, f(x)), b, eq) : {Laws.slots(U, K.Kernel.map.go(~T, ~U, ~f, p, j, _, r2)) == k : U32}
  ih(b, r2, sl)

# Kernel.map.go only ever writes into out: the slots stay k
def map_go_slots(~T: Data, ~U: Data, ~f: T -> U, fuel: Nat, +i: U32, out: Array<U>, r: Array<T> & T, +k: U32, hk: {Laws.slots(U, out) == k : U32}) -> {Laws.slots(U, K.Kernel.map.go(~T, ~U, ~f, fuel, i, out, r)) == k : U32}:
  match fuel:
    case 0n:
      hk
    case 1n+p:
      (a, x) = r
      map_step(~T, ~U, ~f, p, U32.inc(i), out, i, x, k, Array.get(T, a, U32.inc(i)), set_ex(U, out, i, f(x), k, hk), b => r2 => h => map_go_slots(~T, ~U, ~f, p, U32.inc(i), b, r2, k, h))

# a fresh array of depth d has 2^d slots
def new_slots(-T: Data, d: Nat, -v: T) -> {Laws.slots(T, Array.new(T, d, v)) == U32.shln(1, d) : U32}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      %new_slots(T, p, v) : {U32.shl(Laws.slots(T, Array.new(T, p, v))) == U32.shl(_) : U32}
      {==}

def Laws.mask_not_slots(n, d, a):
  map_go_slots(~U32, ~U32, ~(x => U32.xor(x, 1)), U32.to_nat(n), 0, Array.new(U32, d, 0), Array.get(U32, a, 0), U32.shln(1, d), new_slots(U32, d, 0))

# the same for Kernel.zip.go, which reads two arrays per step
def zip_step(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, -p: Nat, -j: U32, -out: Array<V>, -i: U32, -x: T, -y: U, -k: U32, ra2: Array<T> & T, rb2: Array<U> & U,
  w: &c: Array<V> -> {Array.set(V, out, i, f(x, y)) == c : Array<V>} & {Laws.slots(V, c) == k : U32},
  ih: @c: Array<V> -> @ra: Array<T> & T -> @rb: Array<U> & U -> {Laws.slots(V, c) == k : U32} -> {Laws.slots(V, K.Kernel.zip.go(~T, ~U, ~V, ~f, p, j, c, ra, rb)) == k : U32})
  -> {Laws.slots(V, K.Kernel.zip.go(~T, ~U, ~V, ~f, p, j, Array.set(V, out, i, f(x, y)), ra2, rb2)) == k : U32}:
  (c, eq, sl) = w
  %Equal.sym(Array<V>, Array.set(V, out, i, f(x, y)), c, eq) : {Laws.slots(V, K.Kernel.zip.go(~T, ~U, ~V, ~f, p, j, _, ra2, rb2)) == k : U32}
  ih(c, ra2, rb2, sl)

def zip_go_slots(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, fuel: Nat, +i: U32, out: Array<V>, ra: Array<T> & T, rb: Array<U> & U, +k: U32, hk: {Laws.slots(V, out) == k : U32}) -> {Laws.slots(V, K.Kernel.zip.go(~T, ~U, ~V, ~f, fuel, i, out, ra, rb)) == k : U32}:
  match fuel:
    case 0n:
      hk
    case 1n+p:
      (a, x) = ra
      (b, y) = rb
      zip_step(~T, ~U, ~V, ~f, p, U32.inc(i), out, i, x, y, k, Array.get(T, a, U32.inc(i)), Array.get(U, b, U32.inc(i)), set_ex(V, out, i, f(x, y), k, hk), c => ra2 => rb2 => h => zip_go_slots(~T, ~U, ~V, ~f, p, U32.inc(i), c, ra2, rb2, k, h))

def Laws.mask_and_slots(n, d, a, b):
  zip_go_slots(~U32, ~U32, ~U32, ~(x => y => U32.and(x, y)), U32.to_nat(n), 0, Array.new(U32, d, 0), Array.get(U32, a, 0), Array.get(U32, b, 0), U32.shln(1, d), new_slots(U32, d, 0))

# the same for Kernel.iota.go, which reads nothing
def iota_step(-p: Nat, -j: U32, -out: Array<U32>, -i: U32, -off: U32, -k: U32,
  w: &b: Array<U32> -> {Array.set(U32, out, i, U32.add(off, i)) == b : Array<U32>} & {Laws.slots(U32, b) == k : U32},
  ih: @b: Array<U32> -> {Laws.slots(U32, b) == k : U32} -> {Laws.slots(U32, K.Kernel.iota.go(p, j, off, b)) == k : U32})
  -> {Laws.slots(U32, K.Kernel.iota.go(p, j, off, Array.set(U32, out, i, U32.add(off, i)))) == k : U32}:
  (b, eq, sl) = w
  %Equal.sym(Array<U32>, Array.set(U32, out, i, U32.add(off, i)), b, eq) : {Laws.slots(U32, K.Kernel.iota.go(p, j, off, _)) == k : U32}
  ih(b, sl)

def iota_go_slots(fuel: Nat, +i: U32, +off: U32, out: Array<U32>, +k: U32, hk: {Laws.slots(U32, out) == k : U32}) -> {Laws.slots(U32, K.Kernel.iota.go(fuel, i, off, out)) == k : U32}:
  match fuel:
    case 0n:
      hk
    case 1n+p:
      iota_step(p, U32.inc(i), out, i, off, k, set_ex(U32, out, i, U32.add(off, i), k, hk), b => h => iota_go_slots(p, U32.inc(i), off, b, k, h))

def Laws.iota_slots(n, d, off):
  iota_go_slots(U32.to_nat(n), 0, off, Array.new(U32, d, 0), U32.shln(1, d), new_slots(U32, d, 0))

# =====================================================================================
# 6. I32
# =====================================================================================

def Laws.i32_add_comm(a, b):
  match a b:
    case D.I32{x} D.I32{y}:
      Equal.cong(U32, D.I32, w => D.I32{w}, U32.add(x, y), U32.add(y, x), U32.add_comm(x, y))

def Laws.i32_bits_roundtrip(a):
  match a:
    case D.I32{x}:
      {==}
