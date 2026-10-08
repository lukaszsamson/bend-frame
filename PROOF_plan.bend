# PROOF_plan.bend -- proofs of LAWS.bend sections 3 and 4 (Plan.schema and the
# optimizer passes at the schema level).
import Base
import ./src/dtype.bend as D
import ./src/err.bend as E
import ./src/kernels.bend as K
import ./src/column.bend as C
import ./src/schema.bend as S
import ./src/expr.bend as X
import ./src/analysis.bend as A
import ./src/sort.bend as O
import ./src/join.bend as J
import ./src/plan.bend as P
import ./LAWS.bend as Laws
import ./PROOF_lib.bend as L
import ./PROOF_schema.bend as PS

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
      Empty.absurd({out == s : List<&2, S.Field>}, L.fail_done(List<&2, S.Field>, e, out, h))
    case Done{D.TBool{}}:
      Equal.sym(List<&2, S.Field>, s, out, L.done_inj(List<&2, S.Field>, s, out, h))
    case Done{D.TU32{}}:
      Empty.absurd({out == s : List<&2, S.Field>}, L.fail_done(List<&2, S.Field>, E.TypeMismatch{"filter", "bool", "u32"}, out, h))
    case Done{D.TI32{}}:
      Empty.absurd({out == s : List<&2, S.Field>}, L.fail_done(List<&2, S.Field>, E.TypeMismatch{"filter", "bool", "i32"}, out, h))
    case Done{D.TF32{}}:
      Empty.absurd({out == s : List<&2, S.Field>}, L.fail_done(List<&2, S.Field>, E.TypeMismatch{"filter", "bool", "f32"}, out, h))
    case Done{D.TStr{}}:
      Empty.absurd({out == s : List<&2, S.Field>}, L.fail_done(List<&2, S.Field>, E.TypeMismatch{"filter", "bool", "str"}, out, h))

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
      %Equal.sym(Bool, S.Schema.has(s, n), True{}, L.and_left(S.Schema.has(s, n), Laws.keys_exist(t, s), keys)) : {P.Plan.sort.miss.k(_, n, P.Plan.sort.miss(t, s)) == None{} : Maybe<&2, E.Err>}
      keys_miss(t, s, L.and_right(S.Schema.has(s, n), Laws.keys_exist(t, s), keys))

def Laws.sort_keeps_schema(p, s, ks, ok, keys):
  %Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(p), Done{s}, ok) : {P.Plan.schema.sort(ks, _) == Done{s} : E.Res(List<&2, S.Field>)}
  %Equal.sym(Maybe<&2, E.Err>, P.Plan.sort.miss(ks, s), None{}, keys_miss(ks, s, keys)) : {P.Plan.schema.sort.k(_, s) == Done{s} : E.Res(List<&2, S.Field>)}
  {==}

def sort_inv(m: Maybe<&2, E.Err>, -s: List<&2, S.Field>, -out: List<&2, S.Field>, h: {P.Plan.schema.sort.k(m, s) == Done{out} : E.Res(List<&2, S.Field>)}) -> {out == s : List<&2, S.Field>}:
  match m:
    case Some{e}:
      Empty.absurd({out == s : List<&2, S.Field>}, L.fail_done(List<&2, S.Field>, e, out, h))
    case None{}:
      Equal.sym(List<&2, S.Field>, s, out, L.done_inj(List<&2, S.Field>, s, out, h))

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
    %L.done_inj(List<&2, S.Field>, S.Schema.with.go(s, n, S.Field{n, d}), out, h) : {List.length(&2, S.Field, _) == List.length(&2, S.Field, s) : Nat}
    PS.with_go_length(s, n, S.Field{n, d})

# the typed field of the one expression: t its type (the shared analysis)
def wc_inv(t: E.Res(D.DType), +n: String, +s: List<&2, S.Field>, -out: List<&2, S.Field>, has: {S.Schema.has(s, n) == True{} : Bool},
  h: {P.Plan.schema.wc.k(S.Schema.project.chk(P.Plan.fields.put(P.Plan.field.k(t, n), Done{Nil{}})), s) == Done{out} : E.Res(List<&2, S.Field>)})
  -> {List.length(&2, S.Field, out) == List.length(&2, S.Field, s) : Nat}:
  match t:
    case Fail{e}:
      Empty.absurd({List.length(&2, S.Field, out) == List.length(&2, S.Field, s) : Nat}, L.fail_done(List<&2, S.Field>, e, out, h))
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
    case P.Drop{ks, +x}:
      %Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(P.Opt.hwrap(n, P.Drop{ks, P.Opt.head(x, None{})})), P.Plan.schema(P.Drop{ks, P.Opt.head(x, None{})}), hwrap_schema(n, P.Drop{ks, P.Opt.head(x, None{})})) : {_ == P.Plan.schema.drop(ks, P.Plan.schema(x)) : E.Res(List<&2, S.Field>)}
      %Laws.head_pass_keeps_schema(x, None{}) : {P.Plan.schema.drop(ks, P.Plan.schema(P.Opt.head(x, None{}))) == P.Plan.schema.drop(ks, _) : E.Res(List<&2, S.Field>)}
      {==}
    case P.Rename{ks, +x}:
      %Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(P.Opt.hwrap(n, P.Rename{ks, P.Opt.head(x, None{})})), P.Plan.schema(P.Rename{ks, P.Opt.head(x, None{})}), hwrap_schema(n, P.Rename{ks, P.Opt.head(x, None{})})) : {_ == P.Plan.schema.rename(ks, P.Plan.schema(x)) : E.Res(List<&2, S.Field>)}
      %Laws.head_pass_keeps_schema(x, None{}) : {P.Plan.schema.rename(ks, P.Plan.schema(P.Opt.head(x, None{}))) == P.Plan.schema.rename(ks, _) : E.Res(List<&2, S.Field>)}
      {==}
    case P.Slice{ks, kl, +x}:
      %Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(P.Opt.hwrap(n, P.Slice{ks, kl, P.Opt.head(x, None{})})), P.Plan.schema(P.Slice{ks, kl, P.Opt.head(x, None{})}), hwrap_schema(n, P.Slice{ks, kl, P.Opt.head(x, None{})})) : {_ == P.Plan.schema.slice(ks, kl, P.Plan.schema(x)) : E.Res(List<&2, S.Field>)}
      %Laws.head_pass_keeps_schema(x, None{}) : {P.Plan.schema.slice(ks, kl, P.Plan.schema(P.Opt.head(x, None{}))) == P.Plan.schema.slice(ks, kl, _) : E.Res(List<&2, S.Field>)}
      {==}
    case P.Tail{ks, +x}:
      %Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(P.Opt.hwrap(n, P.Tail{ks, P.Opt.head(x, None{})})), P.Plan.schema(P.Tail{ks, P.Opt.head(x, None{})}), hwrap_schema(n, P.Tail{ks, P.Opt.head(x, None{})})) : {_ == P.Plan.schema.tail(ks, P.Plan.schema(x)) : E.Res(List<&2, S.Field>)}
      %Laws.head_pass_keeps_schema(x, None{}) : {P.Plan.schema.tail(ks, P.Plan.schema(P.Opt.head(x, None{}))) == P.Plan.schema.tail(ks, _) : E.Res(List<&2, S.Field>)}
      {==}
    case P.Unique{ks, +x}:
      %Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(P.Opt.hwrap(n, P.Unique{ks, P.Opt.head(x, None{})})), P.Plan.schema(P.Unique{ks, P.Opt.head(x, None{})}), hwrap_schema(n, P.Unique{ks, P.Opt.head(x, None{})})) : {_ == P.Plan.schema.unique(ks, P.Plan.schema(x)) : E.Res(List<&2, S.Field>)}
      %Laws.head_pass_keeps_schema(x, None{}) : {P.Plan.schema.unique(ks, P.Plan.schema(P.Opt.head(x, None{}))) == P.Plan.schema.unique(ks, _) : E.Res(List<&2, S.Field>)}
      {==}
    case P.GroupBy{ks, ags, mo, +x}:
      %Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(P.Opt.hwrap(n, P.GroupBy{ks, ags, mo, P.Opt.head(x, None{})})), P.Plan.schema(P.GroupBy{ks, ags, mo, P.Opt.head(x, None{})}), hwrap_schema(n, P.GroupBy{ks, ags, mo, P.Opt.head(x, None{})})) : {_ == P.Plan.schema.gb(ks, ags, P.Plan.schema(x)) : E.Res(List<&2, S.Field>)}
      %Laws.head_pass_keeps_schema(x, None{}) : {P.Plan.schema.gb(ks, ags, P.Plan.schema(P.Opt.head(x, None{}))) == P.Plan.schema.gb(ks, ags, _) : E.Res(List<&2, S.Field>)}
      {==}
    case P.Join{how, lo, ro, +l, +r}:
      %Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(P.Opt.hwrap(n, P.Join{how, lo, ro, P.Opt.head(l, None{}), P.Opt.head(r, None{})})), P.Plan.schema(P.Join{how, lo, ro, P.Opt.head(l, None{}), P.Opt.head(r, None{})}), hwrap_schema(n, P.Join{how, lo, ro, P.Opt.head(l, None{}), P.Opt.head(r, None{})})) : {_ == P.Plan.schema.join(how, lo, ro, P.Plan.schema(l), P.Plan.schema(r)) : E.Res(List<&2, S.Field>)}
      %Laws.head_pass_keeps_schema(l, None{}) : {P.Plan.schema.join(how, lo, ro, P.Plan.schema(P.Opt.head(l, None{})), P.Plan.schema(P.Opt.head(r, None{}))) == P.Plan.schema.join(how, lo, ro, _, P.Plan.schema(r)) : E.Res(List<&2, S.Field>)}
      %Laws.head_pass_keeps_schema(r, None{}) : {P.Plan.schema.join(how, lo, ro, P.Plan.schema(P.Opt.head(l, None{})), P.Plan.schema(P.Opt.head(r, None{}))) == P.Plan.schema.join(how, lo, ro, P.Plan.schema(P.Opt.head(l, None{})), _) : E.Res(List<&2, S.Field>)}
      {==}
    case P.Concat{ci, +l, +r}:
      %Equal.sym(E.Res(List<&2, S.Field>), P.Plan.schema(P.Opt.hwrap(n, P.Concat{ci, P.Opt.head(l, None{}), P.Opt.head(r, None{})})), P.Plan.schema(P.Concat{ci, P.Opt.head(l, None{}), P.Opt.head(r, None{})}), hwrap_schema(n, P.Concat{ci, P.Opt.head(l, None{}), P.Opt.head(r, None{})})) : {_ == P.Plan.schema.concat(ci, P.Plan.schema(l), P.Plan.schema(r)) : E.Res(List<&2, S.Field>)}
      %Laws.head_pass_keeps_schema(l, None{}) : {P.Plan.schema.concat(ci, P.Plan.schema(P.Opt.head(l, None{})), P.Plan.schema(P.Opt.head(r, None{}))) == P.Plan.schema.concat(ci, _, P.Plan.schema(r)) : E.Res(List<&2, S.Field>)}
      %Laws.head_pass_keeps_schema(r, None{}) : {P.Plan.schema.concat(ci, P.Plan.schema(P.Opt.head(l, None{})), P.Plan.schema(P.Opt.head(r, None{}))) == P.Plan.schema.concat(ci, P.Plan.schema(P.Opt.head(l, None{})), _) : E.Res(List<&2, S.Field>)}
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
      Empty.absurd({f(r2) == Done{s} : E.Res(List<&2, S.Field>)}, L.fail_done(List<&2, S.Field>, e, s, Equal.trans(E.Res(List<&2, S.Field>), Fail{e}, f(Fail{e}), Done{s}, Equal.sym(E.Res(List<&2, S.Field>), f(Fail{e}), Fail{e}, fails(e)), h)))
    case Done{s1}:
      %Equal.sym(E.Res(List<&2, S.Field>), r2, Done{s1}, ih(s1, {==})) : {f(_) == Done{s} : E.Res(List<&2, S.Field>)}
      h

# the join rule over both inputs
def binary(how: J.JoinHow, lo: List<&2, String>, ro: List<&2, String>, rl: E.Res(List<&2, S.Field>), rr: E.Res(List<&2, S.Field>), -rl2: E.Res(List<&2, S.Field>), -rr2: E.Res(List<&2, S.Field>), -s: List<&2, S.Field>,
  h: {P.Plan.schema.join(how, lo, ro, rl, rr) == Done{s} : E.Res(List<&2, S.Field>)},
  ihl: @o: List<&2, S.Field> -> {rl == Done{o} : E.Res(List<&2, S.Field>)} -> {rl2 == Done{o} : E.Res(List<&2, S.Field>)},
  ihr: @o: List<&2, S.Field> -> {rr == Done{o} : E.Res(List<&2, S.Field>)} -> {rr2 == Done{o} : E.Res(List<&2, S.Field>)})
  -> {P.Plan.schema.join(how, lo, ro, rl2, rr2) == Done{s} : E.Res(List<&2, S.Field>)}:
  match rl rr:
    case Fail{e} _:
      Empty.absurd({P.Plan.schema.join(how, lo, ro, rl2, rr2) == Done{s} : E.Res(List<&2, S.Field>)}, L.fail_done(List<&2, S.Field>, e, s, h))
    case Done{a} Fail{e}:
      Empty.absurd({P.Plan.schema.join(how, lo, ro, rl2, rr2) == Done{s} : E.Res(List<&2, S.Field>)}, L.fail_done(List<&2, S.Field>, e, s, h))
    case Done{a} Done{b}:
      %Equal.sym(E.Res(List<&2, S.Field>), rl2, Done{a}, ihl(a, {==})) : {P.Plan.schema.join(how, lo, ro, _, rr2) == Done{s} : E.Res(List<&2, S.Field>)}
      %Equal.sym(E.Res(List<&2, S.Field>), rr2, Done{b}, ihr(b, {==})) : {P.Plan.schema.join(how, lo, ro, Done{a}, _) == Done{s} : E.Res(List<&2, S.Field>)}
      h

# the concat rule over both inputs
def binary_concat(ci: U32, rl: E.Res(List<&2, S.Field>), rr: E.Res(List<&2, S.Field>), -rl2: E.Res(List<&2, S.Field>), -rr2: E.Res(List<&2, S.Field>), -s: List<&2, S.Field>,
  h: {P.Plan.schema.concat(ci, rl, rr) == Done{s} : E.Res(List<&2, S.Field>)},
  ihl: @o: List<&2, S.Field> -> {rl == Done{o} : E.Res(List<&2, S.Field>)} -> {rl2 == Done{o} : E.Res(List<&2, S.Field>)},
  ihr: @o: List<&2, S.Field> -> {rr == Done{o} : E.Res(List<&2, S.Field>)} -> {rr2 == Done{o} : E.Res(List<&2, S.Field>)})
  -> {P.Plan.schema.concat(ci, rl2, rr2) == Done{s} : E.Res(List<&2, S.Field>)}:
  match rl rr:
    case Fail{e} _:
      Empty.absurd({P.Plan.schema.concat(ci, rl2, rr2) == Done{s} : E.Res(List<&2, S.Field>)}, L.fail_done(List<&2, S.Field>, e, s, h))
    case Done{a} Fail{e}:
      Empty.absurd({P.Plan.schema.concat(ci, rl2, rr2) == Done{s} : E.Res(List<&2, S.Field>)}, L.fail_done(List<&2, S.Field>, e, s, h))
    case Done{a} Done{b}:
      %Equal.sym(E.Res(List<&2, S.Field>), rl2, Done{a}, ihl(a, {==})) : {P.Plan.schema.concat(ci, _, rr2) == Done{s} : E.Res(List<&2, S.Field>)}
      %Equal.sym(E.Res(List<&2, S.Field>), rr2, Done{b}, ihr(b, {==})) : {P.Plan.schema.concat(ci, Done{a}, _) == Done{s} : E.Res(List<&2, S.Field>)}
      h

# a bool e over s0 after a bool q (its record rs, k, tot, loc): `q & e` is bool
# over s0 too. re is e's analysis.
def and_e(re: E.Res(A.Ana), -rs: List<&2, String>, -k: A.AKind, -tot: Bool, -loc: Bool, -s0: List<&2, S.Field>, -s: List<&2, S.Field>, h: {P.Plan.schema.filter.k(A.Ana.type.k(re), s0) == Done{s} : E.Res(List<&2, S.Field>)}) -> {P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, Done{A.Ana{D.TBool{}, rs, k, tot, loc}}, re)), s0) == Done{s} : E.Res(List<&2, S.Field>)}:
  match re:
    case Fail{e}:
      Empty.absurd({P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, Done{A.Ana{D.TBool{}, rs, k, tot, loc}}, Fail{e})), s0) == Done{s} : E.Res(List<&2, S.Field>)}, L.fail_done(List<&2, S.Field>, e, s, h))
    case Done{A.Ana{D.TBool{}, rs2, k2, tot2, loc2}}:
      h
    case Done{A.Ana{D.TU32{}, rs2, k2, tot2, loc2}}:
      Empty.absurd({P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, Done{A.Ana{D.TBool{}, rs, k, tot, loc}}, Done{A.Ana{D.TU32{}, rs2, k2, tot2, loc2}})), s0) == Done{s} : E.Res(List<&2, S.Field>)}, L.fail_done(List<&2, S.Field>, E.TypeMismatch{"filter", "bool", "u32"}, s, h))
    case Done{A.Ana{D.TI32{}, rs2, k2, tot2, loc2}}:
      Empty.absurd({P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, Done{A.Ana{D.TBool{}, rs, k, tot, loc}}, Done{A.Ana{D.TI32{}, rs2, k2, tot2, loc2}})), s0) == Done{s} : E.Res(List<&2, S.Field>)}, L.fail_done(List<&2, S.Field>, E.TypeMismatch{"filter", "bool", "i32"}, s, h))
    case Done{A.Ana{D.TF32{}, rs2, k2, tot2, loc2}}:
      Empty.absurd({P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, Done{A.Ana{D.TBool{}, rs, k, tot, loc}}, Done{A.Ana{D.TF32{}, rs2, k2, tot2, loc2}})), s0) == Done{s} : E.Res(List<&2, S.Field>)}, L.fail_done(List<&2, S.Field>, E.TypeMismatch{"filter", "bool", "f32"}, s, h))
    case Done{A.Ana{D.TStr{}, rs2, k2, tot2, loc2}}:
      Empty.absurd({P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, Done{A.Ana{D.TBool{}, rs, k, tot, loc}}, Done{A.Ana{D.TStr{}, rs2, k2, tot2, loc2}})), s0) == Done{s} : E.Res(List<&2, S.Field>)}, L.fail_done(List<&2, S.Field>, E.TypeMismatch{"filter", "bool", "str"}, s, h))

# the inner filter q over s0 resolved to s1 (h1); the outer e over s1 to s (H).
# rq is q's analysis over s0.
def and_q(rq: E.Res(A.Ana), +s0: List<&2, S.Field>, -s1: List<&2, S.Field>, -s: List<&2, S.Field>, +e: X.Expr, h1: {P.Plan.schema.filter.k(A.Ana.type.k(rq), s0) == Done{s1} : E.Res(List<&2, S.Field>)})
  -> {P.Plan.schema.filter.k(A.Ana.type.k(A.Expr.analyse(e, s1)), s1) == Done{s} : E.Res(List<&2, S.Field>)} -> {P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, rq, A.Expr.analyse(e, s0))), s0) == Done{s} : E.Res(List<&2, S.Field>)}:
  match rq:
    case Fail{err}:
      Empty.absurd({P.Plan.schema.filter.k(A.Ana.type.k(A.Expr.analyse(e, s1)), s1) == Done{s} : E.Res(List<&2, S.Field>)} -> {P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, Fail{err}, A.Expr.analyse(e, s0))), s0) == Done{s} : E.Res(List<&2, S.Field>)}, L.fail_done(List<&2, S.Field>, err, s1, h1))
    case Done{A.Ana{D.TBool{}, rs, k, tot, loc}}:
      %L.done_inj(List<&2, S.Field>, s0, s1, h1) : {P.Plan.schema.filter.k(A.Ana.type.k(A.Expr.analyse(e, _)), _) == Done{s} : E.Res(List<&2, S.Field>)} -> {P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, Done{A.Ana{D.TBool{}, rs, k, tot, loc}}, A.Expr.analyse(e, s0))), s0) == Done{s} : E.Res(List<&2, S.Field>)}
      h => and_e(A.Expr.analyse(e, s0), rs, k, tot, loc, s0, s, h)
    case Done{A.Ana{D.TU32{}, rs, k, tot, loc}}:
      Empty.absurd({P.Plan.schema.filter.k(A.Ana.type.k(A.Expr.analyse(e, s1)), s1) == Done{s} : E.Res(List<&2, S.Field>)} -> {P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, Done{A.Ana{D.TU32{}, rs, k, tot, loc}}, A.Expr.analyse(e, s0))), s0) == Done{s} : E.Res(List<&2, S.Field>)}, L.fail_done(List<&2, S.Field>, E.TypeMismatch{"filter", "bool", "u32"}, s1, h1))
    case Done{A.Ana{D.TI32{}, rs, k, tot, loc}}:
      Empty.absurd({P.Plan.schema.filter.k(A.Ana.type.k(A.Expr.analyse(e, s1)), s1) == Done{s} : E.Res(List<&2, S.Field>)} -> {P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, Done{A.Ana{D.TI32{}, rs, k, tot, loc}}, A.Expr.analyse(e, s0))), s0) == Done{s} : E.Res(List<&2, S.Field>)}, L.fail_done(List<&2, S.Field>, E.TypeMismatch{"filter", "bool", "i32"}, s1, h1))
    case Done{A.Ana{D.TF32{}, rs, k, tot, loc}}:
      Empty.absurd({P.Plan.schema.filter.k(A.Ana.type.k(A.Expr.analyse(e, s1)), s1) == Done{s} : E.Res(List<&2, S.Field>)} -> {P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, Done{A.Ana{D.TF32{}, rs, k, tot, loc}}, A.Expr.analyse(e, s0))), s0) == Done{s} : E.Res(List<&2, S.Field>)}, L.fail_done(List<&2, S.Field>, E.TypeMismatch{"filter", "bool", "f32"}, s1, h1))
    case Done{A.Ana{D.TStr{}, rs, k, tot, loc}}:
      Empty.absurd({P.Plan.schema.filter.k(A.Ana.type.k(A.Expr.analyse(e, s1)), s1) == Done{s} : E.Res(List<&2, S.Field>)} -> {P.Plan.schema.filter.k(A.Ana.type.k(A.Ana.bin(X.And{}, Done{A.Ana{D.TStr{}, rs, k, tot, loc}}, A.Expr.analyse(e, s0))), s0) == Done{s} : E.Res(List<&2, S.Field>)}, L.fail_done(List<&2, S.Field>, E.TypeMismatch{"filter", "bool", "str"}, s1, h1))

# Filter{e, Filter{q, z}} resolving to s makes Filter{q & e, z} resolve to s;
# r is z's schema
def and_filter(+q: X.Expr, +e: X.Expr, r: E.Res(List<&2, S.Field>), -s1: List<&2, S.Field>, -s: List<&2, S.Field>,
  h1: {P.Plan.schema.filter(q, r) == Done{s1} : E.Res(List<&2, S.Field>)},
  h: {P.Plan.schema.filter(e, Done{s1}) == Done{s} : E.Res(List<&2, S.Field>)})
  -> {P.Plan.schema.filter(X.Bin{X.And{}, q, e}, r) == Done{s} : E.Res(List<&2, S.Field>)}:
  match r:
    case Fail{err}:
      Empty.absurd({P.Plan.schema.filter(X.Bin{X.And{}, q, e}, Fail{err}) == Done{s} : E.Res(List<&2, S.Field>)}, L.fail_done(List<&2, S.Field>, err, s1, h1))
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
      Empty.absurd({P.Plan.schema(P.Opt.merge.f(e, y)) == Done{s} : E.Res(List<&2, S.Field>)}, L.fail_done(List<&2, S.Field>, err, s, h))
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
    case Done{s1} P.Drop{ks, x}:
      filter_over(e, P.Drop{ks, x}, s1, s, ih(s1, {==}), h)
    case Done{s1} P.Rename{ks, x}:
      filter_over(e, P.Rename{ks, x}, s1, s, ih(s1, {==}), h)
    case Done{s1} P.Slice{ks, kl, x}:
      filter_over(e, P.Slice{ks, kl, x}, s1, s, ih(s1, {==}), h)
    case Done{s1} P.Tail{ks, x}:
      filter_over(e, P.Tail{ks, x}, s1, s, ih(s1, {==}), h)
    case Done{s1} P.Unique{ks, x}:
      filter_over(e, P.Unique{ks, x}, s1, s, ih(s1, {==}), h)
    case Done{s1} P.GroupBy{ks, ags, mo, x}:
      filter_over(e, P.GroupBy{ks, ags, mo, x}, s1, s, ih(s1, {==}), h)
    case Done{s1} P.Join{how, lo, ro, l, r}:
      filter_over(e, P.Join{how, lo, ro, l, r}, s1, s, ih(s1, {==}), h)
    case Done{s1} P.Concat{ci, l, r}:
      filter_over(e, P.Concat{ci, l, r}, s1, s, ih(s1, {==}), h)
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
    case P.Drop{+ks, +x}:
      unary(r => P.Plan.schema.drop(ks, r), e => {==}, P.Plan.schema(x), P.Plan.schema(P.Opt.merge(x)), s, ok, o => h => Laws.merge_pass_keeps_schema(x, o, h))
    case P.Rename{+ks, +x}:
      unary(r => P.Plan.schema.rename(ks, r), e => {==}, P.Plan.schema(x), P.Plan.schema(P.Opt.merge(x)), s, ok, o => h => Laws.merge_pass_keeps_schema(x, o, h))
    case P.Slice{+ks, +kl, +x}:
      unary(r => P.Plan.schema.slice(ks, kl, r), e => {==}, P.Plan.schema(x), P.Plan.schema(P.Opt.merge(x)), s, ok, o => h => Laws.merge_pass_keeps_schema(x, o, h))
    case P.Tail{+ks, +x}:
      unary(r => P.Plan.schema.tail(ks, r), e => {==}, P.Plan.schema(x), P.Plan.schema(P.Opt.merge(x)), s, ok, o => h => Laws.merge_pass_keeps_schema(x, o, h))
    case P.Unique{+ks, +x}:
      unary(r => P.Plan.schema.unique(ks, r), e => {==}, P.Plan.schema(x), P.Plan.schema(P.Opt.merge(x)), s, ok, o => h => Laws.merge_pass_keeps_schema(x, o, h))
    case P.GroupBy{+ks, +ags, mo, +x}:
      unary(r => P.Plan.schema.gb(ks, ags, r), e => {==}, P.Plan.schema(x), P.Plan.schema(P.Opt.merge(x)), s, ok, o => h => Laws.merge_pass_keeps_schema(x, o, h))
    case P.Join{how, +lo, +ro, +l, +r}:
      binary(how, lo, ro, P.Plan.schema(l), P.Plan.schema(r), P.Plan.schema(P.Opt.merge(l)), P.Plan.schema(P.Opt.merge(r)), s, ok, o => h => Laws.merge_pass_keeps_schema(l, o, h), o => h => Laws.merge_pass_keeps_schema(r, o, h))
    case P.Concat{+ci, +l, +r}:
      binary_concat(ci, P.Plan.schema(l), P.Plan.schema(r), P.Plan.schema(P.Opt.merge(l)), P.Plan.schema(P.Opt.merge(r)), s, ok, o => h => Laws.merge_pass_keeps_schema(l, o, h), o => h => Laws.merge_pass_keeps_schema(r, o, h))
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
    case P.Drop{ks, x}:
      h
    case P.Rename{ks, x}:
      h
    case P.Slice{ks, kl, x}:
      h
    case P.Tail{ks, x}:
      h
    case P.Unique{ks, x}:
      h
    case P.GroupBy{ks, ags, mo, x}:
      h
    case P.Join{how, lo, ro, l, r}:
      h
    case P.Concat{ci, l, r}:
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
    case P.Drop{ks, x}:
      Laws.merge_pass_merges(x)
    case P.Rename{ks, x}:
      Laws.merge_pass_merges(x)
    case P.Slice{ks, kl, x}:
      Laws.merge_pass_merges(x)
    case P.Tail{ks, x}:
      Laws.merge_pass_merges(x)
    case P.Unique{ks, x}:
      Laws.merge_pass_merges(x)
    case P.GroupBy{ks, ags, mo, x}:
      Laws.merge_pass_merges(x)
    case P.Join{how, lo, ro, +l, +r}:
      L.and_true(Laws.no_adjacent_filters(P.Opt.merge(l)), Laws.no_adjacent_filters(P.Opt.merge(r)), Laws.merge_pass_merges(l), Laws.merge_pass_merges(r))
    case P.Concat{ci, +l, +r}:
      L.and_true(Laws.no_adjacent_filters(P.Opt.merge(l)), Laws.no_adjacent_filters(P.Opt.merge(r)), Laws.merge_pass_merges(l), Laws.merge_pass_merges(r))
    case P.Head{m, x}:
      Laws.merge_pass_merges(x)

# over a non-Filter input, Opt.merge.f just rebuilds the Filter
def mergef_plain(-e: X.Expr, y: P.Plan, nf: {Laws.is_filter(y) == False{} : Bool}) -> {P.Opt.merge.f(e, y) == P.Filter{e, y} : P.Plan}:
  match y:
    case P.Filter{q, z}:
      Empty.absurd({P.Opt.merge.f(e, P.Filter{q, z}) == P.Filter{e, P.Filter{q, z}} : P.Plan}, L.true_false(nf))
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
    case P.Drop{ks, x}:
      {==}
    case P.Rename{ks, x}:
      {==}
    case P.Slice{ks, kl, x}:
      {==}
    case P.Tail{ks, x}:
      {==}
    case P.Unique{ks, x}:
      {==}
    case P.GroupBy{ks, ags, mo, x}:
      {==}
    case P.Join{how, lo, ro, l, r}:
      {==}
    case P.Concat{ci, l, r}:
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
      %Equal.sym(P.Plan, P.Opt.merge(x), x, Laws.merge_fixed_point(x, L.and_right(Bool.not(Laws.is_filter(x)), Laws.no_adjacent_filters(x), h))) : {P.Opt.merge.f(e, _) == P.Filter{e, x} : P.Plan}
      mergef_plain(e, x, L.not_true(Laws.is_filter(x), L.and_left(Bool.not(Laws.is_filter(x)), Laws.no_adjacent_filters(x), h)))
    case P.Sort{ks, x}:
      %Laws.merge_fixed_point(x, h) : {P.Sort{ks, P.Opt.merge(x)} == P.Sort{ks, _} : P.Plan}
      {==}
    case P.Drop{ks, x}:
      %Laws.merge_fixed_point(x, h) : {P.Drop{ks, P.Opt.merge(x)} == P.Drop{ks, _} : P.Plan}
      {==}
    case P.Rename{ks, x}:
      %Laws.merge_fixed_point(x, h) : {P.Rename{ks, P.Opt.merge(x)} == P.Rename{ks, _} : P.Plan}
      {==}
    case P.Slice{ks, kl, x}:
      %Laws.merge_fixed_point(x, h) : {P.Slice{ks, kl, P.Opt.merge(x)} == P.Slice{ks, kl, _} : P.Plan}
      {==}
    case P.Tail{ks, x}:
      %Laws.merge_fixed_point(x, h) : {P.Tail{ks, P.Opt.merge(x)} == P.Tail{ks, _} : P.Plan}
      {==}
    case P.Unique{ks, x}:
      %Laws.merge_fixed_point(x, h) : {P.Unique{ks, P.Opt.merge(x)} == P.Unique{ks, _} : P.Plan}
      {==}
    case P.GroupBy{ks, ags, mo, x}:
      %Laws.merge_fixed_point(x, h) : {P.GroupBy{ks, ags, mo, P.Opt.merge(x)} == P.GroupBy{ks, ags, mo, _} : P.Plan}
      {==}
    case P.Join{how, lo, ro, +l, +r}:
      %Laws.merge_fixed_point(l, L.and_left(Laws.no_adjacent_filters(l), Laws.no_adjacent_filters(r), h)) : {P.Join{how, lo, ro, P.Opt.merge(l), P.Opt.merge(r)} == P.Join{how, lo, ro, _, r} : P.Plan}
      %Laws.merge_fixed_point(r, L.and_right(Laws.no_adjacent_filters(l), Laws.no_adjacent_filters(r), h)) : {P.Join{how, lo, ro, P.Opt.merge(l), P.Opt.merge(r)} == P.Join{how, lo, ro, P.Opt.merge(l), _} : P.Plan}
      {==}
    case P.Concat{ci, +l, +r}:
      %Laws.merge_fixed_point(l, L.and_left(Laws.no_adjacent_filters(l), Laws.no_adjacent_filters(r), h)) : {P.Concat{ci, P.Opt.merge(l), P.Opt.merge(r)} == P.Concat{ci, _, r} : P.Plan}
      %Laws.merge_fixed_point(r, L.and_right(Laws.no_adjacent_filters(l), Laws.no_adjacent_filters(r), h)) : {P.Concat{ci, P.Opt.merge(l), P.Opt.merge(r)} == P.Concat{ci, P.Opt.merge(l), _} : P.Plan}
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
    case P.Drop{ks, +x}:
      hwrap_nah(n, P.Drop{ks, P.Opt.head(x, None{})}, {==}, Laws.head_pass_merges(x, None{}))
    case P.Rename{ks, +x}:
      hwrap_nah(n, P.Rename{ks, P.Opt.head(x, None{})}, {==}, Laws.head_pass_merges(x, None{}))
    case P.Slice{ks, kl, +x}:
      hwrap_nah(n, P.Slice{ks, kl, P.Opt.head(x, None{})}, {==}, Laws.head_pass_merges(x, None{}))
    case P.Tail{ks, +x}:
      hwrap_nah(n, P.Tail{ks, P.Opt.head(x, None{})}, {==}, Laws.head_pass_merges(x, None{}))
    case P.Unique{ks, +x}:
      hwrap_nah(n, P.Unique{ks, P.Opt.head(x, None{})}, {==}, Laws.head_pass_merges(x, None{}))
    case P.GroupBy{ks, ags, mo, +x}:
      hwrap_nah(n, P.GroupBy{ks, ags, mo, P.Opt.head(x, None{})}, {==}, Laws.head_pass_merges(x, None{}))
    case P.Join{how, lo, ro, +l, +r}:
      hwrap_nah(n, P.Join{how, lo, ro, P.Opt.head(l, None{}), P.Opt.head(r, None{})}, {==}, L.and_true(Laws.no_adjacent_heads(P.Opt.head(l, None{})), Laws.no_adjacent_heads(P.Opt.head(r, None{})), Laws.head_pass_merges(l, None{}), Laws.head_pass_merges(r, None{})))
    case P.Concat{ci, +l, +r}:
      hwrap_nah(n, P.Concat{ci, P.Opt.head(l, None{}), P.Opt.head(r, None{})}, {==}, L.and_true(Laws.no_adjacent_heads(P.Opt.head(l, None{})), Laws.no_adjacent_heads(P.Opt.head(r, None{})), Laws.head_pass_merges(l, None{}), Laws.head_pass_merges(r, None{})))
    case P.Head{m, x}:
      Laws.head_pass_merges(x, Some{P.Opt.hmin(m, n)})
