# PROOF_schema.bend -- proofs of LAWS.bend section 1 (schema operations).
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
# 1. Schema operations
# =====================================================================================

def Laws.project_nil(s):
  {==}

# Schema.project.chk(r) == Done{out} needs r == Done{out}: the duplicate check
# only ever turns a Done into a Fail
def chk_dup_inv(d: Maybe<&2, String>, -fs: List<&2, S.Field>, -out: List<&2, S.Field>, h: {S.Schema.project.dup(d, fs) == Done{out} : E.Res(List<&2, S.Field>)}) -> {Done{fs} == Done{out} : E.Res(List<&2, S.Field>)}:
  match d:
    case Some{n}:
      Empty.absurd({Done{fs} == Done{out} : E.Res(List<&2, S.Field>)}, L.fail_done(List<&2, S.Field>, E.DuplicateColumn{n}, out, h))
    case None{}:
      h

def chk_inv(r: E.Res(List<&2, S.Field>), -out: List<&2, S.Field>, h: {S.Schema.project.chk(r) == Done{out} : E.Res(List<&2, S.Field>)}) -> {r == Done{out} : E.Res(List<&2, S.Field>)}:
  match r:
    case Fail{e}:
      Empty.absurd({Fail{e} == Done{out} : E.Res(List<&2, S.Field>)}, L.fail_done(List<&2, S.Field>, e, out, h))
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
      %L.done_inj(List<&2, S.Field>, S.Field{n, d} <> fs, out, ok) : {List.length(&2, S.Field, _) == 1n+List.length(&2, String, rest) : Nat}
      %ih(fs, {==}) : {1n+List.length(&2, S.Field, fs) == 1n+_ : Nat}
      {==}
    case Some{d} Fail{e}:
      Empty.absurd({List.length(&2, S.Field, out) == 1n+List.length(&2, String, rest) : Nat}, L.fail_done(List<&2, S.Field>, e, out, ok))
    case None{} Done{fs}:
      Empty.absurd({List.length(&2, S.Field, out) == 1n+List.length(&2, String, rest) : Nat}, L.fail_done(List<&2, S.Field>, E.ColumnNotFound{n}, out, ok))
    case None{} Fail{e}:
      Empty.absurd({List.length(&2, S.Field, out) == 1n+List.length(&2, String, rest) : Nat}, L.fail_done(List<&2, S.Field>, E.ColumnNotFound{n}, out, ok))

def project_go_length(names: List<&2, String>, +s: List<&2, S.Field>, -out: List<&2, S.Field>, ok: {S.Schema.project.go(names, s) == Done{out} : E.Res(List<&2, S.Field>)}) -> {List.length(&2, S.Field, out) == List.length(&2, String, names) : Nat}:
  match names:
    case Nil{}:
      %L.done_inj(List<&2, S.Field>, Nil{}, out, ok) : {List.length(&2, S.Field, _) == 0n : Nat}
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
      %L.done_inj(List<&2, S.Field>, S.Field{n, d} <> fs, out, ok) : {S.Schema.names(_) == n <> rest : List<&2, String>}
      %ih(fs, {==}) : {n <> S.Schema.names(fs) == n <> _ : List<&2, String>}
      {==}
    case Some{d} Fail{e}:
      Empty.absurd({S.Schema.names(out) == n <> rest : List<&2, String>}, L.fail_done(List<&2, S.Field>, e, out, ok))
    case None{} Done{fs}:
      Empty.absurd({S.Schema.names(out) == n <> rest : List<&2, String>}, L.fail_done(List<&2, S.Field>, E.ColumnNotFound{n}, out, ok))
    case None{} Fail{e}:
      Empty.absurd({S.Schema.names(out) == n <> rest : List<&2, String>}, L.fail_done(List<&2, S.Field>, E.ColumnNotFound{n}, out, ok))

def project_go_names(names: List<&2, String>, +s: List<&2, S.Field>, -out: List<&2, S.Field>, ok: {S.Schema.project.go(names, s) == Done{out} : E.Res(List<&2, S.Field>)}) -> {S.Schema.names(out) == names : List<&2, String>}:
  match names:
    case Nil{}:
      %L.done_inj(List<&2, S.Field>, Nil{}, out, ok) : {S.Schema.names(_) == Nil{} : List<&2, String>}
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
