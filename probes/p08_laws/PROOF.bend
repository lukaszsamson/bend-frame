# p08: the proofs. `%e : P` rewrites occurrences of e's RIGHT side (marked
# `_` in P) into its LEFT side, so a hypothesis `schema_of(p) == Some{s}`
# is flipped with Equal.sym before it replaces `schema_of(p)` in the goal.
# filter and select then unfold schema_of one step. project_length is an
# induction on the names: the two Maybe results of the step are passed to a
# lemma as PARAMETERS and matched there (a match cannot scrutinize a
# computed value); a None result clashes with Some{out} and is refuted
# through the motive `disc`.
import Base
import ./main.bend as S
import ./LAWS.bend as Laws

def Laws.filter_keeps_schema(p, s, e, ok, t):
  %Equal.sym(Maybe<&2, List<&2, S.Field>>, S.schema_of(p), Some{s}, ok) : {S.schema_of.filter(e, _) == Some{s} : Maybe<&2, List<&2, S.Field>>}
  %Equal.sym(Maybe<&2, S.DType>, S.Expr.type(e, s), Some{S.TBool{}}, t) : {S.schema_of.filter.if(s, _) == Some{s} : Maybe<&2, List<&2, S.Field>>}
  {==}

def Laws.select_is_project(p, s, names, ok):
  %Equal.sym(Maybe<&2, List<&2, S.Field>>, S.schema_of(p), Some{s}, ok) : {S.schema_of.select(names, _) == S.Schema.project(names, s) : Maybe<&2, List<&2, S.Field>>}
  {==}

# Some is injective: the payload, read through a default
def unsome(-xs: List<&2, S.Field>, -ys: List<&2, S.Field>, e: {Some{xs} == Some{ys} : Maybe<&2, List<&2, S.Field>>}) -> {xs == ys : List<&2, S.Field>}:
  Equal.cong(Maybe<&2, List<&2, S.Field>>, List<&2, S.Field>, m => Maybe.default(&2, List<&2, S.Field>, m, Nil{}), Some{xs}, Some{ys}, e)

# None is not Some: the motive sends None to Unit and Some to Empty
def disc(m: Maybe<&2, List<&2, S.Field>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_some(-out: List<&2, S.Field>, e: {None{} == Some{out} : Maybe<&2, List<&2, S.Field>>}) -> Empty:
  %e : disc(_)
  Unit{}

# one step: Schema.project.put(n, t, r) == Some{out} with the induction
# hypothesis ih for r
def step(-n: String, -rest: List<&2, String>, t: Maybe<&2, S.DType>, r: Maybe<&2, List<&2, S.Field>>, -out: List<&2, S.Field>,
  ok: {S.Schema.project.put(n, t, r) == Some{out} : Maybe<&2, List<&2, S.Field>>},
  ih: @o: List<&2, S.Field> -> {r == Some{o} : Maybe<&2, List<&2, S.Field>>} -> {List.length(&2, S.Field, o) == List.length(&2, String, rest) : Nat})
  -> {List.length(&2, S.Field, out) == 1n+List.length(&2, String, rest) : Nat}:
  match t r:
    case Some{t2} Some{+fs}:
      %unsome(S.Field{n, t2} <> fs, out, ok) : {List.length(&2, S.Field, _) == 1n+List.length(&2, String, rest) : Nat}
      %ih(fs, {==}) : {1n+List.length(&2, S.Field, fs) == 1n+_ : Nat}
      {==}
    case None{} Some{fs}:
      Empty.absurd({List.length(&2, S.Field, out) == 1n+List.length(&2, String, rest) : Nat}, none_some(out, ok))
    case Some{t2} None{}:
      Empty.absurd({List.length(&2, S.Field, out) == 1n+List.length(&2, String, rest) : Nat}, none_some(out, ok))
    case None{} None{}:
      Empty.absurd({List.length(&2, S.Field, out) == 1n+List.length(&2, String, rest) : Nat}, none_some(out, ok))

def Laws.project_length(names, s, out, ok):
  match names:
    case Nil{}:
      %unsome(Nil{}, out, ok) : {List.length(&2, S.Field, _) == 0n : Nat}
      {==}
    case +n <> +rest:
      step(n, rest, S.Schema.find(s, n), S.Schema.project(rest, s), out, ok, o => e => Laws.project_length(rest, s, o, e))
