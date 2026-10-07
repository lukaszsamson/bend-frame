# p08: schema laws. The human states them; PROOF.bend proves them.
import Base
import ./main.bend as S

# LAW: a filter never changes the schema of a well-typed plan
law filter_keeps_schema:
  for p: S.Plan
  for +s: List<&2, S.Field>
  for e: S.Expr
  for ok: {S.schema_of(p) == Some{s} : Maybe<&2, List<&2, S.Field>>}
  for t: {S.Expr.type(e, s) == Some{S.TBool{}} : Maybe<&2, S.DType>}
  {S.schema_of(S.Filter{e, p}) == Some{s} : Maybe<&2, List<&2, S.Field>>}

# LAW: selecting from a plan is projecting its schema
law select_is_project:
  for p: S.Plan
  for +s: List<&2, S.Field>
  for names: List<&2, String>
  for ok: {S.schema_of(p) == Some{s} : Maybe<&2, List<&2, S.Field>>}
  {S.schema_of(S.Select{names, p}) == S.Schema.project(names, s) : Maybe<&2, List<&2, S.Field>>}

# LAW: a projection, when it succeeds, has as many fields as names
law project_length:
  for names: List<&2, String>
  for +s: List<&2, S.Field>
  for out: List<&2, S.Field>
  for ok: {S.Schema.project(names, s) == Some{out} : Maybe<&2, List<&2, S.Field>>}
  {List.length(&2, S.Field, out) == List.length(&2, String, names) : Nat}
