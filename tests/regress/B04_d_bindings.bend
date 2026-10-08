# B04-d: missing / duplicate bindings are found only while executing, and Env.take
# silently drops an older duplicate. DESIGN.md 15.7: collect checks, after Plan.schema,
# uniqueness over the whole env ("source bound twice in env: <name>"), then presence
# ("source not in env: <name>", which replaces "source not in env (or used twice)") and
# schema per Source in postfix order; collect_schema never looks at env. This also pins
# B04-f's counterexample to the README claim "collect refuses exactly what collect_schema
# refuses": the missing-binding plan has a schema and still fails at collect.
# DF.validate_bindings / DF.add_source are M1 API (pending/B04_d_validate_bindings.bend.txt).
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/schema.bend as S
import ./../../src/expr.bend as X
import ./../../src/join.bend as J
import ./../../src/groupby.bend as G
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def ta() -> E.ResT(C.Frame):
  R.frame([R.mk("a", [R.u(1), R.u(2)], D.TU32{})])

def tb() -> E.ResT(C.Frame):
  R.frame([R.mk("a", [R.u(7)], D.TU32{})])

def src() -> P.Plan:
  R.src("t", ta())

# t bound twice (a 2-row and a 1-row frame)
def twice() -> P.Env:
  R.env_add(R.env1("t", ta()), "t", tb())

def main() -> IO(Unit):
  do IO<Unit>:
    # missing: Source u, env holds only t
    R.lazy2("B04-d missing", DF.lazy_head(R.src("u", ta()), 5), R.env1("t", ta()), R.env1("t", ta()))
    IO.print(R.schema("B04-d missing", DF.lazy_head(R.src("u", ta()), 5)))
    # duplicate: t bound twice
    R.lazy2("B04-d duplicate", src(), twice(), twice())
    # duplicate wins over missing (uniqueness is checked first, over the whole env)
    R.lazy2("B04-d duplicate-before-missing", DF.lazy_inner_join(R.src("u", ta()), src(), ["a"], ["a"]), twice(), twice())
    # schema: env t is a:u32, the plan says a:str
    R.lazy2("B04-d schema", P.Source{"t", [S.Field{"a", D.TStr{}}]}, R.env1("t", ta()), R.env1("t", ta()))
#|-- B04-d missing raw
#|error	InvalidOperation: source not in env: u
#|
#|-- B04-d missing opt
#|error	InvalidOperation: source not in env: u
#|
#|-- B04-d missing schema
#|a:u32
#|
#|-- B04-d duplicate raw
#|error	InvalidOperation: source bound twice in env: t
#|
#|-- B04-d duplicate opt
#|error	InvalidOperation: source bound twice in env: t
#|
#|-- B04-d duplicate-before-missing raw
#|error	InvalidOperation: source bound twice in env: t
#|
#|-- B04-d duplicate-before-missing opt
#|error	InvalidOperation: source bound twice in env: t
#|
#|-- B04-d schema raw
#|error	InvalidOperation: source t: data schema [a:u32] differs from the plan's [a:str]
#|
#|-- B04-d schema opt
#|error	InvalidOperation: source t: data schema [a:u32] differs from the plan's [a:str]
#|
