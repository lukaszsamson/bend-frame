# T6 coverage: the plan-level API: empty_env, source, add_source, validate_bindings, collect_raw,
# collect, collect_full, collect_show, collect_schema, schema_show, explain, optimize, optimize_full.
# Cases: plans over a frame with nulls, over zero rows and over a zero-column frame; the three collects
# against the eager answer (equal dumps: R.four.text prints the eager dump and `raw same, opt same,
# full same`); collect_schema against the eager result's own schema; explain / optimize / optimize_full
# as text (the rewrites reasoned from DESIGN.md 15.2.8: Head merging in the release optimiser, filter
# merge / pushdown / projection pruning only in optimize_full) with the plans still collecting to the
# eager result; the binding errors (missing, bound twice, schema differs) and the plan errors that come
# before them, as DESIGN.md 15.7 orders them.
# Expectations are reasoned from DESIGN.md 15.2.2, 15.2.8, 15.7, 15.9 and the eager answers (the data of
# these cases is the Polars-confirmed verbs of verbs_basic.bend); explain text is Bend's own format
# (DESIGN 15.2.8 lists the node lines), so there is no Polars twin for this file.
#@ cover empty_env,source,add_source success null empty eager lazy
#@ cover validate_bindings,collect_raw,collect,collect_full,collect_show,collect_schema success null empty invalid eager lazy
#@ cover schema_show success null empty invalid eager lazy
#@ cover explain,optimize,optimize_full success null empty invalid eager lazy
#@ cover select,filter,head,lazy_select,lazy_filter,lazy_head,lazy_with_columns,lazy_sort,lazy_group_by,lazy_inner_join,lazy_left_join,lazy_semi_join,lazy_anti_join,lazy_drop,lazy_rename,lazy_slice,lazy_tail,lazy_unique,lazy_concat_vertical success null empty eager lazy
#@ na empty_env,source,add_source,explain,optimize,optimize_full invalid -- building an environment, a Source plan or a plan tree cannot fail (a bad plan is reported by collect_schema / validate_bindings / collect, covered)
#@ na empty_env,source,add_source,explain,optimize,optimize_full null -- an environment / plan tree holds no cell values: nulls are in the frames the cases bind (covered by the collect cases)
#@ na explain,optimize,optimize_full empty -- the plan text is the same whatever rows its sources hold; the zero-row sources are collected in the collect cases and the empty concat plan is explained
#@ na empty_env,source,add_source,validate_bindings,collect_schema,explain,optimize,optimize_full,schema_show,collect_show,lazy_select,lazy_with_columns,lazy_filter,lazy_head,lazy_sort,lazy_group_by,lazy_inner_join,lazy_left_join,lazy_semi_join,lazy_anti_join,lazy_drop,lazy_rename,lazy_slice,lazy_tail,lazy_unique,lazy_concat_vertical zerocol -- not meaningful to count: a zero-column frame is one of the collect cases below
import Base
import ./../../frame.bend as DF
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./../../src/expr.bend as X
import ./../../src/schema.bend as S
import ./../regress/lib/rx.bend as R
import ./lib/fx.bend as FX

# pm (5 rows): id u32 1..5   g str "x" "y" "x" null "y"   v f32 1.5 null 3.0 NaN 0.5
def pm() -> E.ResT(C.Frame):
  R.frame([
    R.mk("id", [R.u(1), R.u(2), R.u(3), R.u(4), R.u(5)], DF.t_u32()),
    R.mk("g", [R.s("x"), R.s("y"), R.s("x"), R.null(), R.s("y")], DF.t_str()),
    R.mk("v", [R.f(1.5), R.null(), R.f(3.0), R.f(R.nan()), R.f(0.5)], DF.t_f32())])

def pz() -> E.ResT(C.Frame):
  R.frame([R.mk("id", [], DF.t_u32()), R.mk("g", [], DF.t_str()), R.mk("v", [], DF.t_f32())])

# pu (3 rows): g str "x" "y" "z"   w i32 10 20 30
def pu() -> E.ResT(C.Frame):
  R.frame([R.mk("g", [R.s("x"), R.s("y"), R.s("z")], DF.t_str()), R.mk("w", [R.i(10), R.i(20), R.i(30)], DF.t_i32())])

def env.k(r: P.Env & P.Plan) -> P.Env:
  (env, p) = r
  env

def plan.k(r: P.Env & P.Plan) -> P.Plan:
  (env, p) = r
  p

# the environment and the Source plan DF.source / DF.add_source make of a frame (an error gives empty)
def e1(+n: String, r: E.ResT(C.Frame)) -> P.Env:
  match r:
    case Fail{e}:
      DF.empty_env()
    case Done{f}:
      env.k(DF.source(n, f))

def p1(+n: String, r: E.ResT(C.Frame)) -> P.Plan:
  match r:
    case Fail{e}:
      P.Source{n, Nil{}}
    case Done{f}:
      plan.k(DF.source(n, f))

def e2(env: P.Env, +n: String, r: E.ResT(C.Frame)) -> P.Env:
  match r:
    case Fail{e}:
      env
    case Done{f}:
      env.k(DF.add_source(env, n, f))

def p2(env: P.Env, +n: String, r: E.ResT(C.Frame)) -> P.Plan:
  match r:
    case Fail{e}:
      P.Source{n, Nil{}}
    case Done{f}:
      plan.k(DF.add_source(env, n, f))

def ep() -> P.Env:
  e1("p", pm())

def epu() -> P.Env:
  e2(e1("p", pm()), "u", pu())

def ez() -> P.Env:
  e1("z", pz())

def sp() -> P.Plan:
  p1("p", pm())

def sz() -> P.Plan:
  p1("z", pz())

def su() -> P.Plan:
  p2(DF.empty_env(), "u", pu())

def c(+n: String) -> DF.Expr():
  DF.col(n)

def al(e: DF.Expr(), +n: String) -> DF.Expr():
  DF.alias(e, n)

# eager answer against DF.collect_raw, DF.collect and DF.collect_full of the plan (an env each)
def three(+tag: String, eager: E.ResT(C.Frame), +p: P.Plan, e_raw: P.Env, e_opt: P.Env, e_full: P.Env) -> IO(Unit):
  do IO<Unit>:
    r1 : E.ResT(C.Frame) <- DF.collect_raw(p, e_raw)
    r2 : E.ResT(C.Frame) <- DF.collect(p, e_opt)
    r3 : E.ResT(C.Frame) <- DF.collect_full(p, e_full)
    IO.print(R.four.text(tag, DF.dump(eager), DF.dump(r1), DF.dump(r2), DF.dump(r3)) ++ "\n")

# the lazy runs only (no eager twin): the raw dump once, then whether DF.collect and DF.collect_full dump the same
def lazy3.k(+tag: String, +d1: String, +d2: String, +d3: String) -> String:
  R.four.text(tag, d1, d1, d2, d3) ++ "\n"

def lazy3(+tag: String, +p: P.Plan, e_raw: P.Env, e_opt: P.Env, e_full: P.Env) -> IO(Unit):
  do IO<Unit>:
    r1 : E.ResT(C.Frame) <- DF.collect_raw(p, e_raw)
    r2 : E.ResT(C.Frame) <- DF.collect(p, e_opt)
    r3 : E.ResT(C.Frame) <- DF.collect_full(p, e_full)
    IO.print(lazy3.k(tag, DF.dump(r1), DF.dump(r2), DF.dump(r3)))

# the eager twins: the same verbs, one after the other, through DF.then
def v_gt1() -> DF.Expr():
  DF.gt(DF.col("v"), DF.lit_f32(1.0))

def v2() -> List<&2, DF.Expr()>:
  [DF.col("id"), DF.alias(DF.mul(DF.col("v"), DF.lit_f32(2.0)), "v2")]

def eager1(r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  DF.then(DF.then(r, f => DF.filter(f, v_gt1())), f => DF.select(f, v2()))

def eager2(r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  DF.then(DF.then(r, f => DF.sort(f, [DF.desc("v")])), f => DF.head(f, 3))

def eager3(r: E.ResT(C.Frame), u: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  DF.then(r, f => DF.then(u, g => DF.left_join(f, g, ["g"], ["g"])))

def eager4(r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  DF.then(r, f => DF.head(f, 3))

def eager5(r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  DF.then(DF.then(DF.then(r, f => DF.select(f, [DF.col("id"), DF.col("v")])), f => DF.filter(f, DF.gt(DF.col("id"), DF.lit_u32(1)))), f => DF.filter(f, DF.gt(DF.col("v"), DF.lit_f32(0.0))))

def eager_schema.k(x: C.Frame & DF.Schema()) -> String:
  (f, s) = x
  DF.schema_show(Done{s})

def eager_schema(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ DF.err_show(e)
    case Done{f}:
      eager_schema.k(DF.schema(f))

# collect_schema of the plan and the schema of the eager result: they must be the same text
def schemas(+tag: String, +p: P.Plan, eager: E.ResT(C.Frame)) -> IO(Unit):
  IO.print("-- " ++ tag ++ "\nplan:  " ++ DF.schema_show(DF.collect_schema(p)) ++ "\neager: " ++ eager_schema(eager) ++ "\n\n")

def validate.show(x: P.Env & E.Res(Unit)) -> String:
  (env, r) = x
  match r:
    case Fail{e}:
      "error: " ++ DF.err_show(e)
    case Done{u}:
      "ok"

def validate(+tag: String, +p: P.Plan, env: P.Env) -> IO(Unit):
  IO.print("-- " ++ tag ++ "\n" ++ validate.show(DF.validate_bindings(p, env)) ++ "\n\n")

def explain2(+tag: String, +p: P.Plan) -> IO(Unit):
  IO.print("-- " ++ tag ++ "\n" ++ DF.explain(p) ++ "\n-- optimize\n" ++ DF.explain(DF.optimize(p)) ++ "\n-- optimize_full\n" ++ DF.explain(DF.optimize_full(p)) ++ "\n\n")

def main() -> IO(Unit):
  do IO<Unit>:
    three("filter select with nulls", eager1(pm()), DF.lazy_select(DF.lazy_filter(sp(), DF.gt(c("v"), DF.lit_f32(1.0))), [c("id"), al(DF.mul(c("v"), DF.lit_f32(2.0)), "v2")]), ep(), ep(), ep())
    three("head of a sorted plan", eager2(pm()), DF.lazy_head(DF.lazy_sort(sp(), [DF.desc("v")]), 3), ep(), ep(), ep())
    three("zero rows through select and filter", eager1(pz()), DF.lazy_select(DF.lazy_filter(sz(), DF.gt(c("v"), DF.lit_f32(1.0))), [c("id"), al(DF.mul(c("v"), DF.lit_f32(2.0)), "v2")]), ez(), ez(), ez())
    three("a zero-column source", DF.then(R.zcols(4), f => DF.head(f, 2)), DF.lazy_head(p1("z0", R.zcols(4)), 2), e1("z0", R.zcols(4)), e1("z0", R.zcols(4)), e1("z0", R.zcols(4)))
    three("join two sources", eager3(pm(), pu()), DF.lazy_left_join(sp(), su(), ["g"], ["g"]), epu(), epu(), epu())
    three("invalid select of a missing column", DF.then(pm(), f => DF.select(f, [c("nope")])), DF.lazy_select(sp(), [c("nope")]), ep(), ep(), ep())
    lazy3("invalid binding: a missing source (collect reports it)", P.Source{"nope", Nil{}}, ep(), ep(), ep())
    r4 : E.ResT(C.Frame) <- DF.collect(DF.lazy_head(sp(), 2), ep())
    IO.print("-- show of a collected frame with nulls\n" ++ DF.show(r4) ++ "\n\n")
    s1 : String <- DF.collect_show(DF.lazy_head(sp(), 2), ep())
    IO.print("-- collect_show of a plan\n" ++ s1 ++ "\n\n")
    s2 : String <- DF.collect_show(sz(), ez())
    IO.print("-- collect_show of zero rows\n" ++ s2 ++ "\n\n")
    s3 : String <- DF.collect_show(DF.lazy_select(sp(), [c("nope")]), ep())
    IO.print("-- collect_show of an invalid plan\n" ++ s3 ++ "\n\n")
    schemas("collect_schema of a select with a cast", DF.lazy_select(sp(), [c("id"), al(DF.cast_f32(c("id")), "idf"), al(DF.is_null(c("g")), "gn")]), DF.then(pm(), f => DF.select(f, [c("id"), al(DF.cast_f32(c("id")), "idf"), al(DF.is_null(c("g")), "gn")])))
    schemas("collect_schema of a group_by", DF.lazy_group_by(sp(), [c("g")], [DF.sum(c("id")), al(DF.mean(c("v")), "vm")]), DF.then(pm(), f => DF.group_by(f, [c("g")], [DF.sum(c("id")), al(DF.mean(c("v")), "vm")])))
    schemas("collect_schema of a join renames a clashing column", DF.lazy_inner_join(sp(), DF.lazy_rename(su(), [("w", "v")]), ["g"], ["g"]), DF.then(pm(), f => DF.then(DF.then(pu(), u => DF.rename(u, [("w", "v")])), g => DF.inner_join(f, g, ["g"], ["g"]))))
    schemas("collect_schema over zero rows is the same schema", DF.lazy_filter(sz(), DF.gt(c("v"), DF.lit_f32(0.0))), DF.then(pz(), f => DF.filter(f, DF.gt(c("v"), DF.lit_f32(0.0)))))
    schemas("invalid collect_schema: a missing column", DF.lazy_select(sp(), [c("nope")]), DF.then(pm(), f => DF.select(f, [c("nope")])))
    schemas("invalid collect_schema: a type error", DF.lazy_with_columns(sp(), [DF.add(c("id"), c("v"))]), DF.then(pm(), f => DF.with_columns(f, [DF.add(c("id"), c("v"))])))
    schemas("invalid collect_schema: concat of no plans", DF.lazy_concat_vertical([]), DF.concat_vertical([]))
    validate("validate_bindings: every source bound", DF.lazy_inner_join(sp(), su(), ["g"], ["g"]), epu())
    validate("validate_bindings: a zero-row source", sz(), ez())
    validate("validate_bindings: a plan with no Source (a scan with a given schema) needs no binding", DF.scan_csv_schema("no/such/file.csv", DF.csv_opts(',', True{}, 100), [S.Field{"a", DF.t_u32()}]), DF.empty_env())
    validate("invalid validate_bindings: a source missing from the env", DF.lazy_inner_join(sp(), su(), ["g"], ["g"]), ep())
    validate("invalid validate_bindings: a name bound twice", sp(), e2(ep(), "p", pm()))
    validate("invalid validate_bindings: a source whose data differs from the plan", sz(), e1("z", pu()))
    validate("invalid validate_bindings: an empty env", sp(), DF.empty_env())
    explain2("explain: head merging", DF.lazy_head(DF.lazy_head(DF.lazy_head(sp(), 5), 3), 4))
    explain2("explain: filter merge and pushdown", DF.lazy_filter(DF.lazy_filter(DF.lazy_select(sp(), [c("id"), c("v")]), DF.gt(c("id"), DF.lit_u32(1))), DF.gt(c("v"), DF.lit_f32(0.0))))
    explain2("explain: projection pruning below a select", DF.lazy_select(DF.lazy_with_columns(sp(), [al(DF.add(c("id"), DF.lit_u32(1)), "id1")]), [c("id1")]))
    explain2("explain: sort and group_by", DF.lazy_group_by(DF.lazy_sort(sp(), [DF.asc("g")]), [c("g")], [DF.len(), al(DF.max(c("v")), "vmax")]))
    explain2("explain: every join", DF.lazy_anti_join(DF.lazy_semi_join(DF.lazy_left_join(DF.lazy_inner_join(sp(), su(), ["g"], ["g"]), su(), ["g"], ["g"]), su(), ["g"], ["g"]), su(), ["g"], ["g"]))
    explain2("explain: table verbs", DF.lazy_unique(DF.lazy_rename(DF.lazy_drop(DF.lazy_tail(DF.lazy_slice(sp(), 1, 3), 2), ["v"]), [("g", "key")]), []))
    explain2("explain: concat", DF.lazy_concat_vertical([sp(), DF.lazy_head(sp(), 1), sp()]))
    explain2("explain: concat of no plans", DF.lazy_concat_vertical([]))
    explain2("explain: a head above a row-wise select (the sink the optimiser certifies)", DF.lazy_head(DF.lazy_select(sp(), [c("id"), al(DF.mul(c("v"), DF.lit_f32(2.0)), "v2")]), 2))
    explain2("explain: a head above a literal select is a barrier", DF.lazy_head(DF.lazy_select(sp(), [al(DF.lit_u32(1), "one")]), 0))
    three("the optimised plans still collect to the eager answer: head merging", eager4(pm()), DF.lazy_head(DF.lazy_head(DF.lazy_head(sp(), 5), 3), 4), ep(), ep(), ep())
    three("the optimised plans still collect to the eager answer: pushdown", eager5(pm()), DF.lazy_filter(DF.lazy_filter(DF.lazy_select(sp(), [c("id"), c("v")]), DF.gt(c("id"), DF.lit_u32(1))), DF.gt(c("v"), DF.lit_f32(0.0))), ep(), ep(), ep())
#|-- filter select with nulls
#|frame
#|height	3
#|width	2
#|col	u32	"id"
#|col	f32	"v2"
#|row	1	0x40400000
#|row	3	0x40c00000
#|row	4	0x7fc00000
#|raw same, opt same, full same
#|
#|
#|-- head of a sorted plan
#|frame
#|height	3
#|width	3
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|row	2	"y"	null
#|row	4	null	0x7fc00000
#|row	3	"x"	0x40400000
#|raw same, opt same, full same
#|
#|
#|-- zero rows through select and filter
#|frame
#|height	0
#|width	2
#|col	u32	"id"
#|col	f32	"v2"
#|raw same, opt same, full same
#|
#|
#|-- a zero-column source
#|frame
#|height	2
#|width	0
#|raw same, opt same, full same
#|
#|
#|-- join two sources
#|frame
#|height	5
#|width	4
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|col	i32	"w"
#|row	1	"x"	0x3fc00000	10
#|row	2	"y"	null	20
#|row	3	"x"	0x40400000	10
#|row	4	null	0x7fc00000	null
#|row	5	"y"	0x3f000000	20
#|raw same, opt same, full same
#|
#|
#|-- invalid select of a missing column
#|error	ColumnNotFound: nope
#|raw same, opt same, full same
#|
#|
#|-- invalid binding: a missing source (collect reports it)
#|error	InvalidOperation: source not in env: nope
#|raw same, opt same, full same
#|
#|
#|-- show of a collected frame with nulls
#|shape: (2, 3)
#|+-----+-----+-----+
#|| id  | g   | v   |
#|| --- | --- | --- |
#|| u32 | str | f32 |
#|+=====+=====+=====+
#|| 1   | x   | 1.5 |
#|| 2   | y   |     |
#|+-----+-----+-----+
#|
#|
#|-- collect_show of a plan
#|shape: (2, 3)
#|+-----+-----+-----+
#|| id  | g   | v   |
#|| --- | --- | --- |
#|| u32 | str | f32 |
#|+=====+=====+=====+
#|| 1   | x   | 1.5 |
#|| 2   | y   |     |
#|+-----+-----+-----+
#|
#|
#|-- collect_show of zero rows
#|shape: (0, 3)
#|+-----+-----+-----+
#|| id  | g   | v   |
#|| --- | --- | --- |
#|| u32 | str | f32 |
#|+=====+=====+=====+
#|+-----+-----+-----+
#|
#|
#|-- collect_show of an invalid plan
#|error: ColumnNotFound: nope
#|
#|
#|-- collect_schema of a select with a cast
#|plan:  id:u32, idf:f32, gn:bool
#|eager: id:u32, idf:f32, gn:bool
#|
#|
#|-- collect_schema of a group_by
#|plan:  g:str, id:u32, vm:f32
#|eager: g:str, id:u32, vm:f32
#|
#|
#|-- collect_schema of a join renames a clashing column
#|plan:  id:u32, g:str, v:f32, v_right:i32
#|eager: id:u32, g:str, v:f32, v_right:i32
#|
#|
#|-- collect_schema over zero rows is the same schema
#|plan:  id:u32, g:str, v:f32
#|eager: id:u32, g:str, v:f32
#|
#|
#|-- invalid collect_schema: a missing column
#|plan:  error: ColumnNotFound: nope
#|eager: error: ColumnNotFound: nope
#|
#|
#|-- invalid collect_schema: a type error
#|plan:  error: TypeMismatch in add: expected u32, got f32
#|eager: error: TypeMismatch in add: expected u32, got f32
#|
#|
#|-- invalid collect_schema: concat of no plans
#|plan:  error: InvalidOperation: concat_vertical: no inputs
#|eager: error: InvalidOperation: concat_vertical: no inputs
#|
#|
#|-- validate_bindings: every source bound
#|ok
#|
#|
#|-- validate_bindings: a zero-row source
#|ok
#|
#|
#|-- validate_bindings: a plan with no Source (a scan with a given schema) needs no binding
#|ok
#|
#|
#|-- invalid validate_bindings: a source missing from the env
#|error: InvalidOperation: source not in env: u
#|
#|
#|-- invalid validate_bindings: a name bound twice
#|error: InvalidOperation: source bound twice in env: p
#|
#|
#|-- invalid validate_bindings: a source whose data differs from the plan
#|error: InvalidOperation: source z: data schema [g:str, w:i32] differs from the plan's [id:u32, g:str, v:f32]
#|
#|
#|-- invalid validate_bindings: an empty env
#|error: InvalidOperation: source not in env: p
#|
#|
#|-- explain: head merging
#|HEAD 4
#|  HEAD 3
#|    HEAD 5
#|      SOURCE p [id:u32, g:str, v:f32]
#|-- optimize
#|HEAD 3
#|  SOURCE p [id:u32, g:str, v:f32]
#|-- optimize_full
#|HEAD 3
#|  SOURCE p [id:u32, g:str, v:f32]
#|
#|
#|-- explain: filter merge and pushdown
#|FILTER (col("v") > lit(0))
#|  FILTER (col("id") > lit(1))
#|    SELECT [col("id"), col("v")]
#|      SOURCE p [id:u32, g:str, v:f32]
#|-- optimize
#|FILTER (col("v") > lit(0))
#|  FILTER (col("id") > lit(1))
#|    SELECT [col("id"), col("v")]
#|      SOURCE p [id:u32, g:str, v:f32]
#|-- optimize_full
#|SELECT [col("id"), col("v")]
#|  FILTER ((col("id") > lit(1)) & (col("v") > lit(0)))
#|    SELECT [col("id"), col("v")]
#|      SOURCE p [id:u32, g:str, v:f32]
#|
#|
#|-- explain: projection pruning below a select
#|SELECT [col("id1")]
#|  WITH_COLUMNS [(col("id") + lit(1)).alias("id1")]
#|    SOURCE p [id:u32, g:str, v:f32]
#|-- optimize
#|SELECT [col("id1")]
#|  WITH_COLUMNS [(col("id") + lit(1)).alias("id1")]
#|    SOURCE p [id:u32, g:str, v:f32]
#|-- optimize_full
#|SELECT [col("id1")]
#|  WITH_COLUMNS [(col("id") + lit(1)).alias("id1")]
#|    SELECT [col("id")]
#|      SOURCE p [id:u32, g:str, v:f32]
#|
#|
#|-- explain: sort and group_by
#|GROUP_BY [col("g")] AGG [lit(1).len(), col("v").max().alias("vmax")] MAINTAIN_ORDER
#|  SORT BY [col("g")]
#|    SOURCE p [id:u32, g:str, v:f32]
#|-- optimize
#|GROUP_BY [col("g")] AGG [lit(1).len(), col("v").max().alias("vmax")] MAINTAIN_ORDER
#|  SORT BY [col("g")]
#|    SOURCE p [id:u32, g:str, v:f32]
#|-- optimize_full
#|GROUP_BY [col("g")] AGG [lit(1).len(), col("v").max().alias("vmax")] MAINTAIN_ORDER
#|  SORT BY [col("g")]
#|    SELECT [col("g"), col("v")]
#|      SOURCE p [id:u32, g:str, v:f32]
#|
#|
#|-- explain: every join
#|ANTI JOIN ON [g = g]
#|  SEMI JOIN ON [g = g]
#|    LEFT JOIN ON [g = g]
#|      INNER JOIN ON [g = g]
#|        SOURCE p [id:u32, g:str, v:f32]
#|        SOURCE u [g:str, w:i32]
#|      SOURCE u [g:str, w:i32]
#|    SOURCE u [g:str, w:i32]
#|  SOURCE u [g:str, w:i32]
#|-- optimize
#|ANTI JOIN ON [g = g]
#|  SEMI JOIN ON [g = g]
#|    LEFT JOIN ON [g = g]
#|      INNER JOIN ON [g = g]
#|        SOURCE p [id:u32, g:str, v:f32]
#|        SOURCE u [g:str, w:i32]
#|      SOURCE u [g:str, w:i32]
#|    SOURCE u [g:str, w:i32]
#|  SOURCE u [g:str, w:i32]
#|-- optimize_full
#|ANTI JOIN ON [g = g]
#|  SEMI JOIN ON [g = g]
#|    LEFT JOIN ON [g = g]
#|      INNER JOIN ON [g = g]
#|        SOURCE p [id:u32, g:str, v:f32]
#|        SOURCE u [g:str, w:i32]
#|      SOURCE u [g:str, w:i32]
#|    SOURCE u [g:str, w:i32]
#|  SOURCE u [g:str, w:i32]
#|
#|
#|-- explain: table verbs
#|UNIQUE []
#|  RENAME [g -> key]
#|    DROP [v]
#|      TAIL 2
#|        SLICE 1 3
#|          SOURCE p [id:u32, g:str, v:f32]
#|-- optimize
#|UNIQUE []
#|  RENAME [g -> key]
#|    DROP [v]
#|      TAIL 2
#|        SLICE 1 3
#|          SOURCE p [id:u32, g:str, v:f32]
#|-- optimize_full
#|UNIQUE []
#|  RENAME [g -> key]
#|    DROP [v]
#|      TAIL 2
#|        SLICE 1 3
#|          SOURCE p [id:u32, g:str, v:f32]
#|
#|
#|-- explain: concat
#|CONCAT
#|  SOURCE p [id:u32, g:str, v:f32]
#|  HEAD 1
#|    SOURCE p [id:u32, g:str, v:f32]
#|  SOURCE p [id:u32, g:str, v:f32]
#|-- optimize
#|CONCAT
#|  SOURCE p [id:u32, g:str, v:f32]
#|  HEAD 1
#|    SOURCE p [id:u32, g:str, v:f32]
#|  SOURCE p [id:u32, g:str, v:f32]
#|-- optimize_full
#|CONCAT
#|  SOURCE p [id:u32, g:str, v:f32]
#|  HEAD 1
#|    SOURCE p [id:u32, g:str, v:f32]
#|  SOURCE p [id:u32, g:str, v:f32]
#|
#|
#|-- explain: concat of no plans
#|CONCAT
#|-- optimize
#|CONCAT
#|-- optimize_full
#|CONCAT
#|
#|
#|-- explain: a head above a row-wise select (the sink the optimiser certifies)
#|HEAD 2
#|  SELECT [col("id"), (col("v") * lit(2)).alias("v2")]
#|    SOURCE p [id:u32, g:str, v:f32]
#|-- optimize
#|HEAD 2
#|  SELECT [col("id"), (col("v") * lit(2)).alias("v2")]
#|    SOURCE p [id:u32, g:str, v:f32]
#|-- optimize_full
#|SELECT [col("id"), (col("v") * lit(2)).alias("v2")]
#|  HEAD 2
#|    SELECT [col("id"), col("v")]
#|      SOURCE p [id:u32, g:str, v:f32]
#|
#|
#|-- explain: a head above a literal select is a barrier
#|HEAD 0
#|  SELECT [lit(1).alias("one")]
#|    SOURCE p [id:u32, g:str, v:f32]
#|-- optimize
#|HEAD 0
#|  SELECT [lit(1).alias("one")]
#|    SOURCE p [id:u32, g:str, v:f32]
#|-- optimize_full
#|HEAD 0
#|  SELECT [lit(1).alias("one")]
#|    SELECT [col("id")]
#|      SOURCE p [id:u32, g:str, v:f32]
#|
#|
#|-- the optimised plans still collect to the eager answer: head merging
#|frame
#|height	3
#|width	3
#|col	u32	"id"
#|col	str	"g"
#|col	f32	"v"
#|row	1	"x"	0x3fc00000
#|row	2	"y"	null
#|row	3	"x"	0x40400000
#|raw same, opt same, full same
#|
#|
#|-- the optimised plans still collect to the eager answer: pushdown
#|frame
#|height	3
#|width	2
#|col	u32	"id"
#|col	f32	"v"
#|row	3	0x40400000
#|row	4	0x7fc00000
#|row	5	0x3f000000
#|raw same, opt same, full same
#|
#|
