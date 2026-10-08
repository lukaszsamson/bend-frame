# tests/regress/lib/rx.bend -- shared helpers of the defect regressions (plans/M_01.txt
# section 3, DESIGN.md 15.10). Not a test itself: its main prints nothing (the runner
# reports it as "PASS (no expect)").
#
# A regression builds its input frames with `mk` + `frame`, runs a scenario
#   eager      through the facade verbs (the `e_*` wrappers below pass a Fail through),
#   raw lazy   `Q.Exec.run(p, env)` (the plan as written),
#   opt lazy   `DF.collect(p, env)` (= Lazy.collect: optimise, then run),
# and prints the three results as `DF.dump` text (DESIGN.md 15.1) under the headers
#   -- <ID> <case> eager / raw / opt
# so a failing line names its defect row and case. `three` does the printing; the
# caller builds a fresh env for each lazy run (a frame is consumed by its run).
import Base
import ./../../../frame.bend as DF
import ./../../../src/dtype.bend as D
import ./../../../src/err.bend as E
import ./../../../src/column.bend as C
import ./../../../src/schema.bend as S
import ./../../../src/expr.bend as X
import ./../../../src/sort.bend as O
import ./../../../src/plan.bend as P
import ./../../../src/exec.bend as Q
import ./../../../src/csv.bend as V
import ./../../../src/dump.bend as Y

# ---- frames ------------------------------------------------------------------------

def mk.k(name: String, r: E.ResT(C.Column)) -> C.Named:
  match r:
    case Fail{e}:
      C.Named{E.Err.show(e), C.CU32{0, 0n, C.AllValid{}, [0 : U32*1n]}}
    case Done{c}:
      C.Named{name, c}

# a named column from scalars (SNull is a null row); a bad cell names the column
# after the error, so the dump shows it
def mk(name: String, xs: List<&2, D.Scalar>, +t: D.DType) -> C.Named:
  mk.k(name, C.Column.from_scalars(xs, t))

def frame(cols: List<&1, C.Named>) -> E.ResT(C.Frame):
  DF.from_columns(cols)

# a frame with no columns and height h (what `drop` of every column gives)
def zcols(h: U32) -> E.ResT(C.Frame):
  Done{C.Frame{h, Nil{}}}

def nan() -> F32:
  F32.div(0.0, 0.0)

def inf() -> F32:
  F32.div(1.0, 0.0)

def ninf() -> F32:
  F32.neg(F32.div(1.0, 0.0))

def nzero() -> F32:
  F32.neg(0.0)

def f(x: F32) -> D.Scalar:
  D.SF32{x}

def u(x: U32) -> D.Scalar:
  D.SU32{x}

def i(x: U32) -> D.Scalar:
  D.SI32{D.I32{x}}

def ineg(x: U32) -> D.Scalar:
  D.SI32{D.I32.neg(D.I32{x})}

def s(x: String) -> D.Scalar:
  D.SStr{x}

def b(x: Bool) -> D.Scalar:
  D.SBool{x}

def null() -> D.Scalar:
  D.SNull{}

# ---- lazy sources ------------------------------------------------------------------

def env.k(r: P.Env & P.Plan) -> P.Env:
  (env, p) = r
  env

def plan.k(r: P.Env & P.Plan) -> P.Plan:
  (env, p) = r
  p

# a one-frame env holding the frame under `name` (empty when the frame failed)
def env1(+name: String, r: E.ResT(C.Frame)) -> P.Env:
  match r:
    case Fail{e}:
      DF.empty_env()
    case Done{fr}:
      env.k(DF.source(name, fr))

# add a second frame to an env
def env_add(env: P.Env, +name: String, r: E.ResT(C.Frame)) -> P.Env:
  match r:
    case Fail{e}:
      env
    case Done{fr}:
      env.k(P.Env.add(env, name, fr))

# the Source plan of a frame (its schema), the frame itself is dropped
def src(+name: String, r: E.ResT(C.Frame)) -> P.Plan:
  match r:
    case Fail{e}:
      P.Source{name, Nil{}}
    case Done{fr}:
      plan.k(DF.source(name, fr))

# ---- eager verbs over a result (an error passes through) ----------------------------

def e_select(r: E.ResT(C.Frame), es: List<&2, X.Expr>) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{fr}:
      DF.select(fr, es)

def e_with(r: E.ResT(C.Frame), es: List<&2, X.Expr>) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{fr}:
      DF.with_columns(fr, es)

def e_filter(r: E.ResT(C.Frame), pred: X.Expr) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{fr}:
      DF.filter(fr, pred)

def e_head(r: E.ResT(C.Frame), n: U32) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{fr}:
      DF.head(fr, n)

def e_sort(r: E.ResT(C.Frame), ks: List<&2, O.SortKey>) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{fr}:
      DF.sort(fr, ks)

def e_group(r: E.ResT(C.Frame), keys: List<&2, X.Expr>, aggs: List<&2, X.Expr>) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{fr}:
      DF.group_by(fr, keys, aggs)

def e_inner.k(l: C.Frame, r: E.ResT(C.Frame), lo: List<&2, String>, ro: List<&2, String>) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{fr}:
      DF.inner_join(l, fr, lo, ro)

def e_inner(l: E.ResT(C.Frame), r: E.ResT(C.Frame), lo: List<&2, String>, ro: List<&2, String>) -> E.ResT(C.Frame):
  match l:
    case Fail{e}:
      Fail{e}
    case Done{fl}:
      e_inner.k(fl, r, lo, ro)

def e_left.k(l: C.Frame, r: E.ResT(C.Frame), lo: List<&2, String>, ro: List<&2, String>) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{fr}:
      DF.left_join(l, fr, lo, ro)

def e_left(l: E.ResT(C.Frame), r: E.ResT(C.Frame), lo: List<&2, String>, ro: List<&2, String>) -> E.ResT(C.Frame):
  match l:
    case Fail{e}:
      Fail{e}
    case Done{fl}:
      e_left.k(fl, r, lo, ro)

# ---- printing ----------------------------------------------------------------------

# the dump of a result, under a header naming the defect row and case
def show(+tag: String, how: String, r: E.ResT(C.Frame)) -> String:
  "-- " ++ tag ++ " " ++ how ++ "\n" ++ DF.dump(r)

# eager, raw-lazy and optimised-lazy dumps of one scenario
def three(+tag: String, eager: E.ResT(C.Frame), +p: P.Plan, env_raw: P.Env, env_opt: P.Env) -> IO(Unit):
  do IO<Unit>:
    r1 : E.ResT(C.Frame) <- Q.Exec.run(p, env_raw)
    r2 : E.ResT(C.Frame) <- DF.collect(p, env_opt)
    IO.print(show(tag, "eager", eager))
    IO.print(show(tag, "raw", r1))
    IO.print(show(tag, "opt", r2))

def agree.v(+d0: String, d: String) -> String:
  Bool.pick(String, String.eq(d0, d), "same", "DIFFERS")

def agree.d(+name: String, +d0: String, +d: String) -> String:
  Bool.pick(String, String.eq(d0, d), "", "-- " ++ name ++ "\n" ++ d)

def four.text(+tag: String, +d0: String, +d1: String, +d2: String, +d3: String) -> String:
  "-- " ++ tag ++ "\n" ++ d0 ++ "raw " ++ agree.v(d0, d1) ++ ", opt " ++ agree.v(d0, d2) ++ ", full " ++ agree.v(d0, d3) ++ "\n" ++ agree.d("raw", d0, d1) ++ agree.d("opt", d0, d2) ++ agree.d("full", d0, d3)

# the eager dump once, then whether raw lazy, DF.collect and DF.collect_full dump the same
# text ("raw same, opt same, full same"); a differing run's dump is printed under its name
def four(+tag: String, eager: E.ResT(C.Frame), +p: P.Plan, env_raw: P.Env, env_opt: P.Env, env_full: P.Env) -> IO(Unit):
  do IO<Unit>:
    r1 : E.ResT(C.Frame) <- Q.Exec.run(p, env_raw)
    r2 : E.ResT(C.Frame) <- DF.collect(p, env_opt)
    r3 : E.ResT(C.Frame) <- DF.collect_full(p, env_full)
    IO.print(four.text(tag, DF.dump(eager), DF.dump(r1), DF.dump(r2), DF.dump(r3)))

# raw and optimised lazy only (no eager counterpart, e.g. a plan-only defect)
def lazy2(+tag: String, +p: P.Plan, env_raw: P.Env, env_opt: P.Env) -> IO(Unit):
  do IO<Unit>:
    r1 : E.ResT(C.Frame) <- Q.Exec.run(p, env_raw)
    r2 : E.ResT(C.Frame) <- DF.collect(p, env_opt)
    IO.print(show(tag, "raw", r1))
    IO.print(show(tag, "opt", r2))

# collect_schema of a plan, one line: "schema <text>" or "schema error: <text>"
def schema(+tag: String, p: P.Plan) -> String:
  "-- " ++ tag ++ " schema\n" ++ DF.schema_show(DF.collect_schema(p)) ++ "\n"

# ---- CSV ---------------------------------------------------------------------------

# the raw and opt headers over one error (a scan that failed at plan time)
def errs(+tag: String, +e: E.Err) -> String:
  show(tag, "raw", Fail{e}) ++ "\n" ++ show(tag, "opt", Fail{e})

def csv.lazy(+tag: String, rp: E.Res(P.Plan)) -> IO(Unit):
  match rp:
    case Fail{e}:
      IO.print(errs(tag, e))
    case Done{p}:
      lazy2(tag, p, DF.empty_env(), DF.empty_env())

# a CSV file read eagerly (DF.read_csv) and lazily (DF.scan_csv, then collected raw and
# optimised); a scan that fails at plan time prints its error as both lazy results
def csv3(+tag: String, +path: String) -> IO(Unit):
  do IO<Unit>:
    r0 : E.ResT(C.Frame) <- DF.read_csv(path)
    IO.print(show(tag, "eager", r0))
    rp : E.Res(P.Plan) <- DF.scan_csv(path)
    csv.lazy(tag, rp)

def render.k(r: C.Frame & String) -> String:
  (fr, txt) = r
  txt

# the CSV text Csv.render writes for a frame (what DF.write_csv puts in the file), as one
# line quoted and escaped like a dump string (so CR / LF / TAB in it are visible)
def render(+tag: String, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "-- " ++ tag ++ " csv\nerror: " ++ E.Err.show(e) ++ "\n"
    case Done{fr}:
      "-- " ++ tag ++ " csv\n" ++ Y.Dump.quote(render.k(V.Csv.render(fr, None{}))) ++ "\n"

def main() -> IO(Unit):
  IO.pure(Unit, Unit{})
