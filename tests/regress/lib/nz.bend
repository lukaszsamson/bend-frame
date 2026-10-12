# tests/regress/lib/nz.bend -- the engine matrix of the null-slot regressions (post-review B1,
# tests/regress/V02_B1_*.bend; DESIGN.md 14 "v0.2 post-review: the null-slot invariant"). Not a test
# itself: its main prints nothing.
#
# A scenario is an input frame (built fresh for every run: a run consumes it), a staged with_columns
# list `pre` (Nil: none) and a final list of named expressions, run as a select (or a with_columns).
# The REFERENCE is the unfused evaluator: every expression through V.Eval.full (v0.1's stack machine,
# no Eval.fuse, no F1-F5), columns appended one by one. Its dump is printed once, with the P0 report
# of the result (src/p0.bend: "p0 ok" when every null slot holds the dtype default); then every
# engine prints "same" when its dump AND its P0 report equal the reference's, else both in full:
#   eager      DF.with_columns / DF.select (Eval.runz(Eval.fuse(..)): the fused evaluator)
#   raw opt full   DF.collect_raw / DF.collect / DF.collect_full
#   c0 c2      the chunked engine on the plan as written at grains 2^0 and 2^2
# F32 cells are compared by their bits (DF.dump), so -0.0 against +0.0 is a difference.
import Base
import ./../../../frame.bend as DF
import ./../../../src/dtype.bend as D
import ./../../../src/err.bend as E
import ./../../../src/column.bend as C
import ./../../../src/expr.bend as X
import ./../../../src/plan.bend as P
import ./../../../src/eval.bend as V
import ./../../../src/p0.bend as Z

type NE is Data:
  NE{name: String, e: X.Expr}

def ne(name: String, e: X.Expr) -> NE:
  NE{name, e}

# the aliased expressions of a list of named ones
def es(nes: List<&2, NE>) -> List<&2, X.Expr>:
  match nes:
    case Nil{}:
      Nil{}
    case NE{name, e} <> t:
      DF.alias(e, name) <> es(t)

# ---- the unfused reference --------------------------------------------------------------------------

def put(acc: E.ResT(C.Frame), +name: String, rc: E.ResT(C.Column)) -> E.ResT(C.Frame):
  match acc:
    case Fail{e}:
      Fail{e}
    case Done{g}:
      match rc:
        case Fail{e}:
          Fail{e}
        case Done{c}:
          C.Frame.put(g, name, c)

# with_columns of new names through Eval.full, one expression after the other (each sees the frame
# as the previous ones left it, which for new names is what one with_columns sees)
def adds.k(+name: String, r: C.Frame & E.ResT(C.Column)) -> E.ResT(C.Frame):
  (f, rc) = r
  put(Done{f}, name, rc)

def adds.one(acc: E.ResT(C.Frame), +name: String, e: X.Expr) -> E.ResT(C.Frame):
  match acc:
    case Fail{err}:
      Fail{err}
    case Done{f}:
      adds.k(name, V.Eval.full(f, e))

def adds.go(nes: List<&2, NE>, acc: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match nes:
    case Nil{}:
      acc
    case NE{+name, e} <> t:
      adds.go(t, adds.one(acc, name, e))

# select through Eval.full: every expression over the same frame, the columns collected
def sel.k(+name: String, acc: E.ResT(C.Frame), r: C.Frame & E.ResT(C.Column)) -> C.Frame & E.ResT(C.Frame):
  (f, rc) = r
  (f, put(acc, name, rc))

def sel.one(+name: String, e: X.Expr, st: C.Frame & E.ResT(C.Frame)) -> C.Frame & E.ResT(C.Frame):
  (f, acc) = st
  sel.k(name, acc, V.Eval.full(f, e))

def sel.go(nes: List<&2, NE>, st: C.Frame & E.ResT(C.Frame)) -> C.Frame & E.ResT(C.Frame):
  match nes:
    case Nil{}:
      st
    case NE{+name, e} <> t:
      sel.go(t, sel.one(name, e, st))

def sel.fin(st: C.Frame & E.ResT(C.Frame)) -> E.ResT(C.Frame):
  (f, acc) = st
  acc

def sel(r: E.ResT(C.Frame), nes: List<&2, NE>) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      sel.fin(sel.go(nes, (f, Done{C.Frame{0, Nil{}}})))

def reference(is_sel: Bool, r: E.ResT(C.Frame), +pre: List<&2, NE>, +nes: List<&2, NE>) -> E.ResT(C.Frame):
  match is_sel:
    case True{}:
      sel(adds.go(pre, r), nes)
    case False{}:
      adds.go(nes, adds.go(pre, r))

# ---- the engines --------------------------------------------------------------------------------------

def e_with(r: E.ResT(C.Frame), es: List<&2, X.Expr>) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.with_columns(f, es)

def e_select(r: E.ResT(C.Frame), es: List<&2, X.Expr>) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      DF.select(f, es)

def eager(is_sel: Bool, r: E.ResT(C.Frame), +pre: List<&2, NE>, +nes: List<&2, NE>) -> E.ResT(C.Frame):
  match is_sel:
    case True{}:
      e_select(e_with(r, es(pre)), es(nes))
    case False{}:
      e_with(e_with(r, es(pre)), es(nes))

def env.k(r: P.Env & P.Plan) -> P.Env:
  (env, p) = r
  env

def plan.k(r: P.Env & P.Plan) -> P.Plan:
  (env, p) = r
  p

def env(r: E.ResT(C.Frame)) -> P.Env:
  match r:
    case Fail{e}:
      DF.empty_env()
    case Done{fr}:
      env.k(DF.source("t", fr))

def src(r: E.ResT(C.Frame)) -> P.Plan:
  match r:
    case Fail{e}:
      P.Source{"t", Nil{}}
    case Done{fr}:
      plan.k(DF.source("t", fr))

def plan(is_sel: Bool, r: E.ResT(C.Frame), +pre: List<&2, NE>, +nes: List<&2, NE>) -> P.Plan:
  match is_sel:
    case True{}:
      DF.lazy_select(DF.lazy_with_columns(src(r), es(pre)), es(nes))
    case False{}:
      DF.lazy_with_columns(DF.lazy_with_columns(src(r), es(pre)), es(nes))

# ---- printing -----------------------------------------------------------------------------------------

def same(+tag: String, +how: String, +ref: String, r: E.ResT(C.Frame)) -> String:
  +d = Z.P0.dump(r)
  "-- " ++ tag ++ " " ++ how ++ Bool.pick(String, String.eq(d, ref), " same\n", "\n" ++ d)

# the reference dump with its P0 report, then each engine against it; `t` is the input frame, given
# once per run (8 copies: the reference, eager, five lazy runs and one for the plan's schema)
def run(+tag: String, +is_sel: Bool, +pre: List<&2, NE>, +nes: List<&2, NE>, t0: E.ResT(C.Frame), t1: E.ResT(C.Frame), t2: E.ResT(C.Frame), t3: E.ResT(C.Frame), t4: E.ResT(C.Frame), t5: E.ResT(C.Frame), t6: E.ResT(C.Frame), t7: E.ResT(C.Frame)) -> IO(Unit):
  +ref = Z.P0.dump(reference(is_sel, t0, pre, nes))
  +p = plan(is_sel, t7, pre, nes)
  do IO<Unit>:
    r1 : E.ResT(C.Frame) <- DF.collect_raw(p, env(t2))
    r2 : E.ResT(C.Frame) <- DF.collect(p, env(t3))
    r3 : E.ResT(C.Frame) <- DF.collect_full(p, env(t4))
    r4 : E.ResT(C.Frame) <- DF.collect_raw_with(DF.engine_chunked_at(0n), p, env(t5))
    r5 : E.ResT(C.Frame) <- DF.collect_raw_with(DF.engine_chunked_at(2n), p, env(t6))
    IO.print("-- " ++ tag ++ " unfused\n" ++ ref ++ same(tag, "eager", ref, eager(is_sel, t1, pre, nes)) ++ same(tag, "raw", ref, r1) ++ same(tag, "opt", ref, r2) ++ same(tag, "full", ref, r3) ++ same(tag, "c0", ref, r4) ++ same(tag, "c2", ref, r5))

def main() -> IO(Unit):
  IO.print("")
