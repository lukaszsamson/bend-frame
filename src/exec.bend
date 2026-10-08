# src/exec.bend -- Exec.run / Lazy.collect: execute a Plan. DESIGN.md 4.14.
#
# Shape (the M2 lesson for interpreters that thread a Type-kinded state): the
# plan tree is compiled into postfix `Instr` code (pure Data, plain structural
# recursion), then ONE tail-recursive IO loop runs the code over the state
# `St{env, ResT(stack of frames)}`. A leaf pushes a frame (`Source` takes it
# out of the Env, `ScanCsv` reads the file), a unary node pops one frame and
# pushes the result, `Join` pops two. Errors short-circuit as `Fail`. No
# mutual recursion, no destructured call results.
#
#   ScanCsv  -> Csv.read_with(path, opts, the plan's dtypes) (strict), then the
#               file's schema must equal the plan's (names included)
#   Source   -> use counting (DESIGN.md 15.7): `Exec.mark` flags every ISource
#               that is the LAST use of its name in the code; earlier uses
#               clone the frame and leave it in the env (Env.clone), the last
#               one takes it (Env.take, no copy). A self join therefore sees
#               two identical frames. The frame's schema must equal the Source's
#   Select   -> a non-empty list of plain `Col`s: Frame.select_names (moves,
#               no clone); else Eval.select (select([]) is (0, 0))
#   WithColumns / Filter -> Eval.with_columns / Eval.filter
#   Sort / GroupBy / Join -> Sort.frame / GroupBy.run / Join.run
#   Head     -> Frame.head
#
# Exec.run = Plan.schema (its static error first), then Exec.validate (the
# bindings: uniqueness over the whole env, then presence and schema per Source
# in postfix order; DF.validate_bindings), then execution.
# Lazy.collect(p, env) = Exec.run(Optimize.release(p), env).
#
# Idioms (DESIGN.md section 9): helpers above callers; match only on params;
# pairs taken apart in a helper's parameter.
import Base
import ./dtype.bend as D
import ./err.bend as E
import ./column.bend as C
import ./schema.bend as S
import ./expr.bend as X
import ./eval.bend as V
import ./csv.bend as R
import ./sort.bend as O
import ./groupby.bend as G
import ./join.bend as J
import ./plan.bend as P

type Instr is Data:
  IScan{path: String, opts: R.CsvOpts, schema: List<&2, S.Field>}
  ISource{name: String, schema: List<&2, S.Field>, last: Bool}
  ISelect{exprs: List<&2, X.Expr>}
  IWith{exprs: List<&2, X.Expr>}
  IFilter{pred: X.Expr}
  ISort{keys: List<&2, O.SortKey>}
  IGroupBy{keys: List<&2, X.Expr>, aggs: List<&2, X.Expr>, maintain_order: Bool}
  IJoin{how: J.JoinHow, left_on: List<&2, String>, right_on: List<&2, String>}
  IHead{n: U32}

type St is Type:
  St{env: P.Env, stack: E.ResT(List<&1, C.Frame>)}

# the plan in postfix order (children first; a Join's left before its right)
def Exec.compile(p: P.Plan, acc: List<&2, Instr>) -> List<&2, Instr>:
  match p:
    case P.ScanCsv{path, o, s}:
      IScan{path, o, s} <> acc
    case P.Source{n, s}:
      ISource{n, s, True{}} <> acc
    case P.Select{es, x}:
      Exec.compile(x, ISelect{es} <> acc)
    case P.WithColumns{es, x}:
      Exec.compile(x, IWith{es} <> acc)
    case P.Filter{e, x}:
      Exec.compile(x, IFilter{e} <> acc)
    case P.Sort{ks, x}:
      Exec.compile(x, ISort{ks} <> acc)
    case P.GroupBy{ks, as, mo, x}:
      Exec.compile(x, IGroupBy{ks, as, mo} <> acc)
    case P.Join{how, lo, ro, l, r}:
      Exec.compile(l, Exec.compile(r, IJoin{how, lo, ro} <> acc))
    case P.Head{n, x}:
      Exec.compile(x, IHead{n} <> acc)

# does a later instruction read the Source `n`?
def Exec.later(code: List<&2, Instr>, +n: String) -> Bool:
  match code:
    case Nil{}:
      False{}
    case ISource{m, s, l} <> t:
      Bool.or(String.eq(m, n), Exec.later(t, n))
    case i <> t:
      Exec.later(t, n)

def Exec.mark.i(i: Instr, +rest: List<&2, Instr>) -> Instr:
  match i:
    case ISource{+n, s, l}:
      ISource{n, s, Bool.not(Exec.later(rest, n))}
    case other:
      other

# flag each ISource with whether it is the last use of its name (15.7 use counting)
def Exec.mark(code: List<&2, Instr>) -> List<&2, Instr>:
  match code:
    case Nil{}:
      Nil{}
    case i <> +t:
      Exec.mark.i(i, t) <> Exec.mark(t)

def Exec.underflow() -> E.Err:
  E.InvalidOperation{"exec: malformed plan (stack underflow)"}

def Exec.push(r: E.ResT(C.Frame), stack: List<&1, C.Frame>) -> E.ResT(List<&1, C.Frame>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      Done{f <> stack}

# a frame read from a Source/ScanCsv must have exactly the plan's schema
def Exec.check.k(ok: Bool, f: C.Frame, what: String, s: List<&2, S.Field>, fs: List<&2, S.Field>) -> E.ResT(C.Frame):
  match ok:
    case True{}:
      Done{f}
    case False{}:
      Fail{E.InvalidOperation{what ++ ": data schema [" ++ S.Schema.show(fs) ++ "] differs from the plan's [" ++ S.Schema.show(s) ++ "]"}}

def Exec.check(what: String, +s: List<&2, S.Field>, r: C.Frame & List<&2, S.Field>) -> E.ResT(C.Frame):
  (f, +fs) = r
  Exec.check.k(S.Schema.eq(fs, s), f, what, s, fs)

def Exec.source.k(+n: String, s: List<&2, S.Field>, m: Maybe<&1, C.Frame>, stack: List<&1, C.Frame>) -> E.ResT(List<&1, C.Frame>):
  match m:
    case None{}:
      Fail{E.InvalidOperation{"source not in env: " ++ n}}
    case Some{f}:
      Exec.push(Exec.check("source " ++ n, s, S.Frame.schema(f)), stack)

def Exec.source(+n: String, s: List<&2, S.Field>, r: P.Env & Maybe<&1, C.Frame>, stack: List<&1, C.Frame>) -> St:
  (env, m) = r
  St{env, Exec.source.k(n, s, m, stack)}

def Exec.is_col(e: X.Expr) -> Bool:
  match e:
    case X.Col{n}:
      True{}
    case _:
      False{}

def Exec.all_cols(es: List<&2, X.Expr>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case e <> t:
      Bool.and(Exec.is_col(e), Exec.all_cols(t))

def Exec.select.k(cols: Bool, f: C.Frame, +es: List<&2, X.Expr>) -> E.ResT(C.Frame):
  match cols:
    case True{}:
      C.Frame.select_names(f, V.Eval.names(es))
    case False{}:
      V.Eval.select(f, es)

# a non-empty list of plain columns (select([]) goes through Eval.select: (0, 0))
def Exec.plain(es: List<&2, X.Expr>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case e <> t:
      Bool.and(Exec.is_col(e), Exec.all_cols(t))

def Exec.select(f: C.Frame, +es: List<&2, X.Expr>) -> E.ResT(C.Frame):
  Exec.select.k(Exec.plain(es), f, es)

# a one-input operator over the popped frame
def Exec.unary(i: Instr, f: C.Frame) -> E.ResT(C.Frame):
  match i:
    case ISelect{es}:
      Exec.select(f, es)
    case IWith{es}:
      V.Eval.with_columns(f, es)
    case IFilter{e}:
      V.Eval.filter(f, e)
    case ISort{ks}:
      O.Sort.frame(f, ks)
    case IGroupBy{ks, as, mo}:
      G.GroupBy.run(f, ks, as, mo)
    case IHead{n}:
      Done{C.Frame.head(f, n)}
    case _:
      Fail{E.InvalidOperation{"exec: not a one-input operator"}}

def Exec.unary.pop(i: Instr, stack: List<&1, C.Frame>) -> E.ResT(List<&1, C.Frame>):
  match stack:
    case Nil{}:
      Fail{Exec.underflow()}
    case f <> t:
      Exec.push(Exec.unary(i, f), t)

# the right input is on top, the left one below it
def Exec.join(how: J.JoinHow, lo: List<&2, String>, ro: List<&2, String>, stack: List<&1, C.Frame>) -> E.ResT(List<&1, C.Frame>):
  match stack:
    case r <> l <> t:
      Exec.push(J.Join.run(how, l, r, lo, ro), t)
    case _:
      Fail{Exec.underflow()}

# the last use of a name takes the frame; an earlier one clones it
def Exec.source.get(last: Bool, env: P.Env, +n: String) -> P.Env & Maybe<&1, C.Frame>:
  match last:
    case True{}:
      P.Env.take(env, n)
    case False{}:
      P.Env.clone(env, n)

def Exec.step.pure(i: Instr, env: P.Env, stack: List<&1, C.Frame>) -> St:
  match i:
    case ISource{+n, s, last}:
      Exec.source(n, s, Exec.source.get(last, env, n), stack)
    case IJoin{how, lo, ro}:
      St{env, Exec.join(how, lo, ro, stack)}
    case other:
      St{env, Exec.unary.pop(other, stack)}

def Exec.dtypes(s: List<&2, S.Field>) -> List<&2, D.DType>:
  match s:
    case Nil{}:
      Nil{}
    case S.Field{n, t} <> rest:
      t <> Exec.dtypes(rest)

def Exec.scan.k(+path: String, s: List<&2, S.Field>, r: E.ResT(C.Frame), stack: List<&1, C.Frame>) -> E.ResT(List<&1, C.Frame>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      Exec.push(Exec.check("scan_csv " ++ path, s, S.Frame.schema(f)), stack)

def Exec.scan(+path: String, opts: R.CsvOpts, +s: List<&2, S.Field>, stack: List<&1, C.Frame>) -> IO(E.ResT(List<&1, C.Frame>)):
  do IO<E.ResT(List<&1, C.Frame>)>:
    r : E.ResT(C.Frame) <- R.Csv.read_with(path, opts, Exec.dtypes(s))
    return Exec.scan.k(path, s, r, stack)

def Exec.step.i(i: Instr, env: P.Env, stack: List<&1, C.Frame>) -> IO(St):
  match i:
    case IScan{path, o, s}:
      do IO<St>:
        r : E.ResT(List<&1, C.Frame>) <- Exec.scan(path, o, s, stack)
        return St{env, r}
    case other:
      IO.pure(St, Exec.step.pure(other, env, stack))

def Exec.step.r(i: Instr, env: P.Env, r: E.ResT(List<&1, C.Frame>)) -> IO(St):
  match r:
    case Fail{e}:
      IO.pure(St, St{env, Fail{e}})
    case Done{stack}:
      Exec.step.i(i, env, stack)

def Exec.step(i: Instr, st: St) -> IO(St):
  match st:
    case St{env, r}:
      Exec.step.r(i, env, r)

def Exec.loop(code: List<&2, Instr>, st: St) -> IO(St):
  match code:
    case Nil{}:
      IO.pure(St, st)
    case i <> t:
      do IO<St>:
        st2 : St <- Exec.step(i, st)
        Exec.loop(t, st2)

def Exec.fin.s(stack: List<&1, C.Frame>) -> E.ResT(C.Frame):
  match stack:
    case f <> Nil{}:
      Done{f}
    case _:
      Fail{E.InvalidOperation{"exec: malformed plan (not one result)"}}

def Exec.fin.r(r: E.ResT(List<&1, C.Frame>)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{stack}:
      Exec.fin.s(stack)

def Exec.fin(st: St) -> E.ResT(C.Frame):
  match st:
    case St{env, r}:
      Exec.fin.r(r)

# ---- bindings (DESIGN.md 15.7, DF.validate_bindings) ---------------------------------------

def Exec.bnames(bs: List<&2, P.Bind>) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case P.Bind{n, s} <> t:
      n <> Exec.bnames(t)

def Exec.bfind(bs: List<&2, P.Bind>, +n: String) -> Maybe<&2, List<&2, S.Field>>:
  match bs:
    case Nil{}:
      None{}
    case P.Bind{+m, s} <> t:
      Bool.pick(Maybe<&2, List<&2, S.Field>>, String.eq(m, n), Some{s}, Exec.bfind(t, n))

def Exec.bind.k(+n: String, +s: List<&2, S.Field>, m: Maybe<&2, List<&2, S.Field>>) -> Maybe<&2, E.Err>:
  match m:
    case None{}:
      Some{E.InvalidOperation{"source not in env: " ++ n}}
    case Some{+fs}:
      Bool.pick(Maybe<&2, E.Err>, S.Schema.eq(fs, s), None{}, Some{E.InvalidOperation{"source " ++ n ++ ": data schema [" ++ S.Schema.show(fs) ++ "] differs from the plan's [" ++ S.Schema.show(s) ++ "]"}})

# presence and schema of every Source, in postfix (execution) order: the first error
def Exec.binds(code: List<&2, Instr>, +bs: List<&2, P.Bind>) -> Maybe<&2, E.Err>:
  match code:
    case Nil{}:
      None{}
    case ISource{+n, +s, l} <> t:
      Maybe.or(&2, E.Err, Exec.bind.k(n, s, Exec.bfind(bs, n)), Exec.binds(t, bs))
    case i <> t:
      Exec.binds(t, bs)

def Exec.validate.fin(m: Maybe<&2, E.Err>) -> E.Res(Unit):
  match m:
    case Some{e}:
      Fail{e}
    case None{}:
      Done{Unit{}}

def Exec.validate.chk(d: Maybe<&2, String>, +p: P.Plan, +bs: List<&2, P.Bind>) -> E.Res(Unit):
  match d:
    case Some{n}:
      Fail{E.InvalidOperation{"source bound twice in env: " ++ n}}
    case None{}:
      Exec.validate.fin(Exec.binds(Exec.compile(p, Nil{}), bs))

def Exec.validate.k(+p: P.Plan, r: P.Env & List<&2, P.Bind>) -> P.Env & E.Res(Unit):
  (env, +bs) = r
  (env, Exec.validate.chk(C.Names.dup(Exec.bnames(bs), Nil{}, None{}), p, bs))

# the bindings a plan needs, checked against env without running anything: env
# binds each name once ("source bound twice in env: <name>", over the whole env,
# first), then every Source of p in postfix order is present ("source not in env:
# <name>") with the plan's schema ("source <name>: data schema [..] differs from
# the plan's [..]"). env comes back untouched.
def Exec.validate(+p: P.Plan, env: P.Env) -> P.Env & E.Res(Unit):
  Exec.validate.k(p, P.Env.info(env))

# ---- run / collect ---------------------------------------------------------------------------

def Exec.run.v(+p: P.Plan, r: P.Env & E.Res(Unit)) -> IO(E.ResT(C.Frame)):
  (env, v) = r
  match v:
    case Fail{e}:
      IO.pure(E.ResT(C.Frame), Fail{e})
    case Done{u}:
      do IO<E.ResT(C.Frame)>:
        st : St <- Exec.loop(Exec.mark(Exec.compile(p, Nil{})), St{env, Done{Nil{}}})
        return Exec.fin(st)

def Exec.run.k(r: E.Res(List<&2, S.Field>), +p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  match r:
    case Fail{e}:
      IO.pure(E.ResT(C.Frame), Fail{e})
    case Done{s}:
      Exec.run.v(p, Exec.validate(p, env))

# run a plan as written (no optimisation) over the frames of env: the plan's
# schema is resolved first and its error, if any, is the result; then the
# bindings (Exec.validate); then the plan. env is consumed (frames the plan does
# not name are dropped).
def Exec.run(+p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  Exec.run.k(P.Plan.schema(p), p, env)

# Polars collect(): the release optimizer (Optimize.release), then run
def Lazy.collect(+p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  Exec.run(P.Optimize.release(p), env)

# every rewrite of Plan.optimize_full (opt-in, outside the guarantee), then run
def Lazy.collect_full(+p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  Exec.run(P.Plan.optimize_full(p), env)
