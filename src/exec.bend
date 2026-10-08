# src/exec.bend -- Exec.run / Lazy.collect: execute a Plan. DESIGN.md 4.14.
#
# Shape (the M2 lesson for interpreters that thread a Type-kinded state): the
# plan tree is compiled into postfix `Instr` code (pure Data, plain structural
# recursion), then ONE tail-recursive PURE loop (`Exec.loop`, the physical
# runner behind `Exec.run_pure`) runs the code over the state `St{env,
# ResT(stack of frames)}`. A leaf pushes a frame (`Source` takes it out of the
# Env), a unary node pops one frame and pushes the result, `Join` pops two.
# Errors short-circuit as `Fail`. No mutual recursion, no destructured call
# results. IO happens only before the loop: `Exec.mat` reads every ScanCsv
# into env (plan M_01 section 6 P2: IO source materialisation, then the pure
# runner; the proofs in PROOF_exec.bend quantify over `Exec.run_pure`).
#
#   ScanCsv  -> before the run: Csv.read_with(path, opts, the plan's dtypes)
#               (strict), then the file's schema must equal the plan's (names
#               included); the frame is bound as Source "#scan<k>" (Exec.unscan)
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
# in postfix order; DF.validate_bindings), then every scan is read (Exec.mat,
# first scan error wins), then Exec.run_pure (compile, mark, loop).
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
import ./table.bend as TV

# the one-input table verbs of M3 (src/table.bend), one instruction for all of them
type TOp is Data:
  TDrop{names: List<&2, String>}
  TRename{pairs: List<&2, Sigma<&2, &2, String, x => String>>}
  TSlice{offset: U32, len: U32}
  TTail{n: U32}
  TUnique{subset: List<&2, String>}

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
  ITable{op: TOp}
  IConcat{index: U32}

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
    case P.Drop{ns, x}:
      Exec.compile(x, ITable{TDrop{ns}} <> acc)
    case P.Rename{ps, x}:
      Exec.compile(x, ITable{TRename{ps}} <> acc)
    case P.Slice{o, l, x}:
      Exec.compile(x, ITable{TSlice{o, l}} <> acc)
    case P.Tail{n, x}:
      Exec.compile(x, ITable{TTail{n}} <> acc)
    case P.Unique{ss, x}:
      Exec.compile(x, ITable{TUnique{ss}} <> acc)
    case P.Concat{i, l, r}:
      Exec.compile(l, Exec.compile(r, IConcat{i} <> acc))

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

# a table verb over the popped frame (src/table.bend)
def Exec.table(op: TOp, f: C.Frame) -> E.ResT(C.Frame):
  match op:
    case TDrop{ns}:
      TV.Drop.run(f, ns)
    case TRename{ps}:
      TV.Rename.run(f, ps)
    case TSlice{o, l}:
      Done{TV.Slice.run(f, o, l)}
    case TTail{n}:
      Done{TV.Tail.run(f, n)}
    case TUnique{ss}:
      TV.Unique.run(f, ss)

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
    case ITable{op}:
      Exec.table(op, f)
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

# Concat{i, ..}: the right input (input i) is on top, the left one (inputs 0 .. i-1) below it
def Exec.concat(+i: U32, stack: List<&1, C.Frame>) -> E.ResT(List<&1, C.Frame>):
  match stack:
    case r <> l <> t:
      Exec.push(TV.Concat.two(i, l, r), t)
    case _:
      Fail{Exec.underflow()}

# the last use of a name takes the frame; an earlier one clones it
def Exec.source.get(last: Bool, env: P.Env, +n: String) -> P.Env & Maybe<&1, C.Frame>:
  match last:
    case True{}:
      P.Env.take(env, n)
    case False{}:
      P.Env.clone(env, n)

# one instruction of the pure runner. An IScan never reaches it: Exec.run
# materialises every scan into env first (Exec.mat), so here it is an error
def Exec.step.pure(i: Instr, env: P.Env, stack: List<&1, C.Frame>) -> St:
  match i:
    case IScan{path, o, s}:
      St{env, Fail{E.InvalidOperation{"exec: scan_csv not materialised: " ++ path}}}
    case ISource{+n, s, last}:
      Exec.source(n, s, Exec.source.get(last, env, n), stack)
    case IJoin{how, lo, ro}:
      St{env, Exec.join(how, lo, ro, stack)}
    case IConcat{i}:
      St{env, Exec.concat(i, stack)}
    case other:
      St{env, Exec.unary.pop(other, stack)}

def Exec.step.r(i: Instr, env: P.Env, r: E.ResT(List<&1, C.Frame>)) -> St:
  match r:
    case Fail{e}:
      St{env, Fail{e}}
    case Done{stack}:
      Exec.step.pure(i, env, stack)

def Exec.step(i: Instr, st: St) -> St:
  match st:
    case St{env, r}:
      Exec.step.r(i, env, r)

# the ONE runner (plan M_01 P2 "Exec.run_pure"): pure, structural on the code
def Exec.loop(code: List<&2, Instr>, st: St) -> St:
  match code:
    case Nil{}:
      st
    case i <> t:
      Exec.loop(t, Exec.step(i, st))

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

# run compiled (and marked) code over env: the physical runner
def Exec.run_code(code: List<&2, Instr>, env: P.Env) -> E.ResT(C.Frame):
  Exec.fin(Exec.loop(code, St{env, Done{Nil{}}}))

# run a plan over the frames of env with no IO and no checks: compile, mark
# the last uses, run. The pure physical runner the proofs (PROOF_exec.bend)
# quantify over; Exec.run calls it after validation and scan materialisation.
# A ScanCsv node left in p is the error "exec: scan_csv not materialised".
def Exec.run_pure(+p: P.Plan, env: P.Env) -> E.ResT(C.Frame):
  Exec.run_code(Exec.mark(Exec.compile(p, Nil{})), env)

# ---- scan materialisation (the IO boundary) --------------------------------------------------
#
# Every ScanCsv of a plan is read before anything runs: scan k (postfix order)
# is read with Csv.read_with (strict, the plan's dtypes), its schema must equal
# the plan's, and it is bound in env under the reserved name "#scan<k>"
# (Exec.mat); the plan is rewritten with Source{"#scan<k>", s} in its place
# (Exec.unscan). The first failing scan is the result. Names starting with
# "#scan" are reserved for this (DESIGN.md 14).

def Exec.dtypes(s: List<&2, S.Field>) -> List<&2, D.DType>:
  match s:
    case Nil{}:
      Nil{}
    case S.Field{n, t} <> rest:
      t <> Exec.dtypes(rest)

def Exec.scan_name(+k: U32) -> String:
  "#scan" ++ U32.show(k)

# the number of ScanCsv nodes of a plan
def Exec.nscans(p: P.Plan) -> U32:
  match p:
    case P.ScanCsv{path, o, s}:
      1
    case P.Source{n, s}:
      0
    case P.Select{es, x}:
      Exec.nscans(x)
    case P.WithColumns{es, x}:
      Exec.nscans(x)
    case P.Filter{e, x}:
      Exec.nscans(x)
    case P.Sort{ks, x}:
      Exec.nscans(x)
    case P.GroupBy{ks, as, mo, x}:
      Exec.nscans(x)
    case P.Join{how, lo, ro, l, r}:
      U32.add(Exec.nscans(l), Exec.nscans(r))
    case P.Head{n, x}:
      Exec.nscans(x)
    case P.Drop{ns, x}:
      Exec.nscans(x)
    case P.Rename{ps, x}:
      Exec.nscans(x)
    case P.Slice{o, l, x}:
      Exec.nscans(x)
    case P.Tail{n, x}:
      Exec.nscans(x)
    case P.Unique{ss, x}:
      Exec.nscans(x)
    case P.Concat{i, l, r}:
      U32.add(Exec.nscans(l), Exec.nscans(r))

# ScanCsv -> Source{"#scan<k>", s}, numbered in postfix order from k (a Join's
# left scans come first, as in Exec.compile)
def Exec.unscan(p: P.Plan, +k: U32) -> P.Plan:
  match p:
    case P.ScanCsv{path, o, s}:
      P.Source{Exec.scan_name(k), s}
    case P.Source{n, s}:
      P.Source{n, s}
    case P.Select{es, x}:
      P.Select{es, Exec.unscan(x, k)}
    case P.WithColumns{es, x}:
      P.WithColumns{es, Exec.unscan(x, k)}
    case P.Filter{e, x}:
      P.Filter{e, Exec.unscan(x, k)}
    case P.Sort{ks, x}:
      P.Sort{ks, Exec.unscan(x, k)}
    case P.GroupBy{ks, as, mo, x}:
      P.GroupBy{ks, as, mo, Exec.unscan(x, k)}
    case P.Join{how, lo, ro, +l, r}:
      P.Join{how, lo, ro, Exec.unscan(l, k), Exec.unscan(r, U32.add(k, Exec.nscans(l)))}
    case P.Head{n, x}:
      P.Head{n, Exec.unscan(x, k)}
    case P.Drop{ns, x}:
      P.Drop{ns, Exec.unscan(x, k)}
    case P.Rename{ps, x}:
      P.Rename{ps, Exec.unscan(x, k)}
    case P.Slice{o, l, x}:
      P.Slice{o, l, Exec.unscan(x, k)}
    case P.Tail{n, x}:
      P.Tail{n, Exec.unscan(x, k)}
    case P.Unique{ss, x}:
      P.Unique{ss, Exec.unscan(x, k)}
    case P.Concat{i, +l, r}:
      P.Concat{i, Exec.unscan(l, k), Exec.unscan(r, U32.add(k, Exec.nscans(l)))}

# the env being filled, and the first scan error
type Mat is Type:
  Mat{env: P.Env, err: Maybe<&2, E.Err>}

def Exec.mat.put(r: P.Env & P.Plan) -> Mat:
  (env, p) = r
  Mat{env, None{}}

def Exec.mat.add(+k: U32, env: P.Env, r: E.ResT(C.Frame)) -> Mat:
  match r:
    case Fail{e}:
      Mat{env, Some{e}}
    case Done{f}:
      Exec.mat.put(P.Env.add(env, Exec.scan_name(k), f))

# the file's schema must equal the plan's (names included)
def Exec.scan.k(+path: String, s: List<&2, S.Field>, r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      Exec.check("scan_csv " ++ path, s, S.Frame.schema(f))

def Exec.mat.read(+path: String, opts: R.CsvOpts, +s: List<&2, S.Field>, +k: U32, env: P.Env) -> IO(Mat):
  do IO<Mat>:
    r : E.ResT(C.Frame) <- R.Csv.read_with(path, opts, Exec.dtypes(s))
    return Exec.mat.add(k, env, Exec.scan.k(path, s, r))

# read every IScan of the code in order into env (stopping at the first error)
def Exec.mat(code: List<&2, Instr>, +k: U32, m: Mat) -> IO(Mat):
  match code m:
    case Nil{} _:
      IO.pure(Mat, m)
    case i <> t Mat{env, Some{e}}:
      IO.pure(Mat, Mat{env, Some{e}})
    case IScan{path, o, s} <> t Mat{env, None{}}:
      do IO<Mat>:
        m2 : Mat <- Exec.mat.read(path, o, s, k, env)
        Exec.mat(t, U32.inc(k), m2)
    case i <> t Mat{env, None{}}:
      Exec.mat(t, k, Mat{env, None{}})

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

def Exec.run.m(+p: P.Plan, m: Mat) -> E.ResT(C.Frame):
  match m:
    case Mat{env, Some{e}}:
      Fail{e}
    case Mat{env, None{}}:
      Exec.run_pure(Exec.unscan(p, 0), env)

def Exec.run.v(+p: P.Plan, r: P.Env & E.Res(Unit)) -> IO(E.ResT(C.Frame)):
  (env, v) = r
  match v:
    case Fail{e}:
      IO.pure(E.ResT(C.Frame), Fail{e})
    case Done{u}:
      do IO<E.ResT(C.Frame)>:
        m : Mat <- Exec.mat(Exec.compile(p, Nil{}), 0, Mat{env, None{}})
        return Exec.run.m(p, m)

def Exec.run.k(r: E.Res(List<&2, S.Field>), +p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  match r:
    case Fail{e}:
      IO.pure(E.ResT(C.Frame), Fail{e})
    case Done{s}:
      Exec.run.v(p, Exec.validate(p, env))

# run a plan as written (no optimisation) over the frames of env: the plan's
# schema is resolved first and its error, if any, is the result; then the
# bindings (Exec.validate); then every scan is read (Exec.mat, the IO
# boundary); then the pure runner (Exec.run_pure). env is consumed (frames the
# plan does not name are dropped).
def Exec.run(+p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  Exec.run.k(P.Plan.schema(p), p, env)

# Polars collect(): the release optimizer (Optimize.release), then run
def Lazy.collect(+p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  Exec.run(P.Optimize.release(p), env)

# every rewrite of Plan.optimize_full (opt-in, outside the guarantee), then run
def Lazy.collect_full(+p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  Exec.run(P.Plan.optimize_full(p), env)
