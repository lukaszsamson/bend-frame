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
#               included); the frames go to env's SCAN namespace (Env.scans, no
#               names), in postfix order. In the run, IScan takes the next one
#               (Env.scan_take): a scan never shares a name with a user Source
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
#   Drop / Rename / Slice / Tail / Unique -> ITable{op}: TV.Drop.run / TV.Rename.run /
#               TV.Slice.run / TV.Tail.run / TV.Unique.run (src/table.bend)
#   Concat{i, l, r} -> IConcat{i}: pops r (input i) and l, TV.Concat.two (schema, row cap)
#   Join{Semi/Anti} -> Join.run like the other joins
#
# Exec.run = Plan.schema (its static error first), then Exec.validate (the
# bindings: uniqueness over the whole env, then presence and schema per Source
# in postfix order; DF.validate_bindings), then every scan is read (Exec.mat,
# first scan error wins) into env's scan namespace, then Exec.run_pure
# (compile, mark, loop) on the same plan.
# Lazy.collect(p, env) = Exec.run(Optimize.release(p), env).
#
# Idioms (DESIGN.md section 9): helpers above callers; match only on params;
# pairs taken apart in a helper's parameter.
import Base
import ./dtype.bend as D
import ./err.bend as E
import ./kernels.bend as K
import ./column.bend as C
import ./strs.bend as ST
import ./schema.bend as S
import ./expr.bend as X
import ./analysis.bend as A
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

# IScan: the next frame of env's scan namespace (Exec.run put the scans' frames there
# in postfix order, Exec.mat), with the plan's schema; none left is the error "exec:
# scan_csv not materialised" (run_pure called directly on a scan plan, no IO here)
def Exec.scan.k(+path: String, s: List<&2, S.Field>, m: Maybe<&1, C.Frame>, stack: List<&1, C.Frame>) -> E.ResT(List<&1, C.Frame>):
  match m:
    case None{}:
      Fail{E.InvalidOperation{"exec: scan_csv not materialised: " ++ path}}
    case Some{f}:
      Exec.push(Exec.check("scan_csv " ++ path, s, S.Frame.schema(f)), stack)

def Exec.scan(+path: String, s: List<&2, S.Field>, r: P.Env & Maybe<&1, C.Frame>, stack: List<&1, C.Frame>) -> St:
  (env, m) = r
  St{env, Exec.scan.k(path, s, m, stack)}

# one instruction of the pure runner
def Exec.step.pure(i: Instr, env: P.Env, stack: List<&1, C.Frame>) -> St:
  match i:
    case IScan{+path, o, s}:
      Exec.scan(path, s, P.Env.scan_take(env), stack)
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

# run a plan over the frames of env with no IO and no binding checks: compile,
# mark the last uses, run. The pure physical runner the proofs (PROOF_exec.bend)
# quantify over; Exec.run calls it, on the plan itself, after validation and scan
# materialisation. A Source reads env's named frames, a ScanCsv the next frame of
# env's scan namespace; with none left it is "exec: scan_csv not materialised".
def Exec.run_pure(+p: P.Plan, env: P.Env) -> E.ResT(C.Frame):
  Exec.run_code(Exec.mark(Exec.compile(p, Nil{})), env)

# ---- the physical Sort + Head step (v0.2 T3.4) -------------------------------------------------
#
# Exec.run_phys is what Exec.run executes: Exec.run_pure, except that a plan whose ROOT is
# Head{n, Sort{ks, x}} runs x's code and then ONE step, Sort.frame_head (the full stable argsort,
# then only min(n, height) rows gathered), in place of ISort{ks} then IHead{n}. A physical
# pattern of the runner, not a plan rewrite: Exec.compile / Exec.mark / Exec.loop / run_pure (the
# runner the proofs quantify over) and Optimize.release are unchanged. LAWS.bend section 17
# (sort_head_run, run_phys_obs, collect_obs): the same error, height, names, dtypes, lengths and
# cells as run_pure, for every plan and env.

def Exec.sorthead.s(ks: List<&2, O.SortKey>, +n: U32, stack: List<&1, C.Frame>) -> E.ResT(List<&1, C.Frame>):
  match stack:
    case Nil{}:
      Fail{Exec.underflow()}
    case f <> t:
      Exec.push(O.Sort.frame_head(f, ks, n), t)

def Exec.sorthead.r(ks: List<&2, O.SortKey>, +n: U32, env: P.Env, r: E.ResT(List<&1, C.Frame>)) -> St:
  match r:
    case Fail{e}:
      St{env, Fail{e}}
    case Done{stack}:
      St{env, Exec.sorthead.s(ks, n, stack)}

# ISort{ks} then IHead{n}, as one step over the runner's state
def Exec.sorthead(ks: List<&2, O.SortKey>, +n: U32, st: St) -> St:
  match st:
    case St{env, r}:
      Exec.sorthead.r(ks, n, env, r)

def Exec.run_phys.h(+n: U32, x: P.Plan, env: P.Env) -> E.ResT(C.Frame):
  match x:
    case P.Sort{ks, y}:
      Exec.fin(Exec.sorthead(ks, n, Exec.loop(Exec.mark(Exec.compile(y, Nil{})), St{env, Done{Nil{}}})))
    case other:
      Exec.run_pure(P.Head{n, other}, env)

# ---- the physical Filter + Select step (v0.2 T4.3, DESIGN.md 16.3 F8) -------------------------------
#
# A plan whose ROOT is Select{es, Filter{pred, x}} with es a non-empty list of plain columns (the
# Exec.plain case: Exec.select would run Frame.select_names on the filtered frame) runs x's code and
# then ONE step, Exec.fs, in place of IFilter{pred} then ISelect{es}: the mask and kept count come
# from Eval.filter.mask, the function Eval.filter itself calls (the F5 pred_count passes over
# borrowed columns when the predicate is a conjunction of bool columns and `col op lit`, the
# general predicate otherwise; the same errors in the same order: v0.2 T4.4), then
# Frame.select_names takes the selected columns out of the UNFILTERED frame (its errors depend on the
# names only, which the filter keeps), and only those columns are compacted (Exec.fc): AllValid
# columns of the same length four or three at a time with ONE Kernel.compact4 / compact3 loop (one
# mask read, one cursor), anything else (a validity mask, a short group, two or one columns left)
# with Column.compact as Frame.filter_mask does. The columns the select drops are never compacted.
# Root only, like the Sort + Head step: under any other operator the general path runs. Aliases
# (Eval.select) take the general path too (DESIGN.md 14 "v0.2 T4.3"). LAWS.bend section 20
# (fc_filter_mask, select_filter_mask, filter_select_step, filter_select_run_eq / _run; with
# run_phys_obs, collect_obs): the SAME result term as Exec.run_pure (same error, or the same frame:
# names, dtypes, validity, cells, buffers), for every plan, predicate, column list and env.

# a column's one buffer, by element type (the template dispatch of compact3 / compact4)
type Buf is Type:
  BU{a: Array<U32>}
  BF{a: Array<F32>}
  BS{a: Array<String>}

# what an AllValid column is besides its buffer: the constructor (and a Dictionary's table)
type Sh is Type:
  SB{}
  SU{}
  SI{}
  SD{dict: ST.Dict}
  SX{}

# a column split for the fused compaction: AllValid (length, depth, shell, buffer), or kept whole
type Fz is Type:
  FzOk{len: U32, depth: Nat, sh: Sh, b: Buf}
  FzNo{c: C.Column}

type F3 is Type:
  F3{b1: Buf, b2: Buf, b3: Buf, m: Array<U32>}

type F4 is Type:
  F4{b1: Buf, b2: Buf, b3: Buf, b4: Buf, m: Array<U32>}

def Buf.u(a: Array<U32>) -> Buf:
  BU{a}

def Buf.f(a: Array<F32>) -> Buf:
  BF{a}

def Buf.s(a: Array<String>) -> Buf:
  BS{a}

def Exec.mk.u(sh: Sh, a: Array<U32>, +len: U32, +depth: Nat, valid: C.Valid) -> C.Column:
  match sh:
    case SB{}:
      C.CBool{len, depth, valid, a}
    case SU{}:
      C.CU32{len, depth, valid, a}
    case SI{}:
      C.CI32{len, depth, valid, a}
    case SD{dict}:
      C.CStr{len, depth, valid, ST.SDict{a, dict}}
    case SX{}:
      C.CU32{len, depth, valid, a}

# the column of a shell and a buffer (an F32 / String buffer decides the constructor itself)
def Exec.mk(sh: Sh, b: Buf, +len: U32, +depth: Nat, valid: C.Valid) -> C.Column:
  match b:
    case BU{a}:
      Exec.mk.u(sh, a, len, depth, valid)
    case BF{a}:
      C.CF32{len, depth, valid, a}
    case BS{a}:
      C.CStr{len, depth, valid, ST.SRaw{a}}

def Exec.fz.v(sh: Sh, b: Buf, +len: U32, +depth: Nat, valid: C.Valid) -> Fz:
  match valid:
    case C.AllValid{}:
      FzOk{len, depth, sh, b}
    case C.Mask{v}:
      FzNo{Exec.mk(sh, b, len, depth, C.Mask{v})}

def Exec.fz.s(+len: U32, +depth: Nat, valid: C.Valid, data: ST.Strs) -> Fz:
  match data:
    case ST.SRaw{a}:
      Exec.fz.v(SX{}, BS{a}, len, depth, valid)
    case ST.SDict{codes, dict}:
      Exec.fz.v(SD{dict}, BU{codes}, len, depth, valid)

# split a column (no copy: the buffer moves)
def Exec.fz(c: C.Column) -> Fz:
  match c:
    case C.CBool{len, depth, valid, data}:
      Exec.fz.v(SB{}, BU{data}, len, depth, valid)
    case C.CU32{len, depth, valid, data}:
      Exec.fz.v(SU{}, BU{data}, len, depth, valid)
    case C.CI32{len, depth, valid, data}:
      Exec.fz.v(SI{}, BU{data}, len, depth, valid)
    case C.CF32{len, depth, valid, data}:
      Exec.fz.v(SX{}, BF{data}, len, depth, valid)
    case C.CStr{len, depth, valid, data}:
      Exec.fz.s(len, depth, valid, data)

# the column back
def Exec.unfz(z: Fz) -> C.Column:
  match z:
    case FzOk{len, depth, sh, b}:
      Exec.mk(sh, b, len, depth, C.AllValid{})
    case FzNo{c}:
      c

# compact3 over three buffers of any element types: ONE loop (templates chosen buffer by buffer;
# the inputs come back in the record and are dropped here: they were the columns' last owners)
def Exec.c3.k(~A: Data, ~B: Data, ~C: Data, ~wa: Array<A> -> Buf, ~wb: Array<B> -> Buf, ~wc: Array<C> -> Buf, r: K.C3<A, B, C>) -> F3:
  match r:
    case K.C3{o1, o2, o3, m, a1, a2, a3, k}:
      F3{wa(o1), wb(o2), wc(o3), m}

def Exec.c3.c(~A: Data, ~B: Data, ~wa: Array<A> -> Buf, ~wb: Array<B> -> Buf, +n: U32, +d: Nat, m: Array<U32>, a1: Array<A>, a2: Array<B>, +z1: A, +z2: B, b3: Buf) -> F3:
  match b3:
    case BU{a3}:
      Exec.c3.k(~A, ~B, ~U32, ~wa, ~wb, ~(o => Buf.u(o)), K.Kernel.compact3(~A, ~B, ~U32, n, d, m, a1, a2, a3, z1, z2, 0))
    case BF{a3}:
      Exec.c3.k(~A, ~B, ~F32, ~wa, ~wb, ~(o => Buf.f(o)), K.Kernel.compact3(~A, ~B, ~F32, n, d, m, a1, a2, a3, z1, z2, 0.0))
    case BS{a3}:
      Exec.c3.k(~A, ~B, ~String, ~wa, ~wb, ~(o => Buf.s(o)), K.Kernel.compact3(~A, ~B, ~String, n, d, m, a1, a2, a3, z1, z2, ""))

def Exec.c3.b(~A: Data, ~wa: Array<A> -> Buf, +n: U32, +d: Nat, m: Array<U32>, a1: Array<A>, +z1: A, b2: Buf, b3: Buf) -> F3:
  match b2:
    case BU{a2}:
      Exec.c3.c(~A, ~U32, ~wa, ~(o => Buf.u(o)), n, d, m, a1, a2, z1, 0, b3)
    case BF{a2}:
      Exec.c3.c(~A, ~F32, ~wa, ~(o => Buf.f(o)), n, d, m, a1, a2, z1, 0.0, b3)
    case BS{a2}:
      Exec.c3.c(~A, ~String, ~wa, ~(o => Buf.s(o)), n, d, m, a1, a2, z1, "", b3)

def Exec.c3(+n: U32, +d: Nat, m: Array<U32>, b1: Buf, b2: Buf, b3: Buf) -> F3:
  match b1:
    case BU{a1}:
      Exec.c3.b(~U32, ~(o => Buf.u(o)), n, d, m, a1, 0, b2, b3)
    case BF{a1}:
      Exec.c3.b(~F32, ~(o => Buf.f(o)), n, d, m, a1, 0.0, b2, b3)
    case BS{a1}:
      Exec.c3.b(~String, ~(o => Buf.s(o)), n, d, m, a1, "", b2, b3)

# the same with four buffers (Kernel.compact4)
def Exec.c4.k(~A: Data, ~B: Data, ~C: Data, ~D: Data, ~wa: Array<A> -> Buf, ~wb: Array<B> -> Buf, ~wc: Array<C> -> Buf, ~wd: Array<D> -> Buf, r: K.C4<A, B, C, D>) -> F4:
  match r:
    case K.C4{o1, o2, o3, o4, m, a1, a2, a3, a4, k}:
      F4{wa(o1), wb(o2), wc(o3), wd(o4), m}

def Exec.c4.d(~A: Data, ~B: Data, ~C: Data, ~wa: Array<A> -> Buf, ~wb: Array<B> -> Buf, ~wc: Array<C> -> Buf, +n: U32, +d: Nat, m: Array<U32>, a1: Array<A>, a2: Array<B>, a3: Array<C>, +z1: A, +z2: B, +z3: C, b4: Buf) -> F4:
  match b4:
    case BU{a4}:
      Exec.c4.k(~A, ~B, ~C, ~U32, ~wa, ~wb, ~wc, ~(o => Buf.u(o)), K.Kernel.compact4(~A, ~B, ~C, ~U32, n, d, m, a1, a2, a3, a4, z1, z2, z3, 0))
    case BF{a4}:
      Exec.c4.k(~A, ~B, ~C, ~F32, ~wa, ~wb, ~wc, ~(o => Buf.f(o)), K.Kernel.compact4(~A, ~B, ~C, ~F32, n, d, m, a1, a2, a3, a4, z1, z2, z3, 0.0))
    case BS{a4}:
      Exec.c4.k(~A, ~B, ~C, ~String, ~wa, ~wb, ~wc, ~(o => Buf.s(o)), K.Kernel.compact4(~A, ~B, ~C, ~String, n, d, m, a1, a2, a3, a4, z1, z2, z3, ""))

def Exec.c4.c(~A: Data, ~B: Data, ~wa: Array<A> -> Buf, ~wb: Array<B> -> Buf, +n: U32, +d: Nat, m: Array<U32>, a1: Array<A>, a2: Array<B>, +z1: A, +z2: B, b3: Buf, b4: Buf) -> F4:
  match b3:
    case BU{a3}:
      Exec.c4.d(~A, ~B, ~U32, ~wa, ~wb, ~(o => Buf.u(o)), n, d, m, a1, a2, a3, z1, z2, 0, b4)
    case BF{a3}:
      Exec.c4.d(~A, ~B, ~F32, ~wa, ~wb, ~(o => Buf.f(o)), n, d, m, a1, a2, a3, z1, z2, 0.0, b4)
    case BS{a3}:
      Exec.c4.d(~A, ~B, ~String, ~wa, ~wb, ~(o => Buf.s(o)), n, d, m, a1, a2, a3, z1, z2, "", b4)

def Exec.c4.b(~A: Data, ~wa: Array<A> -> Buf, +n: U32, +d: Nat, m: Array<U32>, a1: Array<A>, +z1: A, b2: Buf, b3: Buf, b4: Buf) -> F4:
  match b2:
    case BU{a2}:
      Exec.c4.c(~A, ~U32, ~wa, ~(o => Buf.u(o)), n, d, m, a1, a2, z1, 0, b3, b4)
    case BF{a2}:
      Exec.c4.c(~A, ~F32, ~wa, ~(o => Buf.f(o)), n, d, m, a1, a2, z1, 0.0, b3, b4)
    case BS{a2}:
      Exec.c4.c(~A, ~String, ~wa, ~(o => Buf.s(o)), n, d, m, a1, a2, z1, "", b3, b4)

def Exec.c4(+n: U32, +d: Nat, m: Array<U32>, b1: Buf, b2: Buf, b3: Buf, b4: Buf) -> F4:
  match b1:
    case BU{a1}:
      Exec.c4.b(~U32, ~(o => Buf.u(o)), n, d, m, a1, 0, b2, b3, b4)
    case BF{a1}:
      Exec.c4.b(~F32, ~(o => Buf.f(o)), n, d, m, a1, 0.0, b2, b3, b4)
    case BS{a1}:
      Exec.c4.b(~String, ~(o => Buf.s(o)), n, d, m, a1, "", b2, b3, b4)

# Frame.filter_mask's step (Cols.compact.step) on a split column
def Exec.fc.one(n: String, +kept: U32, z: Fz, st: Array<U32> & List<&1, C.Named>) -> Array<U32> & List<&1, C.Named>:
  C.Cols.compact.step(n, kept, Exec.unfz(z), st)

def Exec.fc.k3(n1: String, s1: Sh, n2: String, s2: Sh, n3: String, s3: Sh, +kept: U32, +d: Nat, acc: List<&1, C.Named>, r: F3) -> Array<U32> & List<&1, C.Named>:
  match r:
    case F3{o1, o2, o3, m}:
      (m, C.Named{n3, Exec.mk(s3, o3, kept, d, C.AllValid{})} <> C.Named{n2, Exec.mk(s2, o2, kept, d, C.AllValid{})} <> C.Named{n1, Exec.mk(s1, o1, kept, d, C.AllValid{})} <> acc)

def Exec.fc.t3(ok: Bool, n1: String, +l1: U32, +p1: Nat, s1: Sh, b1: Buf, n2: String, +l2: U32, +p2: Nat, s2: Sh, b2: Buf, n3: String, +l3: U32, +p3: Nat, s3: Sh, b3: Buf, +kept: U32, +d: Nat, st: Array<U32> & List<&1, C.Named>) -> Array<U32> & List<&1, C.Named>:
  match ok:
    case True{}:
      (m, acc) = st
      Exec.fc.k3(n1, s1, n2, s2, n3, s3, kept, d, acc, Exec.c3(l1, d, m, b1, b2, b3))
    case False{}:
      Exec.fc.one(n3, kept, FzOk{l3, p3, s3, b3}, Exec.fc.one(n2, kept, FzOk{l2, p2, s2, b2}, Exec.fc.one(n1, kept, FzOk{l1, p1, s1, b1}, st)))

# three columns: one compact3 loop when all three are AllValid with one length, else one by one
def Exec.fc.s3(n1: String, z1: Fz, n2: String, z2: Fz, n3: String, z3: Fz, +kept: U32, +d: Nat, st: Array<U32> & List<&1, C.Named>) -> Array<U32> & List<&1, C.Named>:
  match z1 z2 z3:
    case FzOk{+l1, p1, s1, b1} FzOk{+l2, p2, s2, b2} FzOk{+l3, p3, s3, b3}:
      Exec.fc.t3(Bool.and(U32.is_eq(l1, l2), U32.is_eq(l1, l3)), n1, l1, p1, s1, b1, n2, l2, p2, s2, b2, n3, l3, p3, s3, b3, kept, d, st)
    case y1 y2 y3:
      Exec.fc.one(n3, kept, y3, Exec.fc.one(n2, kept, y2, Exec.fc.one(n1, kept, y1, st)))

def Exec.fc.k4(n1: String, s1: Sh, n2: String, s2: Sh, n3: String, s3: Sh, n4: String, s4: Sh, +kept: U32, +d: Nat, acc: List<&1, C.Named>, r: F4) -> Array<U32> & List<&1, C.Named>:
  match r:
    case F4{o1, o2, o3, o4, m}:
      (m, C.Named{n4, Exec.mk(s4, o4, kept, d, C.AllValid{})} <> C.Named{n3, Exec.mk(s3, o3, kept, d, C.AllValid{})} <> C.Named{n2, Exec.mk(s2, o2, kept, d, C.AllValid{})} <> C.Named{n1, Exec.mk(s1, o1, kept, d, C.AllValid{})} <> acc)

def Exec.fc.t4(ok: Bool, n1: String, +l1: U32, +p1: Nat, s1: Sh, b1: Buf, n2: String, +l2: U32, +p2: Nat, s2: Sh, b2: Buf, n3: String, +l3: U32, +p3: Nat, s3: Sh, b3: Buf, n4: String, +l4: U32, +p4: Nat, s4: Sh, b4: Buf, +kept: U32, +d: Nat, st: Array<U32> & List<&1, C.Named>) -> Array<U32> & List<&1, C.Named>:
  match ok:
    case True{}:
      (m, acc) = st
      Exec.fc.k4(n1, s1, n2, s2, n3, s3, n4, s4, kept, d, acc, Exec.c4(l1, d, m, b1, b2, b3, b4))
    case False{}:
      Exec.fc.one(n4, kept, FzOk{l4, p4, s4, b4}, Exec.fc.one(n3, kept, FzOk{l3, p3, s3, b3}, Exec.fc.one(n2, kept, FzOk{l2, p2, s2, b2}, Exec.fc.one(n1, kept, FzOk{l1, p1, s1, b1}, st))))

# four columns: one compact4 loop when all four are AllValid with one length, else one by one
def Exec.fc.s4(n1: String, z1: Fz, n2: String, z2: Fz, n3: String, z3: Fz, n4: String, z4: Fz, +kept: U32, +d: Nat, st: Array<U32> & List<&1, C.Named>) -> Array<U32> & List<&1, C.Named>:
  match z1 z2 z3 z4:
    case FzOk{+l1, p1, s1, b1} FzOk{+l2, p2, s2, b2} FzOk{+l3, p3, s3, b3} FzOk{+l4, p4, s4, b4}:
      Exec.fc.t4(Bool.and(U32.is_eq(l1, l2), Bool.and(U32.is_eq(l1, l3), U32.is_eq(l1, l4))), n1, l1, p1, s1, b1, n2, l2, p2, s2, b2, n3, l3, p3, s3, b3, n4, l4, p4, s4, b4, kept, d, st)
    case y1 y2 y3 y4:
      Exec.fc.one(n4, kept, y4, Exec.fc.one(n3, kept, y3, Exec.fc.one(n2, kept, y2, Exec.fc.one(n1, kept, y1, st))))

# Cols.compact.go with the columns grouped: four at a time, then three; two or one left go one by one
def Exec.fc.go(cols: List<&1, C.Named>, +kept: U32, +d: Nat, st: Array<U32> & List<&1, C.Named>) -> Array<U32> & List<&1, C.Named>:
  match cols:
    case Nil{}:
      st
    case C.Named{n1, c1} <> Nil{}:
      C.Cols.compact.step(n1, kept, c1, st)
    case C.Named{n1, c1} <> C.Named{n2, c2} <> Nil{}:
      C.Cols.compact.step(n2, kept, c2, C.Cols.compact.step(n1, kept, c1, st))
    case C.Named{n1, c1} <> C.Named{n2, c2} <> C.Named{n3, c3} <> Nil{}:
      Exec.fc.s3(n1, Exec.fz(c1), n2, Exec.fz(c2), n3, Exec.fz(c3), kept, d, st)
    case C.Named{n1, c1} <> C.Named{n2, c2} <> C.Named{n3, c3} <> C.Named{n4, c4} <> rest:
      Exec.fc.go(rest, kept, d, Exec.fc.s4(n1, Exec.fz(c1), n2, Exec.fz(c2), n3, Exec.fz(c3), n4, Exec.fz(c4), kept, d, st))

# Frame.filter_mask over the selected columns only (mask consumed)
def Exec.fc(g: C.Frame, m: Array<U32>, +kept: U32) -> C.Frame:
  match g:
    case C.Frame{h, cols}:
      C.Frame.filter_mask.k(kept, Exec.fc.go(cols, kept, K.Kernel.depth_for(U32.add(kept, 1)), (m, Nil{})))

# select then compact; a select error drops the mask
def Exec.fs.cmp(r: E.ResT(C.Frame), m: Array<U32>, +kept: U32) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{g}:
      Done{Exec.fc(g, m, kept)}

# the select on the UNFILTERED frame (its errors depend on the names only, which the filter keeps),
# then the selected columns compacted with filter's mask and kept count
def Exec.fs.q(f: C.Frame, +es: List<&2, X.Expr>, r: Array<U32> & U32) -> E.ResT(C.Frame):
  (m, +kept) = r
  Exec.fs.cmp(C.Frame.select_names(f, V.Eval.names(es)), m, kept)

def Exec.fs.k(+es: List<&2, X.Expr>, x: C.Frame & (Array<U32> & U32)) -> E.ResT(C.Frame):
  (f, r) = x
  Exec.fs.q(f, es, r)

def Exec.fs.r(+es: List<&2, X.Expr>, r: E.ResT(C.Frame & (Array<U32> & U32))) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      Exec.fs.k(es, x)

# Eval.filter(f, pred) then Exec.select (plain columns: Frame.select_names), as one step: the mask
# from the SAME function Eval.filter uses (Eval.filter.mask: the F5 pred_count passes over borrowed
# columns, or the general predicate; its errors first), then only the selected columns compacted
def Exec.fs(f: C.Frame, +pred: X.Expr, +es: List<&2, X.Expr>) -> E.ResT(C.Frame):
  Exec.fs.r(es, V.Eval.filter.mask(f, pred))

def Exec.fsel.s(+pred: X.Expr, +es: List<&2, X.Expr>, stack: List<&1, C.Frame>) -> E.ResT(List<&1, C.Frame>):
  match stack:
    case Nil{}:
      Fail{Exec.underflow()}
    case f <> t:
      Exec.push(Exec.fs(f, pred, es), t)

def Exec.fsel.r(+pred: X.Expr, +es: List<&2, X.Expr>, env: P.Env, r: E.ResT(List<&1, C.Frame>)) -> St:
  match r:
    case Fail{e}:
      St{env, Fail{e}}
    case Done{stack}:
      St{env, Exec.fsel.s(pred, es, stack)}

# IFilter{pred} then ISelect{es}, as one step over the runner's state
def Exec.fsel(+pred: X.Expr, +es: List<&2, X.Expr>, st: St) -> St:
  match st:
    case St{env, r}:
      Exec.fsel.r(pred, es, env, r)

def Exec.run_phys.f(plain: Bool, +es: List<&2, X.Expr>, +pred: X.Expr, +y: P.Plan, env: P.Env) -> E.ResT(C.Frame):
  match plain:
    case True{}:
      Exec.fin(Exec.fsel(pred, es, Exec.loop(Exec.mark(Exec.compile(y, Nil{})), St{env, Done{Nil{}}})))
    case False{}:
      Exec.run_pure(P.Select{es, P.Filter{pred, y}}, env)

def Exec.run_phys.s(+es: List<&2, X.Expr>, x: P.Plan, env: P.Env) -> E.ResT(C.Frame):
  match x:
    case P.Filter{+pred, +y}:
      Exec.run_phys.f(Exec.plain(es), es, pred, y, env)
    case other:
      Exec.run_pure(P.Select{es, other}, env)

# the runner Exec.run executes: run_pure with the Sort + Head step and the Filter + Select step at
# the root
def Exec.run_phys(+p: P.Plan, env: P.Env) -> E.ResT(C.Frame):
  match p:
    case P.Head{+n, x}:
      Exec.run_phys.h(n, x, env)
    case P.Select{+es, x}:
      Exec.run_phys.s(es, x, env)
    case other:
      Exec.run_pure(other, env)

# ---- scan materialisation (the IO boundary) --------------------------------------------------
#
# Every ScanCsv of a plan is read before anything runs: scan k (postfix order, the
# order of Exec.compile and so of the runner's IScans) is read with Csv.read_with
# (strict, the plan's dtypes; W6.3: by the reader engine `eng`, Csv.read_eng: the default engine,
# v0.2 since W8, for Exec.run / Lazy.collect, chosen by Exec.run_rd / Lazy.collect_rd) and its schema must
# equal the plan's (Exec.mat). The
# frames are put, in that order, in env's scan namespace (P.Env.set_scans), which no
# Source name can reach: scans have no names (DESIGN.md 14 "v0.1 review: scan source
# identity"). The plan is not rewritten. The first failing scan is the result.

def Exec.dtypes(s: List<&2, S.Field>) -> List<&2, D.DType>:
  match s:
    case Nil{}:
      Nil{}
    case S.Field{n, t} <> rest:
      t <> Exec.dtypes(rest)

# the frames read so far (newest first), and the first scan error
type Mat is Type:
  Mat{acc: List<&1, C.Frame>, err: Maybe<&2, E.Err>}

def Exec.mat.add(acc: List<&1, C.Frame>, r: E.ResT(C.Frame)) -> Mat:
  match r:
    case Fail{e}:
      Mat{acc, Some{e}}
    case Done{f}:
      Mat{f <> acc, None{}}

# the file's schema must equal the plan's (names included)
def Exec.read.k(+path: String, s: List<&2, S.Field>, r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      Exec.check("scan_csv " ++ path, s, S.Frame.schema(f))

def Exec.mat.read(+path: String, opts: R.CsvOpts, +s: List<&2, S.Field>, acc: List<&1, C.Frame>, eng: R.CsvEngine) -> IO(Mat):
  do IO<Mat>:
    r : E.ResT(C.Frame) <- R.Csv.read_eng(eng, path, opts, Exec.dtypes(s), R.Csv.enc_default())
    return Exec.mat.add(acc, Exec.read.k(path, s, r))

# read every IScan of the code in order (stopping at the first error)
def Exec.mat(code: List<&2, Instr>, m: Mat, +eng: R.CsvEngine) -> IO(Mat):
  match code m:
    case Nil{} _:
      IO.pure(Mat, m)
    case i <> t Mat{acc, Some{e}}:
      IO.pure(Mat, Mat{acc, Some{e}})
    case IScan{path, o, s} <> t Mat{acc, None{}}:
      do IO<Mat>:
        m2 : Mat <- Exec.mat.read(path, o, s, acc, eng)
        Exec.mat(t, m2, eng)
    case i <> t Mat{acc, None{}}:
      Exec.mat(t, Mat{acc, None{}}, eng)

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

# the scans' frames (oldest first: postfix order) become env's scan namespace, whatever
# it held before; the plan runs as it is
def Exec.run.m(+p: P.Plan, env: P.Env, m: Mat) -> E.ResT(C.Frame):
  match m:
    case Mat{acc, Some{e}}:
      Fail{e}
    case Mat{acc, None{}}:
      Exec.run_phys(p, P.Env.set_scans(env, List.reverse(&1, C.Frame, acc)))

def Exec.run.v(+p: P.Plan, r: P.Env & E.Res(Unit), +eng: R.CsvEngine) -> IO(E.ResT(C.Frame)):
  (env, v) = r
  match v:
    case Fail{e}:
      IO.pure(E.ResT(C.Frame), Fail{e})
    case Done{u}:
      do IO<E.ResT(C.Frame)>:
        m : Mat <- Exec.mat(Exec.compile(p, Nil{}), Mat{Nil{}, None{}}, eng)
        return Exec.run.m(p, env, m)

def Exec.run.k(r: E.Res(List<&2, S.Field>), +p: P.Plan, env: P.Env, +eng: R.CsvEngine) -> IO(E.ResT(C.Frame)):
  match r:
    case Fail{e}:
      IO.pure(E.ResT(C.Frame), Fail{e})
    case Done{s}:
      Exec.run.v(p, Exec.validate(p, env), eng)

# run a plan as written (no optimisation) over the frames of env: the plan's
# schema is resolved first and its error, if any, is the result; then the
# bindings (Exec.validate); then every scan is read (Exec.mat, the IO
# boundary) into env's scan namespace; then the physical runner (Exec.run_phys:
# Exec.run_pure with the Sort + Head and Filter + Select steps at the root) on the plan as it is. env is
# consumed (frames the plan does not name are dropped).
# The scans are read by the default reader engine (R.Csv.engine_default: the v0.2 reader since W8).
def Exec.run(+p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  Exec.run.k(P.Plan.schema(p), p, env, R.Csv.engine_default())

# Exec.run with the scans read by the CSV reader engine eng (D7, W6.3: R.CsvV01{} selects the v0.1
# reader, R.CsvV02{piece} the v0.2 reader at a piece size; the result is the same frame or error,
# DESIGN.md 17.4)
def Exec.run_rd(+eng: R.CsvEngine, +p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  Exec.run.k(P.Plan.schema(p), p, env, eng)

# ---- the engine hook (v0.2 T5.3, DESIGN.md 16.5 D7) ------------------------------------------
# Everything Exec.run does BEFORE the physical runner, as one step: the plan's schema, the bindings
# (Exec.validate), every scan read by the CSV engine eng (Exec.mat) into env's scan namespace. The
# answer is the env the physical runner gets (Exec.run.m's), or the first error, in Exec.run's order.
# src/cexec.bend (the chunked runner, Exec.run_with) calls it and then runs its own step function;
# nothing here changes what Exec.run / Lazy.collect do.

def Exec.prep.m(env: P.Env, m: Mat) -> E.ResT(P.Env):
  match m:
    case Mat{acc, Some{e}}:
      Fail{e}
    case Mat{acc, None{}}:
      Done{P.Env.set_scans(env, List.reverse(&1, C.Frame, acc))}

def Exec.prep.v(+p: P.Plan, r: P.Env & E.Res(Unit), +eng: R.CsvEngine) -> IO(E.ResT(P.Env)):
  (env, v) = r
  match v:
    case Fail{e}:
      IO.pure(E.ResT(P.Env), Fail{e})
    case Done{u}:
      do IO<E.ResT(P.Env)>:
        m : Mat <- Exec.mat(Exec.compile(p, Nil{}), Mat{Nil{}, None{}}, eng)
        return Exec.prep.m(env, m)

def Exec.prep.k(r: E.Res(List<&2, S.Field>), +p: P.Plan, env: P.Env, +eng: R.CsvEngine) -> IO(E.ResT(P.Env)):
  match r:
    case Fail{e}:
      IO.pure(E.ResT(P.Env), Fail{e})
    case Done{s}:
      Exec.prep.v(p, Exec.validate(p, env), eng)

def Exec.prep(+eng: R.CsvEngine, +p: P.Plan, env: P.Env) -> IO(E.ResT(P.Env)):
  Exec.prep.k(P.Plan.schema(p), p, env, eng)

# Polars collect(): the release optimizer (Optimize.release), then run
def Lazy.collect(+p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  Exec.run(P.Optimize.release(p), env)

# Lazy.collect with the scans read by the CSV reader engine eng (D7, W6.3)
def Lazy.collect_rd(+eng: R.CsvEngine, +p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  Exec.run_rd(eng, P.Optimize.release(p), env)

# every rewrite of Plan.optimize_full (opt-in, outside the guarantee), then run
def Lazy.collect_full(+p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  Exec.run(P.Plan.optimize_full(p), env)
