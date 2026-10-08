# M7 benchmark driver (Bend side). Native only:
#   ~/.bend/bin/bend bench/main.bend -o build/bench
#   ./build/bench [--threads N] <sales.csv> <q1..q6|parse> [repeats [batch [label [out.csv [consume]]]]]
#
# The CSVs (sales + the sibling products.csv) are parsed UNTIMED into frames and
# every buffer is walked once (`force`) before the clock starts. The timed
# region is `Lazy.collect` (plan optimisation + execution) over those Source
# frames (q6: the eager `describe`), result kept alive until after `IO.now`
# (freeing a big result is not free, IMPLEMENTING.md "M5 join").
#
# Inputs: the run is over a CLONE of the parsed frames and the originals stay
# referenced until after the clock (like Polars, whose inputs survive collect).
# With the 7th arg `consume` the run consumes the parsed frames, so freeing the
# 1M-row string columns happens inside the timed region (~250 ms at 1M).
#
#   repeats  rounds in this process, each over freshly parsed inputs; best kept
#            (default 1: parsing again in one process gets slower and slower, so
#            scripts/bench.sh runs one round per process and keeps the best)
#   batch    collects per timed window, each over its own freshly parsed inputs;
#            window / batch is the per-collect time (IO.now has 1 ms resolution,
#            so tiny inputs need batch > 1; batches also distort: default 1)
#   label    value printed in the "threads" field ("default" when absent; the
#            runtime flag --threads is not visible in IO.args); a number stays a number
#   out.csv  write the first result there, floats with 4 decimals (untimed)
#   parse    pseudo query: times Csv.read of the sales file and the first full walk
#
# stdout: one JSON line {"query":..,"n":..,"seconds":..,"threads":..}
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/kernels.bend as K
import ./../src/column.bend as C
import ./../src/strs.bend as ST
import ./../src/csv.bend as V
import ./../src/join.bend as J
import ./../src/plan.bend as P
import ./../src/exec.bend as X
import ./queries.bend as QS

type In is Type:
  In{s: C.Frame, p: C.Frame, ks: C.Frame, kp: C.Frame, n: U32, chk: U32}

# ---- forcing (see bench/join_bench.bend): every cell read once, untimed ----------------

def fw.k(t: D.DType, +n: U32, d: Nat, v: C.Valid, r: Array<U32> & U32) -> C.Column & U32:
  (x, h) = r
  (C.Column.mk_w(t, n, d, v, x), h)

def ff.k(+n: U32, d: Nat, v: C.Valid, r: Array<F32> & F32) -> C.Column & U32:
  (x, h) = r
  (C.CF32{n, d, v, x}, F32.to_u32(h))

def fs.k(+n: U32, d: Nat, v: C.Valid, r: ST.Strs & U32) -> C.Column & U32:
  (x, h) = r
  (C.CStr{n, d, v, x}, h)

def fs.r(r: Array<String> & U32) -> ST.Strs & U32:
  (a, h) = r
  (ST.SRaw{a}, h)

def fs.d(dict: ST.Dict, r: Array<U32> & U32) -> ST.Strs & U32:
  (c, h) = r
  (ST.SDict{c, dict}, h)

# a Raw column: every string hashed; a Dictionary: every code summed
def fs.walk(+n: U32, x: ST.Strs) -> ST.Strs & U32:
  match x:
    case ST.SRaw{a}:
      fs.r(K.Kernel.fold(~String, ~U32, ~(a => y => U32.add(a, J.Str.hash(y, 0))), n, a, 0))
    case ST.SDict{c, dict}:
      fs.d(dict, K.Kernel.fold(~U32, ~U32, ~(a => y => U32.add(a, y)), n, c, 0))

def force.col(c: C.Column) -> C.Column & U32:
  match c:
    case C.CBool{+n, d, v, x}:
      fw.k(D.TBool{}, n, d, v, K.Kernel.fold(~U32, ~U32, ~(a => y => U32.add(a, y)), n, x, 0))
    case C.CU32{+n, d, v, x}:
      fw.k(D.TU32{}, n, d, v, K.Kernel.fold(~U32, ~U32, ~(a => y => U32.add(a, y)), n, x, 0))
    case C.CI32{+n, d, v, x}:
      fw.k(D.TI32{}, n, d, v, K.Kernel.fold(~U32, ~U32, ~(a => y => U32.add(a, y)), n, x, 0))
    case C.CF32{+n, d, v, x}:
      ff.k(n, d, v, K.Kernel.fold(~F32, ~F32, ~(a => y => F32.add(a, y)), n, x, 0.0))
    case C.CStr{+n, d, v, x}:
      fs.k(n, d, v, fs.walk(n, x))

def force.add(n: String, acc: List<&1, C.Named>, +h: U32, r: C.Column & U32) -> List<&1, C.Named> & U32:
  (c, x) = r
  (C.Named{n, c} <> acc, U32.add(h, x))

def force.step(n: String, c: C.Column, st: List<&1, C.Named> & U32) -> List<&1, C.Named> & U32:
  (acc, +h) = st
  force.add(n, acc, h, force.col(c))

def force.go(cols: List<&1, C.Named>, st: List<&1, C.Named> & U32) -> List<&1, C.Named> & U32:
  match cols:
    case Nil{}:
      st
    case C.Named{n, c} <> rest:
      force.go(rest, force.step(n, c, st))

def force.fin(+h: U32, r: List<&1, C.Named> & U32) -> C.Frame & U32:
  (acc, x) = r
  (C.Frame{h, List.reverse(&1, C.Named, acc)}, x)

def force(f: C.Frame) -> C.Frame & U32:
  match f:
    case C.Frame{+h, cols}:
      force.fin(h, force.go(cols, (Nil{}, 0)))

# ---- keeping the inputs alive ------------------------------------------------------------------
# (`keep`: the query runs over a clone and the original stays referenced until after the clock,
# like Polars, whose inputs survive the collect; otherwise the run consumes and frees the inputs)

def fclone.add(+n: String, a: List<&1, C.Named>, b: List<&1, C.Named>, r: C.Column & C.Column) -> List<&1, C.Named> & List<&1, C.Named>:
  (c1, c2) = r
  (C.Named{n, c1} <> a, C.Named{n, c2} <> b)

def fclone.step(+n: String, c: C.Column, st: List<&1, C.Named> & List<&1, C.Named>) -> List<&1, C.Named> & List<&1, C.Named>:
  (a, b) = st
  fclone.add(n, a, b, C.Column.clone(c))

def fclone.go(cols: List<&1, C.Named>, st: List<&1, C.Named> & List<&1, C.Named>) -> List<&1, C.Named> & List<&1, C.Named>:
  match cols:
    case Nil{}:
      st
    case C.Named{n, c} <> t:
      fclone.go(t, fclone.step(n, c, st))

def fclone.k(+h: U32, r: List<&1, C.Named> & List<&1, C.Named>) -> C.Frame & C.Frame:
  (a, b) = r
  (C.Frame{h, List.reverse(&1, C.Named, a)}, C.Frame{h, List.reverse(&1, C.Named, b)})

def fclone(f: C.Frame) -> C.Frame & C.Frame:
  match f:
    case C.Frame{+h, cols}:
      fclone.k(h, fclone.go(cols, (Nil{}, Nil{})))

# (used, kept): a clone when `keep`, else the frame itself and an empty kept frame
def dup(+keep: Bool, f: C.Frame) -> C.Frame & C.Frame:
  match keep:
    case True{}:
      fclone(f)
    case False{}:
      (f, C.Frame.empty())

# ---- loading -------------------------------------------------------------------------------------

def load.k3(+n: U32, +x: U32, +y: U32, rks: C.Frame & C.Frame, rkp: C.Frame & C.Frame) -> In:
  (s2, ks) = rks
  (p2, kp) = rkp
  In{s2, p2, ks, kp, n, U32.add(x, y)}

def load.k(+keep: Bool, +n: U32, rs: C.Frame & U32, rp: C.Frame & U32) -> In:
  (s, +x) = rs
  (p, +y) = rp
  load.k3(n, x, y, dup(keep, s), dup(keep, p))

def load.p(+keep: Bool, +n: U32, s: C.Frame, rp: E.ResT(C.Frame)) -> E.ResT(In):
  match rp:
    case Fail{e}:
      Fail{e}
    case Done{p}:
      Done{load.k(keep, n, force(s), force(p))}

def load.h(+keep: Bool, r: C.Frame & U32, rp: E.ResT(C.Frame)) -> E.ResT(In):
  (s, +n) = r
  load.p(keep, n, s, rp)

def load.s(+keep: Bool, rs: E.ResT(C.Frame), rp: E.ResT(C.Frame)) -> E.ResT(In):
  match rs:
    case Fail{e}:
      Fail{e}
    case Done{s}:
      load.h(keep, C.Frame.height(s), rp)

def load(+keep: Bool, +path: String, +ppath: String) -> IO(E.ResT(In)):
  do IO<E.ResT(In)>:
    rs : E.ResT(C.Frame) <- V.Csv.read(path, V.Csv.default())
    rp : E.ResT(C.Frame) <- V.Csv.read(ppath, V.Csv.default())
    return load.s(keep, rs, rp)

def load.push.a(i: In, acc: E.ResT(List<&1, In>)) -> E.ResT(List<&1, In>):
  match acc:
    case Fail{e}:
      Fail{e}
    case Done{rest}:
      Done{i <> rest}

def load.push(r: E.ResT(In), acc: E.ResT(List<&1, In>)) -> E.ResT(List<&1, In>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{i}:
      load.push.a(i, acc)

# m inputs, each parsed on its own
def load.many(+keep: Bool, +m: Nat, +path: String, +ppath: String, acc: E.ResT(List<&1, In>)) -> IO(E.ResT(List<&1, In>)):
  match m:
    case 0n:
      IO.pure(E.ResT(List<&1, In>), acc)
    case 1n+k:
      do IO<E.ResT(List<&1, In>)>:
        r : E.ResT(In) <- load(keep, path, ppath)
        load.many(keep, k, path, ppath, load.push(r, acc))

# ---- the job: one collect over one input ------------------------------------------------------

def plan_of(+q: String, +s: P.Plan, +p: P.Plan) -> P.Plan:
  Bool.pick(P.Plan, String.eq(q, "q1"), QS.Q.q1(s, p),
  Bool.pick(P.Plan, String.eq(q, "q2"), QS.Q.q2(s, p),
  Bool.pick(P.Plan, String.eq(q, "q3"), QS.Q.q3(s, p),
  Bool.pick(P.Plan, String.eq(q, "q4"), QS.Q.q4(s, p), QS.Q.q5(s, p)))))

def job.b(+q: String, +s: P.Plan, r: P.Env & P.Plan) -> IO(E.ResT(C.Frame)):
  (env, +p) = r
  X.Lazy.collect(plan_of(q, s, p), env)

def job.a(+q: String, r: P.Env & P.Plan, p: C.Frame) -> IO(E.ResT(C.Frame)):
  (env, +s) = r
  job.b(q, s, P.Env.add(env, "products", p))

def job.k(+is6: Bool, +q: String, s: C.Frame, p: C.Frame) -> IO(E.ResT(C.Frame)):
  match is6:
    case True{}:
      IO.pure(E.ResT(C.Frame), QS.Q.q6(s))
    case False{}:
      job.a(q, P.Lazy.source("sales", s), p)

def job.w(r: E.ResT(C.Frame), ks: C.Frame, kp: C.Frame) -> List<&1, E.ResT(C.Frame)>:
  r <> Done{ks} <> Done{kp} <> Nil{}

# the result, then the kept inputs
def job.i(r: E.ResT(C.Frame), ks: C.Frame, kp: C.Frame) -> IO(List<&1, E.ResT(C.Frame)>):
  IO.pure(List<&1, E.ResT(C.Frame)>, job.w(r, ks, kp))

def job(+is6: Bool, +q: String, i: In) -> IO(List<&1, E.ResT(C.Frame)>):
  match i:
    case In{s, p, ks, kp, n, chk}:
      do IO<List<&1, E.ResT(C.Frame)>>:
        r : E.ResT(C.Frame) <- job.k(is6, q, s, p)
        job.i(r, ks, kp)

def cat(xs: List<&1, E.ResT(C.Frame)>, ys: List<&1, E.ResT(C.Frame)>) -> List<&1, E.ResT(C.Frame)>:
  match xs:
    case Nil{}:
      ys
    case x <> t:
      x <> cat(t, ys)

def run.all(ins: List<&1, In>, +is6: Bool, +q: String, acc: List<&1, E.ResT(C.Frame)>) -> IO(List<&1, E.ResT(C.Frame)>):
  match ins:
    case Nil{}:
      IO.pure(List<&1, E.ResT(C.Frame)>, acc)
    case i <> t:
      do IO<List<&1, E.ResT(C.Frame)>>:
        r : List<&1, E.ResT(C.Frame)> <- job(is6, q, i)
        run.all(t, is6, q, cat(r, acc))

# window in ms and the results (alive past the clock)
def round(ins: List<&1, In>, +is6: Bool, +q: String) -> IO(U32 & List<&1, E.ResT(C.Frame)>):
  do IO<U32 & List<&1, E.ResT(C.Frame)>>:
    t0 : Nat <- IO.now()
    rs : List<&1, E.ResT(C.Frame)> <- run.all(ins, is6, q, Nil{})
    t1 : Nat <- IO.now()
    return (U32.from_nat(Nat.sub(t1, t0)), rs)

# ---- output ---------------------------------------------------------------------------------------

def pad6(+k: Nat, +s: String) -> String:
  match k:
    case 0n:
      s
    case 1n+j:
      pad6(j, "0" ++ s)

def secs(+us: U32) -> String:
  +f = U32.show(U32.mod(us, 1000000))
  U32.show(U32.div(us, 1000000)) ++ "." ++ pad6(Nat.sub(6n, String.length(f)), f)

def thr.k(m: Maybe<&2, Nat>, +label: String) -> String:
  match m:
    case None{}:
      "\"" ++ label ++ "\""
    case Some{v}:
      label

# a number stays a number, anything else is quoted
def thr(+label: String) -> String:
  thr.k(Nat.read(label), label)

def json(+q: String, +n: U32, +ms: U32, +m: Nat, +label: String) -> String:
  +us = U32.div(U32.mul(ms, 1000), U32.from_nat(m))
  "{\"query\":\"" ++ q ++ "\",\"n\":" ++ U32.show(n) ++ ",\"seconds\":" ++ secs(us) ++ ",\"threads\":" ++ thr(label) ++ "}"

def out.c(r: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (file, w) = r
  do IO<Unit>:
    File.close(file)

def out.o(+text: String, o: Result<&1, &1, U32 & String, File>) -> IO(Unit):
  match o:
    case Done{file}:
      do IO<Unit>:
        r : File & Result<&1, &1, U32 & String, Unit> <- File.write(file, text)
        out.c(r)
    case Fail{(code, msg)}:
      IO.print("cannot open output: " ++ msg)

def out.w(+path: String, text: String) -> IO(Unit):
  do IO<Unit>:
    o : Result<&1, &1, U32 & String, File> <- File.open(path, "w")
    out.o(text, o)

def out.r(+path: String, r: C.Frame & String) -> IO(Unit):
  (f, text) = r
  out.w(path, text)

def out.res(+path: String, r: E.ResT(C.Frame)) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("error: " ++ E.Err.show(e))
    case Done{f}:
      out.r(path, V.Csv.render(f, Some{4}))

# first result: error text (or write the file when asked); the rest are dropped
def fin.w(+write: Bool, +path: String, f: C.Frame) -> IO(String):
  match write:
    case True{}:
      do IO<String>:
        out.r(path, V.Csv.render(f, Some{4}))
        return ""
    case False{}:
      IO.pure(String, "")

def fin.one(+write: Bool, +path: String, r: E.ResT(C.Frame)) -> IO(String):
  match r:
    case Fail{e}:
      IO.pure(String, "error: " ++ E.Err.show(e))
    case Done{f}:
      fin.w(write, path, f)

def fin.first(+write: Bool, +path: String, rs: List<&1, E.ResT(C.Frame)>) -> IO(String):
  match rs:
    case Nil{}:
      IO.pure(String, "")
    case r <> t:
      fin.one(write, path, r)

# ---- rounds ---------------------------------------------------------------------------------------

type Meas is Data:
  Meas{ms: U32, n: U32, err: String}

def ins.n.k(+n: U32, s: C.Frame, p: C.Frame, ks: C.Frame, kp: C.Frame, chk: U32, t: List<&1, In>) -> List<&1, In> & U32:
  (In{s, p, ks, kp, n, chk} <> t, n)

def ins.n(ins: List<&1, In>) -> List<&1, In> & U32:
  match ins:
    case Nil{}:
      (Nil{}, 0)
    case i <> t:
      match i:
        case In{s, p, ks, kp, +n, chk}:
          ins.n.k(n, s, p, ks, kp, chk, t)

def measure.e(+ms: U32, +n: U32, e: String) -> IO(Meas):
  IO.pure(Meas, Meas{ms, n, e})

def measure.b(w: U32 & List<&1, E.ResT(C.Frame)>, +n: U32, +write: Bool, +out: String) -> IO(Meas):
  (+ms, rs) = w
  do IO<Meas>:
    e : String <- fin.first(write, out, rs)
    measure.e(ms, n, e)

def measure.n(r: List<&1, In> & U32, +is6: Bool, +q: String, +write: Bool, +out: String) -> IO(Meas):
  (ins, +n) = r
  do IO<Meas>:
    w : U32 & List<&1, E.ResT(C.Frame)> <- round(ins, is6, q)
    measure.b(w, n, write, out)

def measure(r: E.ResT(List<&1, In>), +is6: Bool, +q: String, +write: Bool, +out: String) -> IO(Meas):
  match r:
    case Fail{e}:
      IO.pure(Meas, Meas{4294967295, 0, "error: " ++ E.Err.show(e)})
    case Done{ins}:
      measure.n(ins.n(ins), is6, q, write, out)

def best.min(+a: U32, +b: U32) -> U32:
  Bool.pick(U32, U32.is_lt(a, b), a, b)

def best.err(+a: String, +b: String) -> String:
  Bool.pick(String, String.is_empty(a), b, a)

def fin.json(+q: String, +m: Nat, +label: String, +n: U32, +ms: U32, +err: String) -> IO(Unit):
  IO.print(Bool.pick(String, String.is_empty(err), json(q, n, ms, m, label), err))

def mm.n(+r: Meas) -> U32:
  match r:
    case Meas{ms, n, e}:
      n

def mm.ms(+r: Meas, +best: U32) -> U32:
  match r:
    case Meas{ms, n, e}:
      best.min(best, ms)

def mm.err(+r: Meas, +err: String) -> String:
  match r:
    case Meas{ms, n, e}:
      best.err(err, e)

# `best` starts at 2^32-1: the first round also writes the output file
def loop(+reps: Nat, +path: String, +ppath: String, +m: Nat, +is6: Bool, +q: String, +label: String, +out: String, +keep: Bool, +n: U32, +best: U32, +err: String) -> IO(Unit):
  match reps:
    case 0n:
      fin.json(q, m, label, n, best, err)
    case 1n+k:
      do IO<Unit>:
        r : E.ResT(List<&1, In>) <- load.many(keep, m, path, ppath, Done{Nil{}})
        +mm : Meas <- measure(r, is6, q, Bool.and(Bool.not(String.is_empty(out)), U32.is_eq(best, 4294967295)), out)
        loop(k, path, ppath, m, is6, q, label, out, keep, mm.n(mm), mm.ms(mm, best), mm.err(mm, err))

# ---- args -------------------------------------------------------------------------------------------

def nth(+i: Nat, xs: List<&2, String>, +d: String) -> String:
  match i xs:
    case _ Nil{}:
      d
    case 0n h <> t:
      h
    case 1n+j h <> t:
      nth(j, t, d)

def nat.of(m: Maybe<&2, Nat>, +d: Nat) -> Nat:
  match m:
    case None{}:
      d
    case Some{v}:
      v

def dir.go(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{'/', t}:
      SCon{'/', t}
    case SCon{h, t}:
      dir.go(t)

def products_path(+path: String) -> String:
  String.reverse(dir.go(String.reverse(path))) ++ "products.csv"

# query "parse": Csv.read of the sales file (ms), then the first full walk of its buffers
# (ms; the read's last work is still pending when it returns), in one JSON-ish line
def parse.fin(+n: U32, +t0: Nat, +t1: Nat, +t2: Nat, +x: U32) -> IO(Unit):
  IO.print("{\"query\":\"parse\",\"n\":" ++ U32.show(n) ++ ",\"read_ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"first_walk_ms\":" ++ Nat.show(Nat.sub(t2, t1)) ++ ",\"chk\":" ++ U32.show(x) ++ "}")

def parse.f(+t0: Nat, +t1: Nat, r: C.Frame & U32) -> IO(Unit):
  (f, +x) = r
  do IO<Unit>:
    t2 : Nat <- IO.now()
    parse.fin(0, t0, t1, t2, x)

def parse.k(+t0: Nat, +t1: Nat, r: E.ResT(C.Frame)) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("error: " ++ E.Err.show(e))
    case Done{f}:
      parse.f(t0, t1, force(f))

def parse.run(+path: String) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    r : E.ResT(C.Frame) <- V.Csv.read(path, V.Csv.default())
    t1 : Nat <- IO.now()
    parse.k(t0, t1, r)

def start.k(+is_parse: Bool, +path: String, +q: String, +reps: Nat, +m: Nat, +label: String, +out: String, +keep: Bool) -> IO(Unit):
  match is_parse:
    case True{}:
      parse.run(path)
    case False{}:
      loop(reps, path, products_path(path), m, String.eq(q, "q6"), q, label, out, keep, 0, 4294967295, "")

def start(+path: String, +q: String, +reps: Nat, +m: Nat, +label: String, +out: String, +keep: Bool) -> IO(Unit):
  start.k(String.eq(q, "parse"), path, q, reps, m, label, out, keep)

def run(+path: String, +q: String, +reps: Nat, +m: Nat, +label: String, +out: String, +keep: Bool) -> IO(Unit):
  start(path, q, reps, m, label, out, keep)

def promote(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> promote(t)

# args after the program name: csv query [repeats [batch [label [out.csv]]]]
def go(+xs: List<&2, String>) -> IO(Unit):
  run(nth(0n, xs, "bench/data/sales_1000.csv"), nth(1n, xs, "q1"), nat.of(Nat.read(nth(2n, xs, "1")), 1n), nat.of(Nat.read(nth(3n, xs, "1")), 1n), nth(4n, xs, "default"), nth(5n, xs, ""), Bool.not(String.eq(nth(6n, xs, ""), "consume")))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(List.tail(&2, String, promote(args)))
