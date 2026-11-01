# PDS-H-style driver (native only; TPCH_OPT=full runs DF.collect_full, TPCH_OPT=release the Head merging alone):
#   ~/.bend/bin/bend bench/tpch/run.bend -o build/tpch
#   ./build/tpch [+RTS --threads N -RTS] <dir> <q1..q18|all> [repeats [outdir]]
# <dir> holds the bench/tpch/gen.py tables. Every table is read once with DF.read_csv (each read
# timed, then forced by a clone); each query then runs `repeats` times over a fresh clone of the
# inputs (untimed), the timed region being DF.collect alone, as in bench/main.bend. With `outdir`
# the first result of each query is written there as <q>.csv (4 decimals, untimed).
# stdout: one JSON line per read and per query {"query":..,"ms":[..],"rows":..}
import Base
import ./../../frame.bend as DF
import ./../../src/column.bend as C
import ./../../src/err.bend as E
import ./../../src/csv.bend as V
import ./queries.bend as Q
import ./../../src/plan.bend as P

type Ins is Type:
  Ins{l: C.Frame, o: C.Frame, c: C.Frame, s: C.Frame, n: C.Frame, r: C.Frame}

# shift every frame one slot left, the new one last (six pushes rotate back to the order)
def Ins.push(i: Ins, x: C.Frame) -> Ins:
  match i:
    case Ins{l, o, c, s, n, r}:
      Ins{o, c, s, n, r, x}

def Ins.clone.k(i: Ins & Ins, f: C.Frame & C.Frame) -> Ins & Ins:
  (a, b) = i
  (x, y) = f
  (Ins.push(a, x), Ins.push(b, y))

def Ins.clone.pop(a: Ins, b: Ins) -> Ins & Ins:
  match a:
    case Ins{l, o, c, s, n, r}:
      Ins.clone.k((Ins{C.Frame.empty(), o, c, s, n, r}, b), DF.clone(l))

def Ins.clone.step(i: Ins & Ins) -> Ins & Ins:
  (a, b) = i
  Ins.clone.pop(a, b)

def Ins.clone.go(+k: Nat, i: Ins & Ins) -> Ins & Ins:
  match k:
    case 0n:
      i
    case 1n+j:
      Ins.clone.go(j, Ins.clone.step(i))

# a deep copy: (used, kept)
def Ins.clone(i: Ins) -> Ins & Ins:
  Ins.clone.go(6n, (i, Ins{C.Frame.empty(), C.Frame.empty(), C.Frame.empty(), C.Frame.empty(), C.Frame.empty(), C.Frame.empty()}))

type Meas is Data:
  Meas{ms: Nat, rows: U32, e: String}

type Sum is Data:
  Sum{ms: String, rows: U32, e: String}

def Sum.json(+q: String, +m: Sum) -> String:
  match m:
    case Sum{ms, rows, e}:
      "{\"query\":\"" ++ q ++ "\",\"ms\":[" ++ ms ++ "],\"rows\":" ++ U32.show(rows) ++ ",\"error\":" ++ e ++ "}"

type Info is Data:
  Info{rows: U32, e: String}

def Info.rows(+i: Info) -> U32:
  match i:
    case Info{rows, e}:
      rows

def Info.e(+i: Info) -> String:
  match i:
    case Info{rows, e}:
      e

def summ.k(r: C.Frame & U32) -> E.ResT(C.Frame) & Info:
  (f, +h) = r
  (Done{f}, Info{h, "null"})

# the result back, its height (0 on an error) and the error as JSON (null when none)
def summ(r: E.ResT(C.Frame)) -> E.ResT(C.Frame) & Info:
  match r:
    case Fail{+e}:
      (Fail{e}, Info{0, "\"" ++ E.Err.show(e) ++ "\""})
    case Done{f}:
      summ.k(DF.height(f))

# ---- output -----------------------------------------------------------------------------------

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

def out.r(+path: String, r: C.Frame & String) -> IO(Unit):
  (f, +text) = r
  do IO<Unit>:
    o : Result<&1, &1, U32 & String, File> <- File.open(path, "w")
    out.o(text, o)

def out.res(+path: String, r: E.ResT(C.Frame)) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("error: " ++ E.Err.show(e))
    case Done{f}:
      out.r(path, V.Csv.render(f, Some{4}))

def out.when(+w: Bool, +path: String, r: E.ResT(C.Frame)) -> IO(Unit):
  match w:
    case True{}:
      out.res(path, r)
    case False{}:
      IO.pure(Unit, Unit{})

def out.maybe(+dir: String, +q: String, +first: Bool, r: E.ResT(C.Frame)) -> IO(Unit):
  out.when(Bool.and(first, Bool.not(String.is_empty(dir))), dir ++ "/" ++ q ++ ".csv", r)

# ---- one query ---------------------------------------------------------------------------------

def env.k(ps: List<&2, DF.Plan()>, r: DF.Env() & DF.Plan()) -> DF.Env() & List<&2, DF.Plan()>:
  (e, p) = r
  (e, List.append(&2, DF.Plan(), ps, [p]))

def env.add(+name: String, f: C.Frame, acc: DF.Env() & List<&2, DF.Plan()>) -> DF.Env() & List<&2, DF.Plan()>:
  (e, ps) = acc
  env.k(ps, DF.add_source(e, name, f))

def env(i: Ins) -> DF.Env() & List<&2, DF.Plan()>:
  match i:
    case Ins{l, o, c, s, n, r}:
      env.add("region", r, env.add("nation", n, env.add("supplier", s, env.add("customer", c, env.add("orders", o, env.add("lineitem", l, (DF.empty_env(), Nil{})))))))

def nth(+k: Nat, xs: List<&2, DF.Plan()>) -> DF.Plan():
  match k xs:
    case _ Nil{}:
      DF.lazy_head(DF.lazy_select(DF.scan_csv_schema("", DF.csv_opts(',', True{}, 1), []), []), 0)
    case 0n h <> t:
      h
    case 1n+j h <> t:
      nth(j, t)

def plan(+q: String, +ps: List<&2, DF.Plan()>) -> DF.Plan():
  Q.T.plan(q, nth(0n, ps), nth(1n, ps), nth(2n, ps), nth(3n, ps), nth(4n, ps), nth(5n, ps))

def once.s(+q: String, +dir: String, +first: Bool, +ms: Nat, x: E.ResT(C.Frame) & Info) -> IO(Meas):
  (r, +i) = x
  do IO<Meas>:
    out.maybe(dir, q, first, r)
    return Meas{ms, Info.rows(i), Info.e(i)}

def once.k(+q: String, +dir: String, +first: Bool, +t0: Nat, r: E.ResT(C.Frame)) -> IO(Meas):
  do IO<Meas>:
    t1 : Nat <- IO.now()
    once.s(q, dir, first, Nat.sub(t1, t0), summ(r))

def collect.full(+full: Bool, +p: DF.Plan(), e: DF.Env()) -> IO(E.ResT(C.Frame)):
  match full:
    case True{}:
      DF.collect_full(p, e)
    case False{}:
      DF.collect(p, e)

def collect.rel(+rel: Bool, +v: String, +p: DF.Plan(), e: DF.Env()) -> IO(E.ResT(C.Frame)):
  match rel:
    case True{}:
      DF.collect_raw(P.Optimize.release(p), e)
    case False{}:
      collect.full(String.eq(v, "full"), p, e)

# TPCH_OPT=full: DF.collect_full (the opt-in optimizer); TPCH_OPT=release: Head merging alone, without the
# default's projection pushdown (P.Optimize.release, decision D1's comparison); unset or anything else: DF.collect
def collect.by(ev: Result<&1, &1, U32 & String, String>, +p: DF.Plan(), e: DF.Env()) -> IO(E.ResT(C.Frame)):
  match ev:
    case Done{+v}:
      collect.rel(String.eq(v, "release"), v, p, e)
    case Fail{x}:
      DF.collect(p, e)

def once.e(+q: String, +dir: String, +first: Bool, ep: DF.Env() & List<&2, DF.Plan()>) -> IO(Meas):
  (e, +ps) = ep
  +p = plan(q, ps)
  do IO<Meas>:
    t0 : Nat <- IO.now()
    ev : Result<&1, &1, U32 & String, String> <- IO.get_env("TPCH_OPT")
    r : E.ResT(C.Frame) <- collect.by(ev, p, e)
    once.k(q, dir, first, t0, r)

# (ms, rows, error) of one collect over x, which it consumes
def once(+q: String, +dir: String, +first: Bool, x: Ins) -> IO(Meas):
  once.e(q, dir, first, env(x))

def m.ms(+m: Meas) -> Nat:
  match m:
    case Meas{ms, rows, e}:
      ms

def m.rows(+m: Meas) -> U32:
  match m:
    case Meas{ms, rows, e}:
      rows

def m.e(+m: Meas) -> String:
  match m:
    case Meas{ms, rows, e}:
      e

def reps.keep(p: Ins & Ins) -> Ins:
  (x, keep) = p
  keep

# k collects, each over its own clone; answers the kept inputs, the times, rows and error of the last
def reps(+k: Nat, +q: String, +dir: String, +first: Bool, +acc: String, +rows: U32, +e: String, p: Ins & Ins) -> IO(Ins & Sum):
  match k:
    case 0n:
      IO.pure(Ins & Sum, (reps.keep(p), Sum{acc, rows, e}))
    case 1n+j:
      (x, keep) = p
      do IO<Ins & Sum>:
        +m : Meas <- once(q, dir, first, x)
        reps(j, q, dir, False{}, acc ++ Bool.pick(String, String.is_empty(acc), "", ",") ++ Nat.show(m.ms(m)), m.rows(m), m.e(m), Ins.clone(keep))

def query.k(r: Ins & Sum, +q: String) -> IO(Ins):
  (i, +m) = r
  do IO<Ins>:
    IO.print(Sum.json(q, m))
    return i

def query(+q: String, +k: Nat, +dir: String, i: Ins) -> IO(Ins):
  do IO<Ins>:
    r : Ins & Sum <- reps(k, q, dir, True{}, "", 0, "null", Ins.clone(i))
    query.k(r, q)

def queries(qs: List<&2, String>, +k: Nat, +dir: String, i: Ins) -> IO(Ins):
  match qs:
    case Nil{}:
      IO.pure(Ins, i)
    case q <> t:
      do IO<Ins>:
        j : Ins <- query(q, k, dir, i)
        queries(t, k, dir, j)

# ---- reading ------------------------------------------------------------------------------------

def read.s(+name: String, +ms: Nat, x: E.ResT(C.Frame) & Info) -> IO(E.ResT(C.Frame)):
  (r, +i) = x
  do IO<E.ResT(C.Frame)>:
    IO.print("{\"read\":\"" ++ name ++ "\",\"ms\":" ++ Nat.show(ms) ++ ",\"rows\":" ++ U32.show(Info.rows(i)) ++ ",\"error\":" ++ Info.e(i) ++ "}")
    return r

def read.k(+name: String, +t0: Nat, r: E.ResT(C.Frame)) -> IO(E.ResT(C.Frame)):
  do IO<E.ResT(C.Frame)>:
    t1 : Nat <- IO.now()
    read.s(name, Nat.sub(t1, t0), summ(r))

def read(+dir: String, +name: String) -> IO(E.ResT(C.Frame)):
  do IO<E.ResT(C.Frame)>:
    t0 : Nat <- IO.now()
    r : E.ResT(C.Frame) <- DF.read_csv(dir ++ "/" ++ name ++ ".csv")
    read.k(name, t0, r)

def run.ab(qs: List<&2, String>, +k: Nat, +out: String, p: Ins & Ins) -> IO(Unit):
  (a, b) = p
  do IO<Unit>:
    x : Ins <- queries(qs, k, out, a)
    return Unit{}

# one clone forces every buffer of the inputs before the first clock
def run.ins(qs: List<&2, String>, +k: Nat, +out: String, i: Ins) -> IO(Unit):
  run.ab(qs, k, out, Ins.clone(i))

def run.all(qs: List<&2, String>, +k: Nat, +out: String, l: E.ResT(C.Frame), o: E.ResT(C.Frame), c: E.ResT(C.Frame), s: E.ResT(C.Frame), n: E.ResT(C.Frame), r: E.ResT(C.Frame)) -> IO(Unit):
  match l o c s n r:
    case Done{l} Done{o} Done{c} Done{s} Done{n} Done{r}:
      run.ins(qs, k, out, Ins{l, o, c, s, n, r})
    case _ _ _ _ _ _:
      IO.print("error: an input failed to read")

def go(+dir: String, +qs: List<&2, String>, +k: Nat, +out: String) -> IO(Unit):
  do IO<Unit>:
    l : E.ResT(C.Frame) <- read(dir, "lineitem")
    o : E.ResT(C.Frame) <- read(dir, "orders")
    c : E.ResT(C.Frame) <- read(dir, "customer")
    s : E.ResT(C.Frame) <- read(dir, "supplier")
    n : E.ResT(C.Frame) <- read(dir, "nation")
    r : E.ResT(C.Frame) <- read(dir, "region")
    run.all(qs, k, out, l, o, c, s, n, r)

# ---- args ---------------------------------------------------------------------------------------

def arg(+i: Nat, xs: List<&2, String>, +d: String) -> String:
  match i xs:
    case _ Nil{}:
      d
    case 0n h <> t:
      h
    case 1n+j h <> t:
      arg(j, t, d)

def nat.of(m: Maybe<&2, Nat>, +d: Nat) -> Nat:
  match m:
    case None{}:
      d
    case Some{v}:
      v

def promote(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> promote(t)

def which(+q: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.eq(q, "all"), Q.T.names(), [q])

def start(+xs: List<&2, String>) -> IO(Unit):
  go(arg(0n, xs, "bench/data/tpch/sf0.01"), which(arg(1n, xs, "all")), nat.of(Nat.read(arg(2n, xs, "1")), 1n), arg(3n, xs, ""))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    start(List.tail(&2, String, promote(args)))
