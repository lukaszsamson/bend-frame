# bench/w5/t53.bend -- T5.3 bench: one query of the m2 workloads (q1..q5, the filter cells) collected `reps`
# times in ONE process over fresh clones, by the reference or the chunked engine, with the G6 phases apart:
#   mode 0  reference: DF.collect (Lazy.collect, the v0.1 executor)
#   mode 1  chunked end to end from a flat env frame: DF.collect_with(engine_chunked()) (the conversions to
#           and from chunks inside the compute window, as the m2 driver with BF_ENGINE=chunked measures it)
#   mode 2  (mode 10 + g: at grain 2^g instead of the default 2^14) chunked over a PRE-CHUNKED source (the W6 hand-off: G2 is defined on chunked inputs): the sales
#           frame converted (in_ms: CH.CFrame.of_frame, forked across columns), the plan run (compute_ms:
#           CX.run_x, the result left as it is), the result flattened (out_ms: CX.out)
# Every mode then hashes the result (check_ms: bench/m2/driver.bend's Hc.frame, the content hash the m2
# expectations are frozen with; work still pending is billed there, so compute + out + check is the honest
# figure). Per rep: [in, compute, out, check] ms. The last line also gives the chunked runner's counters of
# the last rep (conversions and their bytes, walks, flat operators).
#   bend bench/w5/t53.bend -o build/t53/t53; build/t53/t53 [--threads N] <sales.csv> <products.csv> <op> <mode> <reps> [param]
# stdout: {"op":..,"mode":..,"parse_ms":..,"chk":<hash of the last rep>,"reps":[[in,compute,out,check],..],"stats":".."}
import Base
import ./../../frame.bend as DF
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./../../src/chunks.bend as CH
import ./../../src/cexec.bend as QC
import ./../m2/driver.bend as DR

# probes beside the m2 workloads: wlit with_columns(lit 1), wadd with_columns(qty + id), wcast
# with_columns(f32(qty) * price); anything else is the driver's plan (DR.Pl.of)
def T.plan(+op: String, +par: U32, +s: P.Plan, +p: P.Plan) -> P.Plan:
  Bool.pick(P.Plan, String.eq(op, "wlit"), DF.lazy_with_columns(s, [DF.alias(DF.lit_u32(1), "one")]),
  Bool.pick(P.Plan, String.eq(op, "wadd"), DF.lazy_with_columns(s, [DF.alias(DF.add(DF.col("qty"), DF.col("id")), "qi")]),
  Bool.pick(P.Plan, String.eq(op, "wcast"), DF.lazy_with_columns(s, [DF.alias(DF.mul(DF.cast_f32(DF.col("qty")), DF.col("price")), "r")]), DR.Pl.of(op, par, s, p))))

def T.env.k2(+op: String, +par: U32, +s: P.Plan, r: P.Env & P.Plan) -> P.Env & P.Plan:
  (env, +pp) = r
  (env, P.Optimize.release(T.plan(op, par, s, pp)))

def T.env.k(+op: String, +par: U32, r: P.Env & P.Plan, p: C.Frame) -> P.Env & P.Plan:
  (env, +s) = r
  T.env.k2(op, par, s, DF.add_source(env, "products", p))

# the env {sales, products} and the plan (released, as collect runs it)
def T.env(+op: String, +par: U32, s: C.Frame, p: C.Frame) -> P.Env & P.Plan:
  T.env.k(op, par, DF.source("sales", s), p)

def T.ms(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> String:
  "[" ++ Nat.show(a) ++ "," ++ Nat.show(b) ++ "," ++ Nat.show(c) ++ "," ++ Nat.show(d) ++ "]"

type R is Type:
  R{line: String, h: U32, stats: String}

def T.chk(r: E.ResT(C.Frame)) -> U32:
  match r:
    case Fail{e}:
      0
    case Done{f}:
      DR.Hc.frame(f)

def T.coll(chunked: Bool, p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  match chunked:
    case True{}:
      DF.collect_with(DF.engine_chunked(), p, env)
    case False{}:
      DF.collect(p, env)

# mode 0 / 1: collect by the engine, then the hash
def T.flat(+chunked: Bool, env: P.Env, +p: P.Plan) -> IO(R):
  do IO<R>:
    +t0 : Nat <- IO.now()
    r : E.ResT(C.Frame) <- T.coll(chunked, p, env)
    +t1 : Nat <- IO.now()
    +h : U32 <- IO.pure(U32, T.chk(r))
    +t2 : Nat <- IO.now()
    return R{T.ms(0n, Nat.sub(t1, t0), 0n, Nat.sub(t2, t1)), h, ""}

def T.pre.out(+a: Nat, +b: Nat, +t2: Nat, r: QC.CStats & E.ResT(C.Frame)) -> IO(R):
  (st, x) = r
  do IO<R>:
    +t3 : Nat <- IO.now()
    +h : U32 <- IO.pure(U32, T.chk(x))
    +t4 : Nat <- IO.now()
    return R{T.ms(a, b, Nat.sub(t3, t2), Nat.sub(t4, t3)), h, QC.CStats.show(st)}

def T.pre.run(+a: Nat, +t1: Nat, r: QC.CStats & E.ResT(QC.XF)) -> IO(R):
  (st, x) = r
  do IO<R>:
    +t2 : Nat <- IO.now()
    o : QC.CStats & E.ResT(C.Frame) <- IO.pure(QC.CStats & E.ResT(C.Frame), QC.CX.out(st, x))
    T.pre.out(a, Nat.sub(t2, t1), t2, o)

def T.pre.go(+g: Nat, +t0: Nat, env: P.Env, +p: P.Plan, r: CH.CFrame & Bool) -> IO(R):
  (cf, ok) = r
  do IO<R>:
    +t1 : Nat <- IO.now()
    x : QC.CStats & E.ResT(QC.XF) <- IO.pure(QC.CStats & E.ResT(QC.XF), QC.CX.run_x(g, p, env, QC.PNF{"sales", cf} <> Nil{}))
    T.pre.run(Nat.sub(t1, t0), t1, x)

# mode 2: the sales frame chunked (timed), the env holds products only
def T.pre(+g: Nat, env: P.Env, +p: P.Plan, s: C.Frame) -> IO(R):
  do IO<R>:
    +t0 : Nat <- IO.now()
    c : CH.CFrame & Bool <- IO.pure(CH.CFrame & Bool, CH.CFrame.check(CH.CFrame.of_frame(g, s)))
    T.pre.go(g, t0, env, p, c)

# the Source plan of the sales frame (its schema)
def T.splan.k(r: P.Env & P.Plan) -> P.Plan:
  (e, p) = r
  p

def T.splan(s: C.Frame) -> P.Plan:
  T.splan.k(DF.source("sales", s))

def T.pre.k2(+g: Nat, env: P.Env, +p: P.Plan, s: C.Frame) -> IO(R):
  T.pre(g, env, p, s)

# (the schema comes from a clone of the sales frame, made before the clock)
def T.pre.k(+g: Nat, +op: String, +par: U32, r: P.Env & P.Plan, ss: C.Frame & C.Frame) -> IO(R):
  (env, +pp) = r
  (s1, s2) = ss
  T.pre.k2(g, env, P.Optimize.release(T.plan(op, par, T.splan(s1), pp)), s2)

def T.pre.env(+g: Nat, +op: String, +par: U32, s: C.Frame, p: C.Frame) -> IO(R):
  T.pre.k(g, op, par, DF.source("products", p), DF.clone(s))

def T.one.k(+mode: U32, +op: String, +par: U32, s: C.Frame, p: C.Frame, r: P.Env & P.Plan) -> IO(R):
  (env, +pl) = r
  T.flat(U32.is_eq(mode, 1), env, pl)

# mode 2: pre-chunked at the default grain 2^14; mode 10 + g: pre-chunked at grain 2^g
def T.grain(+mode: U32) -> Nat:
  Bool.pick(Nat, U32.is_lt(mode, 10), CH.Ch.grain(), U32.to_nat(U32.sub(mode, 10)))

def T.one(+mode: U32, +op: String, +par: U32, s: C.Frame, p: C.Frame) -> IO(R):
  match mode:
    case 0:
      T.one.k(mode, op, par, C.Frame.empty(), C.Frame.empty(), T.env(op, par, s, p))
    case 1:
      T.one.k(mode, op, par, C.Frame.empty(), C.Frame.empty(), T.env(op, par, s, p))
    case _:
      T.pre.env(T.grain(mode), op, par, s, p)

type L is Type:
  L{acc: String, h: U32, stats: String, s: C.Frame, p: C.Frame}

def T.step.k(acc: String, s: C.Frame, p: C.Frame, r: R) -> L:
  match r:
    case R{line, h, st}:
      L{acc ++ line ++ ",", h, st, s, p}

def T.step(+mode: U32, +op: String, +par: U32, acc: String, ss: C.Frame & C.Frame, pp: C.Frame & C.Frame) -> IO(L):
  (s1, s2) = ss
  (p1, p2) = pp
  do IO<L>:
    r : R <- T.one(mode, op, par, s1, p1)
    return T.step.k(acc, s2, p2, r)

def T.loop(left: Nat, +mode: U32, +op: String, +par: U32, l: L) -> IO(Unit):
  match left:
    case 0n:
      match l:
        case L{acc, h, st, s, p}:
          IO.print(acc ++ "[]],\"chk\":" ++ U32.show(h) ++ ",\"stats\":\"" ++ st ++ "\"}")
    case 1n+k:
      match l:
        case L{acc, h, st, s, p}:
          do IO<Unit>:
            l2 : L <- T.step(mode, op, par, acc, DF.clone(s), DF.clone(p))
            T.loop(k, mode, op, par, l2)

def T.start.w(left: Nat, +mode: U32, +op: String, +par: U32, +t0: Nat, +t1: Nat, ins: List<&1, DR.In>) -> IO(Unit):
  match ins:
    case Nil{}:
      IO.print("error: no input")
    case DR.In{s, p, ks, kp} <> t:
      T.loop(left, mode, op, par, L{"{\"op\":\"" ++ op ++ "\",\"mode\":" ++ U32.show(mode) ++ ",\"parse_ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"reps\":[", 0, "", s, p})

def T.start.r(left: Nat, +mode: U32, +op: String, +par: U32, +t0: Nat, +t1: Nat, r: E.ResT(List<&1, DR.In>)) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("error: " ++ E.Err.show(e))
    case Done{ins}:
      T.start.w(left, mode, op, par, t0, t1, ins)

def T.start(left: Nat, +mode: U32, +op: String, +par: U32, +path: String, +ppath: String) -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    r : E.ResT(List<&1, DR.In>) <- DR.rd.many(1n, path, ppath, Done{Nil{}})
    +t1 : Nat <- IO.now()
    T.start.r(left, mode, op, par, t0, t1, r)

def T.args(+xs: List<&2, String>) -> IO(Unit):
  T.start(DR.nat.of(Nat.read(DR.nth(4n, xs, "5")), 5n), U32.from_nat(DR.nat.of(Nat.read(DR.nth(3n, xs, "0")), 0n)), DR.nth(2n, xs, "q1"), U32.from_nat(DR.nat.of(Nat.read(DR.nth(5n, xs, "0")), 0n)), DR.nth(0n, xs, "bench/data/sales_1000000.csv"), DR.nth(1n, xs, "bench/data/products.csv"))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    T.args(List.tail(&2, String, DR.promote(args)))
