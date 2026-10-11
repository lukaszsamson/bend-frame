# bench/w5/t53.bend -- T5.3 bench: one query of the m2 workloads (q1..q5, the filter cells) collected `reps`
# times in ONE process over fresh clones, by the reference or the chunked engine, with the G6 phases apart:
#   mode 0  reference: DF.collect (Lazy.collect, the v0.1 executor)
#   mode 1  chunked end to end from a flat env frame: DF.collect_with(engine_chunked()) (the conversions to
#           and from chunks inside the compute window, as the m2 driver with BF_ENGINE=chunked measures it)
#   mode 3  the pre-chunked compute batched (8 runs per window, us per run; bench/w5/scale/t53b.py)
#   mode 4  the reference compute batched the same way (Exec.run_phys over 8 flat envs; T5.5)
#   mode 30 + g  mode 3 at grain 2^g (T5.5: the per-leaf cost by a grain sweep)
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
import ./../../src/exec.bend as QX
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

# mode 3 (the scaling diagnosis, DESIGN.md 16.10): the pre-chunked compute BATCHED above the 1 ms clock:
# K = 8 chunked copies of the sales frame are built before the clock (each with its own env), the plan runs
# over all K inside ONE window (CX.run_x only), and the compute slot reports the window in MICROSECONDS PER
# RUN (window ms * 1000 / K); the first result is flattened and hashed after the clock (out / check as the
# other modes), the other results are dropped after it. bench/w5/scale/t53b.py drives it.
type BI is Type:
  BI{env: P.Env, cf: CH.CFrame}

def T.b.k() -> Nat:
  8n

def T.b.one.k(cf: CH.CFrame, r: P.Env & P.Plan) -> BI:
  (env, pp) = r
  BI{env, cf}

def T.b.one(+g: Nat, s: C.Frame, p: C.Frame) -> BI:
  T.b.one.k(CH.CFrame.of_frame(g, s), DF.source("products", p))

def T.b.pre(k: Nat, +g: Nat, acc: List<&1, BI>, ss: C.Frame & C.Frame, pp: C.Frame & C.Frame) -> List<&1, BI>:
  match k:
    case 0n:
      acc
    case 1n+j:
      (s1, s2) = ss
      (p1, p2) = pp
      T.b.pre(j, g, T.b.one(g, s1, p1) <> acc, DF.clone(s2), DF.clone(p2))

type BR is Type:
  BR{st: QC.CStats, x: E.ResT(QC.XF)}

def T.b.wrap(r: QC.CStats & E.ResT(QC.XF)) -> BR:
  (st, x) = r
  BR{st, x}

# the window: every copy run once
def T.b.run(+g: Nat, +p: P.Plan, bis: List<&1, BI>, acc: List<&1, BR>) -> List<&1, BR>:
  match bis:
    case Nil{}:
      acc
    case BI{env, cf} <> rest:
      T.b.run(g, p, rest, T.b.wrap(QC.CX.run_x(g, p, env, QC.PNF{"sales", cf} <> Nil{})) <> acc)

def T.b.fin(+us: Nat, rs: List<&1, BR>) -> IO(R):
  match rs:
    case Nil{}:
      do IO<R>:
        return R{T.ms(0n, us, 0n, 0n), 0, "no result"}
    case BR{st, x} <> rest:
      do IO<R>:
        +t2 : Nat <- IO.now()
        o : QC.CStats & E.ResT(C.Frame) <- IO.pure(QC.CStats & E.ResT(C.Frame), QC.CX.out(st, x))
        T.pre.out(0n, us, t2, o)

def T.b.go(+g: Nat, +p: P.Plan, bis: List<&1, BI>) -> IO(R):
  do IO<R>:
    +t0 : Nat <- IO.now()
    rs : List<&1, BR> <- IO.pure(List<&1, BR>, T.b.run(g, p, bis, Nil{}))
    +t1 : Nat <- IO.now()
    T.b.fin(Nat.div(Nat.mul(Nat.sub(t1, t0), 1000n), T.b.k()), rs)

def T.b.k2(+g: Nat, +op: String, +par: U32, r: P.Env & P.Plan, ss: C.Frame & C.Frame, pp: C.Frame & C.Frame) -> IO(R):
  (env, +pl) = r
  (s1, s2) = ss
  T.b.go(g, P.Optimize.release(T.plan(op, par, T.splan(s1), pl)), T.b.pre(T.b.k(), g, Nil{}, DF.clone(s2), pp))

def T.b.env(+g: Nat, +op: String, +par: U32, s: C.Frame, p: C.Frame, pp: C.Frame & C.Frame) -> IO(R):
  (p1, p2) = pp
  T.b.k2(g, op, par, DF.source("products", p1), DF.clone(s), DF.clone(p2))

def T.batch(+g: Nat, +op: String, +par: U32, s: C.Frame, p: C.Frame) -> IO(R):
  T.b.env(g, op, par, s, C.Frame.empty(), DF.clone(p))

# mode 4 (T5.5): the REFERENCE compute batched the same way: K = 8 flat env copies {sales, products} built
# before the clock, the plan run over all K by the reference physical runner (Exec.run_phys: pure, no IO,
# the same code DF.collect runs after its checks) inside ONE window, microseconds per run; the first result
# hashed after the clock. The 1-thread chunked-vs-reference comparison of T5.5 reads mode 3 against mode 4.
def T.r.env(r: P.Env & P.Plan) -> P.Env:
  (env, pp) = r
  env

def T.r.one.k(f: C.Frame, r: P.Env & P.Plan) -> P.Env:
  (env, pp) = r
  T.r.env(DF.add_source(env, "products", f))

def T.r.pre(k: Nat, acc: List<&1, P.Env>, ss: C.Frame & C.Frame, pp: C.Frame & C.Frame) -> List<&1, P.Env>:
  match k:
    case 0n:
      acc
    case 1n+j:
      (s1, s2) = ss
      (p1, p2) = pp
      T.r.pre(j, T.r.one.k(p1, DF.source("sales", s1)) <> acc, DF.clone(s2), DF.clone(p2))

def T.r.run(+p: P.Plan, es: List<&1, P.Env>, acc: List<&1, E.ResT(C.Frame)>) -> List<&1, E.ResT(C.Frame)>:
  match es:
    case Nil{}:
      acc
    case env <> rest:
      T.r.run(p, rest, QX.Exec.run_phys(p, env) <> acc)

def T.r.fin(+us: Nat, rs: List<&1, E.ResT(C.Frame)>) -> IO(R):
  match rs:
    case Nil{}:
      do IO<R>:
        return R{T.ms(0n, us, 0n, 0n), 0, "no result"}
    case x <> rest:
      do IO<R>:
        +t2 : Nat <- IO.now()
        +h : U32 <- IO.pure(U32, T.chk(x))
        +t3 : Nat <- IO.now()
        return R{T.ms(0n, us, 0n, Nat.sub(t3, t2)), h, ""}

def T.r.go(+p: P.Plan, es: List<&1, P.Env>) -> IO(R):
  do IO<R>:
    +t0 : Nat <- IO.now()
    rs : List<&1, E.ResT(C.Frame)> <- IO.pure(List<&1, E.ResT(C.Frame)>, T.r.run(p, es, Nil{}))
    +t1 : Nat <- IO.now()
    T.r.fin(Nat.div(Nat.mul(Nat.sub(t1, t0), 1000n), T.b.k()), rs)

def T.r.k2(+op: String, +par: U32, r: P.Env & P.Plan, ss: C.Frame & C.Frame, pp: C.Frame & C.Frame) -> IO(R):
  (env, +pl) = r
  (s1, s2) = ss
  T.r.go(P.Optimize.release(T.plan(op, par, T.splan(s1), pl)), T.r.pre(T.b.k(), Nil{}, DF.clone(s2), pp))

def T.r.env2(+op: String, +par: U32, s: C.Frame, pp: C.Frame & C.Frame) -> IO(R):
  (p1, p2) = pp
  T.r.k2(op, par, DF.source("products", p1), DF.clone(s), DF.clone(p2))

# (the plan's products Source takes its schema from a clone of the products frame, as mode 3's)
def T.rbatch(+op: String, +par: U32, s: C.Frame, p: C.Frame) -> IO(R):
  T.r.env2(op, par, s, DF.clone(p))

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

# mode 10 + g: mode 2 at grain 2^g; mode 30 + g: mode 3 (batched) at grain 2^g (T5.5's per-leaf cost sweep)
def T.one.g(lo: Bool, +mode: U32, +op: String, +par: U32, s: C.Frame, p: C.Frame) -> IO(R):
  match lo:
    case True{}:
      T.pre.env(T.grain(mode), op, par, s, p)
    case False{}:
      T.batch(U32.to_nat(U32.sub(mode, 30)), op, par, s, p)

def T.one(+mode: U32, +op: String, +par: U32, s: C.Frame, p: C.Frame) -> IO(R):
  match mode:
    case 0:
      T.one.k(mode, op, par, C.Frame.empty(), C.Frame.empty(), T.env(op, par, s, p))
    case 1:
      T.one.k(mode, op, par, C.Frame.empty(), C.Frame.empty(), T.env(op, par, s, p))
    case 3:
      T.batch(CH.Ch.grain(), op, par, s, p)
    case 4:
      T.rbatch(op, par, s, p)
    case _:
      T.one.g(U32.is_lt(mode, 30), mode, op, par, s, p)

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
