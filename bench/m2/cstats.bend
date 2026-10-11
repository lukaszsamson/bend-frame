# bench/m2/cstats.bend -- the chunked executor's own conversion counters (CStats, src/cexec.bend) for ONE m2 workload
# collected over a FLAT env frame, exactly as the driver does under BF_ENGINE=chunked: DF.collect_with(
# engine_chunked(), ..) is Exec.prep + CX.run at grain 2^14 with the CStats dropped (CX.snd); this probe keeps them.
# The facade does not expose CStats, so `make m2-g6` runs this next to the instrumented driver to fill the
# "chunk conversions" columns of its table (conversion counts and LOGICAL bytes = 4 x rows x columns converted;
# the bytes the runtime really allocated for them are in the instrumented driver's counters).
#   bend bench/m2/cstats.bend -o build/m2/cstats; build/m2/cstats [--threads N] <op> <file> <aux|-> [param [scan]]
# With a fifth argument `scan` (W6.6) the sales file is a scan_csv plan collected as `BF_ENGINE=v02,chunked,scan` does
# (cexec.bend Exec.run_with_rd(CsvV02, Chunked{14}): CX.prep.k reads the scan with the v0.2 reader in chunk mode, the
# runner's IScan takes its leaves): its conv_in / bytes_in are the flat -> chunk conversions left on a scan plan.
# stdout: {"op":..,"chk":<the driver's content hash of the result>,"stats":"conv_in n bytes_in b conv_out n bytes_out b walks n flat_ops n"}
# op: q1 q2 q3 q4 q5 nunique group unique join filter (the driver's plans: bench/m2/driver.bend Pl.of); q6 (eager describe)
# and parse do not collect, so there is nothing to count.
import Base
import ./../../frame.bend as DF
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./../../src/csv.bend as R
import ./../../src/exec.bend as Q
import ./../../src/chunks.bend as CH
import ./../../src/cexec.bend as QC
import ./driver.bend as DR

def X.chk(r: E.ResT(C.Frame)) -> U32:
  match r:
    case Fail{e}:
      0
    case Done{f}:
      DR.Hc.frame(f)

def X.print(+op: String, r: QC.CStats & E.ResT(C.Frame)) -> IO(Unit):
  (st, x) = r
  IO.print("{\"op\":\"" ++ op ++ "\",\"chk\":" ++ U32.show(X.chk(x)) ++ ",\"stats\":\"" ++ QC.CStats.show(st) ++ "\"}")

def X.go(+g: Nat, +op: String, +p: P.Plan, r: E.ResT(P.Env)) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("error: " ++ E.Err.show(e))
    case Done{env}:
      X.print(op, QC.CX.run(g, p, env, Nil{}))

# Exec.run_with.c: the checks and scan reads, then the chunked runner
def X.prep(+g: Nat, +op: String, +p: P.Plan, env: P.Env) -> IO(Unit):
  do IO<Unit>:
    r : E.ResT(P.Env) <- Q.Exec.prep(R.CsvV01{}, p, env)
    X.go(g, op, p, r)

# the driver's job: plan over the env {sales, products}, released (Lazy.collect_with releases before running)
def X.b(+g: Nat, +op: String, +par: U32, s: P.Plan, r: P.Env & P.Plan) -> IO(Unit):
  (env, +p) = r
  X.prep(g, op, P.Optimize.release(DR.Pl.of(op, par, s, p)), env)

def X.a(+g: Nat, +op: String, +par: U32, r: P.Env & P.Plan, p: C.Frame) -> IO(Unit):
  (env, +s) = r
  X.b(g, op, par, s, DF.add_source(env, "products", p))

def X.k(+g: Nat, +op: String, +par: U32, i: DR.In) -> IO(Unit):
  match i:
    case DR.In{s, p, ks, kp}:
      X.a(g, op, par, DF.source("sales", s), p)

def X.w(+op: String, +par: U32, ins: List<&1, DR.In>) -> IO(Unit):
  match ins:
    case Nil{}:
      IO.print("error: no input")
    case i <> t:
      X.k(CH.Ch.grain(), op, par, i)

def X.r(+op: String, +par: U32, r: E.ResT(List<&1, DR.In>)) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("error: " ++ E.Err.show(e))
    case Done{ins}:
      X.w(op, par, ins)

def X.start(+op: String, +par: U32, +path: String, +ppath: String) -> IO(Unit):
  do IO<Unit>:
    r : E.ResT(List<&1, DR.In>) <- DR.rd.many(1n, path, ppath, Done{Nil{}})
    X.r(op, par, r)

# ---- scan mode (W6.6): the sales input as a scan_csv plan, read by the v0.2 reader into chunk leaves ----

def X.sgo2(+g: Nat, +op: String, +p: P.Plan, ep: P.Env & List<&1, QC.PNF>) -> IO(Unit):
  (env, pre) = ep
  X.print(op, QC.CX.run(g, p, env, pre))

def X.sgo(+g: Nat, +op: String, +p: P.Plan, r: E.ResT(P.Env & List<&1, QC.PNF>)) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("error: " ++ E.Err.show(e))
    case Done{ep}:
      X.sgo2(g, op, p, ep)

# Exec.run_with.c for CsvV02: the checks, the scans read into chunk leaves (CX.prep.k), then the chunked runner
def X.sprep(+g: Nat, +op: String, +p: P.Plan, env: P.Env) -> IO(Unit):
  do IO<Unit>:
    r : E.ResT(P.Env & List<&1, QC.PNF>) <- QC.CX.prep.k(P.Plan.schema(p), g, R.Csv.engine_v02(), p, env)
    X.sgo(g, op, p, r)

def X.sb(+g: Nat, +op: String, +par: U32, +s: P.Plan, r: P.Env & P.Plan) -> IO(Unit):
  (env, +pp) = r
  X.sprep(g, op, P.Optimize.release(DR.Pl.of(op, par, s, pp)), env)

def X.sj(+op: String, +par: U32, ps: E.Res(P.Plan), rp: E.ResT(C.Frame)) -> IO(Unit):
  match ps rp:
    case Done{+s} Done{p}:
      X.sb(CH.Ch.grain(), op, par, s, DF.add_source(DF.empty_env(), "products", p))
    case Fail{e} _:
      IO.print("error: " ++ E.Err.show(e))
    case _ Fail{e}:
      IO.print("error: " ++ E.Err.show(e))

def X.scan(+op: String, +par: U32, +path: String, +ppath: String) -> IO(Unit):
  do IO<Unit>:
    rp : E.ResT(C.Frame) <- DR.rd.aux(ppath)
    ps : E.Res(P.Plan) <- DF.scan_csv(path)
    X.sj(op, par, ps, rp)

def X.mode(sc: Bool, +op: String, +par: U32, +path: String, +ppath: String) -> IO(Unit):
  match sc:
    case True{}:
      X.scan(op, par, path, ppath)
    case False{}:
      X.start(op, par, path, ppath)

def X.args(+xs: List<&2, String>) -> IO(Unit):
  X.mode(String.eq(DR.nth(4n, xs, ""), "scan"), DR.nth(0n, xs, "q1"), U32.from_nat(DR.nat.of(Nat.read(DR.nth(3n, xs, "0")), 0n)), DR.nth(1n, xs, "bench/data/sales_1000000.csv"), DR.nth(2n, xs, "bench/data/products.csv"))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    X.args(List.tail(&2, String, DR.promote(args)))
