# M6 release-candidate workloads (plans/M_01.txt section 7 M6). Native only:
#   ~/.bend/bin/bend bench/m6.bend -o build/m6
#   ./build/m6 hc <group|unique|join> <t.csv> <dim.csv> <out.csv>
#       high-cardinality: t(k str, v u32, x f32), dim(k str, w u32) over Source frames, one collect
#       (parsed and forced untimed, like bench/main.bend); result written to out.csv; prints
#       {"op":..,"rows":..,"collect_ms":..}
#   ./build/m6 repeat <q1..q6> <sales.csv> <reps>
#       the same query `reps` times in one process over clones of one parse; per iteration prints
#       {"iter":i,"ms":..,"hash":..} with a hash of the rendered result (floats at 4 decimals)
import Base
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/expr.bend as X
import ./../src/join.bend as J
import ./../src/csv.bend as V
import ./../src/plan.bend as P
import ./../src/exec.bend as XE
import ./queries.bend as QS
import ./main.bend as M

# ---- high cardinality ---------------------------------------------------------------------------

def hc.plan(+op: String, +s: P.Plan, +d: P.Plan) -> P.Plan:
  Bool.pick(P.Plan, String.eq(op, "group"), P.GroupBy{[QS.Q.col("k")], [QS.Q.agg(X.Sum{}, QS.Q.col("v"), "vs"), QS.Q.agg(X.Len{}, QS.Q.u32(1), "n")], False{}, s},
  Bool.pick(P.Plan, String.eq(op, "unique"), P.Unique{["k"], P.Select{[QS.Q.col("k")], s}},
  P.Join{J.Inner{}, ["k"], ["k"], s, d}))

def hc.b(+op: String, +s: P.Plan, r: P.Env & P.Plan) -> IO(E.ResT(C.Frame)):
  (env, +d) = r
  XE.Lazy.collect(hc.plan(op, s, d), env)

def hc.a(+op: String, r: P.Env & P.Plan, d: C.Frame) -> IO(E.ResT(C.Frame)):
  (env, +s) = r
  hc.b(op, s, P.Env.add(env, "d", d))

def hc.fin2(+op: String, +ms: Nat, +rows: U32, r: C.Frame & String, +out: String) -> IO(Unit):
  (f, text) = r
  do IO<Unit>:
    M.out.w(out, text)
    IO.print("{\"op\":\"" ++ op ++ "\",\"rows\":" ++ U32.show(rows) ++ ",\"collect_ms\":" ++ Nat.show(ms) ++ "}")

def hc.fin1(+op: String, +ms: Nat, r: C.Frame & U32, +out: String) -> IO(Unit):
  (f, +rows) = r
  hc.fin2(op, ms, rows, V.Csv.render(f, Some{4}), out)

def hc.fin(+op: String, +ms: Nat, r: E.ResT(C.Frame), +out: String) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("error: " ++ E.Err.show(e))
    case Done{f}:
      hc.fin1(op, ms, C.Frame.height(f), out)

def hc.run(+op: String, +out: String, ft: C.Frame & U32, fd: C.Frame & U32) -> IO(Unit):
  (t, +x) = ft
  (d, +y) = fd
  do IO<Unit>:
    t0 : Nat <- IO.now()
    r : E.ResT(C.Frame) <- hc.a(op, P.Lazy.source("t", t), d)
    t1 : Nat <- IO.now()
    hc.fin(op, Nat.sub(t1, t0), r, out)

def hc.k(+op: String, +out: String, rt: E.ResT(C.Frame), rd: E.ResT(C.Frame)) -> IO(Unit):
  match rt:
    case Fail{e}:
      IO.print("error: " ++ E.Err.show(e))
    case Done{t}:
      match rd:
        case Fail{e}:
          IO.print("error: " ++ E.Err.show(e))
        case Done{d}:
          hc.run(op, out, M.force(t), M.force(d))

def hc.go(+op: String, +path: String, +dpath: String, +out: String) -> IO(Unit):
  do IO<Unit>:
    rt : E.ResT(C.Frame) <- V.Csv.read_enc(path, V.Csv.default(), Nil{}, V.Csv.enc_default())
    rd : E.ResT(C.Frame) <- V.Csv.read_enc(dpath, V.Csv.default(), Nil{}, V.Csv.enc_default())
    hc.k(op, out, rt, rd)

# ---- repeated query -------------------------------------------------------------------------------

def rp.ln(+i: Nat, +ms: Nat, +h: U32) -> String:
  "{\"iter\":" ++ Nat.show(i) ++ ",\"ms\":" ++ Nat.show(ms) ++ ",\"hash\":" ++ U32.show(h) ++ "}"

def rp.ln.h(+i: Nat, +ms: Nat, r: C.Frame & String) -> String:
  (f, text) = r
  rp.ln(i, ms, J.Str.hash(text, 0))

def rp.ln.d(+i: Nat, +ms: Nat, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      rp.ln.h(i, ms, V.Csv.render(f, Some{4}))

def rp.line(+i: Nat, +ms: Nat, rs: List<&1, E.ResT(C.Frame)>) -> String:
  match rs:
    case Nil{}:
      "error: no result"
    case r <> t:
      rp.ln.d(i, ms, r)

def rp.split.k(a: C.Frame & C.Frame, b: C.Frame & C.Frame) -> M.In & (C.Frame & C.Frame):
  (s, ks2) = a
  (p, kp2) = b
  (M.In{s, p, C.Frame.empty(), C.Frame.empty(), 0, 0}, (ks2, kp2))

def rp.split(ks: C.Frame, kp: C.Frame) -> M.In & (C.Frame & C.Frame):
  rp.split.k(M.fclone(ks), M.fclone(kp))

def rp.split.n(r: C.Frame & C.Frame) -> M.In & (C.Frame & C.Frame):
  (a, b) = r
  rp.split(a, b)

def rp.loop(+is6: Bool, +q: String, +left: Nat, +i: Nat, r: M.In & (C.Frame & C.Frame)) -> IO(Unit):
  match left:
    case 0n:
      IO.print("{\"done\":true}")
    case 1n+k:
      (inp, kk) = r
      do IO<Unit>:
        t0 : Nat <- IO.now()
        rs : List<&1, E.ResT(C.Frame)> <- M.job(is6, q, inp)
        t1 : Nat <- IO.now()
        IO.print(rp.line(i, Nat.sub(t1, t0), rs))
        rp.loop(is6, q, k, Nat.add(i, 1n), rp.split.n(kk))

def rp.start(+is6: Bool, +q: String, +reps: Nat, r: E.ResT(M.In)) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("error: " ++ E.Err.show(e))
    case Done{M.In{s, p, ks, kp, n, chk}}:
      rp.loop(is6, q, reps, 1n, rp.split(ks, kp))

def rp.go(+q: String, +path: String, +reps: Nat) -> IO(Unit):
  do IO<Unit>:
    r : E.ResT(M.In) <- M.load(True{}, path, M.products_path(path))
    rp.start(String.eq(q, "q6"), q, reps, r)

# ---- args -------------------------------------------------------------------------------------------

def go.k(+hc: Bool, +xs: List<&2, String>) -> IO(Unit):
  match hc:
    case True{}:
      hc.go(M.nth(1n, xs, "group"), M.nth(2n, xs, ""), M.nth(3n, xs, ""), M.nth(4n, xs, "build/hc_out.csv"))
    case False{}:
      rp.go(M.nth(1n, xs, "q3"), M.nth(2n, xs, "bench/data/sales_100000.csv"), M.nat.of(Nat.read(M.nth(3n, xs, "20")), 20n))

def go(+xs: List<&2, String>) -> IO(Unit):
  go.k(String.eq(M.nth(0n, xs, ""), "hc"), xs)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(List.tail(&2, String, M.promote(args)))
