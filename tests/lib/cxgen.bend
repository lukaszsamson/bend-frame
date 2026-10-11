# tests/lib/cxgen.bend -- shared helpers of the chunked-runner tests (tests/cexec*.bend, v0.2 T5.3).
# Not a test itself (no main).
#
# t(n): an n-row frame with every dtype and storage the runner handles differently:
#   id u32 (row i), qty u32 ((37 i + 11) mod 100), price f32 (i / 4; NaN at i % 13 = 5, -0.0 at 6,
#   +inf at 7), ok bool (null at i % 7 = 3, else i % 3 != 0), disc f32 (null at i % 5 = 2, else
#   (i % 4) / 4), s str Raw ("r<i % 6>", null at i % 11 = 4), d str Dictionary ("k<i % 3>"), num str
#   Raw ("<3 i>", but "bad" at row 13, "worse" at row 22, null at i % 10 = 9), n i32 ((i % 9) - 4, null at
#   i % 8 = 6).
# cmp(tag, g, plan, env, env): the plan run by the reference runner (Exec.run_phys: what collect runs
# after its checks) and by the chunked runner at grain 2^g; prints the reference's height (or error
# text), "[same]" when the two DF.dump texts are equal (else "[DIFF]" and both dumps), and the chunked
# runner's counters (walks: per-leaf walks run; flat: operators run by today's flat code; cin / cout:
# conversions to / from chunks).
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./../../src/exec.bend as Q
import ./../../src/cexec.bend as QC

def nan() -> F32:
  F32.div(0.0, 0.0)

def inf() -> F32:
  F32.div(1.0, 0.0)

def ism(+i: U32, +m: U32, +r: U32) -> Bool:
  U32.is_eq(U32.mod(i, m), r)

def v.qty(+i: U32) -> D.Scalar:
  D.SU32{U32.mod(U32.add(U32.mul(i, 37), 11), 100)}

def v.price(+i: U32) -> D.Scalar:
  D.SF32{Bool.pick(F32, ism(i, 13, 5), nan(), Bool.pick(F32, ism(i, 13, 6), F32.neg(0.0), Bool.pick(F32, ism(i, 13, 7), inf(), F32.div(U32.to_f32(i), 4.0))))}

def v.ok(+i: U32) -> D.Scalar:
  Bool.pick(D.Scalar, ism(i, 7, 3), D.SNull{}, D.SBool{Bool.not(ism(i, 3, 0))})

def v.disc(+i: U32) -> D.Scalar:
  Bool.pick(D.Scalar, ism(i, 5, 2), D.SNull{}, D.SF32{F32.div(U32.to_f32(U32.mod(i, 4)), 4.0)})

def v.s(+i: U32) -> D.Scalar:
  Bool.pick(D.Scalar, ism(i, 11, 4), D.SNull{}, D.SStr{"r" ++ U32.show(U32.mod(i, 6))})

def v.d(+i: U32) -> D.Scalar:
  D.SStr{"k" ++ U32.show(U32.mod(i, 3))}

def v.num(+i: U32) -> D.Scalar:
  Bool.pick(D.Scalar, U32.is_eq(i, 13), D.SStr{"bad"}, Bool.pick(D.Scalar, U32.is_eq(i, 22), D.SStr{"worse"}, Bool.pick(D.Scalar, ism(i, 10, 9), D.SNull{}, D.SStr{U32.show(U32.mul(i, 3))})))

def v.n(+i: U32) -> D.Scalar:
  Bool.pick(D.Scalar, ism(i, 8, 6), D.SNull{}, D.SI32{D.I32.sub(D.I32{U32.mod(i, 9)}, D.I32{4})})

def v.at(+k: U32, +i: U32) -> D.Scalar:
  match k:
    case 0:
      D.SU32{i}
    case 1:
      v.qty(i)
    case 2:
      v.price(i)
    case 3:
      v.ok(i)
    case 4:
      v.disc(i)
    case 5:
      v.s(i)
    case 6:
      v.d(i)
    case 7:
      v.num(i)
    case _:
      v.n(i)

def gen.go(f: Nat, +i: U32, +k: U32, acc: List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  match f:
    case 0n:
      acc
    case 1n+p:
      +j = U32.sub(i, 1)
      gen.go(p, j, k, v.at(k, j) <> acc)

# rows off .. off + n - 1 of generator k
def gen(+off: U32, +n: U32, +k: U32) -> List<&2, D.Scalar>:
  gen.go(U32.to_nat(n), U32.add(off, n), k, Nil{})

def mk.k(name: String, r: E.ResT(C.Column)) -> C.Named:
  match r:
    case Fail{e}:
      C.Named{E.Err.show(e), C.CU32{0, 0n, C.AllValid{}, [0 : U32*1n]}}
    case Done{c}:
      C.Named{name, c}

def mk(name: String, xs: List<&2, D.Scalar>, +t: D.DType) -> C.Named:
  mk.k(name, C.Column.from_scalars(xs, t))

def enc(nc: C.Named) -> C.Named:
  match nc:
    case C.Named{n, c}:
      C.Named{n, C.Column.encode(c)}

def frame(r: E.ResT(C.Frame)) -> C.Frame:
  match r:
    case Fail{e}:
      C.Frame.empty()
    case Done{fr}:
      fr

# rows off .. off + n - 1 of the test frame
def tr(+off: U32, +n: U32) -> C.Frame:
  frame(C.Frame.from_columns([mk("id", gen(off, n, 0), D.TU32{}), mk("qty", gen(off, n, 1), D.TU32{}), mk("price", gen(off, n, 2), D.TF32{}), mk("ok", gen(off, n, 3), D.TBool{}), mk("disc", gen(off, n, 4), D.TF32{}), mk("s", gen(off, n, 5), D.TStr{}), enc(mk("d", gen(off, n, 6), D.TStr{})), mk("num", gen(off, n, 7), D.TStr{}), mk("n", gen(off, n, 8), D.TI32{})]))

def t(+n: U32) -> C.Frame:
  tr(0, n)

def env.k(r: P.Env & P.Plan) -> P.Env:
  (e, p) = r
  e

def plan.k(r: P.Env & P.Plan) -> P.Plan:
  (e, p) = r
  p

# env {"t": t(n)} and the Source plan of t(n)
def envt(+n: U32) -> P.Env:
  env.k(DF.source("t", t(n)))

def srct(+n: U32) -> P.Plan:
  plan.k(DF.source("t", t(n)))

# env {"t": a, "u": b}
def env2(a: C.Frame, b: C.Frame) -> P.Env:
  env.k(DF.add_source(env.k(DF.source("t", a)), "u", b))

def srcu(f: C.Frame) -> P.Plan:
  plan.k(DF.source("u", f))

def hstr.k(r: C.Frame & U32) -> String:
  (f, +h) = r
  "h=" ++ U32.show(h)

def hstr(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      hstr.k(C.Frame.height(f))

def dclone.k(r: C.Frame & C.Frame) -> E.ResT(C.Frame) & E.ResT(C.Frame):
  (a, b) = r
  (Done{a}, Done{b})

def dclone(r: E.ResT(C.Frame)) -> E.ResT(C.Frame) & E.ResT(C.Frame):
  match r:
    case Fail{+e}:
      (Fail{e}, Fail{e})
    case Done{f}:
      dclone.k(DF.clone(f))

def cnt(st: QC.CStats) -> String:
  match st:
    case QC.CStats{ci, bi, co, bo, w, fl}:
      "walks=" ++ U32.show(w) ++ " flat=" ++ U32.show(fl) ++ " cin=" ++ U32.show(ci) ++ " cout=" ++ U32.show(co)

def cmp.fin(+tag: String, +da: String, +db: String, +h: String, +c: String) -> String:
  Bool.pick(String, String.eq(da, db), tag ++ ": " ++ h ++ " [same] " ++ c, tag ++ ": " ++ h ++ " [DIFF] " ++ c ++ "\n--- reference\n" ++ da ++ "--- chunked\n" ++ db)

def cmp.c(+tag: String, rr: E.ResT(C.Frame) & E.ResT(C.Frame), +db: String, +c: String) -> String:
  (a1, a2) = rr
  cmp.fin(tag, DF.dump(a1), db, hstr(a2), c)

def cmp.b(+tag: String, ra: E.ResT(C.Frame), rb: QC.CStats & E.ResT(C.Frame)) -> String:
  (st, b) = rb
  cmp.c(tag, dclone(ra), DF.dump(b), cnt(st))

# the reference (run_phys) against the chunked runner at grain 2^g, over two copies of env
def cmp(+tag: String, +g: Nat, +p: P.Plan, e1: P.Env, e2: P.Env) -> String:
  cmp.b(tag, Q.Exec.run_phys(p, e1), QC.CX.run(g, p, e2, Nil{}))
