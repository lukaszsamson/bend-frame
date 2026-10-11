# bench/m2/engine_v01.bend -- the BASELINE build's engine.bend (bench/m2/baseline.sh copies it in as
# engine.bend): the pinned facade (3612482) has only the v0.1 reader and the reference executor, so every
# BF_ENGINE value reads with DF.read_csv and collects with DF.collect. Same API as bench/m2/engine.bend.
# The `scan` token (W6.6) is honoured: the driver's e2e mode then scans the sales file (scan_csv, read by
# v0.1 at collect) as the candidate does, so a scan run compares the same plans end to end.
import Base
import ./../../frame.bend as DF
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P

def Eng.read_csv(+path: String) -> IO(E.ResT(C.Frame)):
  DF.read_csv(path)

def Eng.collect(p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  DF.collect(p, env)

def Eng.has(xs: List<&2, String>, +w: String) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(String.eq(x, w), Eng.has(t, w))

def Eng.tok(r: Result<&1, &1, U32 & String, String>, +w: String) -> Bool:
  match r:
    case Done{s}:
      Eng.has(String.split(s, ','), w)
    case Fail{e}:
      False{}

def Eng.scan_on() -> IO(Bool):
  do IO<Bool>:
    ev : Result<&1, &1, U32 & String, String> <- IO.get_env("BF_ENGINE")
    return Eng.tok(ev, "scan")
