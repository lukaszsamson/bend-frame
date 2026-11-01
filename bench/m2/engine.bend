# bench/m2/engine.bend -- the engines the BF_ENGINE environment variable selects (D7: W6.3, T5.3, W8).
# BF_ENGINE is a comma-separated list of tokens (order does not matter; unknown tokens are ignored):
#   chunked    the chunked executor (DF.collect_with(DF.engine_chunked(), ..): src/cexec.bend, leaves
#              of 2^14 rows) for every collect
#   scan       (W6.6) e2e mode, plan workloads (q1..q5, filter): the sales input is a scan_csv plan read AT
#              COLLECT by the reader (with chunked: the reader's combine builds the chunk leaves the chunked
#              executor takes for its IScan, no flat -> chunk conversion), not an eager read + source
#   (unset, anything else)   the reader and the reference executor
# `v02` (the reader's development name) and `v01` (the first reader, removed before the first release)
# are accepted and ignored, for old command lines.
# The driver reads every CSV input through Eng.read_csv and collects every plan through Eng.collect.
# bench/m2/baseline.sh builds the BASELINE driver with bench/m2/engine_v01.bend copied in as engine.bend
# (the pinned M_01 facade has no engine selector: the baseline binary reads with its reader and collects
# with the reference whatever BF_ENGINE says). The env read is a few microseconds inside the timed read /
# collect.
import Base
import ./../../frame.bend as DF
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P

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

# is the token w in BF_ENGINE
def Eng.on(+w: String) -> IO(Bool):
  do IO<Bool>:
    ev : Result<&1, &1, U32 & String, String> <- IO.get_env("BF_ENGINE")
    return Eng.tok(ev, w)

def Eng.read_csv(+path: String) -> IO(E.ResT(C.Frame)):
  DF.read_csv(path)

def Eng.coll(chunked: Bool, p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  match chunked:
    case True{}:
      DF.collect_with(DF.engine_chunked(), p, env)
    case False{}:
      DF.collect(p, env)

def Eng.collect(p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  do IO<E.ResT(C.Frame)>:
    ch : Bool <- Eng.on("chunked")
    Eng.coll(ch, p, env)

# the `scan` token: the driver's e2e mode scans the sales file instead of reading it first
def Eng.scan_on() -> IO(Bool):
  Eng.on("scan")
