# bench/m2/engine.bend -- the engines the BF_ENGINE environment variable selects (v0.2 D7: W6.3, T5.3, W8).
# BF_ENGINE is a comma-separated list of tokens (order does not matter; unknown tokens are ignored):
#   v02        the v0.2 CSV reader (DF.read_csv_v02: header step, producer, fork of lanes, combine); since
#              W8 the default reader, so `v02` is the same as no token (kept for old command lines)
#   v01        (W8) the v0.1 CSV reader, explicitly (DF.read_csv_engine(DF.csv_engine_v01(), ..) and
#              DF.collect_engine / Lazy.collect_with_rd with csv_engine_v01 for scans); wins over v02
#   chunked    the chunked executor (DF.collect_with(DF.engine_chunked(), ..): src/cexec.bend, leaves
#              of 2^14 rows) for every collect
#   scan       (W6.6) e2e mode, plan workloads (q1..q5, filter): the sales input is a scan_csv plan read AT
#              COLLECT by the selected reader (with the v0.2 reader and chunked: the v0.2 combine builds the
#              chunk leaves the chunked executor takes for its IScan, no flat -> chunk conversion), not an
#              eager read + source
#   (unset, anything else)   the DEFAULT reader (v0.2 since W8) and the reference executor
# e.g. BF_ENGINE=v02,chunked reads with the v0.2 reader and collects with the chunked executor;
# BF_ENGINE=v02,chunked,scan scans the sales file and collects it chunked from the reader's leaves;
# BF_ENGINE=v01 measures the v0.1 reader on the candidate.
# The driver reads every CSV input through Eng.read_csv and collects every plan through Eng.collect.
# bench/m2/baseline.sh builds the BASELINE driver with bench/m2/engine_v01.bend copied in as engine.bend
# (the pinned facade has neither the v0.2 reader nor the engine selector: the baseline binary reads with
# v0.1 and collects with the reference whatever BF_ENGINE says). The env read is a few microseconds
# inside the timed read / collect.
import Base
import ./../../frame.bend as DF
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./../../src/cexec.bend as QC

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

def Eng.pick(v01: Bool, +path: String) -> IO(E.ResT(C.Frame)):
  match v01:
    case True{}:
      DF.read_csv_engine(DF.csv_engine_v01(), path, DF.csv_opts(',', True{}, 100), Nil{}, DF.str_auto())
    case False{}:
      DF.read_csv(path)

# v02 and no token both read with the default reader (v0.2 since W8); v01 with the v0.1 reader
def Eng.read_csv(+path: String) -> IO(E.ResT(C.Frame)):
  do IO<E.ResT(C.Frame)>:
    v01 : Bool <- Eng.on("v01")
    Eng.pick(v01, path)

def Eng.coll(chunked: Bool, p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  match chunked:
    case True{}:
      DF.collect_with(DF.engine_chunked(), p, env)
    case False{}:
      DF.collect(p, env)

# a plan's scans (W6.6, token `scan`) are read at collect by the selected reader: the default (v0.2) reader
# + chunked hands the reader's chunk leaves to the chunked executor (cexec.bend Lazy.collect_with_rd); v01
# reads them with the v0.1 reader; a plan without scans collects exactly as Eng.coll (the reader is unused)
def Eng.coll2(v01: Bool, chunked: Bool, p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  match v01:
    case True{}:
      match chunked:
        case True{}:
          QC.Lazy.collect_with_rd(DF.csv_engine_v01(), DF.engine_chunked(), p, env)
        case False{}:
          DF.collect_engine(DF.csv_engine_v01(), p, env)
    case False{}:
      Eng.coll(chunked, p, env)

def Eng.collect(p: P.Plan, env: P.Env) -> IO(E.ResT(C.Frame)):
  do IO<E.ResT(C.Frame)>:
    v01 : Bool <- Eng.on("v01")
    ch : Bool <- Eng.on("chunked")
    Eng.coll2(v01, ch, p, env)

# the `scan` token: the driver's e2e mode scans the sales file instead of reading it first
def Eng.scan_on() -> IO(Bool):
  Eng.on("scan")
