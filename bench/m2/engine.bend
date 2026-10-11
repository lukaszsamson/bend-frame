# bench/m2/engine.bend -- the CSV reader the BF_ENGINE environment variable selects (v0.2 W6.3, D7).
#   BF_ENGINE=v02            the v0.2 reader (DF.read_csv_v02: header step, producer, fork of lanes, combine)
#   anything else / unset    the v0.1 reader (DF.read_csv), the default
# The driver reads every CSV input through Eng.read_csv. bench/m2/baseline.sh builds the BASELINE driver
# with bench/m2/engine_v01.bend copied in as engine.bend (the pinned facade has no v0.2 reader: the
# baseline binary reads with v0.1 whatever BF_ENGINE says). The env read is a few microseconds inside the
# timed read.
import Base
import ./../../frame.bend as DF
import ./../../src/err.bend as E
import ./../../src/column.bend as C

def Eng.pick(v02: Bool, +path: String) -> IO(E.ResT(C.Frame)):
  match v02:
    case True{}:
      DF.read_csv_v02(path)
    case False{}:
      DF.read_csv(path)

def Eng.got(r: Result<&1, &1, U32 & String, String>, +path: String) -> IO(E.ResT(C.Frame)):
  match r:
    case Done{+s}:
      Eng.pick(String.eq(s, "v02"), path)
    case Fail{e}:
      DF.read_csv(path)

def Eng.read_csv(+path: String) -> IO(E.ResT(C.Frame)):
  do IO<E.ResT(C.Frame)>:
    ev : Result<&1, &1, U32 & String, String> <- IO.get_env("BF_ENGINE")
    Eng.got(ev, path)
