# bench/m2/engine_v01.bend -- the BASELINE build's engine.bend (bench/m2/baseline.sh copies it in as
# engine.bend): the pinned facade (3612482) has only the v0.1 reader, so every BF_ENGINE value reads
# with DF.read_csv. Same API as bench/m2/engine.bend.
import Base
import ./../../frame.bend as DF
import ./../../src/err.bend as E
import ./../../src/column.bend as C

def Eng.read_csv(+path: String) -> IO(E.ResT(C.Frame)):
  DF.read_csv(path)
