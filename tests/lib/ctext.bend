# tests/lib/ctext.bend -- the text-level CSV tests' reader: the text is written to a file under /tmp and
# read back by the reader (Csv.read_v02_full at the default piece size), so a test states its input as a
# string. Test-only; its main prints nothing (the runner reports it as "PASS (no expect)").
import Base
import ./../../src/err.bend as E
import ./../../src/dtype.bend as D
import ./../../src/column.bend as C
import ./../../src/strs.bend as ST
import ./../../src/kernels.bend as K
import ./../../src/csvprod.bend as P
import ./../../src/csv.bend as V

def Tx.mix(+h: U32, +x: U32) -> U32:
  U32.mul(U32.xor(h, x), 16777619)

def Tx.hash(s: String, +h: U32) -> U32:
  match s:
    case SNil{}:
      h
    case SCon{Chr{+c}, t}:
      Tx.hash(t, Tx.mix(h, c))

# one file per test tag and text: tests run in parallel, and one test writes each of its texts in turn
def Tx.path(+tag: String, +text: String) -> String:
  "/tmp/bend_frame_tx_" ++ tag ++ "_" ++ U32.show(Tx.hash(text, 2166136261)) ++ ".csv"

def Tx.wrote(r: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (file, w) = r
  File.close(file)

def Tx.opened(text: String, o: Result<&1, &1, U32 & String, File>) -> IO(Unit):
  match o:
    case Done{file}:
      do IO<Unit>:
        r : File & Result<&1, &1, U32 & String, Unit> <- File.write(file, text)
        Tx.wrote(r)
    case Fail{e}:
      IO.pure(Unit, Unit{})

def Tx.put(+path: String, text: String) -> IO(Unit):
  do IO<Unit>:
    o : Result<&1, &1, U32 & String, File> <- File.open(path, "w")
    Tx.opened(text, o)

# the text read with the options, dtypes ([] infers), Str storage and row cap
def Tx.read(+tag: String, +text: String, opts: V.CsvOpts, ts: List<&2, D.DType>, enc: ST.StrEnc, +cap: U32) -> IO(E.ResT(C.Frame)):
  do IO<E.ResT(C.Frame)>:
    +path : String = Tx.path(tag, text)
    Tx.put(path, text)
    V.Csv.read_v02_full(path, opts, ts, enc, P.Pr.piece(), cap)

# what Csv.parse_with answered: the default Str storage and row cap
def Tx.parse_with(+tag: String, +text: String, opts: V.CsvOpts, ts: List<&2, D.DType>) -> IO(E.ResT(C.Frame)):
  Tx.read(tag, text, opts, ts, V.Csv.enc_default(), K.Kernel.max_rows())

def Tx.parse(+tag: String, +text: String, opts: V.CsvOpts) -> IO(E.ResT(C.Frame)):
  Tx.parse_with(tag, text, opts, Nil{})

def Tx.parse_cap(+tag: String, +cap: U32, +text: String, opts: V.CsvOpts, ts: List<&2, D.DType>) -> IO(E.ResT(C.Frame)):
  Tx.read(tag, text, opts, ts, V.Csv.enc_default(), cap)

# print what f makes of a read
def Tx.pr(m: IO(E.ResT(C.Frame)), f: E.ResT(C.Frame) -> String) -> IO(Unit):
  IO.bind(E.ResT(C.Frame), Unit, m, r => IO.print(f(r)))

# print a text made in IO
def Tx.out(m: IO(String)) -> IO(Unit):
  IO.bind(String, Unit, m, s => IO.print(s))

def main() -> IO(Unit):
  IO.pure(Unit, Unit{})
