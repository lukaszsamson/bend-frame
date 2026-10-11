# W0 spike T4/T5: the piece reader INSIDE a program that imports frame.bend and runs today's
# reader (the "hot" build: String, List, Tuple, ... are refcounted everywhere here, as in every
# real bend-frame program). Modes:
#   spike / pack   rd.bend's reader (see rd_drv.bend)
#   ref            today's Csv.read_with with the same explicit schema (u32, str, str, u32, f32,
#                  f32, bool): read_ms, and the checksum of the same cells (equal chk = equal
#                  values, validity, dictionary codes and dictionary size)
#   hstep          today's parser alone: File.read of the whole file (one String) then H.step
#                  (records of CsvCell lists), no columns: the review's "read + parse" probe
#   ~/.bend/bin/bend bench/spikes/w0_strings/rd_frame.bend -o bench/spikes/w0_strings/build/rd_frame
#   ./build/rd_frame [--threads N] <file.csv> [piece bytes] [spike|pack|ref|hstep]
import Base
import ./../../../src/dtype.bend as D
import ./../../../src/err.bend as E
import ./../../../src/kernels.bend as K
import ./../../../src/column.bend as C
import ./../../../src/strs.bend as ST
import ./../../../src/csv.bend as V
import ./../../../src/csvparse.bend as H
import ./../../../frame.bend as DF
import ./rd_drv.bend as RD

# ---- ref: today's reader, the same checksum ------------------------------------------------------

def Ref.st(+n: U32, +d: Nat, v: C.Valid, x: ST.Strs) -> U32:
  match x:
    case ST.SDict{codes, dict}:
      RD.Ck.mix(RD.Ck.w(n, codes, C.Valid.materialize(v, d)), RD.Ck.d.k(ST.Dict.size(dict)))
    case ST.SRaw{a}:
      1

def Ref.col(c: C.Column) -> U32:
  match c:
    case C.CU32{+n, +d, v, x}:
      RD.Ck.w(n, x, C.Valid.materialize(v, d))
    case C.CBool{+n, +d, v, x}:
      RD.Ck.w(n, x, C.Valid.materialize(v, d))
    case C.CI32{+n, +d, v, x}:
      RD.Ck.w(n, x, C.Valid.materialize(v, d))
    case C.CF32{+n, +d, v, x}:
      RD.Ck.f(n, x, C.Valid.materialize(v, d))
    case C.CStr{+n, +d, v, x}:
      Ref.st(n, d, v, x)

# the same fold as RD.Ck.cols: columns last first
def Ref.cols(cs: List<&1, C.Named>, +acc: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      acc
    case C.Named{n, c} <> t:
      Ref.cols(t, Ref.col(c) <> acc)

def Ref.fold(xs: List<&2, U32>, +h: U32) -> U32:
  match xs:
    case Nil{}:
      h
    case +x <> t:
      Ref.fold(t, RD.Ck.mix(h, x))

def Ref.rfold(xs: List<&2, U32>) -> U32:
  Ref.fold(List.reverse(&2, U32, xs), 2166136261)

def Ref.out(+t0: Nat, +t1: Nat, r: E.ResT(C.Frame)) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("{\"spike\":\"rd\",\"mode\":\"ref\",\"error\":\"" ++ E.Err.show(e) ++ "\"}")
    case Done{C.Frame{+h, cols}}:
      IO.print("{\"spike\":\"rd\",\"mode\":\"ref\",\"n\":" ++ U32.show(h) ++ ",\"read_ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"chk\":" ++ U32.show(Ref.rfold(Ref.cols(cols, Nil{}))) ++ "}")

def Ref.ty(+c: U32) -> D.DType:
  Bool.pick(D.DType, U32.is_eq(c, 85), D.TU32{}, Bool.pick(D.DType, U32.is_eq(c, 70), D.TF32{}, Bool.pick(D.DType, U32.is_eq(c, 66), D.TBool{}, Bool.pick(D.DType, U32.is_eq(c, 73), D.TI32{}, D.TStr{}))))

def Ref.schema(s: String) -> List<&2, D.DType>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      Ref.ty(c) <> Ref.schema(t)

def Ref.run(+path: String, tys: String) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    r : E.ResT(C.Frame) <- V.Csv.read_with(path, V.Csv.default(), Ref.schema(tys))
    t1 : Nat <- IO.now()
    Ref.out(t0, t1, r)

# ---- hstep: File.read + H.step only ----------------------------------------------------------------

def Hs.count(xs: List<&2, H.CsvRec>, +n: U32) -> U32:
  match xs:
    case Nil{}:
      n
    case h <> t:
      Hs.count(t, U32.inc(n))

def Hs.out(+t0: Nat, +t1: Nat, +t2: Nat, st: H.Step) -> IO(Unit):
  match st:
    case H.SRej{}:
      IO.print("{\"spike\":\"rd\",\"mode\":\"hstep\",\"error\":\"rejected\"}")
    case H.SMore{rows, pst}:
      IO.print("{\"spike\":\"rd\",\"mode\":\"hstep\",\"read_ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"parse_ms\":" ++ Nat.show(Nat.sub(t2, t1)) ++ ",\"ms\":" ++ Nat.show(Nat.sub(t2, t0)) ++ ",\"chk\":" ++ U32.show(Hs.count(rows, 0)) ++ "}")

def Hs.parsed(+t0: Nat, +t1: Nat, st: H.Step) -> IO(Unit):
  do IO<Unit>:
    t2 : Nat <- IO.now()
    Hs.out(t0, t1, t2, st)

def Hs.text(+t0: Nat, r: File & Result<&1, &1, U32 & String, String>) -> IO(Unit):
  (f, res) = r
  match res:
    case Fail{e}:
      IO.print("{\"error\":\"io\"}")
    case Done{+s}:
      do IO<Unit>:
        File.close(f)
        t1 : Nat <- IO.now()
        Hs.parsed(t0, t1, H.step(44, s, H.start()))

def Hs.size(+t0: Nat, r: File & Result<&1, &1, U32 & String, U32>) -> IO(Unit):
  (f, res) = r
  match res:
    case Fail{e}:
      IO.print("{\"error\":\"io\"}")
    case Done{+n}:
      do IO<Unit>:
        r2 : File & Result<&1, &1, U32 & String, String> <- File.read(f, n)
        Hs.text(t0, r2)

def Hs.opened(+t0: Nat, o: Result<&1, &1, U32 & String, File>) -> IO(Unit):
  match o:
    case Fail{e}:
      IO.print("{\"error\":\"io\"}")
    case Done{f}:
      do IO<Unit>:
        r : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
        Hs.size(t0, r)

def Hs.run(+path: String) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    o : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    Hs.opened(t0, o)

# ---- main ------------------------------------------------------------------------------------------

def go.m(+path: String, +piece: U32, +mode: String, +tys: String) -> IO(Unit):
  Bool.pick(IO(Unit), String.eq(mode, "ref"), Ref.run(path, tys), Bool.pick(IO(Unit), String.eq(mode, "hstep"), Hs.run(path), RD.Drv.run(path, piece, mode, tys)))

def go(+xs: List<&2, String>) -> IO(Unit):
  go.m(RD.Drv.nth(0n, xs, "bench/data/sales_1000.csv"), RD.Drv.num(U32.read(RD.Drv.nth(1n, xs, "1048576")), 1048576), RD.Drv.nth(2n, xs, "spike"), RD.Drv.nth(3n, xs, "USSUFFB"))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(List.tail(&2, String, RD.Drv.promote(args)))
