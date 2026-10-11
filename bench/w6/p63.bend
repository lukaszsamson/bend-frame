# bench/w6/p63.bend -- W6.3 phase probe of the integrated v0.2 reader (src/csv.bend Csv.v2.*), in a
# program that imports frame.bend (the real hot-type build). The phases of Csv.read_v02_full's inferred
# path (infer_rows 100, header, ',' , EncAuto), each timed on its own:
#   head_ms   the header step (Csv.v2.header)
#   read_ms   the producer (Pr.regions)
#   cls_ms    the head classification (leading regions tokenized + classified until 100 rows)
#   fork_ms   the fork of lanes over the other regions (+ the kept head tokens' columns)
#   comb_ms   the combine (summary, error order, concatenation, dictionary merge, Frame.from_columns)
# then (untimed) the frame's height and DF's content check of bench/m2 (a hash of the logical content).
#
#   ~/.bend/bin/bend bench/w6/p63.bend -o build/w6/p63
#   build/w6/p63 [--threads N] <file> [piece]
import Base
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/kernels.bend as K
import ./../../src/column.bend as C
import ./../../src/strs.bend as ST
import ./../../src/csv.bend as V
import ./../../src/csvprod.bend as P
import ./../../src/csvlane.bend as L
import ./../../frame.bend as DF

# the rows of the lanes (forces them), handed back
def Pb.rows(los: List<&1, L.LO>, +acc: U32, out: List<&1, L.LO>) -> List<&1, L.LO> & U32:
  match los:
    case Nil{}:
      (List.reverse(&1, L.LO, out), acc)
    case L.LO{+n, rej, rag, rgn, lines, cols} <> t:
      Pb.rows(t, U32.add(acc, n), L.LO{n, rej, rag, rgn, lines, cols} <> out)

def Pb.h2(r: C.Frame & U32) -> String:
  (f, +h) = r
  "\"rows\":" ++ U32.show(h)

def Pb.height(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "\"error\":\"" ++ E.Err.show(e) ++ "\""
    case Done{f}:
      Pb.h2(C.Frame.height(f))

def Pb.ms(+a: Nat, +b: Nat) -> String:
  Nat.show(Nat.sub(b, a))

type Ph is Type:
  Ph{t: Nat, w: U32, names: List<&2, String>, regs: List<&1, P.Rg>}

def Pb.comb(+t0: Nat, +t1: Nat, +t2: Nat, +t3: Nat, +w: U32, names: List<&2, String>, +dts: List<&2, D.DType>, r: List<&1, L.LO> & U32) -> IO(Unit):
  (los, +n) = r
  do IO<Unit>:
    +t4 : Nat <- IO.now()
    res : E.ResT(C.Frame) <- IO.pure(E.ResT(C.Frame), V.Csv.v2.fin(None{}, V.Csv.v2.tys(dts, ST.EncAuto{}), dts, names, w, K.Kernel.max_rows(), ST.EncAuto{}, los))
    +t5 : Nat <- IO.now()
    IO.print("{\"head_ms\":" ++ Pb.ms(t0, t1) ++ ",\"read_ms\":" ++ Pb.ms(t1, t2) ++ ",\"cls_ms\":" ++ Pb.ms(t2, t3) ++ ",\"fork_ms\":" ++ Pb.ms(t3, t4) ++ ",\"comb_ms\":" ++ Pb.ms(t4, t5) ++ ",\"total_ms\":" ++ Pb.ms(t0, t5) ++ "," ++ Pb.height(res) ++ ",\"lane_rows\":" ++ U32.show(n) ++ "}")

def Pb.lanes(+t0: Nat, +t1: Nat, +t2: Nat, +w: U32, names: List<&2, String>, r: V.QHR) -> IO(Unit):
  match r:
    case V.QHR{V.QHP{tos, g, off, go}, rest}:
      do IO<Unit>:
        +t3 : Nat <- IO.now()
        +dts : List<&2, D.DType> = V.Csv.v2.ci.dts(g, 100)
        +tys : List<&2, L.Ty> = V.Csv.v2.tys(dts, ST.EncAuto{})
        Pb.comb(t0, t1, t2, t3, w, names, dts, Pb.rows(V.Csv.v2.hcols(tos, tys, w, V.Csv.v2.lanes(tys, w, 44, rest)), 0, Nil{}))

def Pb.prod(+t0: Nat, +t1: Nat, +w: U32, names: List<&2, String>, o: P.PrOut) -> IO(Unit):
  match o:
    case P.PrErr{code, msg}:
      IO.print("error: " ++ msg)
    case P.PrOk{nr, odd, regs}:
      do IO<Unit>:
        +t2 : Nat <- IO.now()
        Pb.lanes(t0, t1, t2, w, names, V.Csv.v2.hp.go(regs, w, 44, 100, V.QHP{Nil{}, V.Csv.v2.ci.zero(U32.to_nat(w)), 0, True{}}))

def Pb.go(+t0: Nat, +path: String, +piece: U32, hd: V.QD) -> IO(Unit):
  match hd:
    case V.QDOk{names, +w, off0, line0}:
      do IO<Unit>:
        +t1 : Nat <- IO.now()
        o : P.PrOut <- P.Pr.regions(path, off0, line0, piece)
        Pb.prod(t0, t1, w, names, o)
    case _:
      IO.print("error: header")

def promote(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> promote(t)

def nth(+i: Nat, xs: List<&2, String>, +d: String) -> String:
  match i xs:
    case _ Nil{}:
      d
    case 0n h <> t:
      h
    case 1n+j h <> t:
      nth(j, t, d)

def run(+path: String, +piece: U32) -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    hd : V.QD <- V.Csv.v2.header(path, True{}, 44, 65536)
    Pb.go(t0, path, piece, hd)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    +xs : List<&2, String> = List.tail(&2, String, promote(args))
    run(nth(0n, xs, "bench/data/sales_1000000.csv"), U32.from_nat(Maybe.default(&2, Nat, Nat.read(nth(1n, xs, "245760")), 245760n)))
