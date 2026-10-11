# W0 spike T4 (disposable): today's parser alone (File.read of the whole file into one String,
# then H.step: records of CsvCell lists), in a program that imports only src/csvparse.bend. Compare
# with `rd_frame <file> 0 hstep` (the same calls inside a program importing frame.bend) and check
# which types are hot in each (tools/hot.py build/hs_solo.c / build/rd_frame.c).
#   ./build/hs_solo [--threads N]      (reads bench/data/sales_1000000.csv from the repo root)
import Base
import ./../../../src/csvparse.bend as H

def count(xs: List<&2, H.CsvRec>, +n: U32) -> U32:
  match xs:
    case Nil{}:
      n
    case h <> t:
      count(t, U32.inc(n))

def out(+t0: Nat, +t1: Nat, +t2: Nat, st: H.Step) -> IO(Unit):
  match st:
    case H.SRej{}:
      IO.print("{\"error\":\"rejected\"}")
    case H.SMore{rows, pst}:
      IO.print("{\"spike\":\"rd\",\"mode\":\"hstep_solo\",\"read_ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"parse_ms\":" ++ Nat.show(Nat.sub(t2, t1)) ++ ",\"ms\":" ++ Nat.show(Nat.sub(t2, t0)) ++ ",\"chk\":" ++ U32.show(count(rows, 0)) ++ "}")

def parsed(+t0: Nat, +t1: Nat, st: H.Step) -> IO(Unit):
  do IO<Unit>:
    t2 : Nat <- IO.now()
    out(t0, t1, t2, st)

def text(+t0: Nat, r: File & Result<&1, &1, U32 & String, String>) -> IO(Unit):
  (f, res) = r
  match res:
    case Fail{e}:
      IO.print("{\"error\":\"io\"}")
    case Done{s}:
      do IO<Unit>:
        File.close(f)
        t1 : Nat <- IO.now()
        parsed(t0, t1, H.step(44, s, H.start()))

def sized(+t0: Nat, r: File & Result<&1, &1, U32 & String, U32>) -> IO(Unit):
  (f, res) = r
  match res:
    case Fail{e}:
      IO.print("{\"error\":\"io\"}")
    case Done{+n}:
      do IO<Unit>:
        r2 : File & Result<&1, &1, U32 & String, String> <- File.read(f, n)
        text(t0, r2)

def opened(+t0: Nat, o: Result<&1, &1, U32 & String, File>) -> IO(Unit):
  match o:
    case Fail{e}:
      IO.print("{\"error\":\"io\"}")
    case Done{f}:
      do IO<Unit>:
        r : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
        sized(t0, r)

def main() -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    o : Result<&1, &1, U32 & String, File> <- File.open("bench/data/sales_1000000.csv", "r")
    opened(t0, o)
