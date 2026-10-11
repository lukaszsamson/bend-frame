# W0 spike T4 (disposable): the producer alone (File.read_at pieces of 1 MiB, pack + lexical
# scan) in a program that never `+`-shares a List, so the byte lists File.read_at builds are
# COLD (no rfc_seal per cell; check: python3 tools/hot.py build/pk_cold.c CON). Compare with
# `rd_frame <file> 1048576 pack` (the same producer in a program where List is hot).
#   ./build/pk_cold [--threads N]      (reads bench/data/sales_1000000.csv from the repo root)
import Base
import ./rd.bend as R

def bytes(xs: List<&1, R.Rg>, +b: U32) -> U32:
  match xs:
    case Nil{}:
      b
    case R.Rg{a, +n, line0, nt, fin, hd} <> rest:
      bytes(rest, U32.add(b, n))

def out(+t0: Nat, +t1: Nat, +b: U32) -> IO(Unit):
  IO.print("{\"spike\":\"rd\",\"mode\":\"pack_cold\",\"bytes\":" ++ U32.show(b) ++ ",\"ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"chk\":" ++ U32.show(b) ++ "}")

def fin(+t0: Nat, rs: R.RS) -> IO(Unit):
  match rs:
    case R.REnd{nr, regs, err}:
      do IO<Unit>:
        t1 : Nat <- IO.now()
        out(t0, t1, bytes(regs, 0))
    case R.RRun{f, off, size, p, line0, hd, nr, pk, regs}:
      IO.print("{\"error\":\"unfinished\"}")

def main() -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    rs : R.RS <- R.Rd.regions("bench/data/sales_1000000.csv", 1048576, 1)
    fin(t0, rs)
