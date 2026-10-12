# Minimal repro: the floor of the File API. Reads data.csv with
# File.read_at in pieces of 1 MiB and only COUNTS the bytes of each List (one walk, nothing
# built), so the time is the runtime building the byte lists (io_list on the IO thread) plus one
# walk that frees them. cnt_cold.bend runs it with List cold, cnt_hot.bend with List hot.
import Base

def cnt(bs: List<&2, U32>, +n: U32) -> U32:
  match bs:
    case Nil{}:
      n
    case b <> t:
      cnt(t, U32.inc(n))

type CS is Type:
  CRun{f: File, off: U32, size: U32, n: U32}
  CEnd{n: U32}

def Cn.got(r: File & Result<&1, &1, U32 & String, List<&2, U32>>, +off: U32, +size: U32, +n: U32) -> IO(CS):
  (f, res) = r
  match res:
    case Fail{e}:
      do IO<CS>:
        File.close(f)
        return CEnd{n}
    case Done{bs}:
      IO.pure(CS, CRun{f, U32.add(off, 1048576), size, cnt(bs, n)})

def Cn.read(done: Bool, f: File, +off: U32, +size: U32, +n: U32) -> IO(CS):
  match done:
    case True{}:
      do IO<CS>:
        File.close(f)
        return CEnd{n}
    case False{}:
      do IO<CS>:
        r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_at(f, off, 1048576)
        Cn.got(r, off, size, n)

def Cn.step(st: CS) -> IO(CS):
  match st:
    case CEnd{n}:
      IO.pure(CS, CEnd{n})
    case CRun{f, +off, +size, +n}:
      Cn.read(U32.is_ge(off, size), f, off, size, n)

def Cn.loop(fuel: Nat, st: CS) -> IO(CS):
  match fuel:
    case 0n:
      IO.pure(CS, st)
    case 1n+p:
      do IO<CS>:
        st2 : CS <- Cn.step(st)
        Cn.loop(p, st2)

def Cn.size(r: File & Result<&1, &1, U32 & String, U32>) -> IO(CS):
  (f, res) = r
  match res:
    case Fail{e}:
      do IO<CS>:
        File.close(f)
        return CEnd{0}
    case Done{+size}:
      Cn.loop(U32.to_nat(U32.add(U32.div(size, 1048576), 3)), CRun{f, 0, size, 0})

def Cn.opened(o: Result<&1, &1, U32 & String, File>) -> IO(CS):
  match o:
    case Fail{e}:
      IO.pure(CS, CEnd{0})
    case Done{f}:
      do IO<CS>:
        r : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
        Cn.size(r)

def Cn.n(st: CS) -> U32:
  match st:
    case CEnd{n}:
      n
    case CRun{f, off, size, n}:
      n

def Cn.out(+mode: String, +t0: Nat, +t1: Nat, +n: U32) -> IO(Unit):
  IO.print("{\"spike\":\"rd\",\"mode\":\"" ++ mode ++ "\",\"bytes\":" ++ U32.show(n) ++ ",\"ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"chk\":" ++ U32.show(n) ++ "}")

def Cn.run(+mode: String) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    o : Result<&1, &1, U32 & String, File> <- File.open("data.csv", "r")
    st : CS <- Cn.opened(o)
    t1 : Nat <- IO.now()
    Cn.out(mode, t0, t1, Cn.n(st))

def main() -> IO(Unit):
  Cn.run("count")
