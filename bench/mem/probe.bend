# Memory probes (native): ~/.bend/bin/bend bench/mem/probe.bend -o build/memprobe
#   /usr/bin/time -l ./build/memprobe <mode> <arg>    (peak RSS from time -l)
# arr D        a U32 array of 2^D slots, summed
# list D       a cons list of 2^D U32s, summed (consumed)
# list_arr D   list D, then (the list freed) arr D: peak ~ max(list, arr) if freed memory is reused
# read PATH    DF.read_csv, then the height
# read2 PATH   read, drop the frame, read again
import Base
import ./../../frame.bend as DF
import ./../../src/kernels.bend as K
import ./../../src/column.bend as C

def arr.k(r: Array<U32> & U32) -> U32:
  (a, +s) = r
  s

def arr(+d: Nat) -> U32:
  arr.k(K.Kernel.fold(~U32, ~U32, ~(a => x => U32.add(a, x)), U32.shln(1, d), Array.new(U32, d, 1), 0))

def list.mk(+n: Nat, acc: List<&1, U32>) -> List<&1, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      list.mk(p, U32.from_nat(p) <> acc)

def list.sum(xs: List<&1, U32>, +s: U32) -> U32:
  match xs:
    case Nil{}:
      s
    case x <> t:
      list.sum(t, U32.add(s, x))

def list(+d: Nat) -> U32:
  list.sum(list.mk(U32.to_nat(U32.shln(1, d)), Nil{}), 0)

def height.k(r: C.Frame & U32) -> U32:
  (f, +h) = r
  h

def height(r: DF.ResT(DF.Frame())) -> U32:
  match r:
    case Fail{e}:
      0
    case Done{f}:
      height.k(DF.height(f))

def show(+x: U32) -> IO(Unit):
  IO.print(U32.show(x))

def run.read(+path: String) -> IO(Unit):
  do IO<Unit>:
    r : DF.ResT(DF.Frame()) <- DF.read_csv(path)
    show(height(r))

def run.read2(+path: String) -> IO(Unit):
  do IO<Unit>:
    r : DF.ResT(DF.Frame()) <- DF.read_csv(path)
    show(height(r))
    r2 : DF.ResT(DF.Frame()) <- DF.read_csv(path)
    show(height(r2))

def run.both(+d: Nat) -> IO(Unit):
  do IO<Unit>:
    show(list(d))
    show(arr(d))

def run.pick(+is_arr: Bool, +is_list: Bool, +d: Nat) -> IO(Unit):
  match is_arr is_list:
    case True{} _:
      show(arr(d))
    case False{} True{}:
      show(list(d))
    case False{} False{}:
      run.both(d)

def run.d(+mode: String, m: Maybe<&2, Nat>) -> IO(Unit):
  match m:
    case None{}:
      IO.print("bad depth")
    case Some{+d}:
      run.pick(String.eq(mode, "arr"), String.eq(mode, "list"), d)

def nth(+i: Nat, xs: List<&2, String>, +d: String) -> String:
  match i xs:
    case _ Nil{}:
      d
    case 0n h <> t:
      h
    case 1n+j h <> t:
      nth(j, t, d)

def promote(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> promote(t)

def go.k(+is_read: Bool, +is_read2: Bool, +mode: String, +arg: String) -> IO(Unit):
  match is_read is_read2:
    case True{} _:
      run.read(arg)
    case False{} True{}:
      run.read2(arg)
    case False{} False{}:
      run.d(mode, Nat.read(arg))

def go(+mode: String, +arg: String) -> IO(Unit):
  go.k(String.eq(mode, "read"), String.eq(mode, "read2"), mode, arg)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    +xs : List<&2, String> = List.tail(&2, String, promote(args))
    go(nth(0n, xs, "arr"), nth(1n, xs, "20"))
