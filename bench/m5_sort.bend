# M5 sort micro-benchmark (native):
#   ~/.bend/bin/bend bench/m5_sort.bend -o build/m5_sort && ./build/m5_sort 1000000
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/kernels.bend as K
import ./../src/column.bend as C
import ./../src/sort.bend as SO

def promote(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> promote(t)

def lcg(+x: U32) -> U32:
  U32.add(U32.mul(x, 1664525), 1013904223)

def gen.go(n: Nat, +i: U32, +x: U32, u: Array<U32>, f: Array<F32>) -> Array<U32> & Array<F32>:
  match n:
    case 0n:
      (u, f)
    case 1n+p:
      +y = lcg(x)
      gen.go(p, U32.inc(i), y, Array.set(U32, u, i, U32.shrn(y, 2n)), Array.set(F32, f, i, F32.div(U32.to_f32(U32.shrn(lcg(y), 9n)), 1000.0)))

def mkframe.b(+n: U32, +d: Nat, r: Array<U32> & Array<F32>) -> C.Frame:
  (u, f) = r
  C.Frame{n, [C.Named{"u", C.CU32{n, d, C.AllValid{}, u}}, C.Named{"f", C.CF32{n, d, C.AllValid{}, f}}]}

def mkframe(+n: U32) -> C.Frame:
  +d = K.Kernel.depth_for(n)
  mkframe.b(n, d, gen.go(U32.to_nat(n), 0, 12345, Array.new(U32, d, 0), Array.new(F32, d, 0.0)))

# count of i with a[i-1] > a[i]
def bad.go(n: Nat, +i: U32, +prev: U32, acc: U32, r: Array<U32> & U32) -> U32:
  match n:
    case 0n:
      acc
    case 1n+p:
      (a, +x) = r
      bad.go(p, U32.inc(i), x, U32.add(acc, Bool.to_u32(U32.is_gt(prev, x))), Array.get(U32, a, U32.inc(i)))

def check.w(+n: U32, r: Array<U32> & C.Valid) -> String:
  (w, v) = r
  "inversions=" ++ U32.show(bad.go(U32.to_nat(n), 0, 0, 0, Array.get(U32, w, 0)))

def check.k(+n: U32, r: C.Frame & E.ResT(C.Column)) -> String:
  (f, rc) = r
  match rc:
    case Fail{e}:
      E.Err.show(e)
    case Done{c}:
      check.w(n, SO.Sort.words(c, False{}))

def check(+n: U32, +name: String, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      E.Err.show(e)
    case Done{f}:
      check.k(n, C.Frame.get_cloned(f, name))

def stamp(label: String, t0: Nat) -> IO(Nat):
  do IO<Nat>:
    t1 : Nat <- IO.now()
    IO.print(label ++ ": " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms")
    IO.now()

def run(+n: U32) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    +s1 : String = check(n, "u", SO.Sort.frame(mkframe(n), [SO.SortKey{"u", False{}, False{}}]))
    IO.print(s1)
    t1 : Nat <- stamp("gen+sort u32 (" ++ U32.show(n) ++ ")", t0)
    +s0 : String = check(n, "u", Done{mkframe(n)})
    IO.print(s0)
    t2 : Nat <- stamp("gen only", t1)
    +s2 : String = check(n, "f", SO.Sort.frame(mkframe(n), [SO.SortKey{"f", False{}, False{}}]))
    IO.print(s2)
    t3 : Nat <- stamp("gen+sort f32", t2)
    +s3 : String = check(n, "u", SO.Sort.frame(mkframe(n), [SO.SortKey{"u", False{}, False{}}, SO.SortKey{"f", True{}, False{}}]))
    IO.print(s3)
    t4 : Nat <- stamp("gen+sort u32,f32 desc", t3)
    return Unit{}

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    +as : List<&2, String> = promote(args)
    run(Maybe.default(&2, U32, U32.read(Maybe.default(&2, String, List.get(&2, String, as, 1n), "100000")), 100000))
