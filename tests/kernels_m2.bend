# The M2 kernels: mask_data, choose, fsum (Neumaier with the non-finite guard, DESIGN.md 15.5.3), map_maybe.
import Base
import ./../src/kernels.bend as K

def arr.k(r: U32 & Array<U32>) -> Array<U32>:
  (n, a) = r
  a

def arr(xs: List<&2, U32>) -> Array<U32>:
  arr.k(K.Kernel.from_list(~U32, xs, 0))

def farr.k(r: U32 & Array<F32>) -> Array<F32>:
  (n, a) = r
  a

def farr(xs: List<&2, F32>) -> Array<F32>:
  farr.k(K.Kernel.from_list(~F32, xs, 0.0))

def us.k(r: Array<U32> & List<&2, U32>) -> String:
  (a, xs) = r
  List.show(~&2, ~U32, ~(x => U32.show(x)), xs)

def us(+n: U32, a: Array<U32>) -> String:
  us.k(K.Kernel.to_list(~U32, n, a))

def two(+n: U32, r: Array<U32> & Array<U32>) -> String:
  (a, b) = r
  us(n, a) ++ " " ++ us(n, b)

def mm.g(r: Array<F32> & List<&2, F32>) -> String:
  (a, xs) = r
  List.show(~&2, ~F32, ~(x => F32.show(x)), xs)

def mm.f(a: Array<F32>) -> String:
  mm.g(K.Kernel.to_list(~F32, 4, a))

def mm.k(r: Array<F32> & Array<U32>) -> String:
  (v, ok) = r
  mm.f(v) ++ " " ++ us(4, ok)

def psqrt(+x: F32) -> Maybe<&2, F32>:
  Bool.pick(Maybe<&2, F32>, F32.is_gt(x, 0.0), Some{F32.sqrt(x)}, None{})

def main() -> IO(Unit):
  do IO<Unit>:
    # mask_data: slots where m = 0 become z, in place; (a, m) back
    IO.print(two(4, K.Kernel.mask_data(~U32, 4, arr([5, 6, 7, 8]), arr([1, 0, 1, 0]), 0)))
    # choose: a[i] where m[i] = 1 else b[i]; (m, a) back
    IO.print(two(4, K.Kernel.choose(~U32, 4, arr([1, 0, 0, 1]), arr([5, 6, 7, 8]), arr([50, 60, 70, 80]))))
    # fsum: compensated; ten 0.1 are exactly 1
    IO.print(F32.show(K.Kernel.fsum(~F32, ~(x => x), 10, farr([0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1]))))
    IO.print(F32.show(K.Kernel.fsum(~U32, ~(x => U32.to_f32(x)), 3, arr([1, 2, 3]))))
    # map_maybe: one pass to values (z on None) and a 0/1 ok mask
    IO.print(mm.k(K.Kernel.map_maybe(~F32, ~F32, ~(x => psqrt(x)), 4, 2n, farr([4.0, F32.neg(1.0), 9.0, 0.0]), 0.0)))
#|[5, 0, 7, 0] [1, 0, 1, 0]
#|[1, 0, 0, 1] [5, 60, 70, 8]
#|1
#|6
#|[2, 0, 3, 0] [1, 0, 1, 0]
