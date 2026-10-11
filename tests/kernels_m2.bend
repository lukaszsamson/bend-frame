# The M2 kernels: mask_data, choose, fsum (Neumaier with the non-finite guard, DESIGN.md 15.5.3), map_r /
# zip_r (the unboxed K.R results that replaced map_maybe / zip_maybe, W1d), range (Column.slice, W1f).
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

def udiv(+x: U32, +y: U32) -> K.R<U32>:
  K.Kernel.r_w(Bool.to_u32(U32.is_ne(y, 0)), U32.div(x, y))

def umod(+x: U32, +y: U32) -> K.R<U32>:
  K.Kernel.r_w(Bool.to_u32(U32.is_ne(y, 0)), U32.mod(x, y))

def main() -> IO(Unit):
  do IO<Unit>:
    # mask_data: slots where m = 0 become z, in place; (a, m) back
    IO.print(two(4, K.Kernel.mask_data(~U32, 4, arr([5, 6, 7, 8]), arr([1, 0, 1, 0]), 0)))
    # choose: a[i] where m[i] = 1 else b[i]; (m, a) back
    IO.print(two(4, K.Kernel.choose(~U32, 4, arr([1, 0, 0, 1]), arr([5, 6, 7, 8]), arr([50, 60, 70, 80]))))
    # fsum: compensated; ten 0.1 are exactly 1
    IO.print(F32.show(K.Kernel.fsum(~F32, ~(x => x), 10, farr([0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1, 0.1]))))
    IO.print(F32.show(K.Kernel.fsum(~U32, ~(x => U32.to_f32(x)), 3, arr([1, 2, 3]))))
    # map_r: one pass to values (z on a failure, here through r_of) and a 0/1 ok mask
    IO.print(mm.k(K.Kernel.map_r(~F32, ~F32, ~(x => K.Kernel.r_of(~F32, psqrt(x), 0.0)), 4, 2n, farr([4.0, F32.neg(1.0), 9.0, 0.0]), 0.0)))
    # zip_r: a zero divisor fails with value 0 (r_w masks U32.div / U32.mod's defined answers 0 and x)
    IO.print(two(4, K.Kernel.zip_r(~U32, ~U32, ~U32, ~(x => y => udiv(x, y)), 4, 2n, arr([7, 8, 9, 10]), arr([2, 0, 3, 0]), 0)))
    IO.print(two(4, K.Kernel.zip_r(~U32, ~U32, ~U32, ~(x => y => umod(x, y)), 4, 2n, arr([7, 8, 9, 10]), arr([2, 0, 4, 0]), 0)))
    # range: out[k] = a[off + k]; at offset 0, and to the last row
    IO.print(us(3, K.Kernel.range(~U32, 3, 2n, 2, arr([1, 2, 3, 4, 5, 6]), 0)))
    IO.print(us(2, K.Kernel.range(~U32, 2, 1n, 0, arr([1, 2, 3, 4, 5, 6]), 0)))
    IO.print(us(1, K.Kernel.range(~U32, 1, 0n, 5, arr([1, 2, 3, 4, 5, 6]), 0)))
#|[5, 0, 7, 0] [1, 0, 1, 0]
#|[1, 0, 0, 1] [5, 60, 70, 8]
#|1
#|6
#|[2, 0, 3, 0] [1, 0, 1, 0]
#|[3, 0, 3, 0] [1, 0, 1, 0]
#|[1, 0, 1, 0] [1, 0, 1, 0]
#|[3, 4, 5]
#|[1, 2]
#|[6]
