# M1: the flat template kernels on small arrays (p02, p10, p14, p17, p22 shapes).
import Base
import ./../src/kernels.bend as K

def shu(a: Array<U32>) -> String:
  List.show(~&1, ~U32, ~(x => U32.show(x)), Array.to_list(~U32, a))

def shf(a: Array<F32>) -> String:
  List.show(~&1, ~F32, ~(x => F32.show(x)), Array.to_list(~F32, a))

def shs(a: Array<String>) -> String:
  List.show(~&1, ~String, ~(s => s), Array.to_list(~String, a))

# the array out of (len, array)
def arr(~T: Data, r: U32 & Array<T>) -> Array<T>:
  (n, a) = r
  a

def lenshu(r: U32 & Array<U32>) -> String:
  (n, a) = r
  U32.show(n) ++ " " ++ shu(a)

def lenshf(r: U32 & Array<F32>) -> String:
  (n, a) = r
  U32.show(n) ++ " " ++ shf(a)

def lenshs(r: U32 & Array<String>) -> String:
  (n, a) = r
  U32.show(n) ++ " " ++ shs(a)

# fold answers (array, acc)
def foldf(r: Array<F32> & F32) -> String:
  (a, x) = r
  F32.show(x)

def foldu(r: Array<U32> & U32) -> String:
  (a, x) = r
  U32.show(x)

# compact answers (out, kept)
def cmp(r: Array<F32> & U32) -> String:
  (out, k) = r
  U32.show(k) ++ " kept; slots: " ++ shf(out)

# gather answers (out, perm)
def gat(r: Array<F32> & Array<U32>) -> String:
  (out, perm) = r
  shf(out) ++ " perm " ++ shu(perm)

# compact_keep answers (out, mask); slots past `kept` are unspecified, so
# only the first 2 are shown
def cmpk.k(mask: Array<U32>, r: Array<F32> & List<&2, F32>) -> String:
  (out, xs) = r
  List.show(~&2, ~F32, ~(x => F32.show(x)), xs) ++ " mask " ++ shu(mask)

def cmpk(r: Array<F32> & Array<U32>) -> String:
  (out, mask) = r
  cmpk.k(mask, K.Kernel.to_list(~F32, 2, out))

# to_list answers (array, list)
def tol(r: Array<U32> & List<&2, U32>) -> String:
  (a, xs) = r
  List.show(~&2, ~U32, ~(x => U32.show(x)), xs)

# a > 2.0 as 0/1 words
def gt2(x: F32) -> U32:
  Bool.to_u32(F32.is_gt(x, 2.0))

def count(acc: U32, x: F32) -> U32:
  U32.inc(acc)

def eqs(a: String, b: String) -> Bool:
  String.eq(a, b)

def main() -> IO(Unit):
  do IO<Unit>:
    # depth_for / from_list (p14)
    IO.print(Nat.show(K.Kernel.depth_for(0)) ++ " " ++ Nat.show(K.Kernel.depth_for(1)) ++ " " ++ Nat.show(K.Kernel.depth_for(2)) ++ " " ++ Nat.show(K.Kernel.depth_for(5)) ++ " " ++ Nat.show(K.Kernel.depth_for(1024)) ++ " " ++ Nat.show(K.Kernel.depth_for(1025)))
    IO.print(lenshs(K.Kernel.from_list(~String, ["ann", "bob", "cy"], "")))
    IO.print(lenshf(K.Kernel.from_list(~F32, [1.5, 2.5, 3.5, 4.5, 5.5], 0.0)))
    IO.print(lenshf(K.Kernel.from_list(~F32, [], 0.0)))
    # map / zip / fold
    IO.print(shf(K.Kernel.map(~F32, ~F32, ~(x => F32.mul(x, 2.0)), 3, 2n, arr(~F32, K.Kernel.from_list(~F32, [1.0, 2.0, 3.0], 0.0)), 0.0)))
    IO.print(shu(K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), 3, 2n, arr(~U32, K.Kernel.from_list(~U32, [1, 2, 3], 0)), arr(~U32, K.Kernel.from_list(~U32, [10, 20, 30], 0)), 0)))
    IO.print(shu(K.Kernel.zip(~F32, ~F32, ~U32, ~(x => y => Bool.to_u32(F32.is_lt(x, y))), 3, 2n, arr(~F32, K.Kernel.from_list(~F32, [1.0, 5.0, 3.0], 0.0)), arr(~F32, K.Kernel.from_list(~F32, [2.0, 4.0, 3.0], 0.0)), 0)))
    IO.print(foldf(K.Kernel.fold(~F32, ~F32, ~(acc => x => F32.add(acc, x)), 5, arr(~F32, K.Kernel.from_list(~F32, [1.0, 2.0, 3.0, 4.0, 5.0], 0.0)), 0.0)))
    IO.print(foldu(K.Kernel.fold(~U32, ~U32, ~(acc => x => U32.add(acc, x)), 0, arr(~U32, K.Kernel.from_list(~U32, [], 0)), 7)))
    # compact (p17): keep the rows > 2.0
    IO.print(cmp(K.Kernel.compact(~F32, 8, 3n, arr(~F32, K.Kernel.from_list(~F32, [1.0, 5.0, 1.0, 1.0, 3.0, 1.0, 1.0, 9.0], 0.0)), K.Kernel.map(~F32, ~U32, ~gt2, 8, 3n, arr(~F32, K.Kernel.from_list(~F32, [1.0, 5.0, 1.0, 1.0, 3.0, 1.0, 1.0, 9.0], 0.0)), 0), 0.0)))
    IO.print(cmpk(K.Kernel.compact_keep(~F32, 4, 2n, arr(~F32, K.Kernel.from_list(~F32, [1.0, 2.0, 3.0, 4.0], 0.0)), arr(~U32, K.Kernel.from_list(~U32, [0, 1, 1, 0], 0)), 0.0)))
    # gather (p10)
    IO.print(gat(K.Kernel.gather(~F32, 4, 2n, arr(~F32, K.Kernel.from_list(~F32, [10.0, 20.0, 30.0, 40.0], 0.0)), arr(~U32, K.Kernel.from_list(~U32, [3, 0, 2, 1], 0)), 0.0)))
    # scatter (p22): per-group sums and counts
    IO.print(shf(K.Kernel.scatter(~F32, ~F32, ~(acc => x => F32.add(acc, x)), 6, arr(~U32, K.Kernel.from_list(~U32, [0, 1, 2, 1, 0, 1], 0)), arr(~F32, K.Kernel.from_list(~F32, [1.0, 2.0, 3.0, 4.0, 5.0, 6.0], 0.0)), [0.0 : F32*4n])))
    IO.print(shu(K.Kernel.scatter(~F32, ~U32, ~count, 6, arr(~U32, K.Kernel.from_list(~U32, [0, 1, 2, 1, 0, 1], 0)), arr(~F32, K.Kernel.from_list(~F32, [1.0, 2.0, 3.0, 4.0, 5.0, 6.0], 0.0)), [0 : U32*4n])))
    # extras
    IO.print(shu(K.Kernel.iota(5, 3n)))
    IO.print(shu(K.Kernel.iota_from(3, 2n, 10)))
    IO.print(shf(K.Kernel.const(~F32, 1n, 1.5)))
    IO.print(tol(K.Kernel.to_list(~U32, 3, arr(~U32, K.Kernel.from_list(~U32, [7, 8, 9], 0)))))
    IO.print(tol(K.Kernel.to_list(~U32, 0, arr(~U32, K.Kernel.from_list(~U32, [], 0)))))
    IO.print(shu(K.Kernel.mask_and(4, 2n, arr(~U32, K.Kernel.from_list(~U32, [1, 0, 1, 1], 0)), arr(~U32, K.Kernel.from_list(~U32, [1, 1, 0, 1], 0)))))
    IO.print(shu(K.Kernel.mask_or(4, 2n, arr(~U32, K.Kernel.from_list(~U32, [1, 0, 1, 0], 0)), arr(~U32, K.Kernel.from_list(~U32, [1, 1, 0, 0], 0)))))
    IO.print(shu(K.Kernel.mask_not(4, 2n, arr(~U32, K.Kernel.from_list(~U32, [1, 0, 1, 1], 0)))))
    IO.print(foldu(K.Kernel.popcount(5, arr(~U32, K.Kernel.from_list(~U32, [1, 0, 1, 1, 0], 0)))))
    IO.print(Bool.show(K.Kernel.all_eq(~U32, ~(x => y => U32.is_eq(x, y)), 3, arr(~U32, K.Kernel.from_list(~U32, [1, 2, 3], 0)), arr(~U32, K.Kernel.from_list(~U32, [1, 2, 3], 0)))))
    IO.print(Bool.show(K.Kernel.all_eq(~U32, ~(x => y => U32.is_eq(x, y)), 3, arr(~U32, K.Kernel.from_list(~U32, [1, 2, 3], 0)), arr(~U32, K.Kernel.from_list(~U32, [1, 2, 4], 0)))))
    IO.print(Bool.show(K.Kernel.all_eq(~U32, ~(x => y => U32.is_eq(x, y)), 2, arr(~U32, K.Kernel.from_list(~U32, [1, 2, 3], 0)), arr(~U32, K.Kernel.from_list(~U32, [1, 2, 4], 0)))))
    IO.print(Bool.show(K.Kernel.all_eq(~String, ~eqs, 2, arr(~String, K.Kernel.from_list(~String, ["a", "b"], "")), arr(~String, K.Kernel.from_list(~String, ["a", "b"], "")))))
    IO.print(Nat.show(K.Kernel.fork_depth()))
#|0 0 1 3 10 11
#|3 [ann, bob, cy, ]
#|5 [1.5, 2.5, 3.5, 4.5, 5.5, 0, 0, 0]
#|0 [0]
#|[2, 4, 6, 0]
#|[11, 22, 33, 0]
#|[1, 0, 0, 0]
#|15
#|7
#|3 kept; slots: [5, 3, 9, 0, 0, 0, 0, 0]
#|[2, 3] mask [0, 1, 1, 0]
#|[40, 10, 30, 20] perm [3, 0, 2, 1]
#|[6, 12, 3, 0]
#|[2, 3, 1, 0]
#|[0, 1, 2, 3, 4, 0, 0, 0]
#|[10, 11, 12, 0]
#|[1.5, 1.5]
#|[7, 8, 9]
#|[]
#|[1, 0, 0, 1]
#|[1, 1, 1, 0]
#|[0, 1, 0, 0]
#|3
#|True
#|False
#|True
#|True
#|0
