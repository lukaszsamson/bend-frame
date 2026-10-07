# p10: sort by key as argsort + gather. Keys come out of the array as a
# list of (key, index) pairs (Data), Base's List.sort (a stable merge sort)
# orders them, and a loop writes the permutation into an Array<U32>;
# gather then builds the sorted F32 column through Array.get/Array.set,
# with every (array, element) pair taken apart in a helper's parameter.
#   ~/.bend/bin/bend probes/p10_argsort_gather.bend
import Base

# a Data pair (a tuple A & B is a Type and cannot live in a List<&2, ..>)
type KI is Data:
  KI{key: F32, idx: U32}

# pairs (key, i) for i in [0, n), newest first, by a fuel loop that hands
# the array back (matching ALeaf/ANode would consume it)
def keyed.go(n: Nat, +i: U32, acc: List<&2, KI>, r: Array<F32> & F32) -> Array<F32> & List<&2, KI>:
  match n:
    case 0n:
      (a, x) = r
      (a, acc)
    case 1n+p:
      (a, x) = r
      +j = U32.inc(i)
      keyed.go(p, j, KI{x, i} <> acc, Array.get(F32, a, j))

def keyed(+n: U32, a: Array<F32>) -> Array<F32> & List<&2, KI>:
  keyed.go(U32.to_nat(n), 0, Nil{}, Array.get(F32, a, 0))

def le(p: KI, q: KI) -> Bool:
  match p q:
    case KI{x, i} KI{y, j}:
      F32.is_le(x, y)

# perm[j] = i for the j-th pair
def perm.go(ps: List<&2, KI>, +j: U32, perm: Array<U32>) -> Array<U32>:
  match ps:
    case Nil{}:
      perm
    case KI{k, i} <> rest:
      perm.go(rest, U32.inc(j), Array.set(U32, perm, j, i))

# out[j] = src[perm[j]]: fuel n. A pair returned by a call can only be
# taken apart as a PARAMETER (never by a let on the call), and a helper may
# not call a def declared below it, so: (1) `put` does one read+write and
# answers both arrays as a pair; (2) the loop receives the previous step's
# results as pair parameters and makes every call in tail position (Base's
# Array.map.go idiom). State threads through parameters.
def put.k(out: Array<F32>, +j: U32, r: Array<F32> & F32) -> Array<F32> & Array<F32>:
  (src, x) = r
  (src, Array.set(F32, out, j, x))

def put(src: Array<F32>, out: Array<F32>, +i: U32, +j: U32) -> Array<F32> & Array<F32>:
  put.k(out, j, Array.get(F32, src, i))

def gather.go(n: Nat, +j: U32, so: Array<F32> & Array<F32>, r: Array<U32> & U32) -> Array<F32>:
  match n:
    case 0n:
      (src, out) = so
      out
    case 1n+p:
      (src, out) = so
      (perm, i) = r
      +j2 = U32.inc(j)
      gather.go(p, j2, put(src, out, i, j), Array.get(U32, perm, j2))

# sort a column: keys out, sort the pairs, permutation in, gather
def sort_col.k(+n: U32, r: Array<F32> & List<&2, KI>) -> Array<F32>:
  (src, ks) = r
  perm = perm.go(List.sort(~KI, ~le, ks), 0, Array.new(U32, 2n, 0))
  gather.go(U32.to_nat(n), 0, (src, Array.new(F32, 2n, 0.0)), Array.get(U32, perm, 0))

def sort_col(+n: U32, src: Array<F32>) -> Array<F32>:
  sort_col.k(n, keyed(n, src))

def main() -> IO(Unit):
  do IO<Unit>:
    src : Array<F32> = Array.set(F32, Array.set(F32, Array.set(F32, [9.0 : F32*4n], 0, 3.5), 1, 1.0), 3, 2.0)
    IO.print(List.show(~&1, ~F32, ~(x => F32.show(x)), Array.to_list(~F32, sort_col(4, src))))

#|[1, 2, 3.5, 9]
