# p17: filter as branch-free compaction. A loop cannot `match` on a
# predicate it just computed, so the kept rows are written unconditionally
# at slot k and k advances by the mask bit (0 or 1). Slots past the final k
# are garbage the column's logical length hides. Also: the mask as an
# Array<U32> of 0/1 words and its popcount (the output length).
#   ~/.bend/bin/bend probes/p17_filter_compact.bend
import Base

def gt2.join(l: Array<F32> & Array<U32>, r: Array<F32> & Array<U32>) -> Array<F32> & Array<U32>:
  (a, m) = l
  (b, n) = r
  (ANode{a, b}, ANode{m, n})

# mask[i] = a[i] > 2.0, as 0/1 words: structural map, parallel per node
def gt2(a: Array<F32>) -> Array<F32> & Array<U32>:
  match a:
    case ALeaf{+x}:
      (ALeaf{x}, ALeaf{Bool.to_u32(F32.is_gt(x, 2.0))})
    case ANode{xs, ys}:
      l r = gt2(xs) gt2(ys)
      gt2.join(l, r)

# out[k] = a[i]; k += mask[i]. State rides as pair parameters: ao = (a, out),
# mi = (mask, mask[i]) is the NEXT step's read.
def put.k(out: Array<F32>, +k: U32, r: Array<F32> & F32) -> Array<F32> & Array<F32>:
  (a, x) = r
  (a, Array.set(F32, out, k, x))

def compact.go(n: Nat, +i: U32, +k: U32, ao: Array<F32> & Array<F32>, mi: Array<U32> & U32) -> Array<F32> & U32:
  match n:
    case 0n:
      (a, out) = ao
      (out, k)
    case 1n+p:
      (a, out) = ao
      (mask, bit) = mi
      +j = U32.inc(i)
      compact.go(p, j, U32.add(k, bit), put.k(out, k, Array.get(F32, a, i)), Array.get(U32, mask, j))

def compact(+n: U32, +d: Nat, a: Array<F32>, mask: Array<U32>) -> Array<F32> & U32:
  compact.go(U32.to_nat(n), 0, 0, (a, Array.new(F32, d, 0.0)), Array.get(U32, mask, 0))

def filter_gt2.k(+n: U32, +d: Nat, r: Array<F32> & Array<U32>) -> Array<F32> & U32:
  (a, mask) = r
  compact(n, d, a, mask)

def filter_gt2(+n: U32, +d: Nat, a: Array<F32>) -> Array<F32> & U32:
  filter_gt2.k(n, d, gt2(a))

def show(r: Array<F32> & U32) -> String:
  (out, k) = r
  U32.show(k) ++ " kept; slots: " ++ List.show(~&1, ~F32, ~(x => F32.show(x)), Array.to_list(~F32, out))

def main() -> IO(Unit):
  do IO<Unit>:
    a : Array<F32> = Array.set(F32, Array.set(F32, Array.set(F32, [1.0 : F32*8n], 1, 5.0), 4, 3.0), 7, 9.0)
    IO.print(show(filter_gt2(8, 3n, a)))

#|3 kept; slots: [5, 3, 9, 0, 0, 0, 0, 0]
