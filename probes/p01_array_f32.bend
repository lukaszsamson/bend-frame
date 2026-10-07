# p01: Array<F32> basics -- new, get, set, size, and a balanced parallel
# reduction by matching ALeaf/ANode on a CONCRETE element type.
#   ~/.bend/bin/bend probes/p01_array_f32.bend
import Base

# a 2^d array filled by index: a[i] = f(i), built by structural recursion on
# the tree (no fuel), base index carried down
def F32s.iota(d: Nat, +base: U32) -> Array<F32>:
  match d:
    case 0n:
      ALeaf{U32.to_f32(base)}
    case 1n++p:
      +h = U32.shln(1, p)
      a b = F32s.iota(p, base) F32s.iota(p, U32.add(base, h))
      ANode{a, b}

# balanced fork-join sum: one parallel let per node
def F32s.sum(a: Array<F32>) -> F32:
  match a:
    case ALeaf{x}:
      x
    case ANode{xs, ys}:
      l r = F32s.sum(xs) F32s.sum(ys)
      F32.add(l, r)

# get/set through Base on a non-U32 element type
def probe.get(r: Array<F32> & F32) -> String:
  (a, x) = r
  F32.show(x) ++ " " ++ F32.show(F32s.sum(a))

def main() -> IO(Unit):
  do IO<Unit>:
    a : Array<F32> = F32s.iota(3n, 0)
    a2 : Array<F32> = Array.set(F32, a, 5, 100.5)
    IO.print(probe.get(Array.get(F32, a2, 5)))

#|100.5 123.5
