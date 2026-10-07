# p15: which kernel SHAPE is fast? Over one 2^22 Array<F32> built once:
#   flat   : one sequential fuel loop with Array.get (returns the array)
#   tree   : structural ALeaf/ANode recursion, a parallel let per node
#   forked : parallel lets for K levels, then a flat Array.get loop per block
#   map    : out[i] = 2 * a[i] as a structural rebuild vs forked + Array.set
# Run natively with 1 thread and with all threads; compare.
#   ~/.bend/bin/bend probes/p15_kernel_shapes.bend -o /tmp/p15 && /tmp/p15 --threads 1 --gpu off && /tmp/p15 --gpu off && /tmp/p15
import Base

def D() -> Nat:
  22n

def K() -> Nat:
  10n

def iota(d: Nat, +base: U32) -> Array<F32>:
  match d:
    case 0n:
      ALeaf{U32.to_f32(U32.and(base, 1023))}
    case 1n++p:
      +h = U32.shln(1, p)
      a b = iota(p, base) iota(p, U32.add(base, h))
      ANode{a, b}

# flat: a fuel loop; the (array, element) pair of the NEXT read rides as the
# parameter r (Base's Array.map.go idiom)
def flat.go(n: Nat, +i: U32, +acc: F32, r: Array<F32> & F32) -> Array<F32> & F32:
  match n:
    case 0n:
      (a, x) = r
      (a, acc)
    case 1n+p:
      (a, x) = r
      +j = U32.inc(i)
      flat.go(p, j, F32.add(acc, x), Array.get(F32, a, j))

def flat(+n: U32, a: Array<F32>) -> Array<F32> & F32:
  flat.go(U32.to_nat(U32.sub(n, 1)), 0, 0.0, Array.get(F32, a, 0))

# tree: structural, one parallel let per node, rebuilds the spine
def tree.join(r1: Array<F32> & F32, r2: Array<F32> & F32) -> Array<F32> & F32:
  (a, x) = r1
  (b, y) = r2
  (ANode{a, b}, F32.add(x, y))

def tree(a: Array<F32>) -> Array<F32> & F32:
  match a:
    case ALeaf{+x}:
      (ALeaf{x}, x)
    case ANode{xs, ys}:
      l r = tree(xs) tree(ys)
      tree.join(l, r)

# forked: K levels of forks, then flat over each block of 2^(D-K)
def forked(k: Nat, +blk: U32, a: Array<F32>) -> Array<F32> & F32:
  match k a:
    case _ ALeaf{+x}:
      (ALeaf{x}, x)
    case 0n ANode{xs, ys}:
      flat(blk, ANode{xs, ys})
    case 1n++p ANode{xs, ys}:
      l r = forked(p, blk, xs) forked(p, blk, ys)
      tree.join(l, r)

def map_tree.join(l: Array<F32> & Array<F32>, r: Array<F32> & Array<F32>) -> Array<F32> & Array<F32>:
  (a, b) = l
  (c, d) = r
  (ANode{a, c}, ANode{b, d})

# map, structural: a new array, parallel let per node
def map_tree(a: Array<F32>) -> Array<F32> & Array<F32>:
  match a:
    case ALeaf{+x}:
      (ALeaf{x}, ALeaf{F32.mul(x, 2.0)})
    case ANode{xs, ys}:
      l r = map_tree(xs) map_tree(ys)
      map_tree.join(l, r)

# map, forked + flat Array.set into a preallocated block
def map_flat.go(n: Nat, +i: U32, out: Array<F32>, r: Array<F32> & F32) -> Array<F32> & Array<F32>:
  match n:
    case 0n:
      (a, x) = r
      (a, Array.set(F32, out, i, F32.mul(x, 2.0)))
    case 1n+p:
      (a, x) = r
      +j = U32.inc(i)
      map_flat.go(p, j, Array.set(F32, out, i, F32.mul(x, 2.0)), Array.get(F32, a, j))

def map_forked(k: Nat, +blk: U32, +bd: Nat, a: Array<F32>) -> Array<F32> & Array<F32>:
  match k a:
    case _ ALeaf{+x}:
      (ALeaf{x}, ALeaf{F32.mul(x, 2.0)})
    case 0n ANode{xs, ys}:
      map_flat.go(U32.to_nat(U32.sub(blk, 1)), 0, Array.new(F32, bd, 0.0), Array.get(F32, ANode{xs, ys}, 0))
    case 1n++p ANode{xs, ys}:
      l r = map_forked(p, blk, bd, xs) map_forked(p, blk, bd, ys)
      map_tree.join(l, r)

def drop_sum(r: Array<F32> & F32) -> F32:
  (a, x) = r
  x

def drop_map(r: Array<F32> & Array<F32>) -> F32:
  (a, b) = r
  drop_sum(flat(U32.shln(1, D()), b))

def time(~f: Unit -> F32, label: String) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    v : F32 = f(Unit{})
    t1 : Nat <- IO.now()
    IO.print(label ++ ": " ++ F32.show(v) ++ " in " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms")

def main() -> IO(Unit):
  do IO<Unit>:
    n : U32 <- IO.thread_count()
    IO.print("threads: " ++ U32.show(n))
    time(~(u => drop_sum(flat(U32.shln(1, D()), iota(D(), 0)))), "build+flat")
    time(~(u => drop_sum(tree(iota(D(), 0)))), "build+tree")
    time(~(u => drop_sum(forked(K(), U32.shln(1, Nat.sub(D(), K())), iota(D(), 0)))), "build+forked")
    time(~(u => drop_sum(forked!(K(), U32.shln(1, Nat.sub(D(), K())), iota(D(), 0)))), "build+forked!")
    time(~(u => drop_map(map_tree(iota(D(), 0)))), "build+map_tree+flat")
    time(~(u => drop_map(map_forked(K(), U32.shln(1, Nat.sub(D(), K())), Nat.sub(D(), K()), iota(D(), 0)))), "build+map_forked+flat")
    time(~(u => F32.add(0.0, 0.0)), "nothing")
