# p15b: p15 with the build taken out of the clock. One 2^22 Array<F32> is
# built once in IO and threaded through each timed kernel, which hands it
# back. Kernels: flat (sequential Array.get loop), forked (K fork levels,
# then flat per block), forked! (same, on the GPU), map_forked (new array).
#   ~/.bend/bin/bend probes/p15b_kernel_only.bend -o /tmp/p15b && /tmp/p15b --threads 1 --gpu off && /tmp/p15b --gpu off && /tmp/p15b
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

def join(r1: Array<F32> & F32, r2: Array<F32> & F32) -> Array<F32> & F32:
  (a, x) = r1
  (b, y) = r2
  (ANode{a, b}, F32.add(x, y))

def forked(k: Nat, +blk: U32, a: Array<F32>) -> Array<F32> & F32:
  match k a:
    case _ ALeaf{+x}:
      (ALeaf{x}, x)
    case 0n ANode{xs, ys}:
      flat(blk, ANode{xs, ys})
    case 1n++p ANode{xs, ys}:
      l r = forked(p, blk, xs) forked(p, blk, ys)
      join(l, r)

def map_join(l: Array<F32> & Array<F32>, r: Array<F32> & Array<F32>) -> Array<F32> & Array<F32>:
  (a, b) = l
  (c, d) = r
  (ANode{a, c}, ANode{b, d})

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
      map_join(l, r)

# drop the mapped copy by a cheap walk-free consumer: sum its first slot
def drop_second.k(r: Array<F32> & F32) -> F32:
  (b, x) = r
  x

def drop_second(r: Array<F32> & Array<F32>) -> Array<F32> & F32:
  (a, b) = r
  (a, drop_second.k(Array.get(F32, b, 0)))

def report.k(label: String, t0: Nat, r: Array<F32> & F32) -> IO(Array<F32>):
  (a, v) = r
  do IO<Array<F32>>:
    t1 : Nat <- IO.now()
    IO.print(label ++ ": " ++ F32.show(v) ++ " in " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms")
    return a

def time(~f: Array<F32> -> Array<F32> & F32, label: String, a: Array<F32>) -> IO(Array<F32>):
  do IO<Array<F32>>:
    t0 : Nat <- IO.now()
    report.k(label, t0, f(a))

def main() -> IO(Unit):
  do IO<Unit>:
    n : U32 <- IO.thread_count()
    IO.print("threads: " ++ U32.show(n))
    t0 : Nat <- IO.now()
    a0 : Array<F32> = iota(D(), 0)
    a1 : Array<F32> <- time(~(a => flat(U32.shln(1, D()), a)), "build+flat", a0)
    a2 : Array<F32> <- time(~(a => flat(U32.shln(1, D()), a)), "flat", a1)
    a3 : Array<F32> <- time(~(a => forked(K(), U32.shln(1, Nat.sub(D(), K())), a)), "forked", a2)
    a4 : Array<F32> <- time(~(a => forked!(K(), U32.shln(1, Nat.sub(D(), K())), a)), "forked!", a3)
    a5 : Array<F32> <- time(~(a => drop_second(map_forked(K(), U32.shln(1, Nat.sub(D(), K())), Nat.sub(D(), K()), a))), "map_forked", a4)
    a6 : Array<F32> <- time(~(a => drop_second(map_forked!(K(), U32.shln(1, Nat.sub(D(), K())), Nat.sub(D(), K()), a))), "map_forked!", a5)
    a7 : Array<F32> <- time(~(a => flat(U32.shln(1, D()), a)), "flat again", a6)
    a8 : Array<F32> <- time(~(a => forked(6n, U32.shln(1, Nat.sub(D(), 6n)), a)), "forked K=6", a7)
    a9 : Array<F32> <- time(~(a => forked(14n, U32.shln(1, Nat.sub(D(), 14n)), a)), "forked K=14", a8)
    a10 : Array<F32> <- time(~(a => flat(1, a)), "touch", a9)
    return Unit{}
