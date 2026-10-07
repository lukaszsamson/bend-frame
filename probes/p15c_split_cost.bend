# p15c: what does splitting an Array (matching ANode) cost, and when does a
# fork pay? Over one 2^22 Array<F32>:
#   split K   : match ANode K levels deep, rebuild the spine, no work
#   set loop  : write every slot in place (flat)
#   heavy flat: y = sqrt(x) * sin(x) summed, one flat loop
#   heavy fork: the same, forked 6 levels then flat per block
#   ~/.bend/bin/bend probes/p15c_split_cost.bend -o /tmp/p15c && /tmp/p15c --threads 1 --gpu off && /tmp/p15c --gpu off
import Base

def D() -> Nat:
  22n

def iota(d: Nat, +base: U32) -> Array<F32>:
  match d:
    case 0n:
      ALeaf{U32.to_f32(U32.and(base, 1023))}
    case 1n++p:
      +h = U32.shln(1, p)
      a b = iota(p, base) iota(p, U32.add(base, h))
      ANode{a, b}

def split(k: Nat, a: Array<F32>) -> Array<F32>:
  match k a:
    case _ ALeaf{x}:
      ALeaf{x}
    case 0n ANode{xs, ys}:
      ANode{xs, ys}
    case 1n++p ANode{xs, ys}:
      ANode{split(p, xs), split(p, ys)}

def split_par(k: Nat, a: Array<F32>) -> Array<F32>:
  match k a:
    case _ ALeaf{x}:
      ALeaf{x}
    case 0n ANode{xs, ys}:
      ANode{xs, ys}
    case 1n++p ANode{xs, ys}:
      l r = split_par(p, xs) split_par(p, ys)
      ANode{l, r}

def setloop(n: Nat, +i: U32, a: Array<F32>) -> Array<F32>:
  match n:
    case 0n:
      a
    case 1n+p:
      setloop(p, U32.inc(i), Array.set(F32, a, i, 1.5))

def heavy(+x: F32) -> F32:
  F32.mul(F32.sqrt(x), F32.sin(x))

def hflat.go(n: Nat, +i: U32, +acc: F32, r: Array<F32> & F32) -> Array<F32> & F32:
  match n:
    case 0n:
      (a, x) = r
      (a, acc)
    case 1n+p:
      (a, x) = r
      +j = U32.inc(i)
      hflat.go(p, j, F32.add(acc, heavy(x)), Array.get(F32, a, j))

def hflat(+n: U32, a: Array<F32>) -> Array<F32> & F32:
  hflat.go(U32.to_nat(U32.sub(n, 1)), 0, 0.0, Array.get(F32, a, 0))

def join(r1: Array<F32> & F32, r2: Array<F32> & F32) -> Array<F32> & F32:
  (a, x) = r1
  (b, y) = r2
  (ANode{a, b}, F32.add(x, y))

def hfork(k: Nat, +blk: U32, a: Array<F32>) -> Array<F32> & F32:
  match k a:
    case _ ALeaf{+x}:
      (ALeaf{x}, x)
    case 0n ANode{xs, ys}:
      hflat(blk, ANode{xs, ys})
    case 1n++p ANode{xs, ys}:
      l r = hfork(p, blk, xs) hfork(p, blk, ys)
      join(l, r)

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
    a0 : Array<F32> = iota(D(), 0)
    a1 : Array<F32> <- time(~(a => (split(1n, a), 0.0)), "split K=1", a0)
    a2 : Array<F32> <- time(~(a => (split(4n, a), 0.0)), "split K=4", a1)
    a3 : Array<F32> <- time(~(a => (split(10n, a), 0.0)), "split K=10", a2)
    a4 : Array<F32> <- time(~(a => (split_par(10n, a), 0.0)), "split_par K=10", a3)
    a5 : Array<F32> <- time(~(a => (setloop(U32.to_nat(U32.shln(1, D())), 0, a), 0.0)), "set loop", a4)
    a6 : Array<F32> <- time(~(a => hflat(U32.shln(1, D()), a)), "heavy flat", a5)
    a7 : Array<F32> <- time(~(a => hfork(6n, U32.shln(1, Nat.sub(D(), 6n)), a)), "heavy fork K=6", a6)
    a8 : Array<F32> <- time(~(a => hfork(10n, U32.shln(1, Nat.sub(D(), 10n)), a)), "heavy fork K=10", a7)
    a9 : Array<F32> <- time(~(a => hflat(U32.shln(1, D()), a)), "heavy flat again", a8)
    return Unit{}
