# p07: does a balanced fork-join over an Array<F32> actually run in parallel
# on the CPU, and is the GPU (`!`) worth it? Builds 2^N floats, sums them
# with one parallel let per node down to blocks of 2^B leaves, then flat
# loops. Times with IO.now.
#   ~/.bend/bin/bend probes/p07_parallel_bench.bend -o /tmp/p07 && /tmp/p07 --threads 1 && /tmp/p07 --threads 8
import Base

def N() -> Nat:
  22n

def iota(d: Nat, +base: U32) -> Array<F32>:
  match d:
    case 0n:
      ALeaf{U32.to_f32(U32.and(base, 1023))}
    case 1n++p:
      +h = U32.shln(1, p)
      a b = iota(p, base) iota(p, U32.add(base, h))
      ANode{a, b}

# sequential sum (structural, no fork)
def seq(a: Array<F32>) -> F32:
  match a:
    case ALeaf{x}:
      x
    case ANode{xs, ys}:
      F32.add(seq(xs), seq(ys))

# fork for k levels, then sequential
def par(k: Nat, a: Array<F32>) -> F32:
  match k a:
    case _ ALeaf{x}:
      x
    case 0n ANode{xs, ys}:
      F32.add(seq(xs), seq(ys))
    case 1n++p ANode{xs, ys}:
      l r = par(p, xs) par(p, ys)
      F32.add(l, r)

# the array is consumed by each sum, so each run rebuilds it (same cost
# for every variant: subtract build-only)
def build_only() -> F32:
  seq(iota(N(), 0))

def run_seq() -> F32:
  seq(iota(N(), 0))

def run_par() -> F32:
  par(12n, iota(N(), 0))

def run_gpu() -> F32:
  par!(12n, iota(N(), 0))

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
    time(~(u => run_seq()), "seq")
    time(~(u => run_par()), "par")
    time(~(u => run_gpu()), "gpu")
