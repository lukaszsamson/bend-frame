import Base
import ./../../src/kernels.bend as K

def flat(+d: Nat, a: Array<U32>) -> Array<U32>:
  K.Kernel.map(~U32, ~U32, ~(x => U32.inc(x)), U32.shln(1, d), d, a, 0)

def par(k: Nat, +d: Nat, a: Array<U32>) -> Array<U32>:
  match k a:
    case 0n a2:
      flat(d, a2)
    case 1n+p ALeaf{x}:
      ALeaf{U32.inc(x)}
    case 1n++p ANode{xs, ys}:
      l r = par(p, Nat.sub(d, 1n), xs) par(p, Nat.sub(d, 1n), ys)
      ANode{l, r}

def loop(n: Nat, +k: Nat, a: Array<U32>) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+p:
      loop(p, k, par(k, 20n, a))

def blockloop(n: Nat, +d: Nat, a: Array<U32>) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+p:
      blockloop(p, d, flat(d, a))

def pipeline(k: Nat, +d: Nat, a: Array<U32>) -> Array<U32>:
  match k a:
    case 0n a2:
      blockloop(128n, d, a2)
    case 1n+p ALeaf{x}:
      ALeaf{U32.add(x, 128)}
    case 1n++p ANode{xs, ys}:
      l r = pipeline(p, Nat.sub(d, 1n), xs) pipeline(p, Nat.sub(d, 1n), ys)
      ANode{l, r}

def execute(mode: String, a: Array<U32>) -> Array<U32>:
  match mode:
    case "pipeline":
      pipeline(6n, 20n, a)
    case "flat":
      loop(128n, 0n, a)
    case _:
      loop(128n, 6n, a)

def finish(r: Array<U32> & U32) -> String:
  (a, x) = r
  U32.show(x) ++ " cells_ok=" ++ Bool.show(K.Kernel.all_eq(~U32, ~(u => v => U32.is_eq(u, v)), 1048576, a, K.Kernel.iota_from(1048576, 20n, 128)))

def timed(+mode: String, a: Array<U32>) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    out : Array<U32> <- IO.pure(Array<U32>, execute(mode, a))
    t1 : Nat <- IO.now()
    IO.print(mode ++ " ms=" ++ Nat.show(Nat.sub(t1, t0)))
    IO.print("sum=" ++ finish(K.Kernel.fold(~U32, ~U32, ~(a => b => U32.add(a,b)), 1048576, out, 0)))

def go(args: List<String>) -> IO(Unit):
  match args:
    case exe <> mode <> Nil{}:
      timed(mode, K.Kernel.iota(1048576, 20n))
    case _:
      IO.print("usage: maps flat|par|pipeline")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
