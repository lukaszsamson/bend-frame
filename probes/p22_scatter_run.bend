# p22: the group_by scatter kernel at runtime: acc[g[i]] = f(acc[g[i]], v[i]).
# Three groups over six rows: sums per group and counts per group.
#   ~/.bend/bin/bend probes/p22_scatter_run.bend
import Base

def Kernel.scatter.put(~T: Data, ~A: Data, ~f: A -> T -> A, +g: U32, x: T, r: Array<A> & A) -> Array<A>:
  (acc, old) = r
  Array.set(A, acc, g, f(old, x))

def Kernel.scatter.go(~T: Data, ~A: Data, ~f: A -> T -> A, n: Nat, +i: U32, acc: Array<A>, rg: Array<U32> & U32, rv: Array<T> & T) -> Array<A>:
  match n:
    case 0n:
      acc
    case 1n+p:
      (gs, +g) = rg
      (vs, x) = rv
      +j = U32.inc(i)
      Kernel.scatter.go(~T, ~A, ~f, p, j, Kernel.scatter.put(~T, ~A, ~f, g, x, Array.get(A, acc, g)), Array.get(U32, gs, j), Array.get(T, vs, j))

def Kernel.scatter(~T: Data, ~A: Data, ~f: A -> T -> A, +n: U32, gids: Array<U32>, vals: Array<T>, acc: Array<A>) -> Array<A>:
  Kernel.scatter.go(~T, ~A, ~f, U32.to_nat(n), 0, acc, Array.get(U32, gids, 0), Array.get(T, vals, 0))

def fill.go(~T: Data, xs: List<&2, T>, +i: U32, a: Array<T>) -> Array<T>:
  match xs:
    case Nil{}:
      a
    case h <> t:
      fill.go(~T, t, U32.inc(i), Array.set(T, a, i, h))

def count(acc: U32, x: F32) -> U32:
  U32.inc(acc)

def main() -> IO(Unit):
  do IO<Unit>:
    gids : Array<U32> = fill.go(~U32, [0, 1, 2, 1, 0, 1], 0, [0 : U32*8n])
    vals : Array<F32> = fill.go(~F32, [1.0, 2.0, 3.0, 4.0, 5.0, 6.0], 0, [0.0 : F32*8n])
    sums : Array<F32> = Kernel.scatter(~F32, ~F32, ~F32.add, 6, gids, vals, [0.0 : F32*4n])
    IO.print(List.show(~&1, ~F32, ~(x => F32.show(x)), Array.to_list(~F32, sums)))
    gids2 : Array<U32> = fill.go(~U32, [0, 1, 2, 1, 0, 1], 0, [0 : U32*8n])
    vals2 : Array<F32> = fill.go(~F32, [1.0, 2.0, 3.0, 4.0, 5.0, 6.0], 0, [0.0 : F32*8n])
    counts : Array<U32> = Kernel.scatter(~F32, ~U32, ~count, 6, gids2, vals2, [0 : U32*4n])
    IO.print(List.show(~&1, ~U32, ~(x => U32.show(x)), Array.to_list(~U32, counts)))

#|[6, 12, 3, 0]
#|[2, 3, 1, 0]
