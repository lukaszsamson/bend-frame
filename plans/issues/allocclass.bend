# Freed heap memory is reusable only by blocks of the same size class (Base only).
#   bend allocclass.bend -o allocclass
#   /usr/bin/time -l ./allocclass small   # 4096 arrays of 2^12 U32 alive at once (64 MB), then freed
#   /usr/bin/time -l ./allocclass big     # one array of 2^24 U32 (64 MB)
#   /usr/bin/time -l ./allocclass both    # small, freed, then big: peak ~128 MB, not ~64 MB
#   /usr/bin/time -l ./allocclass same    # small, freed, then small again: peak ~64 MB (same class reused)
#   /usr/bin/time -l ./allocclass rev     # big, freed, then small: peak ~128 MB (a big free block is not split)
# Each phase prints a checksum, so nothing is dead code.
import Base

# sum of a[0..n), a consumed
def sum.go(n: Nat, +i: U32, +s: U32, r: Array<U32> & U32) -> U32:
  match n:
    case 0n:
      (a, x) = r
      s
    case 1n+p:
      (a, +x) = r
      +j = U32.inc(i)
      sum.go(p, j, U32.add(s, x), Array.get(U32, a, j))

def sum(+d: Nat, a: Array<U32>) -> U32:
  sum.go(U32.to_nat(U32.shln(1, d)), 0, 0, Array.get(U32, a, 0))

# k arrays of 2^d words, all alive at once
def many(+k: Nat, +d: Nat, acc: List<&1, Array<U32>>) -> List<&1, Array<U32>>:
  match k:
    case 0n:
      acc
    case 1n+p:
      many(p, d, Array.new(U32, d, U32.from_nat(p)) <> acc)

def sums(+d: Nat, xs: List<&1, Array<U32>>, +s: U32) -> U32:
  match xs:
    case Nil{}:
      s
    case a <> t:
      sums(d, t, U32.add(s, sum(d, a)))

def small() -> U32:
  sums(12n, many(4096n, 12n, Nil{}), 0)

def big() -> U32:
  sum(24n, Array.new(U32, 24n, 1))

def show(+x: U32) -> IO(Unit):
  IO.print(U32.show(x))

def run(+is_small: Bool, +is_big: Bool, +is_same: Bool, +is_rev: Bool) -> IO(Unit):
  match is_small is_big is_same is_rev:
    case True{} False{} False{} False{}:
      show(small())
    case False{} True{} False{} False{}:
      show(big())
    case False{} False{} True{} False{}:
      do IO<Unit>:
        show(small())
        show(small())
    case False{} False{} False{} True{}:
      do IO<Unit>:
        show(big())
        show(small())
    case _ _ _ _:
      do IO<Unit>:
        show(small())
        show(big())

def go(+m: String) -> IO(Unit):
  run(String.eq(m, "small"), String.eq(m, "big"), String.eq(m, "same"), String.eq(m, "rev"))

def arg(xs: List<&1, String>) -> String:
  match xs:
    case Nil{}:
      "both"
    case h <> Nil{}:
      "both"
    case h <> a <> t:
      a

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(arg(args))
