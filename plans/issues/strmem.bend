# The heap cost of a String per character (Base only).
#   bend strmem.bend -o strmem
#   /usr/bin/time -l ./strmem 20 0     # 2^20 empty strings in a list (the list's own cost)
#   /usr/bin/time -l ./strmem 20 16    # 2^20 strings of 16 characters, all alive at once
# (peak(16) - peak(0)) / (2^20 * 16) is the cost of one character. Each string is built fresh
# (its first character depends on its index), so nothing is shared.
import Base

# a fresh string of k characters, the first one 'a' + (i mod 26)
def str.go(+k: Nat, +i: U32, acc: String) -> String:
  match k:
    case 0n:
      acc
    case 1n+p:
      str.go(p, i, SCon{Chr{U32.add(97, U32.mod(U32.add(i, U32.from_nat(p)), 26))}, acc})

def strs(+n: Nat, +k: Nat, acc: List<&1, String>) -> List<&1, String>:
  match n:
    case 0n:
      acc
    case 1n+p:
      strs(p, k, str.go(k, U32.from_nat(p), SNil{}) <> acc)

# every character counted once all strings exist (the list is consumed)
def total(xs: List<&1, String>, +s: Nat) -> Nat:
  match xs:
    case Nil{}:
      s
    case x <> t:
      total(t, Nat.add(s, String.length(x)))

def nat(m: Maybe<&2, Nat>, +d: Nat) -> Nat:
  match m:
    case None{}:
      d
    case Some{v}:
      v

def args2(xs: List<&1, String>) -> Nat & Nat:
  match xs:
    case _ <> d <> k <> t:
      (nat(Nat.read(d), 20n), nat(Nat.read(k), 16n))
    case _:
      (20n, 16n)

def run(r: Nat & Nat) -> IO(Unit):
  (+d, +k) = r
  IO.print(Nat.show(total(strs(U32.to_nat(U32.shln(1, d)), k, Nil{}), 0n)))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    run(args2(args))
