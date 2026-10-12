# Minimal repro: a non-flat call before a parallel let serialises the subtree.
# Same leaves, same per-leaf work (a flat tail loop), two fork shapes:
#   mode 1 "split": the forking def splits its list (a non-tail recursive helper) in the branch arguments
#   mode 2 "tree" : the list is turned into a balanced tree first (sequential), the forking def only matches
#   mode 0        : build the input only (baseline)
# Run: bend forkshape.bend -o forkshape && time ./forkshape --threads N MODE
import Base

# per-leaf work: a flat tail loop (an LCG), ~2^24 steps
def work(n: Nat, +x: U32) -> U32:
  match n:
    case 0n:
      x
    case 1n+p:
      work(p, U32.add(U32.mul(x, 1664525), 1013904223))

def wk(+x: U32) -> U32:
  work(U32.to_nat(16777216), x)

def iota.go(n: Nat, +i: U32, acc: List<&1, U32>) -> List<&1, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      iota.go(p, U32.inc(i), i <> acc)

def split.c(+x: U32, r: List<&1, U32> & List<&1, U32>) -> List<&1, U32> & List<&1, U32>:
  (a, b) = r
  (x <> a, b)

# the first k elements and the rest: a NON-TAIL recursion (not flat)
def split(k: Nat, xs: List<&1, U32>) -> List<&1, U32> & List<&1, U32>:
  match k xs:
    case 0n _:
      (Nil{}, xs)
    case 1n+p Nil{}:
      (Nil{}, Nil{})
    case 1n+p x <> rest:
      split.c(x, split(p, rest))

def head(xs: List<&1, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case x <> rest:
      x

def half(+p: Nat) -> Nat:
  U32.to_nat(U32.shln(1, p))

# mode 1: r holds this node's two halves (2^d elements each); the split of each child happens in the
# branch arguments of the parallel let
def ps(d: Nat, r: List<&1, U32> & List<&1, U32>) -> U32:
  match d:
    case 0n:
      (l, rr) = r
      a b = wk(head(l)) wk(head(rr))
      U32.add(a, b)
    case 1n++p:
      (l, rr) = r
      a b = ps(p, split(half(p), l)) ps(p, split(half(p), rr))
      U32.add(a, b)

type T is Type:
  L{x: U32}
  N{l: T, r: T}

# mode 2: build the balanced tree sequentially (the same splits), then fork by match only
# r: this node's two halves (2^d elements each)
def build(d: Nat, r: List<&1, U32> & List<&1, U32>) -> T:
  match d:
    case 0n:
      (a, b) = r
      N{L{head(a)}, L{head(b)}}
    case 1n++p:
      (a, b) = r
      N{build(p, split(half(p), a)), build(p, split(half(p), b))}

def pt(t: T) -> U32:
  match t:
    case L{x}:
      wk(x)
    case N{l, r}:
      a b = pt(l) pt(r)
      U32.add(a, b)

def run(+m: U32, xs: List<&1, U32>) -> U32:
  match m:
    case 1:
      ps(7n, split(128n, xs))
    case 2:
      pt(build(7n, split(128n, xs)))
    case _:
      head(xs)

def num(m: Maybe<&2, U32>) -> U32:
  match m:
    case None{}:
      0
    case Some{x}:
      x

def mode.b(xs: List<&1, String>) -> U32:
  match xs:
    case Nil{}:
      0
    case m <> rest:
      num(U32.read(m))

# IO.args starts with the program name
def mode(xs: List<&1, String>) -> U32:
  match xs:
    case Nil{}:
      0
    case p <> rest:
      mode.b(rest)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args
    IO.print(U32.show(run(mode(args), iota.go(256n, 0, Nil{}))))
