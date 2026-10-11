# bench/w5/scale/probe.bend -- the scaling probes of the G2 diagnosis (DESIGN.md 16.10): one balanced
# binary fork tree over an owned tree of U32 leaves (2^24 rows in total), the per-leaf work varied to
# separate the hypotheses of the ~2x ceiling seen by T5.3 (bench/w5/t53x.bend):
#
#   mode  leaf work                                           allocation inside the fork   drop inside
#   0     fold (U32 sum), the leaf handed back                none                          no
#   1     fold, the leaf dropped after the fold               none                          yes (input)
#   2     Kernel.map into a FRESH leaf, the input dropped     one block per leaf            yes (input)
#   3     Kernel.map_pb (borrow): fresh output, input back    one block per leaf            no
#   4     in-place map over the owned leaf (Array.set)        none                          no
#   5     fresh map whose OUTPUT is dropped at once (count)   one block per leaf            yes (output)
#   6     fold, the fork tree replaced by a sequential walk   none                          no  (the no-fork control)
#
# Timing styles (the "style" argument):
#   io    each rep is its own IO.pure (a cold entry into the runtime's scheduler: pool wake + grow + drain);
#         between reps `gap` ms of sequential busy work on the main thread (gap 0: none), so the pool's
#         workers either stay spinning (gap 0) or sleep (gap >= 1)
#   pure  all reps in ONE pure recursion (T5.2's shape: every rep's join forks the next rep, so the reps are
#         iterations of one scheduler run; nothing sleeps between them)
#
#   bend bench/w5/scale/probe.bend -o build/scale/probe
#   build/scale/probe [--threads N] <mode> <depth> <reps> <style io|pure> <gap ms>
# depth 8 / 10 / 12 = 256 / 1024 / 4096 leaves of 2^16 / 2^14 / 2^12 rows (2^24 rows, 64 MB, in total). Prints one JSON-ish line per
# process: per-rep ms (io) or the total (pure), the checksum, and the leaf count.
import Base
import ./../../../src/kernels.bend as K
import ./../../../src/chunks.bend as CH

type T is Type:
  L{n: U32, d: Nat, a: Array<U32>}
  N{l: T, r: T}

def total() -> Nat:
  24n

def empty() -> T:
  L{0, 0n, Array.new(U32, 0n, 0)}

# ---- build: a balanced tree of 2^depth leaves, leaf i holding (i * 2^ld + k) * 37 mod 1000 at row k ----

def leaf(+ld: Nat, +n: U32, +off: U32) -> T:
  L{n, ld, K.Kernel.map(~U32, ~U32, ~(x => U32.mod(U32.mul(x, 37), 1000)), n, ld, K.Kernel.iota_from(n, ld, off), 0)}

def build(depth: Nat, +ld: Nat, +n: U32, +off: U32) -> T:
  match depth:
    case 0n:
      leaf(ld, n, off)
    case 1n+ +p:
      +half = U32.shln(1, Nat.add(p, ld))
      l r = build(p, ld, n, off) build(p, ld, n, U32.add(off, half))
      N{l, r}

# ---- the per-leaf operations ----

def fold.k(r: Array<U32> & U32, +n: U32, +d: Nat) -> T & U32:
  (a, +s) = r
  (L{n, d, a}, s)

# mode 0: fold, the leaf handed back
def m0.j(x: T & U32, y: T & U32) -> T & U32:
  (l, +a) = x
  (r, +b) = y
  (N{l, r}, U32.add(a, b))

def m0(t: T) -> T & U32:
  match t:
    case L{+n, +d, a}:
      fold.k(K.Kernel.fold(~U32, ~U32, ~(acc => x => U32.add(acc, x)), n, a, 0), n, d)
    case N{l, r}:
      x y = m0(l) m0(r)
      m0.j(x, y)

def drop.k(r: Array<U32> & U32) -> U32:
  (a, +s) = r
  s

# mode 1: fold, the leaf dropped inside the fork (the array is dead after the fold)
def m1(t: T) -> U32:
  match t:
    case L{+n, d, a}:
      drop.k(K.Kernel.fold(~U32, ~U32, ~(acc => x => U32.add(acc, x)), n, a, 0))
    case N{l, r}:
      x y = m1(l) m1(r)
      U32.add(x, y)

# mode 2: a fresh output leaf per leaf (Kernel.map consumes the input: dropped inside)
def m2(t: T) -> T:
  match t:
    case L{+n, +d, a}:
      L{n, d, K.Kernel.map(~U32, ~U32, ~(x => U32.add(x, 1)), n, d, a, 0)}
    case N{l, r}:
      x y = m2(l) m2(r)
      N{x, y}

# mode 3: a fresh output per leaf, the input handed back (borrow: nothing dropped inside)
def m3.k(r: Array<U32> & Array<U32>, +n: U32, +d: Nat) -> T & T:
  (out, a) = r
  (L{n, d, out}, L{n, d, a})

def m3.j(x: T & T, y: T & T) -> T & T:
  (ol, il) = x
  (or, ir) = y
  (N{ol, or}, N{il, ir})

def m3(t: T) -> T & T:
  match t:
    case L{+n, +d, a}:
      m3.k(K.Kernel.map_pb(~U32, ~U32, ~U32, ~(p => x => U32.add(x, p)), n, d, a, 1, 0), n, d)
    case N{l, r}:
      x y = m3(l) m3(r)
      m3.j(x, y)

# mode 4: in place over the owned leaf: a[i] = a[i] + 1 (Array.set on an owned array writes in place)
def inpl.go(n: Nat, +i: U32, r: Array<U32> & U32) -> Array<U32>:
  match n:
    case 0n:
      (a, x) = r
      a
    case 1n+p:
      (a, x) = r
      +j = U32.inc(i)
      inpl.go(p, j, Array.get(U32, Array.set(U32, a, i, U32.add(x, 1)), j))

def inpl(+n: U32, a: Array<U32>) -> Array<U32>:
  inpl.go(U32.to_nat(n), 0, Array.get(U32, a, 0))

def m4(t: T) -> T:
  match t:
    case L{+n, +d, a}:
      L{n, d, inpl(n, a)}
    case N{l, r}:
      x y = m4(l) m4(r)
      N{x, y}

# mode 5: a fresh output per leaf, consumed at once by a fold (both input and output die inside)
def m5(t: T) -> U32:
  match t:
    case L{+n, +d, a}:
      drop.k(K.Kernel.fold(~U32, ~U32, ~(acc => x => U32.add(acc, x)), n, K.Kernel.map(~U32, ~U32, ~(x => U32.add(x, 1)), n, d, a, 0), 0))
    case N{l, r}:
      x y = m5(l) m5(r)
      U32.add(x, y)

# mode 6: mode 0 without the fork (the sequential control: the same leaves, the same loop)
def m6.j(x: T & U32, y: T & U32) -> T & U32:
  (l, +a) = x
  (r, +b) = y
  (N{l, r}, U32.add(a, b))

def m6(t: T) -> T & U32:
  match t:
    case L{+n, +d, a}:
      fold.k(K.Kernel.fold(~U32, ~U32, ~(acc => x => U32.add(acc, x)), n, a, 0), n, d)
    case N{l, r}:
      m6.j(m6(l), m6(r))

# mode 9: the fork tree with NO leaf work (the leaf answers its row count): the scheduling cost alone
def m9(t: T) -> T & U32:
  match t:
    case L{+n, +d, a}:
      (L{n, d, a}, n)
    case N{l, r}:
      x y = m9(l) m9(r)
      m0.j(x, y)

# mode 10: mode 0 with a FORK-FREE helper call in the argument of each branch (the shape of Lst.pmap.go's
# `Lst.split(..)` and the runner's `CX.cut(a)`): the helper is a task the grow phase refuses to run
def pass.go(n: Nat, t: T) -> T:
  match n:
    case 0n:
      t
    case 1n+p:
      pass.go(p, t)

def pass(t: T) -> T:
  pass.go(1n, t)

def m10(f: Nat, t: T) -> T & U32:
  match f t:
    case _ L{+n, +d, a}:
      fold.k(K.Kernel.fold(~U32, ~U32, ~(acc => x => U32.add(acc, x)), n, a, 0), n, d)
    case 0n N{l, r}:
      (N{l, r}, 0)
    case 1n+ +p N{l, r}:
      x y = m10(p, pass(l)) m10(p, pass(r))
      m0.j(x, y)

# mode 11: the leaves as a List, forked by CH.Lst.pmap (the T5.3 probe's shape), each leaf folded and
# handed back; the list is rebuilt into a tree afterwards (outside the fork, inside the clock: O(leaves))
def leaves.go(t: T, acc: List<&1, T>) -> List<&1, T>:
  match t:
    case L{n, d, a}:
      L{n, d, a} <> acc
    case N{l, r}:
      leaves.go(l, leaves.go(r, acc))

def m11.leaf(+u: U32, t: T) -> T & U32:
  match t:
    case L{+n, +d, a}:
      fold.k(K.Kernel.fold(~U32, ~U32, ~(acc => x => U32.add(acc, x)), n, a, 0), n, d)
    case N{l, r}:
      (N{l, r}, 0)

def m11.sum(rs: List<&1, T & U32>, +acc: U32, ts: List<&1, T>) -> List<&1, T> & U32:
  match rs:
    case Nil{}:
      (ts, acc)
    case r <> rest:
      (t, +s) = r
      m11.sum(rest, U32.add(acc, s), t <> ts)

# a balanced tree from a list of 2^k leaves (sequential): pairs folded level by level
def pairs(xs: List<&1, T>, acc: List<&1, T>) -> List<&1, T>:
  match xs:
    case Nil{}:
      acc
    case a <> rest:
      match rest:
        case Nil{}:
          a <> acc
        case b <> rest2:
          pairs(rest2, N{a, b} <> acc)

def tree.of(f: Nat, xs: List<&1, T>) -> T:
  match f xs:
    case _ Nil{}:
      empty()
    case 0n x <> rest:
      x
    case 1n+p x <> rest:
      match rest:
        case Nil{}:
          x
        case y <> more:
          tree.of(p, List.reverse(&1, T, pairs(x <> y <> more, Nil{})))

def m11.k(r: List<&1, T> & U32) -> T & U32:
  (ts, +s) = r
  (tree.of(32n, ts), s)

def m11(t: T) -> T & U32:
  m11.k(m11.sum(CH.Lst.pmap(~T, ~(T & U32), ~U32, ~(u => x => m11.leaf(u, x)), 0, leaves.go(t, Nil{})), 0, Nil{}))

# ---- a checksum of a tree (sequential, after the clock): the sum of the rows ----

def csum(t: T) -> T & U32:
  m6(t)

# ---- one rep: St{t, spare, acc} in and out. A mode that consumes its tree (1, 5) leaves `empty()` and the
# prep step (outside the clock in the io style) rebuilds it; mode 3 (borrow) puts the input into `spare`,
# which the prep step drops outside the clock. The pure style has no prep step: there the rebuild and the
# drop happen inside the recursion (documented in the summary; use modes 0 / 2 / 4 / 6 for it).

type St is Type:
  St{t: T, spare: T, acc: U32}

def rep.k0(r: T & U32, spare: T, +acc: U32) -> St:
  (t, +s) = r
  St{t, spare, U32.add(acc, s)}

def rep.k3(r: T & T, spare: T, +acc: U32) -> St:
  (out, inp) = r
  St{out, inp, acc}

def rebuild(+depth: Nat) -> T:
  build(depth, Nat.sub(total(), depth), U32.shln(1, Nat.sub(total(), depth)), 0)

def rep.m(+m: U32, t: T, spare: T, +acc: U32) -> St:
  match m:
    case 0:
      rep.k0(m0(t), spare, acc)
    case 1:
      St{empty(), spare, U32.add(acc, m1(t))}
    case 2:
      St{m2(t), spare, acc}
    case 3:
      rep.k3(m3(t), spare, acc)
    case 4:
      St{m4(t), spare, acc}
    case 5:
      St{empty(), spare, U32.add(acc, m5(t))}
    case 9:
      rep.k0(m9(t), spare, acc)
    case 10:
      rep.k0(m10(32n, t), spare, acc)
    case 11:
      rep.k0(m11(t), spare, acc)
    case _:
      rep.k0(m6(t), spare, acc)

def rep(+m: U32, st: St) -> St:
  match st:
    case St{t, spare, +acc}:
      rep.m(m, t, spare, acc)

# the prep step: rebuild a consumed tree, drop the spare (outside the clock)
def prep.t.k(+depth: Nat, z: Bool, t: T) -> T:
  match z:
    case True{}:
      rebuild(depth)
    case False{}:
      t

def prep.t(+depth: Nat, t: T) -> T:
  match t:
    case L{+n, d, a}:
      prep.t.k(depth, U32.is_eq(n, 0), L{n, d, a})
    case N{l, r}:
      N{l, r}

def prep(+depth: Nat, st: St) -> St:
  match st:
    case St{t, spare, +acc}:
      St{prep.t(depth, t), empty(), acc}

# the pure style: reps chained in one recursion (the rebuild of modes 1 / 5 inside)
def reps.pure(f: Nat, +m: U32, +depth: Nat, st: St) -> St:
  match f:
    case 0n:
      st
    case 1n+p:
      reps.pure(p, m, depth, rep(m, prep(depth, st)))

# a sequential busy loop of ~gap ms on the main thread (about 2^20 U32 adds per ms is far too many; the
# loop below is tuned by the caller: it does `k` iterations of a trivial fold)
def busy.go(f: Nat, +acc: U32) -> U32:
  match f:
    case 0n:
      acc
    case 1n+p:
      busy.go(p, U32.add(U32.mul(acc, 1664525), 1013904223))

def busy(gap: Nat) -> U32:
  busy.go(Nat.mul(gap, 3000000n), 1)

def fin.k(r: T & U32, +acc: U32) -> U32:
  (t, +s) = r
  U32.add(acc, s)

def fin(st: St) -> U32:
  match st:
    case St{t, spare, +acc}:
      fin.k(csum(t), acc)

def loop.io(left: Nat, +m: U32, +depth: Nat, +gap: Nat, st: St, +acc: String) -> IO(Unit):
  match left:
    case 0n:
      IO.print("{\"ms\": [" ++ acc ++ "0], \"check\": " ++ U32.show(fin(st)) ++ "}")
    case 1n+k:
      do IO<Unit>:
        s1 : St <- IO.pure(St, prep(depth, st))
        +g : U32 <- IO.pure(U32, busy(gap))
        +t0 : Nat <- IO.now()
        s2 : St <- IO.pure(St, rep(m, s1))
        +t1 : Nat <- IO.now()
        loop.io(k, m, depth, gap, s2, acc ++ Nat.show(Nat.add(Nat.sub(t1, t0), U32.to_nat(U32.and(g, 0)))) ++ ", ")

def loop.pure(reps: Nat, +m: U32, +depth: Nat, st: St) -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    s2 : St <- IO.pure(St, reps.pure(reps, m, depth, st))
    +t1 : Nat <- IO.now()
    IO.print("{\"total_ms\": " ++ Nat.show(Nat.sub(t1, t0)) ++ ", \"check\": " ++ U32.show(fin(s2)) ++ "}")

def start.k(pure: Bool, +m: U32, +depth: Nat, reps: Nat, gap: Nat, t: T) -> IO(Unit):
  match pure:
    case True{}:
      loop.pure(reps, m, depth, St{t, empty(), 0})
    case False{}:
      loop.io(reps, m, depth, gap, St{t, empty(), 0}, "")

def start(+m: U32, +depth: Nat, reps: Nat, +style: String, gap: Nat) -> IO(Unit):
  do IO<Unit>:
    t : T <- IO.pure(T, rebuild(depth))
    start.k(String.eq(style, "pure"), m, depth, reps, gap, t)

def nat(s: String, +z: Nat) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), z)

def go(args: List<String>) -> IO(Unit):
  match args:
    case exe <> mode <> depth <> reps <> style <> gap <> Nil{}:
      start(U32.from_nat(nat(mode, 0n)), nat(depth, 10n), nat(reps, 10n), style, nat(gap, 0n))
    case _:
      IO.print("usage: probe MODE DEPTH REPS io|pure GAP_MS")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
