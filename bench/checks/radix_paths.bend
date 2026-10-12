# NATIVE check (make radix-check; the JS interpreter cannot build 2^15-slot arrays in reasonable time, so
# this is not under tests/). Radix.sort's two paths agree (src/radix.bend): inputs of at most 2^14 slots sort with 8-bit digits
# (Radix.s8, the 1k-control fix of GATES_V02.md G3), bigger ones with 16-bit digits (Radix.run).
# The same words are sorted twice. Side A is the 8-bit path: Radix.sort at the input's own depth when
# that is <= 14 (n <= 16384), and for n > 16384 (depth 15, where Radix.sort itself takes the 16-bit
# path) Radix.s8 called directly with every byte marked as varying. Side B is the 16-bit path:
# Radix.sort in a 2^15-slot copy (the path is chosen by the depth, and every n here is <= 2^15).
# Sizes: 1 2 7 300 1000, the dispatch boundary 16383 16384 (depth 14, 8-bit in production) 16385
# 32768 (depth 15, 16-bit in production), and the empty input n = 0 (answered as 3 ones: nothing to
# disagree about). Each line checks, over the first n rows:
#   eq      the two answers are the same (words and rows), slot by slot
#   sorted  the words are non-decreasing
#   stable  equal words keep their rows in increasing order (the rows start as 0..n-1)
# so the expected value of every flag is 1, derived from what a stable sort must answer.
# Shapes (word of row i): 0 i*2654435761 (distinct, every byte varies); 1 (i mod 7)*2654435761
# (duplicates); 2 i (already sorted: no pass runs); 3 n - i (reversed); 4 (i mod 13) << 24 (only
# the top byte varies); 5 ((i*37) mod 251) << 8 | (i mod 3) << 16 (two middle bytes); 6 5
# (constant); 7 i mod 256 (only the low byte).
import Base
import ./../../src/kernels.bend as K
import ./../../src/radix.bend as RD

def word(+k: U32, +n: U32, +i: U32) -> U32:
  match k:
    case 0:
      U32.mul(i, 2654435761)
    case 1:
      U32.mul(U32.mod(i, 7), 2654435761)
    case 2:
      i
    case 3:
      U32.sub(n, i)
    case 4:
      U32.shln(U32.mod(i, 13), 24n)
    case 5:
      U32.or(U32.shln(U32.mod(U32.mul(i, 37), 251), 8n), U32.shln(U32.mod(i, 3), 16n))
    case 6:
      5
    case 7:
      U32.mod(i, 256)
    case _:
      U32.mod(U32.mul(i, 7919), 1000)

def gen(c: Nat, +k: U32, +n: U32, +i: U32, a: Array<U32>) -> Array<U32>:
  match c:
    case 0n:
      a
    case 1n+p:
      gen(p, k, n, U32.inc(i), Array.set(U32, a, i, word(k, n, i)))

# (eq, sorted, stable) folded over rows i < n, answered as the bits eq | sorted << 1 | stable << 2: a = small path, b = big path
def chk(c: Nat, +i: U32, +pw: U32, +pp: U32, +eq: U32, +so: U32, +st: U32, ra: Array<U32> & U32, rap: Array<U32> & U32, rb: Array<U32> & U32, rbp: Array<U32> & U32) -> U32:
  match c:
    case 0n:
      U32.or(eq, U32.or(U32.shln(so, 1n), U32.shln(st, 2n)))
    case 1n+p:
      (a, +w) = ra
      (ap, +r) = rap
      (b, +w2) = rb
      (bp, +r2) = rbp
      +j = U32.inc(i)
      +same = Bool.and(U32.is_eq(w, w2), U32.is_eq(r, r2))
      +inc = Bool.or(U32.is_zero(i), U32.is_le(pw, w))
      +stab = Bool.or(Bool.or(U32.is_zero(i), U32.is_ne(pw, w)), U32.is_lt(pp, r))
      chk(p, j, w, r, U32.and(eq, Bool.to_u32(same)), U32.and(so, Bool.to_u32(inc)), U32.and(st, Bool.to_u32(stab)), Array.get(U32, a, j), Array.get(U32, ap, j), Array.get(U32, b, j), Array.get(U32, bp, j))

def show(+k: U32, +n: U32, +r: U32) -> String:
  "s" ++ U32.show(k) ++ " n=" ++ U32.show(n) ++ " eq=" ++ U32.show(U32.and(r, 1)) ++ " sorted=" ++ U32.show(U32.and(U32.shrn(r, 1n), 1)) ++ " stable=" ++ U32.show(U32.shrn(r, 2n))

def cmp(+k: U32, +n: U32, sa: Array<U32> & Array<U32>, sb: Array<U32> & Array<U32>) -> String:
  (aw, ap) = sa
  (bw, bp) = sb
  show(k, n, chk(U32.to_nat(n), 0, 0, 0, 1, 1, 1, Array.get(U32, aw, 0), Array.get(U32, ap, 0), Array.get(U32, bw, 0), Array.get(U32, bp, 0)))

# side A: the 8-bit path (Radix.sort at depth d <= 14, else Radix.s8 forced at depth d with all four bytes varying)
def side_a.go(sm: Bool, +n: U32, +d: Nat, ws: Array<U32>, pm: Array<U32>) -> Array<U32> & Array<U32>:
  match sm:
    case True{}:
      RD.Radix.sort(n, d, (ws, pm))
    case False{}:
      RD.Radix.s8(n, d, 4294967295, ws, pm)

def side_a(+k: U32, +n: U32, +d: Nat) -> Array<U32> & Array<U32>:
  side_a.go(Nat.is_le(d, 14n), n, d, gen(U32.to_nat(n), k, n, 0, Array.new(U32, d, 0)), K.Kernel.iota(n, d))

def one(+k: U32, +n: U32) -> String:
  +d = K.Kernel.depth_for(n)
  cmp(k, n, side_a(k, n, d), RD.Radix.sort(n, 15n, (gen(U32.to_nat(n), k, n, 0, Array.new(U32, 15n, 0)), K.Kernel.iota(n, 15n))))

def sizes(+k: U32) -> String:
  one(k, 0) ++ "\n" ++ one(k, 1) ++ "\n" ++ one(k, 2) ++ "\n" ++ one(k, 7) ++ "\n" ++ one(k, 300) ++ "\n" ++ one(k, 1000) ++ "\n" ++ one(k, 16383) ++ "\n" ++ one(k, 16384) ++ "\n" ++ one(k, 16385) ++ "\n" ++ one(k, 32768)

def main() -> IO(Unit):
  IO.print(sizes(0) ++ "\n" ++ sizes(1) ++ "\n" ++ sizes(2) ++ "\n" ++ sizes(3) ++ "\n" ++ sizes(4) ++ "\n" ++ sizes(5) ++ "\n" ++ sizes(6) ++ "\n" ++ sizes(7) ++ "\n" ++ sizes(8))
