# The v0.1 string coding, kept as the REFERENCE of the W2 differential tests (v0.2 W2.3 deleted it
# from src/): the Base-Map first-appearance coder `Sort.str_codes` and its parallel-block variant
# `Sort.pcodes` / `Sort.str_codes_par` (from src/sort.bend at c79d5f5), the Map-ranked
# `Sort.str_words`, and `Dict.ranks` (from src/strs.bend at c79d5f5). Byte-identical definitions
# apart from module prefixes (ST.Dict, ST.SSlot). Imported as V1 by tests/hcode_diff.bend,
# tests/ranks_diff.bend, tests/sort_strcodes.bend and bench/w2/; tests/lib is not run by
# scripts/test.sh (no `#|` lines).
import Base
import ./../../src/kernels.bend as K
import ./../../src/strs.bend as ST

# string -> first-appearance code, and the next free code
type CS is Data:
  CS{m: Map<&2, U32>, next: U32}

def Sort.none() -> U32:
  4294967295

# ---- word maps: out[i] = f(a[i]) xor flip ----------------------------------------------

def Sort.xmap.go(~T: Data, ~f: T -> U32, n: Nat, +i: U32, +flip: U32, out: Array<U32>, r: Array<T> & T) -> Array<U32>:
  match n:
    case 0n:
      out
    case 1n+p:
      (a, x) = r
      +j = U32.inc(i)
      Sort.xmap.go(~T, ~f, p, j, flip, Array.set(U32, out, i, U32.xor(f(x), flip)), Array.get(T, a, j))

def Sort.xmap(~T: Data, ~f: T -> U32, +n: U32, +d: Nat, +flip: U32, a: Array<T>) -> Array<U32>:
  Sort.xmap.go(~T, ~f, U32.to_nat(n), 0, flip, Array.new(U32, d, 0), Array.get(T, a, 0))

# ---- string codes ------------------------------------------------------------------------

def Sort.snd0(r: Array<U32> & Array<U32>) -> Array<U32>:
  (a, b) = r
  a

def Sort.code.put(isnew: Bool, out: Array<U32>, +i: U32, +next: U32, s: String, m: Map<&2, U32>, +g: U32) -> Array<U32> & CS:
  match isnew:
    case True{}:
      (Array.set(U32, out, i, next), CS{Map.set(&2, U32, m, s, next), U32.inc(next)})
    case False{}:
      (Array.set(U32, out, i, g), CS{m, next})

def Sort.code.look(out: Array<U32>, +i: U32, +next: U32, s: String, r: Map<&2, U32> & U32) -> Array<U32> & CS:
  (m, +g) = r
  Sort.code.put(U32.is_eq(g, Sort.none()), out, i, next, s, m, g)

def Sort.code.step(+i: U32, +s: String, st: Array<U32> & CS) -> Array<U32> & CS:
  (out, cs) = st
  match cs:
    case CS{m, next}:
      Sort.code.look(out, i, next, s, Map.get(U32, Sort.none(), m, s))

def Sort.codes.go(n: Nat, +i: U32, st: Array<U32> & CS, r: Array<String> & String) -> Array<String> & Array<U32> & CS:
  match n:
    case 0n:
      (out, cs) = st
      (a, s) = r
      (a, out, cs)
    case 1n+p:
      (a, +s) = r
      +j = U32.inc(i)
      Sort.codes.go(p, j, Sort.code.step(i, s, st), Array.get(String, a, j))

# out[i] = the first-appearance code of a[i] (codes start at `first`); answers
# the strings back, the codes and the final map state (its `next` = first +
# distinct count)
def Sort.str_codes(+n: U32, +d: Nat, +first: U32, a: Array<String>) -> Array<String> & Array<U32> & CS:
  Sort.codes.go(U32.to_nat(n), 0, (Array.new(U32, d, 0), CS{Map.new(&2, U32), first}), Array.get(String, a, 0))

# ---- parallel string codes ----------------------------------------------------------------
# The array is split along its ANode spine `k` levels deep; each block is coded
# with its own Map in a parallel let, then the right block's distinct strings
# are looked up / appended in the left block's Map IN THE RIGHT BLOCK'S
# first-appearance order, so the merged codes are exactly the sequential ones
# (global first-appearance order). Only the distinct strings are re-coded.

# keys[code] = string
def Sort.kbc.put(keys: Array<String>, kv: Sigma<&2, &2, String, _ => U32>) -> Array<String>:
  (k, v) = kv
  Array.set(String, keys, v, k)

def Sort.kbc(xs: List<&2, Sigma<&2, &2, String, _ => U32>>, keys: Array<String>) -> Array<String>:
  match xs:
    case Nil{}:
      keys
    case kv <> t:
      Sort.kbc(t, Sort.kbc.put(keys, kv))

def Sort.pmerge.c(+nr: U32, +dr: Nat, xa: Array<String>, ya: Array<String>, lc: Array<U32>, rc: Array<U32>, r: Array<String> & Array<U32> & CS) -> Array<String> & Array<U32> & CS:
  (keys, remap, cs) = r
  (ANode{xa, ya}, ANode{lc, Sort.snd0(K.Kernel.gather(~U32, nr, dr, remap, rc, 0))}, cs)

def Sort.pmerge.b(+nr: U32, +dr: Nat, xa: Array<String>, ya: Array<String>, lc: Array<U32>, lcs: CS, rc: Array<U32>, rcs: CS) -> Array<String> & Array<U32> & CS:
  match rcs:
    case CS{rm, +rk}:
      +kd = K.Kernel.depth_for(rk)
      Sort.pmerge.c(nr, dr, xa, ya, lc, rc, Sort.codes.go(U32.to_nat(rk), 0, (Array.new(U32, kd, 0), lcs), Array.get(String, Sort.kbc(Map.to_list(&2, U32, rm), Array.new(String, kd, "")), 0)))

def Sort.pmerge(+nr: U32, +dr: Nat, l: Array<String> & Array<U32> & CS, r: Array<String> & Array<U32> & CS) -> Array<String> & Array<U32> & CS:
  (xa, lc, lcs) = l
  (ya, rc, rcs) = r
  Sort.pmerge.b(nr, dr, xa, ya, lc, lcs, rc, rcs)

def Sort.pcodes(k: Nat, +n: U32, +d: Nat, +first: U32, a: Array<String>) -> Array<String> & Array<U32> & CS:
  match k a:
    case 0n a2:
      Sort.str_codes(n, d, first, a2)
    case 1n+p ALeaf{x}:
      Sort.str_codes(n, d, first, ALeaf{x})
    case 1n++p ANode{xs, ys}:
      +dr = Nat.sub(d, 1n)
      +nl = U32.min(n, U32.shln(1, dr))
      +nr = U32.sub(n, nl)
      l r = Sort.pcodes(p, nl, dr, first, xs) Sort.pcodes(p, nr, dr, 0, ys)
      Sort.pmerge(nr, dr, l, r)

# fork levels for string coding: 8 blocks from 2^16 rows on
def Sort.str_fork(+d: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_ge(d, 16n), 3n, 0n)

# Sort.str_codes, in parallel blocks for long columns (same result)
def Sort.str_codes_par(+n: U32, +d: Nat, +first: U32, a: Array<String>) -> Array<String> & Array<U32> & CS:
  Sort.pcodes(Sort.str_fork(d), n, d, first, a)

# rank[code] = position of the code's string in String order
def Sort.ranks.put(+pos: U32, rk: Array<U32>, kv: Sigma<&2, &2, String, _ => U32>) -> Array<U32>:
  (k, v) = kv
  Array.set(U32, rk, v, pos)

def Sort.ranks.go(xs: List<&2, Sigma<&2, &2, String, _ => U32>>, +pos: U32, rk: Array<U32>) -> Array<U32>:
  match xs:
    case Nil{}:
      rk
    case kv <> t:
      Sort.ranks.go(t, U32.inc(pos), Sort.ranks.put(pos, rk, kv))

def Sort.str_words.c(+n: U32, +d: Nat, +flip: U32, r: Array<U32> & Array<U32>) -> Array<U32>:
  (w, codes) = r
  Sort.xmap(~U32, ~(x => x), n, d, flip, w)

def Sort.str_words.b(+n: U32, +d: Nat, +flip: U32, r: Array<String> & Array<U32> & CS) -> Array<U32>:
  (strs, codes, cs) = r
  match cs:
    case CS{m, +k}:
      Sort.str_words.c(n, d, flip, K.Kernel.gather(~U32, n, d, Sort.ranks.go(Map.to_list(&2, U32, m), 0, Array.new(U32, K.Kernel.depth_for(k), 0)), codes, 0))

# order-preserving words of strings: rank among the distinct strings
def Sort.str_words(+n: U32, +d: Nat, +flip: U32, a: Array<String>) -> Array<U32>:
  Sort.str_words.b(n, d, flip, Sort.str_codes_par(n, d, 0, a))


# rank[c] = the position of entry c among the entries in String order (Base Map's crit-bit
# order: code points, a prefix first; Sort.str_words ranks Raw strings by the same Map)
def Dict.rk.ins(+c: U32, m: Map<&2, U32>, s: String) -> Map<&2, U32>:
  Map.set(&2, U32, m, s, c)

def Dict.rk.go(n: Nat, +c: U32, m: Map<&2, U32>, r: Array<String> & String) -> Array<String> & Map<&2, U32>:
  match n:
    case 0n:
      (strs, s) = r
      (strs, m)
    case 1n+p:
      (strs, s) = r
      +j = U32.inc(c)
      Dict.rk.go(p, j, Dict.rk.ins(c, m, s), Array.get(String, strs, j))

def Dict.rk.put(+pos: U32, rk: Array<U32>, kv: Sigma<&2, &2, String, _ => U32>) -> Array<U32>:
  (key, v) = kv
  Array.set(U32, rk, v, pos)

def Dict.rk.list(xs: List<&2, Sigma<&2, &2, String, _ => U32>>, +pos: U32, rk: Array<U32>) -> Array<U32>:
  match xs:
    case Nil{}:
      rk
    case kv <> t:
      Dict.rk.list(t, U32.inc(pos), Dict.rk.put(pos, rk, kv))

def Dict.rk.fin(+k: U32, +dd: Nat, +b: Nat, slots: Array<ST.SSlot>, +tag: U32, r: Array<String> & Map<&2, U32>) -> ST.Dict & Array<U32>:
  (strs, m) = r
  (ST.Dict{k, dd, strs, b, slots, tag}, Dict.rk.list(Map.to_list(&2, U32, m), 0, Array.new(U32, dd, 0)))

def Dict.ranks(d: ST.Dict) -> ST.Dict & Array<U32>:
  match d:
    case ST.Dict{+k, +dd, strs, +b, slots, +tag}:
      Dict.rk.fin(k, dd, b, slots, tag, Dict.rk.go(U32.to_nat(k), 0, Map.new(&2, U32), Array.get(String, strs, 0)))
