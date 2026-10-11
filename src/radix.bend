# src/radix.bend -- the stable LSD radix sort over (word, row) pairs (v0.2 T3.2) and its read-pass
# state WS. Moved out of src/sort.bend by W2.3 (byte-identical definitions) so that src/ranks.bend
# (the rank stage, which sorts entry keys with Radix.sort) can be imported by sort.bend, eval.bend
# and groupby.bend without an import cycle. Depends on Base only.
#
# Users: sort.bend (the key passes build WS with WS.new / WS.put and finish with Radix.core),
# groupby.bend (rank codes, medians, Radix.pre.go), eval.bend (n_unique over words, median),
# ranks.bend (the radix refinement rounds).
#
# Idioms (DESIGN.md section 9): helpers above callers; Nat fuel first; pairs taken apart in the next
# helper's parameter.
import Base

# ---- LSD radix sort over (word, row) pairs (v0.2 T3.2) -------------------------------------
#
# Two 16-bit digits. ONE read pass computes everything the passes need: the bits that vary
# (OR of the words xor AND of the words), whether the words are already non-decreasing, and
# BOTH digit histograms (one 2^17-slot array: the low digit's counts at [0, 2^16), the high
# digit's at [2^16, 2^17)). Sorted words need no permutation change (a stable sort of a
# non-decreasing sequence is the identity), so the passes are skipped; otherwise one counting
# pass per varying digit, ping-ponging between the input pair and ONE scratch pair allocated
# once per sort (the second pass writes back into the input pair, which the first pass has
# read in full). The result is the unique stable order, as before.

def Radix.digit(+x: U32, +sh: Nat, +mk: U32) -> U32:
  U32.and(U32.shrn(x, sh), mk)

def Radix.inc(+g: U32, r: Array<U32> & U32) -> Array<U32>:
  (h, c) = r
  Array.set(U32, h, g, U32.inc(c))

# h[low digit]++ and h[2^16 + high digit]++
def Radix.inc2(+x: U32, h: Array<U32>) -> Array<U32>:
  +g0 = U32.and(x, 65535)
  +g1 = U32.or(U32.shrn(x, 16n), 65536)
  Radix.inc(g1, Array.get(U32, Radix.inc(g0, Array.get(U32, h, g0)), g1))

# exclusive prefix sums in place
def Radix.pre.go(n: Nat, +i: U32, +s: U32, r: Array<U32> & U32) -> Array<U32>:
  match n:
    case 0n:
      (h, c) = r
      h
    case 1n+p:
      (h, +c) = r
      +j = U32.inc(i)
      Radix.pre.go(p, j, U32.add(s, c), Array.get(U32, Array.set(U32, h, i, s), j))

# the read pass's state: the words (written for the key kernels, read for Radix.sort), the
# histograms, the previous word, OR and AND of the words so far, and "non-decreasing so far"
type WS is Type:
  WS{ws: Array<U32>, h: Array<U32>, prev: U32, vor: U32, vand: U32, ok: Bool}

def WS.new(+d: Nat) -> WS:
  WS{Array.new(U32, d, 0), Array.new(U32, 17n, 0), 0, 0, 4294967295, True{}}

# word w is row j of the words: written, counted, folded into vary / sortedness
def WS.put(+j: U32, +w: U32, st: WS) -> WS:
  match st:
    case WS{ws, h, +prev, +vor, +vand, ok}:
      WS{Array.set(U32, ws, j, w), Radix.inc2(w, h), w, U32.or(vor, w), U32.and(vand, w), Bool.and(ok, U32.is_le(prev, w))}

# Radix.sort's read pass over words already in ws: counted, folded into vary / sortedness
def Radix.scan.go(n: Nat, +i: U32, h: Array<U32>, +prev: U32, +vor: U32, +vand: U32, ok: Bool, r: Array<U32> & U32) -> WS:
  match n:
    case 0n:
      (ws, x) = r
      WS{ws, h, prev, vor, vand, ok}
    case 1n+p:
      (ws, +x) = r
      +j = U32.inc(i)
      Radix.scan.go(p, j, Radix.inc2(x, h), x, U32.or(vor, x), U32.and(vand, x), Bool.and(ok, U32.is_le(prev, x)), Array.get(U32, ws, j))

# the scatter pass's result: the histograms, the source pair (read in full, now dead) and the
# destination pair (the words and rows in the new order)
type RSc is Type:
  RSc{h: Array<U32>, sw: Array<U32>, sp: Array<U32>, dw: Array<U32>, dp: Array<U32>}

def Radix.sc.put(+x: U32, +p: U32, +g: U32, dw: Array<U32>, dp: Array<U32>, r: Array<U32> & U32) -> Array<U32> & Array<U32> & Array<U32>:
  (h, +pos) = r
  (Array.set(U32, h, g, U32.inc(pos)), Array.set(U32, dw, pos, x), Array.set(U32, dp, pos, p))

# stable scatter of (sw[i], sp[i]) to slot h[base + digit]++ (h holds exclusive prefix sums)
def Radix.sc.go(n: Nat, +i: U32, +sh: Nat, +base: U32, st: Array<U32> & Array<U32> & Array<U32>, rw: Array<U32> & U32, rp: Array<U32> & U32) -> RSc:
  match n:
    case 0n:
      (h, dw, dp) = st
      (sw, x) = rw
      (sp, p) = rp
      RSc{h, sw, sp, dw, dp}
    case 1n+q:
      (h, dw, dp) = st
      (sw, +x) = rw
      (sp, +p) = rp
      +g = U32.or(Radix.digit(x, sh, 65535), base)
      +j = U32.inc(i)
      Radix.sc.go(q, j, sh, base, Radix.sc.put(x, p, g, dw, dp, Array.get(U32, h, g)), Array.get(U32, sw, j), Array.get(U32, sp, j))

# one counting pass on the digit at bit sh (histogram region base): (sw, sp) -> (dw, dp)
def Radix.pass2(+n: U32, +sh: Nat, +base: U32, h: Array<U32>, sw: Array<U32>, sp: Array<U32>, dw: Array<U32>, dp: Array<U32>) -> RSc:
  Radix.sc.go(U32.to_nat(n), 0, sh, base, (Radix.pre.go(65536n, base, 0, Array.get(U32, h, base)), dw, dp), Array.get(U32, sw, 0), Array.get(U32, sp, 0))

def Radix.out(r: RSc) -> Array<U32> & Array<U32>:
  match r:
    case RSc{h, sw, sp, dw, dp}:
      (dw, dp)

# the high pass after the low one: back into the (dead) input pair
def Radix.back(+n: U32, r: RSc) -> Array<U32> & Array<U32>:
  match r:
    case RSc{h, sw, sp, dw, dp}:
      Radix.out(Radix.pass2(n, 16n, 65536, h, dw, dp, sw, sp))

# by which digits vary (lo, hi); not sorted, so at least one does
def Radix.run(lo: Bool, hi: Bool, +n: U32, +d: Nat, h: Array<U32>, ws: Array<U32>, perm: Array<U32>) -> Array<U32> & Array<U32>:
  match lo hi:
    case True{} True{}:
      Radix.back(n, Radix.pass2(n, 0n, 0, h, ws, perm, Array.new(U32, d, 0), Array.new(U32, d, 0)))
    case True{} False{}:
      Radix.out(Radix.pass2(n, 0n, 0, h, ws, perm, Array.new(U32, d, 0), Array.new(U32, d, 0)))
    case False{} True{}:
      Radix.out(Radix.pass2(n, 16n, 65536, h, ws, perm, Array.new(U32, d, 0), Array.new(U32, d, 0)))
    case False{} False{}:
      (ws, perm)

def Radix.core.b(ok: Bool, +n: U32, +d: Nat, +vary: U32, h: Array<U32>, ws: Array<U32>, perm: Array<U32>) -> Array<U32> & Array<U32>:
  match ok:
    case True{}:
      (ws, perm)
    case False{}:
      Radix.run(U32.is_ne(U32.and(vary, 65535), 0), U32.is_ne(U32.shrn(vary, 16n), 0), n, d, h, ws, perm)

# stable sort of (ws[i], perm[i]), i < n, by ws, given the read pass's state over ws
def Radix.core(+n: U32, +d: Nat, perm: Array<U32>, st: WS) -> Array<U32> & Array<U32>:
  match st:
    case WS{ws, h, +prev, +vor, +vand, ok}:
      Radix.core.b(ok, n, d, U32.xor(vor, vand), h, ws, perm)

# stable sort of the pairs (ws[i], perm[i]), i < n <= 2^d, by ws (unsigned); answers the
# sorted (ws, perm) (rows past n unspecified). Already non-decreasing words come back as they
# are; otherwise one pass per 16-bit digit that varies.
def Radix.sort(+n: U32, +d: Nat, st: Array<U32> & Array<U32>) -> Array<U32> & Array<U32>:
  (ws, perm) = st
  Radix.core(n, d, perm, Radix.scan.go(U32.to_nat(n), 0, Array.new(U32, 17n, 0), 0, 0, 4294967295, True{}, Array.get(U32, ws, 0)))
