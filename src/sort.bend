# src/sort.bend -- argsort, multi-key stable sort, Sort.frame. DESIGN.md 4.8.
#
# Algorithm (deviates from 4.8's List.sort chain, see DESIGN.md 14 M5): every
# key column becomes an Array<U32> of ORDER-PRESERVING sort words
#   u32: x   i32: x xor 2^31   bool: 0/1   f32: IEEE bits mapped to a total
#   order (negatives flipped, -0.0 = 0.0, every NaN = the largest word)
#   str: the rank of the string among the column's distinct strings (a Map
#   from string to first-appearance code; Map.to_list walks the crit-bit trie
#   in String.order, so the list position is the rank)
# `descending` xors the word with 2^32-1. Keys are then processed LAST to
# FIRST with a stable LSD radix sort (16-bit digits, a digit whose bits never
# vary in the column is skipped) over (word, row) pairs in the current order;
# a key with a validity mask gets one more stable 1-bit pass on its null flag
# (nulls first unless nulls_last). Stability of every pass makes the chain a
# lexicographic stable sort: ties keep input order. No comparison sort and no
# List on the hot path.
#
# The word/code helpers (Sort.words, Sort.str_codes, Radix.argsort) are also
# what src/groupby.bend uses to dictionary-encode group keys.
#
# Idioms (DESIGN.md section 9): helpers above callers; Nat fuel first; pairs
# taken apart in the next helper's parameter; templates ~T: Data.
import Base
import ./dtype.bend as D
import ./err.bend as E
import ./kernels.bend as K
import ./column.bend as C
import ./strs.bend as ST

type SortKey is Data:
  SortKey{name: String, descending: Bool, nulls_last: Bool}

# string -> first-appearance code, and the next free code
type CS is Data:
  CS{m: Map<&2, U32>, next: U32}

# the frame threaded through the key loop with the permutation so far
type SortSt is Type:
  SortSt{f: C.Frame, r: E.ResT(Array<U32>)}

# ---- constants / small helpers ---------------------------------------------------------

def Sort.none() -> U32:
  4294967295

def Sort.sign() -> U32:
  2147483648

# order-preserving word of an f32: NaN (any payload) is the largest word, -0.0 equals 0.0,
# negatives are bit-flipped, positives get the sign bit set. This is THE f32 relation of
# DESIGN.md 15.5.2, shared with comparisons, group_by, n_unique (K.Kernel.fword).
def Sort.fword(x: F32) -> U32:
  K.Kernel.fword(x)

def Sort.iword(x: U32) -> U32:
  U32.xor(x, 2147483648)

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

# order-preserving words of a Dictionary column (M4): the dictionary is ranked ONCE (its k
# entries through the same Map as Sort.str_words, so the order is the same), then each row's
# word is its code's rank (one gather)
def Sort.dict_words.b(+n: U32, +d: Nat, +flip: U32, codes: Array<U32>, r: ST.Dict & Array<U32>) -> Array<U32>:
  (dict, rk) = r
  Sort.xmap(~U32, ~(x => x), n, d, flip, Sort.snd0(K.Kernel.gather(~U32, n, d, rk, codes, 0)))

def Sort.str_words.st(+n: U32, +d: Nat, +flip: U32, x: ST.Strs) -> Array<U32>:
  match x:
    case ST.SRaw{a}:
      Sort.str_words(n, d, flip, a)
    case ST.SDict{codes, dict}:
      Sort.dict_words.b(n, d, flip, codes, ST.Dict.ranks(dict))

# ---- column -> sort words ----------------------------------------------------------------

def Sort.words.zm(r: Array<U32> & Array<U32>) -> Array<U32> & C.Valid:
  (w, m) = r
  (w, C.Mask{m})

# words with null rows forced to 0 (so nulls tie and keep their order)
def Sort.words.z(+n: U32, w: Array<U32>, v: C.Valid) -> Array<U32> & C.Valid:
  match v:
    case C.AllValid{}:
      (w, C.AllValid{})
    case C.Mask{m}:
      Sort.words.zm(K.Kernel.mask_data(~U32, n, w, m, 0))

# the column's order-preserving words (row order) and its validity; the column
# is consumed. `desc` flips every word.
def Sort.words.go(c: C.Column, +flip: U32) -> Array<U32> & C.Valid:
  match c:
    case C.CBool{+n, d, v, x}:
      Sort.words.z(n, Sort.xmap(~U32, ~(w => w), n, d, flip, x), v)
    case C.CU32{+n, d, v, x}:
      Sort.words.z(n, Sort.xmap(~U32, ~(w => w), n, d, flip, x), v)
    case C.CI32{+n, d, v, x}:
      Sort.words.z(n, Sort.xmap(~U32, ~(w => Sort.iword(w)), n, d, flip, x), v)
    case C.CF32{+n, d, v, x}:
      Sort.words.z(n, Sort.xmap(~F32, ~(w => Sort.fword(w)), n, d, flip, x), v)
    case C.CStr{+n, d, v, x}:
      Sort.words.z(n, Sort.str_words.st(n, d, flip, x), v)

def Sort.words(c: C.Column, desc: Bool) -> Array<U32> & C.Valid:
  Sort.words.go(c, Bool.pick(U32, desc, 4294967295, 0))

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

# ---- key words, fused with the read pass (v0.2 T3.2) ----------------------------------------
#
# The key column is BORROWED (Sort.split / Sort.unsplit put it back where it was): its buffers
# are read in place, never cloned (a Raw string key is the exception: its v0.1 coder consumes
# the strings, so it codes a clone). The words of the rows in the current order perm are built
# in ONE pass that also does the radix read pass: out[j] = f(src[perm[j]]) xor flip (0 for a
# null row). The first key (perm is the identity) reads src directly.

# rows perm[j], j < n: the words and the read-pass state; src and perm come back
def Sort.wg.put(~T: Data, ~f: T -> U32, +j: U32, +flip: U32, st: WS, r: Array<T> & T) -> Array<T> & WS:
  (src, x) = r
  (src, WS.put(j, U32.xor(f(x), flip), st))

def Sort.wg.go(~T: Data, ~f: T -> U32, n: Nat, +j: U32, +flip: U32, sw: Array<T> & WS, rp: Array<U32> & U32) -> Array<T> & Array<U32> & WS:
  match n:
    case 0n:
      (src, st) = sw
      (perm, i) = rp
      (src, perm, st)
    case 1n+p:
      (src, st) = sw
      (perm, +i) = rp
      +j2 = U32.inc(j)
      Sort.wg.go(~T, ~f, p, j2, flip, Sort.wg.put(~T, ~f, j, flip, st, Array.get(T, src, i)), Array.get(U32, perm, j2))

# rows j < n in order (the identity permutation): src comes back
def Sort.wm.go(~T: Data, ~f: T -> U32, n: Nat, +j: U32, +flip: U32, st: WS, r: Array<T> & T) -> Array<T> & WS:
  match n:
    case 0n:
      (src, x) = r
      (src, st)
    case 1n+p:
      (src, x) = r
      +j2 = U32.inc(j)
      Sort.wm.go(~T, ~f, p, j2, flip, WS.put(j, U32.xor(f(x), flip), st), Array.get(T, src, j2))

# rows perm[j] with a validity mask: a null row's word is 0 (nulls tie, keeping their order)
def Sort.wgm.put(~T: Data, ~f: T -> U32, +j: U32, +flip: U32, st: WS, r: Array<T> & T, rm: Array<U32> & U32) -> Array<T> & Array<U32> & WS:
  (src, x) = r
  (m, +b) = rm
  (src, m, WS.put(j, Bool.pick(U32, U32.is_ne(b, 0), U32.xor(f(x), flip), 0), st))

def Sort.wgm.go(~T: Data, ~f: T -> U32, n: Nat, +j: U32, +flip: U32, sw: Array<T> & Array<U32> & WS, rp: Array<U32> & U32) -> Array<T> & Array<U32> & Array<U32> & WS:
  match n:
    case 0n:
      (src, m, st) = sw
      (perm, i) = rp
      (src, m, perm, st)
    case 1n+p:
      (src, m, st) = sw
      (perm, +i) = rp
      +j2 = U32.inc(j)
      Sort.wgm.go(~T, ~f, p, j2, flip, Sort.wgm.put(~T, ~f, j, flip, st, Array.get(T, src, i), Array.get(U32, m, i)), Array.get(U32, perm, j2))

# a Dictionary key without nulls: out[j] = rk[codes[perm[j]]] xor flip (the code's rank), in
# the same pass; codes, rk and perm come back
def Sort.wgd.put2(+j: U32, +flip: U32, st: WS, codes: Array<U32>, r: Array<U32> & U32) -> Array<U32> & Array<U32> & WS:
  (rk, +w) = r
  (codes, rk, WS.put(j, U32.xor(w, flip), st))

def Sort.wgd.put(+j: U32, +flip: U32, st: WS, rk: Array<U32>, r: Array<U32> & U32) -> Array<U32> & Array<U32> & WS:
  (codes, +c) = r
  Sort.wgd.put2(j, flip, st, codes, Array.get(U32, rk, c))

def Sort.wgd.go(n: Nat, +j: U32, +flip: U32, sw: Array<U32> & Array<U32> & WS, rp: Array<U32> & U32) -> Array<U32> & Array<U32> & Array<U32> & WS:
  match n:
    case 0n:
      (codes, rk, st) = sw
      (perm, i) = rp
      (codes, rk, perm, st)
    case 1n+p:
      (codes, rk, st) = sw
      (perm, +i) = rp
      +j2 = U32.inc(j)
      Sort.wgd.go(p, j2, flip, Sort.wgd.put(j, flip, st, rk, Array.get(U32, codes, i)), Array.get(U32, perm, j2))

# ---- one key ------------------------------------------------------------------------------

def Sort.snd(st: Array<U32> & Array<U32>) -> Array<U32>:
  (a, b) = st
  b

# the null flags in the order perm, then a stable sort by them: nulls first -> null 0 /
# valid 1; nulls last -> 1 / 0 (bit 0 of the mask word, as v0.1's 1-bit pass read it)
def Sort.nulls.b(+n: U32, +d: Nat, r: Array<U32> & Array<U32> & WS) -> Array<U32> & Array<U32>:
  (m, perm, st) = r
  (m, Sort.snd(Radix.core(n, d, perm, st)))

def Sort.nulls(+n: U32, +d: Nat, +nl: Bool, m: Array<U32>, perm: Array<U32>) -> Array<U32> & Array<U32>:
  Sort.nulls.b(n, d, Sort.wg.go(~U32, ~(w => U32.and(w, 1)), U32.to_nat(n), 0, Bool.pick(U32, nl, 1, 0), (m, WS.new(d)), Array.get(U32, perm, 0)))

def Sort.av.b(r: Array<U32> & Array<U32>) -> C.Valid & Array<U32>:
  (m, perm) = r
  (C.Mask{m}, perm)

def Sort.mk.c(+n: U32, +d: Nat, +nl: Bool, m: Array<U32>, r: Array<U32> & Array<U32>) -> C.Valid & Array<U32>:
  (ws, perm) = r
  Sort.av.b(Sort.nulls(n, d, nl, m, perm))

def Sort.mk.b(~T: Data, +n: U32, +d: Nat, +nl: Bool, r: Array<T> & Array<U32> & Array<U32> & WS) -> Array<T> & (C.Valid & Array<U32>):
  (x, m, perm, st) = r
  (x, Sort.mk.c(n, d, nl, m, Radix.core(n, d, perm, st)))

def Sort.av.g(~T: Data, +n: U32, +d: Nat, r: Array<T> & Array<U32> & WS) -> Array<T> & (C.Valid & Array<U32>):
  (x, perm, st) = r
  (x, (C.AllValid{}, Sort.snd(Radix.core(n, d, perm, st))))

def Sort.av.m(~T: Data, +n: U32, +d: Nat, perm: Array<U32>, r: Array<T> & WS) -> Array<T> & (C.Valid & Array<U32>):
  (x, st) = r
  (x, (C.AllValid{}, Sort.snd(Radix.core(n, d, perm, st))))

def Sort.av(~T: Data, ~f: T -> U32, first: Bool, +n: U32, +d: Nat, +flip: U32, x: Array<T>, perm: Array<U32>) -> Array<T> & (C.Valid & Array<U32>):
  match first:
    case True{}:
      Sort.av.m(~T, n, d, perm, Sort.wm.go(~T, ~f, U32.to_nat(n), 0, flip, WS.new(d), Array.get(T, x, 0)))
    case False{}:
      Sort.av.g(~T, n, d, Sort.wg.go(~T, ~f, U32.to_nat(n), 0, flip, (x, WS.new(d)), Array.get(U32, perm, 0)))

# refine perm by the column's data x (word f) and validity v; x and v come back unchanged
def Sort.kt(~T: Data, ~f: T -> U32, +first: Bool, +n: U32, +d: Nat, +flip: U32, +nl: Bool, v: C.Valid, x: Array<T>, perm: Array<U32>) -> Array<T> & (C.Valid & Array<U32>):
  match v:
    case C.AllValid{}:
      Sort.av(~T, ~f, first, n, d, flip, x, perm)
    case C.Mask{m}:
      Sort.mk.b(~T, n, d, nl, Sort.wgm.go(~T, ~f, U32.to_nat(n), 0, flip, (x, m, WS.new(d)), Array.get(U32, perm, 0)))

# the column rebuilt around its (unchanged) buffers, and the refined permutation
def Sort.kw.w(+t: D.DType, +len: U32, +depth: Nat, r: Array<U32> & (C.Valid & Array<U32>)) -> C.Column & Array<U32>:
  (x, vp) = r
  (v, perm) = vp
  (C.Column.mk_w(t, len, depth, v, x), perm)

def Sort.kw.f(+len: U32, +depth: Nat, r: Array<F32> & (C.Valid & Array<U32>)) -> C.Column & Array<U32>:
  (x, vp) = r
  (v, perm) = vp
  (C.CF32{len, depth, v, x}, perm)

# a Dictionary key: the row's word is its code's rank (Dict.ranks, as Sort.dict_words). Without
# nulls the rank is looked up inside the words pass (Sort.wgd); with a mask, one gather into
# row-order rank words, then the U32 path over them (which zeroes the null rows)
def Sort.kd.c(+len: U32, +depth: Nat, dict: ST.Dict, codes: Array<U32>, r: Array<U32> & (C.Valid & Array<U32>)) -> C.Column & Array<U32>:
  (rw, vp) = r
  (v, perm) = vp
  (C.CStr{len, depth, v, ST.SDict{codes, dict}}, perm)

def Sort.kd.m(+first: Bool, +n: U32, +d: Nat, +flip: U32, +nl: Bool, +len: U32, +depth: Nat, v: C.Valid, dict: ST.Dict, perm: Array<U32>, r: Array<U32> & Array<U32>) -> C.Column & Array<U32>:
  (rw, codes) = r
  Sort.kd.c(len, depth, dict, codes, Sort.kt(~U32, ~(w => w), first, n, d, flip, nl, v, rw, perm))

def Sort.kd.a(+n: U32, +d: Nat, +len: U32, +depth: Nat, dict: ST.Dict, r: Array<U32> & Array<U32> & Array<U32> & WS) -> C.Column & Array<U32>:
  (codes, rk, perm, st) = r
  (C.CStr{len, depth, C.AllValid{}, ST.SDict{codes, dict}}, Sort.snd(Radix.core(n, d, perm, st)))

def Sort.kd.v(v: C.Valid, +first: Bool, +n: U32, +d: Nat, +flip: U32, +nl: Bool, +len: U32, +depth: Nat, codes: Array<U32>, perm: Array<U32>, dict: ST.Dict, rk: Array<U32>) -> C.Column & Array<U32>:
  match v:
    case C.AllValid{}:
      Sort.kd.a(n, d, len, depth, dict, Sort.wgd.go(U32.to_nat(n), 0, flip, (codes, rk, WS.new(d)), Array.get(U32, perm, 0)))
    case C.Mask{m}:
      Sort.kd.m(first, n, d, flip, nl, len, depth, C.Mask{m}, dict, perm, K.Kernel.gather(~U32, n, d, rk, codes, 0))

def Sort.kd(+first: Bool, +n: U32, +d: Nat, +flip: U32, +nl: Bool, +len: U32, +depth: Nat, v: C.Valid, codes: Array<U32>, perm: Array<U32>, r: ST.Dict & Array<U32>) -> C.Column & Array<U32>:
  (dict, rk) = r
  Sort.kd.v(v, first, n, d, flip, nl, len, depth, codes, perm, dict, rk)

# a Raw string key: v0.1's coder (Sort.words) consumes the strings, so it codes a clone
# (the words come with nulls zeroed and desc applied: the U32 path with flip 0)
def Sort.kr.c(r: Array<U32> & (C.Valid & Array<U32>)) -> Array<U32>:
  (w, vp) = r
  (v, perm) = vp
  perm

def Sort.kr.b(+n: U32, +d: Nat, +nl: Bool, perm: Array<U32>, r: Array<U32> & C.Valid) -> Array<U32>:
  (w, v) = r
  Sort.kr.c(Sort.kt(~U32, ~(x => x), False{}, n, d, 0, nl, v, w, perm))

def Sort.kr(+n: U32, +d: Nat, +desc: Bool, +nl: Bool, perm: Array<U32>, r: C.Column & C.Column) -> C.Column & Array<U32>:
  (c1, c2) = r
  (c1, Sort.kr.b(n, d, nl, perm, Sort.words(c2, desc)))

def Sort.key.s(+first: Bool, +n: U32, +d: Nat, +flip: U32, +desc: Bool, +nl: Bool, +len: U32, +depth: Nat, v: C.Valid, x: ST.Strs, perm: Array<U32>) -> C.Column & Array<U32>:
  match x:
    case ST.SDict{codes, dict}:
      Sort.kd(first, n, d, flip, nl, len, depth, v, codes, perm, ST.Dict.ranks(dict))
    case ST.SRaw{a}:
      Sort.kr(n, d, desc, nl, perm, C.Column.clone(C.CStr{len, depth, v, ST.SRaw{a}}))

def Sort.key.c(+first: Bool, +n: U32, +d: Nat, +flip: U32, +desc: Bool, +nl: Bool, c: C.Column, perm: Array<U32>) -> C.Column & Array<U32>:
  match c:
    case C.CBool{+len, +depth, v, x}:
      Sort.kw.w(D.TBool{}, len, depth, Sort.kt(~U32, ~(w => w), first, n, d, flip, nl, v, x, perm))
    case C.CU32{+len, +depth, v, x}:
      Sort.kw.w(D.TU32{}, len, depth, Sort.kt(~U32, ~(w => w), first, n, d, flip, nl, v, x, perm))
    case C.CI32{+len, +depth, v, x}:
      Sort.kw.w(D.TI32{}, len, depth, Sort.kt(~U32, ~(w => Sort.iword(w)), first, n, d, flip, nl, v, x, perm))
    case C.CF32{+len, +depth, v, x}:
      Sort.kw.f(len, depth, Sort.kt(~F32, ~(w => Sort.fword(w)), first, n, d, flip, nl, v, x, perm))
    case C.CStr{+len, +depth, v, x}:
      Sort.key.s(first, n, d, flip, desc, nl, len, depth, v, x, perm)

# refine the permutation perm (current order) stably by one key column, borrowed: the column
# comes back unchanged. `first`: perm is the identity (no key processed yet).
def Sort.key(+first: Bool, +n: U32, +d: Nat, +desc: Bool, +nl: Bool, c: C.Column, perm: Array<U32>) -> C.Column & Array<U32>:
  Sort.key.c(first, n, d, Bool.pick(U32, desc, 4294967295, 0), desc, nl, c, perm)

# ---- borrowing the key column ---------------------------------------------------------------

# a walk over the columns: not found yet (the columns so far, newest first), or found (the
# columns before it, newest first; its name and column; the columns after it, newest first)
type KS is Type:
  KLook{pre: List<&1, C.Named>}
  KHit{pre: List<&1, C.Named>, name: String, col: C.Column, post: List<&1, C.Named>}

def Sort.split.look(eq: Bool, n: String, c: C.Column, pre: List<&1, C.Named>) -> KS:
  match eq:
    case True{}:
      KHit{pre, n, c, Nil{}}
    case False{}:
      KLook{C.Named{n, c} <> pre}

def Sort.split.step(+name: String, +n: String, c: C.Column, st: KS) -> KS:
  match st:
    case KLook{pre}:
      Sort.split.look(String.eq(name, n), n, c, pre)
    case KHit{pre, m, col, post}:
      KHit{pre, m, col, C.Named{n, c} <> post}

# the first column called name, taken out (no copy) with what it takes to put it back
def Sort.split(cols: List<&1, C.Named>, +name: String, st: KS) -> KS:
  match cols:
    case Nil{}:
      st
    case C.Named{+n, c} <> rest:
      Sort.split(rest, name, Sort.split.step(name, n, c, st))

# the column back in its place (same order as before Sort.split)
def Sort.unsplit(pre: List<&1, C.Named>, name: String, c: C.Column, post: List<&1, C.Named>) -> List<&1, C.Named>:
  List.reverse.go(&1, C.Named, pre, C.Named{name, c} <> List.reverse(&1, C.Named, post))

# ---- keys -----------------------------------------------------------------------------------

def Sort.step.c(+h: U32, pre: List<&1, C.Named>, name: String, post: List<&1, C.Named>, r: C.Column & Array<U32>) -> SortSt:
  (c, perm) = r
  SortSt{C.Frame{h, Sort.unsplit(pre, name, c, post)}, Done{perm}}

def Sort.step.b(+first: Bool, +n: U32, +d: Nat, +desc: Bool, +nl: Bool, +h: U32, +key: String, perm: Array<U32>, ks: KS) -> SortSt:
  match ks:
    case KLook{pre}:
      SortSt{C.Frame{h, List.reverse(&1, C.Named, pre)}, Fail{E.ColumnNotFound{key}}}
    case KHit{pre, name, c, post}:
      Sort.step.c(h, pre, name, post, Sort.key(first, n, d, desc, nl, c, perm))

def Sort.step.f(+first: Bool, +n: U32, +d: Nat, +name: String, +desc: Bool, +nl: Bool, f: C.Frame, perm: Array<U32>) -> SortSt:
  match f:
    case C.Frame{+h, cols}:
      Sort.step.b(first, n, d, desc, nl, h, name, perm, Sort.split(cols, name, KLook{Nil{}}))

def Sort.step(+first: Bool, +n: U32, +d: Nat, k: SortKey, st: SortSt) -> SortSt:
  match k st:
    case SortKey{+name, +desc, +nl} SortSt{f, Done{perm}}:
      Sort.step.f(first, n, d, name, desc, nl, f, perm)
    case SortKey{name, desc, nl} SortSt{f, Fail{e}}:
      SortSt{f, Fail{e}}

# keys are given last first; the first one processed starts from the identity
def Sort.keys(rev: List<&2, SortKey>, +n: U32, +d: Nat, first: Bool, st: SortSt) -> SortSt:
  match rev:
    case Nil{}:
      st
    case k <> t:
      Sort.keys(t, n, d, False{}, Sort.step(first, n, d, k, st))

def Sort.argsort.b(+n: U32, keys: List<&2, SortKey>, f: C.Frame) -> SortSt:
  +d = K.Kernel.depth_for(n)
  Sort.keys(List.reverse(&2, SortKey, keys), n, d, True{}, SortSt{f, Done{K.Kernel.iota(n, d)}})

def Sort.argsort.a(keys: List<&2, SortKey>, r: C.Frame & U32) -> SortSt:
  (f, +n) = r
  Sort.argsort.b(n, keys, f)

def Sort.argsort.fin(st: SortSt) -> C.Frame & E.ResT(Array<U32>):
  match st:
    case SortSt{f, r}:
      (f, r)

# the stable permutation that sorts the frame by the keys (first key most
# significant): row perm[j] goes to position j. The frame comes back.
# ColumnNotFound for an unknown key name.
def Sort.argsort(f: C.Frame, keys: List<&2, SortKey>) -> C.Frame & E.ResT(Array<U32>):
  Sort.argsort.fin(Sort.argsort.a(keys, C.Frame.height(f)))

# ---- frame ----------------------------------------------------------------------------------

def Sort.gcols.add(n: String, acc: List<&1, C.Named>, r: C.Column & Array<U32>) -> Array<U32> & List<&1, C.Named>:
  (c, perm) = r
  (perm, C.Named{n, c} <> acc)

def Sort.gcols.step(n: String, +h: U32, col: C.Column, st: Array<U32> & List<&1, C.Named>) -> Array<U32> & List<&1, C.Named>:
  (perm, acc) = st
  Sort.gcols.add(n, acc, C.Column.gather(col, perm, h))

def Sort.gcols(cols: List<&1, C.Named>, +h: U32, st: Array<U32> & List<&1, C.Named>) -> Array<U32> & List<&1, C.Named>:
  match cols:
    case Nil{}:
      st
    case C.Named{n, col} <> rest:
      Sort.gcols(rest, h, Sort.gcols.step(n, h, col, st))

def Sort.gather.k(+h: U32, st: Array<U32> & List<&1, C.Named>) -> C.Frame:
  (perm, acc) = st
  C.Frame{h, List.reverse(&1, C.Named, acc)}

# every column gathered by perm (rows perm[0..h)); perm is consumed
def Sort.gather(f: C.Frame, perm: Array<U32>) -> C.Frame:
  match f:
    case C.Frame{+h, cols}:
      Sort.gather.k(h, Sort.gcols(cols, h, (perm, Nil{})))

def Sort.frame.a(r: C.Frame & E.ResT(Array<U32>)) -> E.ResT(C.Frame):
  (f, rp) = r
  match rp:
    case Fail{e}:
      Fail{e}
    case Done{perm}:
      Done{Sort.gather(f, perm)}

def Sort.miss.k(has: Bool, n: String, rest: Maybe<&2, E.Err>) -> Maybe<&2, E.Err>:
  match has:
    case True{}:
      rest
    case False{}:
      Some{E.ColumnNotFound{n}}

# ColumnNotFound for the first key (list order) that is not a column: Plan.schema.sort's
# check. Sort.argsort walks the keys last first, so without it a later missing key would be
# reported before an earlier one (eager != lazy, NEW-1)
def Sort.miss(ks: List<&2, SortKey>, +ns: List<&2, String>) -> Maybe<&2, E.Err>:
  match ks:
    case Nil{}:
      None{}
    case SortKey{+n, d, nl} <> t:
      Sort.miss.k(C.Names.has(ns, n), n, Sort.miss(t, ns))

def Sort.frame.c(m: Maybe<&2, E.Err>, f: C.Frame, keys: List<&2, SortKey>) -> E.ResT(C.Frame):
  match m:
    case Some{e}:
      Fail{e}
    case None{}:
      Sort.frame.a(Sort.argsort(f, keys))

def Sort.frame.b(+keys: List<&2, SortKey>, r: C.Frame & C.FInfo) -> E.ResT(C.Frame):
  (f, i) = r
  match i:
    case C.FInfo{h, ns}:
      Sort.frame.c(Sort.miss(keys, ns), f, keys)

# the frame sorted by the keys: stable, multi-key, per-key descending and
# nulls_last (nulls first by default, independent of descending; NaN is the
# largest f32). No keys: the frame as is. Every key is checked before any work
# (ColumnNotFound for the first missing one).
def Sort.frame(f: C.Frame, keys: List<&2, SortKey>) -> E.ResT(C.Frame):
  match keys:
    case Nil{}:
      Done{f}
    case +k <> t:
      Sort.frame.b(k <> t, C.Frame.info(f))

# ---- Sort + Head (v0.2 T3.4): the exact full argsort, then only min(n, height) rows gathered ---
#
# Bounded gathering, not a top-k selection: the permutation is the full stable argsort of
# Sort.frame (every key checked and coded, every error and its precedence unchanged, n = 0
# included); only the gather is cut to the rows Head keeps. LAWS.bend section 16 proves the
# result shows exactly what Sort.frame then Frame.head shows (sort_head_frame).

# the height under which every gather's rows fit their slots (Kernel.depth_for is exact for
# n <= 2^31); a frame never exceeds the 2^23 row cap, so the bounded path is the one taken
def Sort.head_cap() -> U32:
  U32.shln(1, 31n)

def Sort.gh.k(ok: Bool, +h: U32, cols: List<&1, C.Named>, perm: Array<U32>, +n: U32) -> C.Frame:
  match ok:
    case True{}:
      Sort.gather.k(U32.min(n, h), Sort.gcols(cols, U32.min(n, h), (perm, Nil{})))
    case False{}:
      C.Frame.head(Sort.gather.k(h, Sort.gcols(cols, h, (perm, Nil{}))), n)

# rows perm[0..min(n, height)) of every column (Frame.head(Sort.gather(f, perm), n) without
# gathering the rows head drops); perm is consumed
def Sort.gather_head(f: C.Frame, perm: Array<U32>, +n: U32) -> C.Frame:
  match f:
    case C.Frame{+h, cols}:
      Sort.gh.k(U32.is_le(h, Sort.head_cap()), h, cols, perm, n)

def Sort.fh.a(+n: U32, r: C.Frame & E.ResT(Array<U32>)) -> E.ResT(C.Frame):
  (f, rp) = r
  match rp:
    case Fail{e}:
      Fail{e}
    case Done{perm}:
      Done{Sort.gather_head(f, perm, n)}

def Sort.fh.c(m: Maybe<&2, E.Err>, f: C.Frame, keys: List<&2, SortKey>, +n: U32) -> E.ResT(C.Frame):
  match m:
    case Some{e}:
      Fail{e}
    case None{}:
      Sort.fh.a(n, Sort.argsort(f, keys))

def Sort.fh.b(+keys: List<&2, SortKey>, +n: U32, r: C.Frame & C.FInfo) -> E.ResT(C.Frame):
  (f, i) = r
  match i:
    case C.FInfo{h, ns}:
      Sort.fh.c(Sort.miss(keys, ns), f, keys, n)

# Sort.frame(f, keys) then Frame.head(_, n), gathering min(n, height) rows: the same errors
# (in the same order), the same rows in the same (stable) order, the same schema; n = 0 still
# checks and sorts every key. No keys: Frame.head(f, n).
def Sort.frame_head(f: C.Frame, keys: List<&2, SortKey>, +n: U32) -> E.ResT(C.Frame):
  match keys:
    case Nil{}:
      Done{C.Frame.head(f, n)}
    case +k <> t:
      Sort.fh.b(k <> t, n, C.Frame.info(f))
