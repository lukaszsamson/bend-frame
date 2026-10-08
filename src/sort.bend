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

# order-preserving word of an f32: NaN (any payload) is the largest word,
# -0.0 equals 0.0, negatives are bit-flipped, positives get the sign bit set
def Sort.fword.b(+b: U32) -> U32:
  +a = U32.and(b, 2147483647)
  Bool.pick(U32, U32.is_gt(a, 2139095040), 4294967295, Bool.pick(U32, U32.is_zero(a), 2147483648, Bool.pick(U32, U32.is_ge(b, 2147483648), U32.xor(b, 4294967295), U32.or(b, 2147483648))))

def Sort.fword(x: F32) -> U32:
  Sort.fword.b(F32.bits(x))

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
      Sort.words.z(n, Sort.str_words(n, d, flip, x), v)

def Sort.words(c: C.Column, desc: Bool) -> Array<U32> & C.Valid:
  Sort.words.go(c, Bool.pick(U32, desc, 4294967295, 0))

# ---- LSD radix sort over (word, row) pairs -------------------------------------------------

def Radix.digit(+x: U32, +sh: Nat, +mk: U32) -> U32:
  U32.and(U32.shrn(x, sh), mk)

def Radix.inc(+g: U32, r: Array<U32> & U32) -> Array<U32>:
  (h, c) = r
  Array.set(U32, h, g, U32.inc(c))

# h[digit(ws[i])] += 1; answers (ws, h)
def Radix.hist.go(n: Nat, +i: U32, +sh: Nat, +mk: U32, h: Array<U32>, r: Array<U32> & U32) -> Array<U32> & Array<U32>:
  match n:
    case 0n:
      (ws, x) = r
      (ws, h)
    case 1n+p:
      (ws, +x) = r
      +g = Radix.digit(x, sh, mk)
      +j = U32.inc(i)
      Radix.hist.go(p, j, sh, mk, Radix.inc(g, Array.get(U32, h, g)), Array.get(U32, ws, j))

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

def Radix.put(+g: U32, x: U32, p: U32, nw: Array<U32>, np: Array<U32>, r: Array<U32> & U32) -> Array<U32> & Array<U32> & Array<U32>:
  (off, +pos) = r
  (Array.set(U32, off, g, U32.inc(pos)), Array.set(U32, nw, pos, x), Array.set(U32, np, pos, p))

# stable scatter of (ws[i], perm[i]) to the slot off[digit]++
def Radix.scat.go(n: Nat, +i: U32, +sh: Nat, +mk: U32, st: Array<U32> & Array<U32> & Array<U32>, rw: Array<U32> & U32, rp: Array<U32> & U32) -> Array<U32> & Array<U32>:
  match n:
    case 0n:
      (off, nw, np) = st
      (nw, np)
    case 1n+q:
      (off, nw, np) = st
      (ws, +x) = rw
      (perm, p) = rp
      +g = Radix.digit(x, sh, mk)
      +j = U32.inc(i)
      Radix.scat.go(q, j, sh, mk, Radix.put(g, x, p, nw, np, Array.get(U32, off, g)), Array.get(U32, ws, j), Array.get(U32, perm, j))

def Radix.pass.b(+sh: Nat, +mk: U32, +b: Nat, +n: U32, +d: Nat, perm: Array<U32>, r: Array<U32> & Array<U32>) -> Array<U32> & Array<U32>:
  (ws, h) = r
  off = Radix.pre.go(U32.to_nat(U32.inc(mk)), 0, 0, Array.get(U32, h, 0))
  Radix.scat.go(U32.to_nat(n), 0, sh, mk, (off, Array.new(U32, d, 0), Array.new(U32, d, 0)), Array.get(U32, ws, 0), Array.get(U32, perm, 0))

# one stable counting-sort pass on the digit (word >> sh) & mk (mk = 2^b - 1)
def Radix.pass(+sh: Nat, +mk: U32, +b: Nat, +n: U32, +d: Nat, st: Array<U32> & Array<U32>) -> Array<U32> & Array<U32>:
  (ws, perm) = st
  Radix.pass.b(sh, mk, b, n, d, perm, Radix.hist.go(U32.to_nat(n), 0, sh, mk, Array.new(U32, b, 0), Array.get(U32, ws, 0)))

def Radix.maybe(need: Bool, +sh: Nat, +mk: U32, +b: Nat, +n: U32, +d: Nat, st: Array<U32> & Array<U32>) -> Array<U32> & Array<U32>:
  match need:
    case True{}:
      Radix.pass(sh, mk, b, n, d, st)
    case False{}:
      st

def Radix.passes(np: Nat, +sh: Nat, +b: Nat, +mk: U32, +vary: U32, +n: U32, +d: Nat, st: Array<U32> & Array<U32>) -> Array<U32> & Array<U32>:
  match np:
    case 0n:
      st
    case 1n+p:
      Radix.passes(p, Nat.add(sh, b), b, mk, vary, n, d, Radix.maybe(U32.is_ne(Radix.digit(vary, sh, mk), 0), sh, mk, b, n, d, st))

# the bits in which some word differs from ws[0]
def Radix.vary.go(n: Nat, +i: U32, +w0: U32, acc: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  match n:
    case 0n:
      (ws, x) = r
      (ws, acc)
    case 1n+p:
      (ws, x) = r
      +j = U32.inc(i)
      Radix.vary.go(p, j, w0, U32.or(acc, U32.xor(x, w0)), Array.get(U32, ws, j))

def Radix.vary.a(+n: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  (ws, +w0) = r
  Radix.vary.go(U32.to_nat(n), 0, w0, 0, Array.get(U32, ws, 0))

def Radix.bits() -> Nat:
  16n

def Radix.sort.b(+n: U32, +d: Nat, perm: Array<U32>, r: Array<U32> & U32) -> Array<U32> & Array<U32>:
  (ws, +vary) = r
  +b = Radix.bits()
  Radix.passes(2n, 0n, b, U32.sub(U32.shln(1, b), 1), vary, n, d, (ws, perm))

# stable sort of the pairs (ws[i], perm[i]), i < n, by ws (unsigned); answers
# the sorted (ws, perm). 2 passes of 16 bits, a pass whose digit never varies
# is skipped (so a column of small values costs one pass, a constant one none)
def Radix.sort(+n: U32, +d: Nat, st: Array<U32> & Array<U32>) -> Array<U32> & Array<U32>:
  (ws, perm) = st
  Radix.sort.b(n, d, perm, Radix.vary.a(n, Array.get(U32, ws, 0)))

# one stable pass on a 0/1 flag per pair
def Radix.flag(+n: U32, +d: Nat, st: Array<U32> & Array<U32>) -> Array<U32> & Array<U32>:
  Radix.pass(0n, 1, 1n, n, d, st)

# ---- one key ------------------------------------------------------------------------------

def Sort.snd(st: Array<U32> & Array<U32>) -> Array<U32>:
  (a, b) = st
  b

# null flag in sort order: nulls first -> null 0 / valid 1; nulls last -> 1 / 0
def Sort.nulls.b(+n: U32, +d: Nat, +nl: Bool, m: Array<U32>, perm: Array<U32>) -> Array<U32>:
  Sort.snd(Radix.flag(n, d, K.Kernel.gather(~U32, n, d, Sort.xmap(~U32, ~(w => w), n, d, Bool.pick(U32, nl, 1, 0), m), perm, 0)))

def Sort.nulls(+n: U32, +d: Nat, +nl: Bool, v: C.Valid, st: Array<U32> & Array<U32>) -> Array<U32>:
  match v:
    case C.AllValid{}:
      Sort.snd(st)
    case C.Mask{m}:
      Sort.nulls.b(n, d, nl, m, Sort.snd(st))

def Sort.by_col.a(+n: U32, +d: Nat, +nl: Bool, perm: Array<U32>, r: Array<U32> & C.Valid) -> Array<U32>:
  (w, v) = r
  Sort.nulls(n, d, nl, v, Radix.sort(n, d, K.Kernel.gather(~U32, n, d, w, perm, 0)))

# refine the permutation `perm` (current order) stably by one key column
def Sort.by_col(+n: U32, +d: Nat, +desc: Bool, +nl: Bool, c: C.Column, perm: Array<U32>) -> Array<U32>:
  Sort.by_col.a(n, d, nl, perm, Sort.words(c, desc))

# ---- keys -----------------------------------------------------------------------------------

def Sort.step.b(+n: U32, +d: Nat, +desc: Bool, +nl: Bool, perm: Array<U32>, r: C.Frame & E.ResT(C.Column)) -> SortSt:
  (f, rc) = r
  match rc:
    case Fail{e}:
      SortSt{f, Fail{e}}
    case Done{c}:
      SortSt{f, Done{Sort.by_col(n, d, desc, nl, c, perm)}}

def Sort.step(+n: U32, +d: Nat, k: SortKey, st: SortSt) -> SortSt:
  match k st:
    case SortKey{name, desc, nl} SortSt{f, Done{perm}}:
      Sort.step.b(n, d, desc, nl, perm, C.Frame.get_cloned(f, name))
    case SortKey{name, desc, nl} SortSt{f, Fail{e}}:
      SortSt{f, Fail{e}}

# keys are given last first
def Sort.keys(rev: List<&2, SortKey>, +n: U32, +d: Nat, st: SortSt) -> SortSt:
  match rev:
    case Nil{}:
      st
    case k <> t:
      Sort.keys(t, n, d, Sort.step(n, d, k, st))

def Sort.argsort.b(+n: U32, keys: List<&2, SortKey>, f: C.Frame) -> SortSt:
  +d = K.Kernel.depth_for(n)
  Sort.keys(List.reverse(&2, SortKey, keys), n, d, SortSt{f, Done{K.Kernel.iota(n, d)}})

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

# the frame sorted by the keys: stable, multi-key, per-key descending and
# nulls_last (nulls first by default, independent of descending; NaN is the
# largest f32). No keys: the frame as is.
def Sort.frame(f: C.Frame, keys: List<&2, SortKey>) -> E.ResT(C.Frame):
  match keys:
    case Nil{}:
      Done{f}
    case +k <> t:
      Sort.frame.a(Sort.argsort(f, k <> t))
