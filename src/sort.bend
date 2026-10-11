# src/sort.bend -- argsort, multi-key stable sort, Sort.frame. DESIGN.md 4.8.
#
# Algorithm (deviates from 4.8's List.sort chain, see DESIGN.md 14 M5): every
# key column becomes an Array<U32> of ORDER-PRESERVING sort words
#   u32: x   i32: x xor 2^31   bool: 0/1   f32: IEEE bits mapped to a total
#   order (negatives flipped, -0.0 = 0.0, every NaN = the largest word)
#   str: the rank of the string among the column's distinct strings in
#   code-point order, a prefix first (= String.is_lt, Base Map.to_list order):
#   Raw strings by the flat coder and the rank stage (R.Rk.words, src/hcode.bend
#   + src/ranks.bend, v0.2 W2.3), a Dictionary by the rank stage over its
#   entries (R.Rk.dict)
# `descending` xors the word with 2^32-1. Keys are then processed LAST to
# FIRST with a stable LSD radix sort (src/radix.bend: 16-bit digits, a digit
# whose bits never vary in the column is skipped) over (word, row) pairs in the
# current order; a key with a validity mask gets one more stable 1-bit pass on
# its null flag (nulls first unless nulls_last). Stability of every pass makes
# the chain a lexicographic stable sort: ties keep input order. No comparison
# sort and no List on the hot path.
#
# The word helpers (Sort.words, Sort.xmap, Sort.words.z) are also what
# src/groupby.bend uses to dictionary-encode numeric group keys.
#
# Idioms (DESIGN.md section 9): helpers above callers; Nat fuel first; pairs
# taken apart in the next helper's parameter; templates ~T: Data.
import Base
import ./dtype.bend as D
import ./err.bend as E
import ./kernels.bend as K
import ./column.bend as C
import ./strs.bend as ST
import ./radix.bend as RD
import ./ranks.bend as R

type SortKey is Data:
  SortKey{name: String, descending: Bool, nulls_last: Bool}

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

# ---- string words ------------------------------------------------------------------------

def Sort.snd0(r: Array<U32> & Array<U32>) -> Array<U32>:
  (a, b) = r
  a

def Sort.str_words.d(r: Array<String> & Array<U32>) -> Array<U32>:
  (a, w) = r
  w

# order-preserving words of strings: rank among the distinct strings (R.Rk.words: the flat coder,
# then the rank stage over the entries; the rows are dropped here, Sort.kr keeps them)
def Sort.str_words(+n: U32, +d: Nat, +flip: U32, a: Array<String>) -> Array<U32>:
  Sort.str_words.d(R.Rk.words(n, d, flip, a))

# order-preserving words of a Dictionary column (M4): the dictionary is ranked ONCE (its k
# entries through the rank stage, R.Rk.dict: the order of Sort.str_words), then each row's word
# is its code's rank (one gather)
def Sort.dict_words.b(+n: U32, +d: Nat, +flip: U32, codes: Array<U32>, r: ST.Dict & Array<U32>) -> Array<U32>:
  (dict, rk) = r
  Sort.xmap(~U32, ~(x => x), n, d, flip, Sort.snd0(K.Kernel.gather(~U32, n, d, rk, codes, 0)))

def Sort.str_words.st(+n: U32, +d: Nat, +flip: U32, x: ST.Strs) -> Array<U32>:
  match x:
    case ST.SRaw{a}:
      Sort.str_words(n, d, flip, a)
    case ST.SDict{codes, dict}:
      Sort.dict_words.b(n, d, flip, codes, R.Rk.dict(dict))

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

# ---- key words, fused with the read pass (v0.2 T3.2) ----------------------------------------
#
# The key column is BORROWED (Sort.split / Sort.unsplit put it back where it was): its buffers
# are read in place, never cloned (a Raw string key too since W2.3: R.Rk.words hands its rows
# back). The words of the rows in the current order perm are built
# in ONE pass that also does the radix read pass: out[j] = f(src[perm[j]]) xor flip (0 for a
# null row). The first key (perm is the identity) reads src directly.

# rows perm[j], j < n: the words and the read-pass state; src and perm come back
def Sort.wg.put(~T: Data, ~f: T -> U32, +j: U32, +flip: U32, st: RD.WS, r: Array<T> & T) -> Array<T> & RD.WS:
  (src, x) = r
  (src, RD.WS.put(j, U32.xor(f(x), flip), st))

def Sort.wg.go(~T: Data, ~f: T -> U32, n: Nat, +j: U32, +flip: U32, sw: Array<T> & RD.WS, rp: Array<U32> & U32) -> Array<T> & Array<U32> & RD.WS:
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
def Sort.wm.go(~T: Data, ~f: T -> U32, n: Nat, +j: U32, +flip: U32, st: RD.WS, r: Array<T> & T) -> Array<T> & RD.WS:
  match n:
    case 0n:
      (src, x) = r
      (src, st)
    case 1n+p:
      (src, x) = r
      +j2 = U32.inc(j)
      Sort.wm.go(~T, ~f, p, j2, flip, RD.WS.put(j, U32.xor(f(x), flip), st), Array.get(T, src, j2))

# rows perm[j] with a validity mask: a null row's word is 0 (nulls tie, keeping their order)
def Sort.wgm.put(~T: Data, ~f: T -> U32, +j: U32, +flip: U32, st: RD.WS, r: Array<T> & T, rm: Array<U32> & U32) -> Array<T> & Array<U32> & RD.WS:
  (src, x) = r
  (m, +b) = rm
  (src, m, RD.WS.put(j, Bool.pick(U32, U32.is_ne(b, 0), U32.xor(f(x), flip), 0), st))

def Sort.wgm.go(~T: Data, ~f: T -> U32, n: Nat, +j: U32, +flip: U32, sw: Array<T> & Array<U32> & RD.WS, rp: Array<U32> & U32) -> Array<T> & Array<U32> & Array<U32> & RD.WS:
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
def Sort.wgd.put2(+j: U32, +flip: U32, st: RD.WS, codes: Array<U32>, r: Array<U32> & U32) -> Array<U32> & Array<U32> & RD.WS:
  (rk, +w) = r
  (codes, rk, RD.WS.put(j, U32.xor(w, flip), st))

def Sort.wgd.put(+j: U32, +flip: U32, st: RD.WS, rk: Array<U32>, r: Array<U32> & U32) -> Array<U32> & Array<U32> & RD.WS:
  (codes, +c) = r
  Sort.wgd.put2(j, flip, st, codes, Array.get(U32, rk, c))

def Sort.wgd.go(n: Nat, +j: U32, +flip: U32, sw: Array<U32> & Array<U32> & RD.WS, rp: Array<U32> & U32) -> Array<U32> & Array<U32> & Array<U32> & RD.WS:
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
def Sort.nulls.b(+n: U32, +d: Nat, r: Array<U32> & Array<U32> & RD.WS) -> Array<U32> & Array<U32>:
  (m, perm, st) = r
  (m, Sort.snd(RD.Radix.core(n, d, perm, st)))

def Sort.nulls(+n: U32, +d: Nat, +nl: Bool, m: Array<U32>, perm: Array<U32>) -> Array<U32> & Array<U32>:
  Sort.nulls.b(n, d, Sort.wg.go(~U32, ~(w => U32.and(w, 1)), U32.to_nat(n), 0, Bool.pick(U32, nl, 1, 0), (m, RD.WS.new(d)), Array.get(U32, perm, 0)))

def Sort.av.b(r: Array<U32> & Array<U32>) -> C.Valid & Array<U32>:
  (m, perm) = r
  (C.Mask{m}, perm)

def Sort.mk.c(+n: U32, +d: Nat, +nl: Bool, m: Array<U32>, r: Array<U32> & Array<U32>) -> C.Valid & Array<U32>:
  (ws, perm) = r
  Sort.av.b(Sort.nulls(n, d, nl, m, perm))

def Sort.mk.b(~T: Data, +n: U32, +d: Nat, +nl: Bool, r: Array<T> & Array<U32> & Array<U32> & RD.WS) -> Array<T> & (C.Valid & Array<U32>):
  (x, m, perm, st) = r
  (x, Sort.mk.c(n, d, nl, m, RD.Radix.core(n, d, perm, st)))

def Sort.av.g(~T: Data, +n: U32, +d: Nat, r: Array<T> & Array<U32> & RD.WS) -> Array<T> & (C.Valid & Array<U32>):
  (x, perm, st) = r
  (x, (C.AllValid{}, Sort.snd(RD.Radix.core(n, d, perm, st))))

def Sort.av.m(~T: Data, +n: U32, +d: Nat, perm: Array<U32>, r: Array<T> & RD.WS) -> Array<T> & (C.Valid & Array<U32>):
  (x, st) = r
  (x, (C.AllValid{}, Sort.snd(RD.Radix.core(n, d, perm, st))))

def Sort.av(~T: Data, ~f: T -> U32, first: Bool, +n: U32, +d: Nat, +flip: U32, x: Array<T>, perm: Array<U32>) -> Array<T> & (C.Valid & Array<U32>):
  match first:
    case True{}:
      Sort.av.m(~T, n, d, perm, Sort.wm.go(~T, ~f, U32.to_nat(n), 0, flip, RD.WS.new(d), Array.get(T, x, 0)))
    case False{}:
      Sort.av.g(~T, n, d, Sort.wg.go(~T, ~f, U32.to_nat(n), 0, flip, (x, RD.WS.new(d)), Array.get(U32, perm, 0)))

# refine perm by the column's data x (word f) and validity v; x and v come back unchanged
def Sort.kt(~T: Data, ~f: T -> U32, +first: Bool, +n: U32, +d: Nat, +flip: U32, +nl: Bool, v: C.Valid, x: Array<T>, perm: Array<U32>) -> Array<T> & (C.Valid & Array<U32>):
  match v:
    case C.AllValid{}:
      Sort.av(~T, ~f, first, n, d, flip, x, perm)
    case C.Mask{m}:
      Sort.mk.b(~T, n, d, nl, Sort.wgm.go(~T, ~f, U32.to_nat(n), 0, flip, (x, m, RD.WS.new(d)), Array.get(U32, perm, 0)))

# the column rebuilt around its (unchanged) buffers, and the refined permutation
def Sort.kw.w(+t: D.DType, +len: U32, +depth: Nat, r: Array<U32> & (C.Valid & Array<U32>)) -> C.Column & Array<U32>:
  (x, vp) = r
  (v, perm) = vp
  (C.Column.mk_w(t, len, depth, v, x), perm)

def Sort.kw.f(+len: U32, +depth: Nat, r: Array<F32> & (C.Valid & Array<U32>)) -> C.Column & Array<U32>:
  (x, vp) = r
  (v, perm) = vp
  (C.CF32{len, depth, v, x}, perm)

# a Dictionary key: the row's word is its code's rank (R.Rk.dict, as Sort.dict_words). Without
# nulls the rank is looked up inside the words pass (Sort.wgd); with a mask, one gather into
# row-order rank words, then the U32 path over them (which zeroes the null rows)
def Sort.kd.c(+len: U32, +depth: Nat, dict: ST.Dict, codes: Array<U32>, r: Array<U32> & (C.Valid & Array<U32>)) -> C.Column & Array<U32>:
  (rw, vp) = r
  (v, perm) = vp
  (C.CStr{len, depth, v, ST.SDict{codes, dict}}, perm)

def Sort.kd.m(+first: Bool, +n: U32, +d: Nat, +flip: U32, +nl: Bool, +len: U32, +depth: Nat, v: C.Valid, dict: ST.Dict, perm: Array<U32>, r: Array<U32> & Array<U32>) -> C.Column & Array<U32>:
  (rw, codes) = r
  Sort.kd.c(len, depth, dict, codes, Sort.kt(~U32, ~(w => w), first, n, d, flip, nl, v, rw, perm))

def Sort.kd.a(+n: U32, +d: Nat, +len: U32, +depth: Nat, dict: ST.Dict, r: Array<U32> & Array<U32> & Array<U32> & RD.WS) -> C.Column & Array<U32>:
  (codes, rk, perm, st) = r
  (C.CStr{len, depth, C.AllValid{}, ST.SDict{codes, dict}}, Sort.snd(RD.Radix.core(n, d, perm, st)))

def Sort.kd.v(v: C.Valid, +first: Bool, +n: U32, +d: Nat, +flip: U32, +nl: Bool, +len: U32, +depth: Nat, codes: Array<U32>, perm: Array<U32>, dict: ST.Dict, rk: Array<U32>) -> C.Column & Array<U32>:
  match v:
    case C.AllValid{}:
      Sort.kd.a(n, d, len, depth, dict, Sort.wgd.go(U32.to_nat(n), 0, flip, (codes, rk, RD.WS.new(d)), Array.get(U32, perm, 0)))
    case C.Mask{m}:
      Sort.kd.m(first, n, d, flip, nl, len, depth, C.Mask{m}, dict, perm, K.Kernel.gather(~U32, n, d, rk, codes, 0))

def Sort.kd(+first: Bool, +n: U32, +d: Nat, +flip: U32, +nl: Bool, +len: U32, +depth: Nat, v: C.Valid, codes: Array<U32>, perm: Array<U32>, r: ST.Dict & Array<U32>) -> C.Column & Array<U32>:
  (dict, rk) = r
  Sort.kd.v(v, first, n, d, flip, nl, len, depth, codes, perm, dict, rk)

# a Raw string key, BORROWED like the other dtypes: R.Rk.words codes the rows (the flat coder)
# and ranks the entries, handing the rows back; desc is folded into the words (flip), so the U32
# path runs with flip 0 (and gives the null rows word 0, as v0.1's Sort.words.z did)
def Sort.kr.c(+len: U32, +depth: Nat, a: Array<String>, r: Array<U32> & (C.Valid & Array<U32>)) -> C.Column & Array<U32>:
  (w, vp) = r
  (v, perm) = vp
  (C.CStr{len, depth, v, ST.SRaw{a}}, perm)

def Sort.kr(+first: Bool, +n: U32, +d: Nat, +nl: Bool, +len: U32, +depth: Nat, v: C.Valid, perm: Array<U32>, r: Array<String> & Array<U32>) -> C.Column & Array<U32>:
  (a, w) = r
  Sort.kr.c(len, depth, a, Sort.kt(~U32, ~(x => x), first, n, d, 0, nl, v, w, perm))

def Sort.key.s(+first: Bool, +n: U32, +d: Nat, +flip: U32, +nl: Bool, +len: U32, +depth: Nat, v: C.Valid, x: ST.Strs, perm: Array<U32>) -> C.Column & Array<U32>:
  match x:
    case ST.SDict{codes, dict}:
      Sort.kd(first, n, d, flip, nl, len, depth, v, codes, perm, R.Rk.dict(dict))
    case ST.SRaw{a}:
      Sort.kr(first, n, d, nl, len, depth, v, perm, R.Rk.words(n, d, flip, a))

def Sort.key.c(+first: Bool, +n: U32, +d: Nat, +flip: U32, +nl: Bool, c: C.Column, perm: Array<U32>) -> C.Column & Array<U32>:
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
      Sort.key.s(first, n, d, flip, nl, len, depth, v, x, perm)

# refine the permutation perm (current order) stably by one key column, borrowed: the column
# comes back unchanged. `first`: perm is the identity (no key processed yet).
def Sort.key(+first: Bool, +n: U32, +d: Nat, +desc: Bool, +nl: Bool, c: C.Column, perm: Array<U32>) -> C.Column & Array<U32>:
  Sort.key.c(first, n, d, Bool.pick(U32, desc, 4294967295, 0), nl, c, perm)

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

# ---- coarse forks over a list (v0.2 T5.4, DESIGN.md 16.4 D4) -------------------------------------------
# One balanced binary parallel let per level over the HALVES of a list (never 1-vs-rest), the leaves
# running their few elements one after the other in order. Mirror of Lst.pmap (src/chunks.bend; this
# file may not import chunks.bend: it would put the chunk layer under the operators). Used by
# Fmt.describe (the columns). The forks over the group_by aggregates and over the column gathers were
# built on this shape, measured and REMOVED (they did not pay; DESIGN.md 14 T5.4, bench/w5/t54_*).
# Forks go only 5 levels deep (32 leaves) and stop at a single element.

# the length of a list, as a tail call; the list comes back
def Sort.pm.len(-A: Type, xs: List<&1, A>, +k: U32, acc: List<&1, A>) -> List<&1, A> & U32:
  match xs:
    case Nil{}:
      (List.reverse(&1, A, acc), k)
    case x <> rest:
      Sort.pm.len(A, rest, U32.inc(k), x <> acc)

def Sort.pm.split.k(-A: Type, x: A, r: List<&1, A> & List<&1, A>) -> List<&1, A> & List<&1, A>:
  (a, b) = r
  (x <> a, b)

# the first k elements and the rest (z: k == 0, computed by the caller)
def Sort.pm.split(-A: Type, xs: List<&1, A>, +k: U32, z: Bool) -> List<&1, A> & List<&1, A>:
  match xs z:
    case Nil{} _:
      (Nil{}, Nil{})
    case x <> rest True{}:
      (Nil{}, x <> rest)
    case x <> rest False{}:
      Sort.pm.split.k(A, x, Sort.pm.split(A, rest, U32.sub(k, 1), U32.is_zero(U32.sub(k, 1))))

def Sort.pm.seq(~A: Type, ~B: Type, ~P: Data, ~f: P -> A -> B, +p: P, xs: List<&1, A>) -> List<&1, B>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      f(p, x) <> Sort.pm.seq(~A, ~B, ~P, ~f, p, rest)

# r: a list of k elements split at k / 2; the halves go to the two sides of a parallel let
def Sort.pm.go(~A: Type, ~B: Type, ~P: Data, ~f: P -> A -> B, fl: Nat, small: Bool, +p: P, +k: U32, r: List<&1, A> & List<&1, A>) -> List<&1, B>:
  match fl small:
    case _ True{}:
      (a, b) = r
      List.append(&1, B, Sort.pm.seq(~A, ~B, ~P, ~f, p, a), Sort.pm.seq(~A, ~B, ~P, ~f, p, b))
    case 0n False{}:
      (a, b) = r
      List.append(&1, B, Sort.pm.seq(~A, ~B, ~P, ~f, p, a), Sort.pm.seq(~A, ~B, ~P, ~f, p, b))
    case 1n++q False{}:
      (a, b) = r
      +h1 = U32.shr(k)
      +h2 = U32.sub(k, h1)
      x y = Sort.pm.go(~A, ~B, ~P, ~f, q, U32.is_le(h1, 1), p, h1, Sort.pm.split(A, a, U32.shr(h1), U32.is_zero(U32.shr(h1)))) Sort.pm.go(~A, ~B, ~P, ~f, q, U32.is_le(h2, 1), p, h2, Sort.pm.split(A, b, U32.shr(h2), U32.is_zero(U32.shr(h2))))
      List.append(&1, B, x, y)

def Sort.pm.k(~A: Type, ~B: Type, ~P: Data, ~f: P -> A -> B, +p: P, r: List<&1, A> & U32) -> List<&1, B>:
  (xs, +k) = r
  Sort.pm.go(~A, ~B, ~P, ~f, 32n, U32.is_le(k, 1), p, k, Sort.pm.split(A, xs, U32.shr(k), U32.is_zero(U32.shr(k))))

# f(p, x) for every element, in order, the elements forked in a balanced tree
def Sort.pm(~A: Type, ~B: Type, ~P: Data, ~f: P -> A -> B, +p: P, xs: List<&1, A>) -> List<&1, B>:
  Sort.pm.k(~A, ~B, ~P, ~f, p, Sort.pm.len(A, xs, 0, Nil{}))

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
# included); only the gather is cut to the rows Head keeps. LAWS.bend section 17 proves the
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
