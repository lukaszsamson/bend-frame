# src/chunks.bend -- owned chunk trees: the chunked column representation of the v0.2 engine
# (plans/M_02.txt W5 / D1, DESIGN.md 16.1). No executor wiring here: T5.2 writes the chunked kernel
# wrappers, T5.3 the chunked runner (src/cexec.bend).
#
# A column's rows live in a USER-DEFINED binary tree of owned flat leaves, one tree per 32-bit payload
# kind (monomorphic: CW words for Bool/U32/I32 payloads, validity masks and dictionary codes; CF f32;
# CS Raw strings; a Dictionary column is a CW of codes plus ONE Dict per column):
#   WL{n, d, a}             n rows in the 2^d slots of a (n <= 2^d); slots past n are padding, never read
#   WN{rows, lrows, l, r}   rows = lrows + rows(r), lrows = rows(l) (exact, below the row cap): the
#                           node carries its left child's count, so a walk addresses the right child at
#                           off + lrows without reading the left child twice
# Invariants (LAWS.bend section 21: WFChunks, the shape and counts; WFCFrame below: one shape per
# frame, checked by one lockstep walk at the executor boundary, never per kernel). Grain: leaves of
# 2^G rows, G = Ch.grain() = 14; a column of at most 2^G rows is ONE leaf, its flat buffer moved as is
# (today's flat column exactly: small inputs run today's loops, no copy, no fork).
#
# Parallel shape (AGENT_BRIEF_M2 rule 3): the forks are balanced parallel lets over these user trees
# (rechunk, and T5.2's kernels) or over the frame's column list split in halves (of_frame / to_frame /
# the per-column ops); the leaves run flat tail loops (Kernel.copy_into, Kernel.append, Kernel.range,
# Ch.rng). No Array is split by its ANode, no Array.fork. Builders and flatten are sequential per
# column (one owner of the flat buffer) and fork ACROSS columns.
#
# Idioms (DESIGN.md section 9 and IMPLEMENTING.md W0): helpers above callers, no mutual recursion; a
# walk that must thread state through a tree threads ONE accumulator through nested calls
# (`f(r, f(l, acc))`, Kernel.copy_into's out in flatten, a stack of built trees in remap / decode);
# a build that must open a pair result uses the binary-counter stack and read-ahead leaf loop.
import Base
import ./err.bend as E
import ./dtype.bend as D
import ./kernels.bend as K
import ./column.bend as C
import ./strs.bend as ST

# the grain: leaves of 2^14 rows (DESIGN.md 16.1; S1: grains 13..16 within noise at 1M rows)
def Ch.grain() -> Nat:
  14n

# a tree's shape and counts, without payload: what WFCFrame compares across a frame's columns
type Skel is Data:
  KLeaf{n: U32}
  KNode{rows: U32, lrows: U32, l: Skel, r: Skel}

# a - b, 0 when b >= a
def Ch.ssub(+a: U32, +b: U32) -> U32:
  Bool.pick(U32, U32.is_le(a, b), 0, U32.sub(a, b))

# a + b saturating at 2^32 - 1 (as Cat.sat: the error text of a refused concat names this sum)
def Ch.sat(+a: U32, +b: U32) -> U32:
  +s = U32.add(a, b)
  Bool.pick(U32, U32.is_lt(s, a), 4294967295, s)

# does a + b fit the cap (exact, no wrap: b <= cap - a after a <= cap)
def Ch.fits2(+cap: U32, +a: U32, +b: U32) -> Bool:
  Bool.and(U32.is_le(a, cap), U32.is_le(b, U32.sub(cap, a)))

# the error of a refused sum: Kernel.check_rows' text on the saturating sum (v0.1's Cat.join text)
def Ch.over.k(m: Maybe<&2, E.Err>) -> E.Err:
  match m:
    case Some{e}:
      e
    case None{}:
      E.InvalidOperation{"too many rows"}

def Ch.over(+cap: U32, +a: U32, +b: U32) -> E.Err:
  Ch.over.k(K.Kernel.check_rows.cap(cap, Ch.sat(a, b)))

# trailing zeros of x > 0 (the binary counter's merge count)
def Ch.tz.go(f: Nat, +x: U32, +acc: Nat, odd: Bool) -> Nat:
  match f odd:
    case _ True{}:
      acc
    case 0n False{}:
      acc
    case 1n+p False{}:
      +y = U32.shr(x)
      Ch.tz.go(p, y, 1n+acc, U32.is_ne(U32.and(y, 1), 0))

def Ch.tz(+x: U32) -> Nat:
  Ch.tz.go(32n, x, 0n, U32.is_ne(U32.and(x, 1), 0))

# out[k] = a[off + k] for k < n into a fresh array of 2^d slots padded with z; a is handed BACK
# (answers (out, a)). The loop of Kernel.range with the source returned, so one flat buffer feeds every
# leaf of a build; the reads are spelled as Kernel.range's (LAWS section 21: ch_rng_range).
def Ch.rng.go(~T: Data, f: Nat, +k: U32, +off: U32, out: Array<T>, r: Array<T> & T) -> Array<T> & Array<T>:
  match f:
    case 0n:
      (a, x) = r
      (out, a)
    case 1n+p:
      (a, x) = r
      +j = U32.inc(k)
      Ch.rng.go(~T, p, j, off, Array.set(T, out, k, x), Array.get(T, a, U32.add(off, j)))

def Ch.rng(~T: Data, +n: U32, +d: Nat, +off: U32, a: Array<T>, +z: T) -> Array<T> & Array<T>:
  Ch.rng.go(~T, U32.to_nat(n), 0, off, Array.new(T, d, z), Array.get(T, a, U32.add(off, 0)))

# a gather that hands its source back: out[j] = src[perm[j]] for j < n into 2^d slots; perm is
# consumed (the dictionary remap of a concat: the merge map is read by every leaf)
type GH<-T: Data> is Type:
  GH{out: Array<T>, src: Array<T>}

def Ch.gat.go(~T: Data, n: Nat, +j: U32, so: Array<T> & Array<T>, r: Array<U32> & U32) -> GH<T>:
  match n:
    case 0n:
      (src, out) = so
      (perm, i) = r
      GH{out, src}
    case 1n+p:
      (src, out) = so
      (perm, i) = r
      +j2 = U32.inc(j)
      Ch.gat.go(~T, p, j2, K.Kernel.gather.put(~T, out, j, Array.get(T, src, i)), Array.get(U32, perm, j2))

def Ch.gat(~T: Data, +n: U32, +d: Nat, src: Array<T>, perm: Array<U32>, +z: T) -> GH<T>:
  Ch.gat.go(~T, U32.to_nat(n), 0, (src, Array.new(T, d, z)), Array.get(U32, perm, 0))

# out[i] = the entry of codes[i] for i < n (a Dictionary leaf decoded); the dictionary comes back
def Ch.dec.put(+i: U32, out: Array<String>, r: ST.Dict & String) -> ST.Dict & Array<String>:
  (dict, s) = r
  (dict, Array.set(String, out, i, s))

def Ch.dec.go(f: Nat, +i: U32, st: ST.Dict & Array<String>, r: Array<U32> & U32) -> ST.Dict & Array<String>:
  match f:
    case 0n:
      st
    case 1n+p:
      (dict, out) = st
      (codes, c) = r
      +j = U32.inc(i)
      Ch.dec.go(p, j, Ch.dec.put(i, out, ST.Dict.get(dict, c)), Array.get(U32, codes, j))

def Ch.dec(+n: U32, +d: Nat, codes: Array<U32>, dict: ST.Dict) -> ST.Dict & Array<String>:
  Ch.dec.go(U32.to_nat(n), 0, (dict, Array.new(String, d, "")), Array.get(U32, codes, 0))

# ==== CW: the U32 tree (generated alongside CW/CF/CS from one template: the three copies are the same text) ====

# n rows in the 2^d slots of a (n <= 2^d) | rows = lrows + rows(r), lrows = rows(l)
type CW is Type:
  WL{n: U32, d: Nat, a: Array<U32>}
  WN{rows: U32, lrows: U32, l: CW, r: CW}

# an empty tree: one leaf of 0 rows in one slot
def CW.empty() -> CW:
  WL{0, 0n, Array.new(U32, 0n, 0)}

# the row count; the tree comes back
def CW.rows(t: CW) -> CW & U32:
  match t:
    case WL{+n, d, a}:
      (WL{n, d, a}, n)
    case WN{+rows, lrows, l, r}:
      (WN{rows, lrows, l, r}, rows)

# the leaf count (O(leaves)); the tree comes back
def CW.leaves.j(+rows: U32, +lrows: U32, x: CW & U32, y: CW & U32) -> CW & U32:
  (l, +a) = x
  (r, +b) = y
  (WN{rows, lrows, l, r}, U32.add(a, b))

def CW.leaves(t: CW) -> CW & U32:
  match t:
    case WL{n, d, a}:
      (WL{n, d, a}, 1)
    case WN{+rows, +lrows, l, r}:
      CW.leaves.j(rows, lrows, CW.leaves(l), CW.leaves(r))

# the skeleton (row counts and shape, no payload); the tree comes back
def CW.skel.j(+rows: U32, +lrows: U32, x: CW & Skel, y: CW & Skel) -> CW & Skel:
  (l, sl) = x
  (r, sr) = y
  (WN{rows, lrows, l, r}, KNode{rows, lrows, sl, sr})

def CW.skel(t: CW) -> CW & Skel:
  match t:
    case WL{+n, d, a}:
      (WL{n, d, a}, KLeaf{n})
    case WN{+rows, +lrows, l, r}:
      CW.skel.j(rows, lrows, CW.skel(l), CW.skel(r))

# the lockstep shape walk: does the tree have the skeleton s (same shape, same counts at every leaf
# and node)? The tree comes back. One O(leaves) walk at the executor boundary (WFCFrame), never per kernel.
def CW.fits.j(ok: Bool, +rows: U32, +lrows: U32, x: CW & Bool, y: CW & Bool) -> CW & Bool:
  (l, a) = x
  (r, b) = y
  (WN{rows, lrows, l, r}, Bool.and(ok, Bool.and(a, b)))

def CW.fits(t: CW, s: Skel) -> CW & Bool:
  match t s:
    case WL{+n, d, a} KLeaf{+m}:
      (WL{n, d, a}, U32.is_eq(n, m))
    case WL{n, d, a} KNode{rows2, lrows2, sl, sr}:
      (WL{n, d, a}, False{})
    case WN{rows, lrows, l, r} KLeaf{m}:
      (WN{rows, lrows, l, r}, False{})
    case WN{+rows, +lrows, l, r} KNode{+rows2, +lrows2, sl, sr}:
      CW.fits.j(Bool.and(U32.is_eq(rows, rows2), U32.is_eq(lrows, lrows2)), rows, lrows, CW.fits(l, sl), CW.fits(r, sr))

# ---- build from a flat buffer: leaves of 2^g rows (the last one partial) folded into a balanced tree ----

type CWS is Type:
  CWNil{}
  CWCons{rows: U32, c: CW, next: CWS}

# push c (rows rows) and merge the top m times: the binary counter (leaf i merges tz(i + 1) times)
def CWS.merge(m: Nat, +rows: U32, c: CW, s: CWS) -> CWS:
  match m s:
    case 0n CWNil{}:
      CWCons{rows, c, CWNil{}}
    case 0n CWCons{r2, c2, nx}:
      CWCons{rows, c, CWCons{r2, c2, nx}}
    case 1n+p CWNil{}:
      CWCons{rows, c, CWNil{}}
    case 1n+p CWCons{+r2, c2, nx}:
      +t = U32.add(r2, rows)
      CWS.merge(p, t, WN{t, r2, c2, c}, nx)

def CWS.push(+i: U32, +rows: U32, c: CW, s: CWS) -> CWS:
  CWS.merge(Ch.tz(U32.inc(i)), rows, c, s)

# fold what is left on the stack into one tree (the earlier rows on the left); structural, no fuel
def CWS.collapse.go(s: CWS, +rows: U32, c: CW) -> CW:
  match s:
    case CWNil{}:
      c
    case CWCons{+r2, c2, nx}:
      +t = U32.add(r2, rows)
      CWS.collapse.go(nx, t, WN{t, r2, c2, c})

def CWS.collapse(s: CWS) -> CW:
  match s:
    case CWNil{}:
      CW.empty()
    case CWCons{+rows, c, nx}:
      CWS.collapse.go(nx, rows, c)

# the leaf loop. r = (out, a): the range copy of the current leaf (rows off .. off + 2^g when `more`,
# else off .. n) and the source handed back; the next copy is made in the recursive call's argument
# list (read-ahead). Out of fuel (never: fuel = n >> g is enough), the rest is one leaf of the source's
# depth (rows - off <= rows <= 2^ds: correct whatever the fuel, so the law needs no fuel argument).
def CW.of.rest(+i: U32, +off: U32, +n: U32, +ds: Nat, s: CWS, r: Array<U32> & Array<U32>) -> CWS:
  (out, a) = r
  CWS.push(i, U32.sub(n, off), WL{U32.sub(n, off), ds, out}, s)

def CW.of.go(f: Nat, more: Bool, +i: U32, +off: U32, +n: U32, +g: Nat, +ds: Nat, s: CWS, r: Array<U32> & Array<U32>) -> CWS:
  match f more:
    case _ False{}:
      (out, a) = r
      CWS.push(i, U32.sub(n, off), WL{U32.sub(n, off), g, out}, s)
    case 0n True{}:
      (out, a) = r
      +o2 = U32.add(off, U32.shln(1, g))
      CW.of.rest(U32.inc(i), o2, n, ds, CWS.push(i, U32.shln(1, g), WL{U32.shln(1, g), g, out}, s), Ch.rng(~U32, U32.sub(n, o2), ds, o2, a, 0))
    case 1n+p True{}:
      (out, a) = r
      +o2 = U32.add(off, U32.shln(1, g))
      +more2 = U32.is_lt(U32.shln(1, g), U32.sub(n, o2))
      CW.of.go(p, more2, U32.inc(i), o2, n, g, ds, CWS.push(i, U32.shln(1, g), WL{U32.shln(1, g), g, out}, s), Ch.rng(~U32, Bool.pick(U32, more2, U32.shln(1, g), U32.sub(n, o2)), g, o2, a, 0))

def CW.of.k(small: Bool, +n: U32, +ds: Nat, +g: Nat, src: Array<U32>) -> CW:
  match small:
    case True{}:
      WL{n, ds, src}
    case False{}:
      +more = U32.is_lt(U32.shln(1, g), U32.sub(n, 0))
      CWS.collapse(CW.of.go(U32.to_nat(U32.shrn(n, g)), more, 0, 0, n, g, ds, CWNil{}, Ch.rng(~U32, Bool.pick(U32, more, U32.shln(1, g), U32.sub(n, 0)), g, 0, src, 0)))

# the chunk tree of the first n rows of src (2^ds slots, n <= 2^ds), leaves of 2^g rows: under 2^g + 1
# rows the buffer itself becomes the one leaf (no copy: today's flat column exactly); src is consumed
def CW.of(+n: U32, +ds: Nat, +g: Nat, src: Array<U32>) -> CW:
  CW.of.k(U32.is_le(n, U32.shln(1, g)), n, ds, g, src)

# ---- flatten: one Kernel.copy_into per leaf, left to right (lrows addresses the right child) ----

def CW.flat(t: CW, +off: U32, out: Array<U32>) -> Array<U32>:
  match t:
    case WL{+n, d, a}:
      K.Kernel.copy_into(~U32, n, off, out, a)
    case WN{rows, +lrows, l, r}:
      CW.flat(r, U32.add(off, lrows), CW.flat(l, off, out))

# the rows of t in order in a fresh buffer of 2^dd slots (rows <= 2^dd); t is consumed
def CW.flatten(+dd: Nat, t: CW) -> Array<U32>:
  CW.flat(t, 0, Array.new(U32, dd, 0))

# the depth a flat column of this tree takes: a leaf keeps its own (it is moved, not copied)
def CW.depth(t: CW) -> CW & Nat:
  match t:
    case WL{+n, +d, a}:
      (WL{n, d, a}, d)
    case WN{+rows, lrows, l, r}:
      (WN{rows, lrows, l, r}, K.Kernel.depth_for(U32.max(rows, 1)))

def CW.to_flat.l(same: Bool, +n: U32, +dd: Nat, a: Array<U32>) -> Array<U32>:
  match same:
    case True{}:
      a
    case False{}:
      K.Kernel.copy_into(~U32, n, 0, Array.new(U32, dd, 0), a)

# the flat buffer of 2^dd slots: a leaf of depth dd is moved as is, anything else is flattened
def CW.to_flat(+dd: Nat, t: CW) -> Array<U32>:
  match t:
    case WL{+n, +d, a}:
      CW.to_flat.l(Nat.is_eq(d, dd), n, dd, a)
    case WN{rows, lrows, l, r}:
      CW.flatten(dd, WN{rows, lrows, l, r})

# ---- rechunk: sibling leaves whose rows fit 2^g merge into one leaf (decided by row counts only) ----

def CW.rc.leaf(fits: Bool, +g: Nat, +rows: U32, +lrows: U32, +n1: U32, +d1: Nat, a1: Array<U32>, +n2: U32, +d2: Nat, a2: Array<U32>) -> CW:
  match fits:
    case True{}:
      WL{rows, g, K.Kernel.append(~U32, n1, n2, g, a1, a2, 0)}
    case False{}:
      WN{rows, lrows, WL{n1, d1, a1}, WL{n2, d2, a2}}

def CW.rc.join(+g: Nat, +rows: U32, +lrows: U32, x: CW, y: CW) -> CW:
  match x y:
    case WL{+n1, +d1, a1} WL{+n2, +d2, a2}:
      CW.rc.leaf(U32.is_le(rows, U32.shln(1, g)), g, rows, lrows, n1, d1, a1, n2, d2, a2)
    case WL{n1, d1, a1} WN{r2, l2, xl, xr}:
      WN{rows, lrows, WL{n1, d1, a1}, WN{r2, l2, xl, xr}}
    case WN{r1, l1, yl, yr} WL{n2, d2, a2}:
      WN{rows, lrows, WN{r1, l1, yl, yr}, WL{n2, d2, a2}}
    case WN{r1, l1, yl, yr} WN{r2, l2, xl, xr}:
      WN{rows, lrows, WN{r1, l1, yl, yr}, WN{r2, l2, xl, xr}}

# bottom-up, one balanced fork per node; copies at most the rows of the merged leaves
def CW.rechunk(+g: Nat, t: CW) -> CW:
  match t:
    case WL{n, d, a}:
      WL{n, d, a}
    case WN{+rows, +lrows, l, r}:
      x y = CW.rechunk(g, l) CW.rechunk(g, r)
      CW.rc.join(g, rows, lrows, x, y)

# ---- cut: head (drop the leaves past h, shorten the boundary leaf: no copy) and drop (the boundary leaf
# re-cut by one range copy of its kept rows) ----

def CW.head.j(left: Bool, +lrows: U32, x: CW, y: CW & U32) -> CW:
  match left:
    case True{}:
      x
    case False{}:
      (r, +ry) = y
      WN{U32.add(lrows, ry), lrows, x, r}

# the first min(h, rows) rows; O(nodes), the kept leaves are not copied
def CW.head(t: CW, +h: U32) -> CW:
  match t:
    case WL{n, d, a}:
      WL{U32.min(h, n), d, a}
    case WN{rows, +lrows, l, r}:
      CW.head.j(U32.is_le(h, lrows), lrows, CW.head(l, h), CW.rows(CW.head(r, Ch.ssub(h, lrows))))

def CW.drop.l(z: Bool, all: Bool, +off: U32, +n: U32, +d: Nat, a: Array<U32>) -> CW:
  match z all:
    case True{} _:
      WL{n, d, a}
    case False{} True{}:
      CW.empty()
    case False{} False{}:
      WL{U32.sub(n, off), d, K.Kernel.range(~U32, U32.sub(n, off), d, off, a, 0)}

def CW.drop.j(right: Bool, +rows: U32, +off: U32, x: CW & U32, y: CW) -> CW:
  match right:
    case True{}:
      y
    case False{}:
      (l, +rl) = x
      WN{U32.sub(rows, off), rl, l, y}

# rows off .. rows - 1 (all of them when off = 0); the boundary leaf is copied, the others are kept
def CW.drop(t: CW, +off: U32) -> CW:
  match t:
    case WL{+n, +d, a}:
      CW.drop.l(U32.is_zero(off), U32.is_le(n, off), off, n, d, a)
    case WN{+rows, +lrows, l, r}:
      CW.drop.j(U32.is_le(lrows, off), rows, off, CW.rows(CW.drop(l, U32.min(off, lrows))), CW.drop(r, Ch.ssub(off, lrows)))

# rows off .. off + len - 1 (clipped to the rows)
def CW.slice(t: CW, +off: U32, +len: U32) -> CW:
  CW.head(CW.drop(t, off), len)

# ---- concat: one node over the two trees (O(1)); the row cap on the exact sum ----

def CW.concat.k(ok: Bool, +cap: U32, +ra: U32, +rb: U32, a: CW, b: CW) -> E.ResT(CW):
  match ok:
    case True{}:
      Done{WN{U32.add(ra, rb), ra, a, b}}
    case False{}:
      Fail{Ch.over(cap, ra, rb)}

def CW.concat.b(+cap: U32, +ra: U32, b: CW & U32, a: CW) -> E.ResT(CW):
  (b2, +rb) = b
  CW.concat.k(Ch.fits2(cap, ra, rb), cap, ra, rb, a, b2)

def CW.concat.a(+cap: U32, a: CW & U32, b: CW) -> E.ResT(CW):
  (a2, +ra) = a
  CW.concat.b(cap, ra, CW.rows(b), a2)

# a's rows then b's rows, refused (InvalidOperation, the v0.1 text) past cap rows
def CW.concat.cap(+cap: U32, a: CW, b: CW) -> E.ResT(CW):
  CW.concat.a(cap, CW.rows(a), b)

def CW.concat(a: CW, b: CW) -> E.ResT(CW):
  CW.concat.cap(K.Kernel.max_rows(), a, b)

# ==== CF: the F32 tree (generated alongside CW/CF/CS from one template: the three copies are the same text) ====

# n rows in the 2^d slots of a (n <= 2^d) | rows = lrows + rows(r), lrows = rows(l)
type CF is Type:
  FL{n: U32, d: Nat, a: Array<F32>}
  FN{rows: U32, lrows: U32, l: CF, r: CF}

# an empty tree: one leaf of 0 rows in one slot
def CF.empty() -> CF:
  FL{0, 0n, Array.new(F32, 0n, 0.0)}

# the row count; the tree comes back
def CF.rows(t: CF) -> CF & U32:
  match t:
    case FL{+n, d, a}:
      (FL{n, d, a}, n)
    case FN{+rows, lrows, l, r}:
      (FN{rows, lrows, l, r}, rows)

# the leaf count (O(leaves)); the tree comes back
def CF.leaves.j(+rows: U32, +lrows: U32, x: CF & U32, y: CF & U32) -> CF & U32:
  (l, +a) = x
  (r, +b) = y
  (FN{rows, lrows, l, r}, U32.add(a, b))

def CF.leaves(t: CF) -> CF & U32:
  match t:
    case FL{n, d, a}:
      (FL{n, d, a}, 1)
    case FN{+rows, +lrows, l, r}:
      CF.leaves.j(rows, lrows, CF.leaves(l), CF.leaves(r))

# the skeleton (row counts and shape, no payload); the tree comes back
def CF.skel.j(+rows: U32, +lrows: U32, x: CF & Skel, y: CF & Skel) -> CF & Skel:
  (l, sl) = x
  (r, sr) = y
  (FN{rows, lrows, l, r}, KNode{rows, lrows, sl, sr})

def CF.skel(t: CF) -> CF & Skel:
  match t:
    case FL{+n, d, a}:
      (FL{n, d, a}, KLeaf{n})
    case FN{+rows, +lrows, l, r}:
      CF.skel.j(rows, lrows, CF.skel(l), CF.skel(r))

# the lockstep shape walk: does the tree have the skeleton s (same shape, same counts at every leaf
# and node)? The tree comes back. One O(leaves) walk at the executor boundary (WFCFrame), never per kernel.
def CF.fits.j(ok: Bool, +rows: U32, +lrows: U32, x: CF & Bool, y: CF & Bool) -> CF & Bool:
  (l, a) = x
  (r, b) = y
  (FN{rows, lrows, l, r}, Bool.and(ok, Bool.and(a, b)))

def CF.fits(t: CF, s: Skel) -> CF & Bool:
  match t s:
    case FL{+n, d, a} KLeaf{+m}:
      (FL{n, d, a}, U32.is_eq(n, m))
    case FL{n, d, a} KNode{rows2, lrows2, sl, sr}:
      (FL{n, d, a}, False{})
    case FN{rows, lrows, l, r} KLeaf{m}:
      (FN{rows, lrows, l, r}, False{})
    case FN{+rows, +lrows, l, r} KNode{+rows2, +lrows2, sl, sr}:
      CF.fits.j(Bool.and(U32.is_eq(rows, rows2), U32.is_eq(lrows, lrows2)), rows, lrows, CF.fits(l, sl), CF.fits(r, sr))

# ---- build from a flat buffer: leaves of 2^g rows (the last one partial) folded into a balanced tree ----

type CFS is Type:
  CFNil{}
  CFCons{rows: U32, c: CF, next: CFS}

# push c (rows rows) and merge the top m times: the binary counter (leaf i merges tz(i + 1) times)
def CFS.merge(m: Nat, +rows: U32, c: CF, s: CFS) -> CFS:
  match m s:
    case 0n CFNil{}:
      CFCons{rows, c, CFNil{}}
    case 0n CFCons{r2, c2, nx}:
      CFCons{rows, c, CFCons{r2, c2, nx}}
    case 1n+p CFNil{}:
      CFCons{rows, c, CFNil{}}
    case 1n+p CFCons{+r2, c2, nx}:
      +t = U32.add(r2, rows)
      CFS.merge(p, t, FN{t, r2, c2, c}, nx)

def CFS.push(+i: U32, +rows: U32, c: CF, s: CFS) -> CFS:
  CFS.merge(Ch.tz(U32.inc(i)), rows, c, s)

# fold what is left on the stack into one tree (the earlier rows on the left); structural, no fuel
def CFS.collapse.go(s: CFS, +rows: U32, c: CF) -> CF:
  match s:
    case CFNil{}:
      c
    case CFCons{+r2, c2, nx}:
      +t = U32.add(r2, rows)
      CFS.collapse.go(nx, t, FN{t, r2, c2, c})

def CFS.collapse(s: CFS) -> CF:
  match s:
    case CFNil{}:
      CF.empty()
    case CFCons{+rows, c, nx}:
      CFS.collapse.go(nx, rows, c)

# the leaf loop. r = (out, a): the range copy of the current leaf (rows off .. off + 2^g when `more`,
# else off .. n) and the source handed back; the next copy is made in the recursive call's argument
# list (read-ahead). Out of fuel (never: fuel = n >> g is enough), the rest is one leaf of the source's
# depth (rows - off <= rows <= 2^ds: correct whatever the fuel, so the law needs no fuel argument).
def CF.of.rest(+i: U32, +off: U32, +n: U32, +ds: Nat, s: CFS, r: Array<F32> & Array<F32>) -> CFS:
  (out, a) = r
  CFS.push(i, U32.sub(n, off), FL{U32.sub(n, off), ds, out}, s)

def CF.of.go(f: Nat, more: Bool, +i: U32, +off: U32, +n: U32, +g: Nat, +ds: Nat, s: CFS, r: Array<F32> & Array<F32>) -> CFS:
  match f more:
    case _ False{}:
      (out, a) = r
      CFS.push(i, U32.sub(n, off), FL{U32.sub(n, off), g, out}, s)
    case 0n True{}:
      (out, a) = r
      +o2 = U32.add(off, U32.shln(1, g))
      CF.of.rest(U32.inc(i), o2, n, ds, CFS.push(i, U32.shln(1, g), FL{U32.shln(1, g), g, out}, s), Ch.rng(~F32, U32.sub(n, o2), ds, o2, a, 0.0))
    case 1n+p True{}:
      (out, a) = r
      +o2 = U32.add(off, U32.shln(1, g))
      +more2 = U32.is_lt(U32.shln(1, g), U32.sub(n, o2))
      CF.of.go(p, more2, U32.inc(i), o2, n, g, ds, CFS.push(i, U32.shln(1, g), FL{U32.shln(1, g), g, out}, s), Ch.rng(~F32, Bool.pick(U32, more2, U32.shln(1, g), U32.sub(n, o2)), g, o2, a, 0.0))

def CF.of.k(small: Bool, +n: U32, +ds: Nat, +g: Nat, src: Array<F32>) -> CF:
  match small:
    case True{}:
      FL{n, ds, src}
    case False{}:
      +more = U32.is_lt(U32.shln(1, g), U32.sub(n, 0))
      CFS.collapse(CF.of.go(U32.to_nat(U32.shrn(n, g)), more, 0, 0, n, g, ds, CFNil{}, Ch.rng(~F32, Bool.pick(U32, more, U32.shln(1, g), U32.sub(n, 0)), g, 0, src, 0.0)))

# the chunk tree of the first n rows of src (2^ds slots, n <= 2^ds), leaves of 2^g rows: under 2^g + 1
# rows the buffer itself becomes the one leaf (no copy: today's flat column exactly); src is consumed
def CF.of(+n: U32, +ds: Nat, +g: Nat, src: Array<F32>) -> CF:
  CF.of.k(U32.is_le(n, U32.shln(1, g)), n, ds, g, src)

# ---- flatten: one Kernel.copy_into per leaf, left to right (lrows addresses the right child) ----

def CF.flat(t: CF, +off: U32, out: Array<F32>) -> Array<F32>:
  match t:
    case FL{+n, d, a}:
      K.Kernel.copy_into(~F32, n, off, out, a)
    case FN{rows, +lrows, l, r}:
      CF.flat(r, U32.add(off, lrows), CF.flat(l, off, out))

# the rows of t in order in a fresh buffer of 2^dd slots (rows <= 2^dd); t is consumed
def CF.flatten(+dd: Nat, t: CF) -> Array<F32>:
  CF.flat(t, 0, Array.new(F32, dd, 0.0))

# the depth a flat column of this tree takes: a leaf keeps its own (it is moved, not copied)
def CF.depth(t: CF) -> CF & Nat:
  match t:
    case FL{+n, +d, a}:
      (FL{n, d, a}, d)
    case FN{+rows, lrows, l, r}:
      (FN{rows, lrows, l, r}, K.Kernel.depth_for(U32.max(rows, 1)))

def CF.to_flat.l(same: Bool, +n: U32, +dd: Nat, a: Array<F32>) -> Array<F32>:
  match same:
    case True{}:
      a
    case False{}:
      K.Kernel.copy_into(~F32, n, 0, Array.new(F32, dd, 0.0), a)

# the flat buffer of 2^dd slots: a leaf of depth dd is moved as is, anything else is flattened
def CF.to_flat(+dd: Nat, t: CF) -> Array<F32>:
  match t:
    case FL{+n, +d, a}:
      CF.to_flat.l(Nat.is_eq(d, dd), n, dd, a)
    case FN{rows, lrows, l, r}:
      CF.flatten(dd, FN{rows, lrows, l, r})

# ---- rechunk: sibling leaves whose rows fit 2^g merge into one leaf (decided by row counts only) ----

def CF.rc.leaf(fits: Bool, +g: Nat, +rows: U32, +lrows: U32, +n1: U32, +d1: Nat, a1: Array<F32>, +n2: U32, +d2: Nat, a2: Array<F32>) -> CF:
  match fits:
    case True{}:
      FL{rows, g, K.Kernel.append(~F32, n1, n2, g, a1, a2, 0.0)}
    case False{}:
      FN{rows, lrows, FL{n1, d1, a1}, FL{n2, d2, a2}}

def CF.rc.join(+g: Nat, +rows: U32, +lrows: U32, x: CF, y: CF) -> CF:
  match x y:
    case FL{+n1, +d1, a1} FL{+n2, +d2, a2}:
      CF.rc.leaf(U32.is_le(rows, U32.shln(1, g)), g, rows, lrows, n1, d1, a1, n2, d2, a2)
    case FL{n1, d1, a1} FN{r2, l2, xl, xr}:
      FN{rows, lrows, FL{n1, d1, a1}, FN{r2, l2, xl, xr}}
    case FN{r1, l1, yl, yr} FL{n2, d2, a2}:
      FN{rows, lrows, FN{r1, l1, yl, yr}, FL{n2, d2, a2}}
    case FN{r1, l1, yl, yr} FN{r2, l2, xl, xr}:
      FN{rows, lrows, FN{r1, l1, yl, yr}, FN{r2, l2, xl, xr}}

# bottom-up, one balanced fork per node; copies at most the rows of the merged leaves
def CF.rechunk(+g: Nat, t: CF) -> CF:
  match t:
    case FL{n, d, a}:
      FL{n, d, a}
    case FN{+rows, +lrows, l, r}:
      x y = CF.rechunk(g, l) CF.rechunk(g, r)
      CF.rc.join(g, rows, lrows, x, y)

# ---- cut: head (drop the leaves past h, shorten the boundary leaf: no copy) and drop (the boundary leaf
# re-cut by one range copy of its kept rows) ----

def CF.head.j(left: Bool, +lrows: U32, x: CF, y: CF & U32) -> CF:
  match left:
    case True{}:
      x
    case False{}:
      (r, +ry) = y
      FN{U32.add(lrows, ry), lrows, x, r}

# the first min(h, rows) rows; O(nodes), the kept leaves are not copied
def CF.head(t: CF, +h: U32) -> CF:
  match t:
    case FL{n, d, a}:
      FL{U32.min(h, n), d, a}
    case FN{rows, +lrows, l, r}:
      CF.head.j(U32.is_le(h, lrows), lrows, CF.head(l, h), CF.rows(CF.head(r, Ch.ssub(h, lrows))))

def CF.drop.l(z: Bool, all: Bool, +off: U32, +n: U32, +d: Nat, a: Array<F32>) -> CF:
  match z all:
    case True{} _:
      FL{n, d, a}
    case False{} True{}:
      CF.empty()
    case False{} False{}:
      FL{U32.sub(n, off), d, K.Kernel.range(~F32, U32.sub(n, off), d, off, a, 0.0)}

def CF.drop.j(right: Bool, +rows: U32, +off: U32, x: CF & U32, y: CF) -> CF:
  match right:
    case True{}:
      y
    case False{}:
      (l, +rl) = x
      FN{U32.sub(rows, off), rl, l, y}

# rows off .. rows - 1 (all of them when off = 0); the boundary leaf is copied, the others are kept
def CF.drop(t: CF, +off: U32) -> CF:
  match t:
    case FL{+n, +d, a}:
      CF.drop.l(U32.is_zero(off), U32.is_le(n, off), off, n, d, a)
    case FN{+rows, +lrows, l, r}:
      CF.drop.j(U32.is_le(lrows, off), rows, off, CF.rows(CF.drop(l, U32.min(off, lrows))), CF.drop(r, Ch.ssub(off, lrows)))

# rows off .. off + len - 1 (clipped to the rows)
def CF.slice(t: CF, +off: U32, +len: U32) -> CF:
  CF.head(CF.drop(t, off), len)

# ---- concat: one node over the two trees (O(1)); the row cap on the exact sum ----

def CF.concat.k(ok: Bool, +cap: U32, +ra: U32, +rb: U32, a: CF, b: CF) -> E.ResT(CF):
  match ok:
    case True{}:
      Done{FN{U32.add(ra, rb), ra, a, b}}
    case False{}:
      Fail{Ch.over(cap, ra, rb)}

def CF.concat.b(+cap: U32, +ra: U32, b: CF & U32, a: CF) -> E.ResT(CF):
  (b2, +rb) = b
  CF.concat.k(Ch.fits2(cap, ra, rb), cap, ra, rb, a, b2)

def CF.concat.a(+cap: U32, a: CF & U32, b: CF) -> E.ResT(CF):
  (a2, +ra) = a
  CF.concat.b(cap, ra, CF.rows(b), a2)

# a's rows then b's rows, refused (InvalidOperation, the v0.1 text) past cap rows
def CF.concat.cap(+cap: U32, a: CF, b: CF) -> E.ResT(CF):
  CF.concat.a(cap, CF.rows(a), b)

def CF.concat(a: CF, b: CF) -> E.ResT(CF):
  CF.concat.cap(K.Kernel.max_rows(), a, b)

# ==== CS: the String tree (generated alongside CW/CF/CS from one template: the three copies are the same text) ====

# n rows in the 2^d slots of a (n <= 2^d) | rows = lrows + rows(r), lrows = rows(l)
type CS is Type:
  SL{n: U32, d: Nat, a: Array<String>}
  SN{rows: U32, lrows: U32, l: CS, r: CS}

# an empty tree: one leaf of 0 rows in one slot
def CS.empty() -> CS:
  SL{0, 0n, Array.new(String, 0n, "")}

# the row count; the tree comes back
def CS.rows(t: CS) -> CS & U32:
  match t:
    case SL{+n, d, a}:
      (SL{n, d, a}, n)
    case SN{+rows, lrows, l, r}:
      (SN{rows, lrows, l, r}, rows)

# the leaf count (O(leaves)); the tree comes back
def CS.leaves.j(+rows: U32, +lrows: U32, x: CS & U32, y: CS & U32) -> CS & U32:
  (l, +a) = x
  (r, +b) = y
  (SN{rows, lrows, l, r}, U32.add(a, b))

def CS.leaves(t: CS) -> CS & U32:
  match t:
    case SL{n, d, a}:
      (SL{n, d, a}, 1)
    case SN{+rows, +lrows, l, r}:
      CS.leaves.j(rows, lrows, CS.leaves(l), CS.leaves(r))

# the skeleton (row counts and shape, no payload); the tree comes back
def CS.skel.j(+rows: U32, +lrows: U32, x: CS & Skel, y: CS & Skel) -> CS & Skel:
  (l, sl) = x
  (r, sr) = y
  (SN{rows, lrows, l, r}, KNode{rows, lrows, sl, sr})

def CS.skel(t: CS) -> CS & Skel:
  match t:
    case SL{+n, d, a}:
      (SL{n, d, a}, KLeaf{n})
    case SN{+rows, +lrows, l, r}:
      CS.skel.j(rows, lrows, CS.skel(l), CS.skel(r))

# the lockstep shape walk: does the tree have the skeleton s (same shape, same counts at every leaf
# and node)? The tree comes back. One O(leaves) walk at the executor boundary (WFCFrame), never per kernel.
def CS.fits.j(ok: Bool, +rows: U32, +lrows: U32, x: CS & Bool, y: CS & Bool) -> CS & Bool:
  (l, a) = x
  (r, b) = y
  (SN{rows, lrows, l, r}, Bool.and(ok, Bool.and(a, b)))

def CS.fits(t: CS, s: Skel) -> CS & Bool:
  match t s:
    case SL{+n, d, a} KLeaf{+m}:
      (SL{n, d, a}, U32.is_eq(n, m))
    case SL{n, d, a} KNode{rows2, lrows2, sl, sr}:
      (SL{n, d, a}, False{})
    case SN{rows, lrows, l, r} KLeaf{m}:
      (SN{rows, lrows, l, r}, False{})
    case SN{+rows, +lrows, l, r} KNode{+rows2, +lrows2, sl, sr}:
      CS.fits.j(Bool.and(U32.is_eq(rows, rows2), U32.is_eq(lrows, lrows2)), rows, lrows, CS.fits(l, sl), CS.fits(r, sr))

# ---- build from a flat buffer: leaves of 2^g rows (the last one partial) folded into a balanced tree ----

type CSS is Type:
  CSNil{}
  CSCons{rows: U32, c: CS, next: CSS}

# push c (rows rows) and merge the top m times: the binary counter (leaf i merges tz(i + 1) times)
def CSS.merge(m: Nat, +rows: U32, c: CS, s: CSS) -> CSS:
  match m s:
    case 0n CSNil{}:
      CSCons{rows, c, CSNil{}}
    case 0n CSCons{r2, c2, nx}:
      CSCons{rows, c, CSCons{r2, c2, nx}}
    case 1n+p CSNil{}:
      CSCons{rows, c, CSNil{}}
    case 1n+p CSCons{+r2, c2, nx}:
      +t = U32.add(r2, rows)
      CSS.merge(p, t, SN{t, r2, c2, c}, nx)

def CSS.push(+i: U32, +rows: U32, c: CS, s: CSS) -> CSS:
  CSS.merge(Ch.tz(U32.inc(i)), rows, c, s)

# fold what is left on the stack into one tree (the earlier rows on the left); structural, no fuel
def CSS.collapse.go(s: CSS, +rows: U32, c: CS) -> CS:
  match s:
    case CSNil{}:
      c
    case CSCons{+r2, c2, nx}:
      +t = U32.add(r2, rows)
      CSS.collapse.go(nx, t, SN{t, r2, c2, c})

def CSS.collapse(s: CSS) -> CS:
  match s:
    case CSNil{}:
      CS.empty()
    case CSCons{+rows, c, nx}:
      CSS.collapse.go(nx, rows, c)

# the leaf loop. r = (out, a): the range copy of the current leaf (rows off .. off + 2^g when `more`,
# else off .. n) and the source handed back; the next copy is made in the recursive call's argument
# list (read-ahead). Out of fuel (never: fuel = n >> g is enough), the rest is one leaf of the source's
# depth (rows - off <= rows <= 2^ds: correct whatever the fuel, so the law needs no fuel argument).
def CS.of.rest(+i: U32, +off: U32, +n: U32, +ds: Nat, s: CSS, r: Array<String> & Array<String>) -> CSS:
  (out, a) = r
  CSS.push(i, U32.sub(n, off), SL{U32.sub(n, off), ds, out}, s)

def CS.of.go(f: Nat, more: Bool, +i: U32, +off: U32, +n: U32, +g: Nat, +ds: Nat, s: CSS, r: Array<String> & Array<String>) -> CSS:
  match f more:
    case _ False{}:
      (out, a) = r
      CSS.push(i, U32.sub(n, off), SL{U32.sub(n, off), g, out}, s)
    case 0n True{}:
      (out, a) = r
      +o2 = U32.add(off, U32.shln(1, g))
      CS.of.rest(U32.inc(i), o2, n, ds, CSS.push(i, U32.shln(1, g), SL{U32.shln(1, g), g, out}, s), Ch.rng(~String, U32.sub(n, o2), ds, o2, a, ""))
    case 1n+p True{}:
      (out, a) = r
      +o2 = U32.add(off, U32.shln(1, g))
      +more2 = U32.is_lt(U32.shln(1, g), U32.sub(n, o2))
      CS.of.go(p, more2, U32.inc(i), o2, n, g, ds, CSS.push(i, U32.shln(1, g), SL{U32.shln(1, g), g, out}, s), Ch.rng(~String, Bool.pick(U32, more2, U32.shln(1, g), U32.sub(n, o2)), g, o2, a, ""))

def CS.of.k(small: Bool, +n: U32, +ds: Nat, +g: Nat, src: Array<String>) -> CS:
  match small:
    case True{}:
      SL{n, ds, src}
    case False{}:
      +more = U32.is_lt(U32.shln(1, g), U32.sub(n, 0))
      CSS.collapse(CS.of.go(U32.to_nat(U32.shrn(n, g)), more, 0, 0, n, g, ds, CSNil{}, Ch.rng(~String, Bool.pick(U32, more, U32.shln(1, g), U32.sub(n, 0)), g, 0, src, "")))

# the chunk tree of the first n rows of src (2^ds slots, n <= 2^ds), leaves of 2^g rows: under 2^g + 1
# rows the buffer itself becomes the one leaf (no copy: today's flat column exactly); src is consumed
def CS.of(+n: U32, +ds: Nat, +g: Nat, src: Array<String>) -> CS:
  CS.of.k(U32.is_le(n, U32.shln(1, g)), n, ds, g, src)

# ---- flatten: one Kernel.copy_into per leaf, left to right (lrows addresses the right child) ----

def CS.flat(t: CS, +off: U32, out: Array<String>) -> Array<String>:
  match t:
    case SL{+n, d, a}:
      K.Kernel.copy_into(~String, n, off, out, a)
    case SN{rows, +lrows, l, r}:
      CS.flat(r, U32.add(off, lrows), CS.flat(l, off, out))

# the rows of t in order in a fresh buffer of 2^dd slots (rows <= 2^dd); t is consumed
def CS.flatten(+dd: Nat, t: CS) -> Array<String>:
  CS.flat(t, 0, Array.new(String, dd, ""))

# the depth a flat column of this tree takes: a leaf keeps its own (it is moved, not copied)
def CS.depth(t: CS) -> CS & Nat:
  match t:
    case SL{+n, +d, a}:
      (SL{n, d, a}, d)
    case SN{+rows, lrows, l, r}:
      (SN{rows, lrows, l, r}, K.Kernel.depth_for(U32.max(rows, 1)))

def CS.to_flat.l(same: Bool, +n: U32, +dd: Nat, a: Array<String>) -> Array<String>:
  match same:
    case True{}:
      a
    case False{}:
      K.Kernel.copy_into(~String, n, 0, Array.new(String, dd, ""), a)

# the flat buffer of 2^dd slots: a leaf of depth dd is moved as is, anything else is flattened
def CS.to_flat(+dd: Nat, t: CS) -> Array<String>:
  match t:
    case SL{+n, +d, a}:
      CS.to_flat.l(Nat.is_eq(d, dd), n, dd, a)
    case SN{rows, lrows, l, r}:
      CS.flatten(dd, SN{rows, lrows, l, r})

# ---- rechunk: sibling leaves whose rows fit 2^g merge into one leaf (decided by row counts only) ----

def CS.rc.leaf(fits: Bool, +g: Nat, +rows: U32, +lrows: U32, +n1: U32, +d1: Nat, a1: Array<String>, +n2: U32, +d2: Nat, a2: Array<String>) -> CS:
  match fits:
    case True{}:
      SL{rows, g, K.Kernel.append(~String, n1, n2, g, a1, a2, "")}
    case False{}:
      SN{rows, lrows, SL{n1, d1, a1}, SL{n2, d2, a2}}

def CS.rc.join(+g: Nat, +rows: U32, +lrows: U32, x: CS, y: CS) -> CS:
  match x y:
    case SL{+n1, +d1, a1} SL{+n2, +d2, a2}:
      CS.rc.leaf(U32.is_le(rows, U32.shln(1, g)), g, rows, lrows, n1, d1, a1, n2, d2, a2)
    case SL{n1, d1, a1} SN{r2, l2, xl, xr}:
      SN{rows, lrows, SL{n1, d1, a1}, SN{r2, l2, xl, xr}}
    case SN{r1, l1, yl, yr} SL{n2, d2, a2}:
      SN{rows, lrows, SN{r1, l1, yl, yr}, SL{n2, d2, a2}}
    case SN{r1, l1, yl, yr} SN{r2, l2, xl, xr}:
      SN{rows, lrows, SN{r1, l1, yl, yr}, SN{r2, l2, xl, xr}}

# bottom-up, one balanced fork per node; copies at most the rows of the merged leaves
def CS.rechunk(+g: Nat, t: CS) -> CS:
  match t:
    case SL{n, d, a}:
      SL{n, d, a}
    case SN{+rows, +lrows, l, r}:
      x y = CS.rechunk(g, l) CS.rechunk(g, r)
      CS.rc.join(g, rows, lrows, x, y)

# ---- cut: head (drop the leaves past h, shorten the boundary leaf: no copy) and drop (the boundary leaf
# re-cut by one range copy of its kept rows) ----

def CS.head.j(left: Bool, +lrows: U32, x: CS, y: CS & U32) -> CS:
  match left:
    case True{}:
      x
    case False{}:
      (r, +ry) = y
      SN{U32.add(lrows, ry), lrows, x, r}

# the first min(h, rows) rows; O(nodes), the kept leaves are not copied
def CS.head(t: CS, +h: U32) -> CS:
  match t:
    case SL{n, d, a}:
      SL{U32.min(h, n), d, a}
    case SN{rows, +lrows, l, r}:
      CS.head.j(U32.is_le(h, lrows), lrows, CS.head(l, h), CS.rows(CS.head(r, Ch.ssub(h, lrows))))

def CS.drop.l(z: Bool, all: Bool, +off: U32, +n: U32, +d: Nat, a: Array<String>) -> CS:
  match z all:
    case True{} _:
      SL{n, d, a}
    case False{} True{}:
      CS.empty()
    case False{} False{}:
      SL{U32.sub(n, off), d, K.Kernel.range(~String, U32.sub(n, off), d, off, a, "")}

def CS.drop.j(right: Bool, +rows: U32, +off: U32, x: CS & U32, y: CS) -> CS:
  match right:
    case True{}:
      y
    case False{}:
      (l, +rl) = x
      SN{U32.sub(rows, off), rl, l, y}

# rows off .. rows - 1 (all of them when off = 0); the boundary leaf is copied, the others are kept
def CS.drop(t: CS, +off: U32) -> CS:
  match t:
    case SL{+n, +d, a}:
      CS.drop.l(U32.is_zero(off), U32.is_le(n, off), off, n, d, a)
    case SN{+rows, +lrows, l, r}:
      CS.drop.j(U32.is_le(lrows, off), rows, off, CS.rows(CS.drop(l, U32.min(off, lrows))), CS.drop(r, Ch.ssub(off, lrows)))

# rows off .. off + len - 1 (clipped to the rows)
def CS.slice(t: CS, +off: U32, +len: U32) -> CS:
  CS.head(CS.drop(t, off), len)

# ---- concat: one node over the two trees (O(1)); the row cap on the exact sum ----

def CS.concat.k(ok: Bool, +cap: U32, +ra: U32, +rb: U32, a: CS, b: CS) -> E.ResT(CS):
  match ok:
    case True{}:
      Done{SN{U32.add(ra, rb), ra, a, b}}
    case False{}:
      Fail{Ch.over(cap, ra, rb)}

def CS.concat.b(+cap: U32, +ra: U32, b: CS & U32, a: CS) -> E.ResT(CS):
  (b2, +rb) = b
  CS.concat.k(Ch.fits2(cap, ra, rb), cap, ra, rb, a, b2)

def CS.concat.a(+cap: U32, a: CS & U32, b: CS) -> E.ResT(CS):
  (a2, +ra) = a
  CS.concat.b(cap, ra, CS.rows(b), a2)

# a's rows then b's rows, refused (InvalidOperation, the v0.1 text) past cap rows
def CS.concat.cap(+cap: U32, a: CS, b: CS) -> E.ResT(CS):
  CS.concat.a(cap, CS.rows(a), b)

def CS.concat(a: CS, b: CS) -> E.ResT(CS):
  CS.concat.cap(K.Kernel.max_rows(), a, b)

# ==== the chunked map (one balanced fork per node, Kernel.map at the leaves) ====
# The template T5.2's wrappers follow; LAWS section 21 proves its shape and leaf-wise laws at the
# mask_not instance (ported from the W0 spike's cmap_shape / cmap_leafwise).
def CW.map(~f: U32 -> U32, t: CW) -> CW:
  match t:
    case WL{+n, +d, a}:
      WL{n, d, K.Kernel.map(~U32, ~U32, ~f, n, d, a, 0)}
    case WN{rows, lrows, l, r}:
      x y = CW.map(~f, l) CW.map(~f, r)
      WN{rows, lrows, x, y}

# ==== walks that thread state through a tree: one accumulator, a stack of the trees built so far ====

# pop the two trees built for a node's children (the right one on top) and push the node
def CWS.join(+rows: U32, +lrows: U32, s: CWS) -> CWS:
  match s:
    case CWCons{r1, y, CWCons{r2, x, nx}}:
      CWCons{rows, WN{rows, lrows, x, y}, nx}
    case CWCons{r1, y, CWNil{}}:
      CWCons{r1, y, CWNil{}}
    case CWNil{}:
      CWNil{}

def CSS.join(+rows: U32, +lrows: U32, s: CSS) -> CSS:
  match s:
    case CSCons{r1, y, CSCons{r2, x, nx}}:
      CSCons{rows, SN{rows, lrows, x, y}, nx}
    case CSCons{r1, y, CSNil{}}:
      CSCons{r1, y, CSNil{}}
    case CSNil{}:
      CSNil{}

# remap a Dictionary's codes through a merge map, leaf by leaf, the tree's shape kept (sequential: the
# map is read by every leaf and threaded, not shared or cloned)
type RMS is Type:
  RMS{map: Array<U32>, s: CWS}

def CW.remap.l(+n: U32, +d: Nat, s: CWS, r: GH<U32>) -> RMS:
  match r:
    case GH{out, src}:
      RMS{src, CWCons{n, WL{n, d, out}, s}}

def CW.remap.leaf(+n: U32, +d: Nat, a: Array<U32>, st: RMS) -> RMS:
  match st:
    case RMS{map, s}:
      CW.remap.l(n, d, s, Ch.gat(~U32, n, d, map, a, 0))

def RMS.join(+rows: U32, +lrows: U32, st: RMS) -> RMS:
  match st:
    case RMS{map, s}:
      RMS{map, CWS.join(rows, lrows, s)}

def CW.remap.go(t: CW, st: RMS) -> RMS:
  match t:
    case WL{+n, +d, a}:
      CW.remap.leaf(n, d, a, st)
    case WN{+rows, +lrows, l, r}:
      RMS.join(rows, lrows, CW.remap.go(r, CW.remap.go(l, st)))

def CW.remap.fin(st: RMS) -> CW & Array<U32>:
  match st:
    case RMS{map, s}:
      (CWS.collapse(s), map)

# codes[i] := m[codes[i]] at every row; the map comes back
def CW.remap(t: CW, m: Array<U32>) -> CW & Array<U32>:
  CW.remap.fin(CW.remap.go(t, RMS{m, CWNil{}}))

# a Dictionary column's codes decoded to a Raw tree of the same shape; the dictionary is consumed
type DCS is Type:
  DCS{dict: ST.Dict, s: CSS}

def CS.dec.l(+n: U32, +d: Nat, s: CSS, r: ST.Dict & Array<String>) -> DCS:
  (dict, out) = r
  DCS{dict, CSCons{n, SL{n, d, out}, s}}

def CS.dec.leaf(+n: U32, +d: Nat, a: Array<U32>, st: DCS) -> DCS:
  match st:
    case DCS{dict, s}:
      CS.dec.l(n, d, s, Ch.dec(n, d, a, dict))

def DCS.join(+rows: U32, +lrows: U32, st: DCS) -> DCS:
  match st:
    case DCS{dict, s}:
      DCS{dict, CSS.join(rows, lrows, s)}

def CS.dec.go(t: CW, st: DCS) -> DCS:
  match t:
    case WL{+n, +d, a}:
      CS.dec.leaf(n, d, a, st)
    case WN{+rows, +lrows, l, r}:
      DCS.join(rows, lrows, CS.dec.go(r, CS.dec.go(l, st)))

def CS.dec.fin(st: DCS) -> CS:
  match st:
    case DCS{dict, s}:
      CSS.collapse(s)

def CS.of_codes(t: CW, dict: ST.Dict) -> CS:
  CS.dec.fin(CS.dec.go(t, DCS{dict, CSNil{}}))

# ==== operations on a whole column: the same decision at every tree of the column (and of the frame) ====

type COp is Data:
  OHead{h: U32}
  ODrop{off: U32}
  ORechunk{g: Nat}

# the row count after the operation
def COp.len(+o: COp, +n: U32) -> U32:
  match o:
    case OHead{h}:
      U32.min(h, n)
    case ODrop{off}:
      Ch.ssub(n, off)
    case ORechunk{g}:
      n

def CW.op(+o: COp, t: CW) -> CW:
  match o:
    case OHead{h}:
      CW.head(t, h)
    case ODrop{off}:
      CW.drop(t, off)
    case ORechunk{g}:
      CW.rechunk(g, t)

def CF.op(+o: COp, t: CF) -> CF:
  match o:
    case OHead{h}:
      CF.head(t, h)
    case ODrop{off}:
      CF.drop(t, off)
    case ORechunk{g}:
      CF.rechunk(g, t)

def CS.op(+o: COp, t: CS) -> CS:
  match o:
    case OHead{h}:
      CS.head(t, h)
    case ODrop{off}:
      CS.drop(t, off)
    case ORechunk{g}:
      CS.rechunk(g, t)

# a mask tree of the skeleton's shape, every row valid (an AllValid side of a concat)
def CW.ones(s: Skel) -> CW:
  match s:
    case KLeaf{+n}:
      WL{n, K.Kernel.depth_for(U32.max(n, 1)), Array.new(U32, K.Kernel.depth_for(U32.max(n, 1)), 1)}
    case KNode{rows, lrows, l, r}:
      WN{rows, lrows, CW.ones(l), CW.ones(r)}

def Skel.rows(s: Skel) -> U32:
  match s:
    case KLeaf{n}:
      n
    case KNode{rows, lrows, l, r}:
      rows

def Skel.leaves(s: Skel) -> U32:
  match s:
    case KLeaf{n}:
      1
    case KNode{rows, lrows, l, r}:
      U32.add(Skel.leaves(l), Skel.leaves(r))

# ---- validity ----

type CValid is Type:
  CAllValid{}
  CMask{m: CW}

def CValid.of(+n: U32, +ds: Nat, +g: Nat, v: C.Valid) -> CValid:
  match v:
    case C.AllValid{}:
      CAllValid{}
    case C.Mask{m}:
      CMask{CW.of(n, ds, g, m)}

def CValid.to(+dd: Nat, v: CValid) -> C.Valid:
  match v:
    case CAllValid{}:
      C.AllValid{}
    case CMask{m}:
      C.Mask{CW.to_flat(dd, m)}

def CValid.op(+o: COp, v: CValid) -> CValid:
  match v:
    case CAllValid{}:
      CAllValid{}
    case CMask{m}:
      CMask{CW.op(o, m)}

def CValid.fits.k(r: CW & Bool) -> CValid & Bool:
  (m, ok) = r
  (CMask{m}, ok)

def CValid.fits(v: CValid, s: Skel) -> CValid & Bool:
  match v:
    case CAllValid{}:
      (CAllValid{}, True{})
    case CMask{m}:
      CValid.fits.k(CW.fits(m, s))

def CValid.mat(v: CValid, s: Skel) -> CW:
  match v:
    case CAllValid{}:
      CW.ones(s)
    case CMask{m}:
      m

def CValid.cat(va: CValid, vb: CValid, +s: U32, +ha: U32, ska: Skel, skb: Skel) -> CValid:
  match va vb:
    case CAllValid{} CAllValid{}:
      CAllValid{}
    case x y:
      CMask{WN{s, ha, CValid.mat(x, ska), CValid.mat(y, skb)}}

# ---- strings: Raw (a CS tree) or Dictionary (a CW of codes, one Dict per column) ----

type CStrs is Type:
  CSRaw{t: CS}
  CSDict{codes: CW, dict: ST.Dict}

def CStrs.of(+n: U32, +ds: Nat, +g: Nat, s: ST.Strs) -> CStrs:
  match s:
    case ST.SRaw{a}:
      CSRaw{CS.of(n, ds, g, a)}
    case ST.SDict{codes, dict}:
      CSDict{CW.of(n, ds, g, codes), dict}

def CStrs.to(+dd: Nat, s: CStrs) -> ST.Strs:
  match s:
    case CSRaw{t}:
      ST.SRaw{CS.to_flat(dd, t)}
    case CSDict{codes, dict}:
      ST.SDict{CW.to_flat(dd, codes), dict}

def CStrs.depth.r(r: CS & Nat) -> CStrs & Nat:
  (t, +d) = r
  (CSRaw{t}, d)

def CStrs.depth.d(dict: ST.Dict, r: CW & Nat) -> CStrs & Nat:
  (t, +d) = r
  (CSDict{t, dict}, d)

def CStrs.depth(s: CStrs) -> CStrs & Nat:
  match s:
    case CSRaw{t}:
      CStrs.depth.r(CS.depth(t))
    case CSDict{codes, dict}:
      CStrs.depth.d(dict, CW.depth(codes))

def CStrs.op(+o: COp, s: CStrs) -> CStrs:
  match s:
    case CSRaw{t}:
      CSRaw{CS.op(o, t)}
    case CSDict{codes, dict}:
      CSDict{CW.op(o, codes), dict}

def CStrs.skel.r(r: CS & Skel) -> CStrs & Skel:
  (t, s) = r
  (CSRaw{t}, s)

def CStrs.skel.d(dict: ST.Dict, r: CW & Skel) -> CStrs & Skel:
  (t, s) = r
  (CSDict{t, dict}, s)

def CStrs.skel(s: CStrs) -> CStrs & Skel:
  match s:
    case CSRaw{t}:
      CStrs.skel.r(CS.skel(t))
    case CSDict{codes, dict}:
      CStrs.skel.d(dict, CW.skel(codes))

def CStrs.fits.r(r: CS & Bool) -> CStrs & Bool:
  (t, ok) = r
  (CSRaw{t}, ok)

def CStrs.fits.d(dict: ST.Dict, r: CW & Bool) -> CStrs & Bool:
  (t, ok) = r
  (CSDict{t, dict}, ok)

def CStrs.fits(s: CStrs, sk: Skel) -> CStrs & Bool:
  match s:
    case CSRaw{t}:
      CStrs.fits.r(CS.fits(t, sk))
    case CSDict{codes, dict}:
      CStrs.fits.d(dict, CW.fits(codes, sk))

def CStrs.cat.k(+s: U32, +ha: U32, ca: CW, da: ST.Dict, r: CW & Array<U32>) -> CStrs:
  (cb, m) = r
  CSDict{WN{s, ha, ca, cb}, da}

def CStrs.cat.m(+s: U32, +ha: U32, ca: CW, cb: CW, r: ST.Dict & ST.Dict & Array<U32>) -> CStrs:
  (dbb, da, m) = r
  CStrs.cat.k(s, ha, ca, da, CW.remap(cb, m))

# a's rows then b's rows (v0.1 Strs.append's storage rule): two Dictionaries merge b's entries into a's
# (Dict.merge, a's codes kept) and b's codes are re-coded leaf by leaf; any other pair is Raw (the
# Dictionary side decoded leaf by leaf, its shape kept)
def CStrs.cat(+s: U32, +ha: U32, a: CStrs, b: CStrs) -> CStrs:
  match a b:
    case CSRaw{x} CSRaw{y}:
      CSRaw{SN{s, ha, x, y}}
    case CSDict{ca, da} CSDict{cb, db}:
      CStrs.cat.m(s, ha, ca, cb, ST.Dict.merge(db, da))
    case CSRaw{x} CSDict{cb, db}:
      CSRaw{SN{s, ha, x, CS.of_codes(cb, db)}}
    case CSDict{ca, da} CSRaw{y}:
      CSRaw{SN{s, ha, CS.of_codes(ca, da), y}}

# ---- columns ----

type CColumn is Type:
  CBool{len: U32, valid: CValid, data: CW}
  CU32{len: U32, valid: CValid, data: CW}
  CI32{len: U32, valid: CValid, data: CW}
  CF32{len: U32, valid: CValid, data: CF}
  CStr{len: U32, valid: CValid, data: CStrs}

type CNamed is Type:
  CNamed{name: String, col: CColumn}

# the chunked frame: every column (and every validity mask) has the frame's height and ONE shape
# (WFCFrame: CFrame.check); a frame with no columns carries its height alone (DESIGN.md section 9)
type CFrame is Type:
  CFrame{height: U32, cols: List<&1, CNamed>}

def CColumn.mk_w(t: D.DType, +len: U32, valid: CValid, data: CW) -> CColumn:
  match t:
    case D.TBool{}:
      CBool{len, valid, data}
    case D.TI32{}:
      CI32{len, valid, data}
    case _:
      CU32{len, valid, data}

# the column's buffers chunked at grain g (each sequentially: one owner per flat buffer)
def CColumn.of(+g: Nat, c: C.Column) -> CColumn:
  match c:
    case C.CBool{+len, +depth, valid, data}:
      CBool{len, CValid.of(len, depth, g, valid), CW.of(len, depth, g, data)}
    case C.CU32{+len, +depth, valid, data}:
      CU32{len, CValid.of(len, depth, g, valid), CW.of(len, depth, g, data)}
    case C.CI32{+len, +depth, valid, data}:
      CI32{len, CValid.of(len, depth, g, valid), CW.of(len, depth, g, data)}
    case C.CF32{+len, +depth, valid, data}:
      CF32{len, CValid.of(len, depth, g, valid), CF.of(len, depth, g, data)}
    case C.CStr{+len, +depth, valid, data}:
      CStr{len, CValid.of(len, depth, g, valid), CStrs.of(len, depth, g, data)}

def CColumn.to.w(t: D.DType, +len: U32, valid: CValid, r: CW & Nat) -> C.Column:
  (data, +dd) = r
  C.Column.mk_w(t, len, dd, CValid.to(dd, valid), CW.to_flat(dd, data))

def CColumn.to.f(+len: U32, valid: CValid, r: CF & Nat) -> C.Column:
  (data, +dd) = r
  C.CF32{len, dd, CValid.to(dd, valid), CF.to_flat(dd, data)}

def CColumn.to.s(+len: U32, valid: CValid, r: CStrs & Nat) -> C.Column:
  (data, +dd) = r
  C.CStr{len, dd, CValid.to(dd, valid), CStrs.to(dd, data)}

# the flat column: a one-leaf tree is moved as is (no copy), anything else flattened into
# depth_for(rows) slots; the validity mask takes the data's depth
def CColumn.to(c: CColumn) -> C.Column:
  match c:
    case CBool{+len, valid, data}:
      CColumn.to.w(D.TBool{}, len, valid, CW.depth(data))
    case CU32{+len, valid, data}:
      CColumn.to.w(D.TU32{}, len, valid, CW.depth(data))
    case CI32{+len, valid, data}:
      CColumn.to.w(D.TI32{}, len, valid, CW.depth(data))
    case CF32{+len, valid, data}:
      CColumn.to.f(len, valid, CF.depth(data))
    case CStr{+len, valid, data}:
      CColumn.to.s(len, valid, CStrs.depth(data))

def CColumn.len(c: CColumn) -> CColumn & U32:
  match c:
    case CBool{+len, valid, data}:
      (CBool{len, valid, data}, len)
    case CU32{+len, valid, data}:
      (CU32{len, valid, data}, len)
    case CI32{+len, valid, data}:
      (CI32{len, valid, data}, len)
    case CF32{+len, valid, data}:
      (CF32{len, valid, data}, len)
    case CStr{+len, valid, data}:
      (CStr{len, valid, data}, len)

# head / drop / rechunk: the same decision on the data tree and the mask tree (equal shapes in, equal
# shapes out: every decision reads row counts only)
def CColumn.op(+o: COp, c: CColumn) -> CColumn:
  match c:
    case CBool{+len, valid, data}:
      CBool{COp.len(o, len), CValid.op(o, valid), CW.op(o, data)}
    case CU32{+len, valid, data}:
      CU32{COp.len(o, len), CValid.op(o, valid), CW.op(o, data)}
    case CI32{+len, valid, data}:
      CI32{COp.len(o, len), CValid.op(o, valid), CW.op(o, data)}
    case CF32{+len, valid, data}:
      CF32{COp.len(o, len), CValid.op(o, valid), CF.op(o, data)}
    case CStr{+len, valid, data}:
      CStr{COp.len(o, len), CValid.op(o, valid), CStrs.op(o, data)}

# the data tree's skeleton (the column comes back)
def CColumn.skel.w(t: D.DType, +len: U32, valid: CValid, r: CW & Skel) -> CColumn & Skel:
  (data, s) = r
  (CColumn.mk_w(t, len, valid, data), s)

def CColumn.skel.f(+len: U32, valid: CValid, r: CF & Skel) -> CColumn & Skel:
  (data, s) = r
  (CF32{len, valid, data}, s)

def CColumn.skel.s(+len: U32, valid: CValid, r: CStrs & Skel) -> CColumn & Skel:
  (data, s) = r
  (CStr{len, valid, data}, s)

def CColumn.skel(c: CColumn) -> CColumn & Skel:
  match c:
    case CBool{+len, valid, data}:
      CColumn.skel.w(D.TBool{}, len, valid, CW.skel(data))
    case CU32{+len, valid, data}:
      CColumn.skel.w(D.TU32{}, len, valid, CW.skel(data))
    case CI32{+len, valid, data}:
      CColumn.skel.w(D.TI32{}, len, valid, CW.skel(data))
    case CF32{+len, valid, data}:
      CColumn.skel.f(len, valid, CF.skel(data))
    case CStr{+len, valid, data}:
      CColumn.skel.s(len, valid, CStrs.skel(data))

# len == h, the data tree and the mask tree both of skeleton s (the column comes back)
def CColumn.fits.w(t: D.DType, +len: U32, +h: U32, rv: CValid & Bool, rd: CW & Bool) -> CColumn & Bool:
  (v, okv) = rv
  (data, okd) = rd
  (CColumn.mk_w(t, len, v, data), Bool.and(U32.is_eq(len, h), Bool.and(okv, okd)))

def CColumn.fits.f(+len: U32, +h: U32, rv: CValid & Bool, rd: CF & Bool) -> CColumn & Bool:
  (v, okv) = rv
  (data, okd) = rd
  (CF32{len, v, data}, Bool.and(U32.is_eq(len, h), Bool.and(okv, okd)))

def CColumn.fits.s(+len: U32, +h: U32, rv: CValid & Bool, rd: CStrs & Bool) -> CColumn & Bool:
  (v, okv) = rv
  (data, okd) = rd
  (CStr{len, v, data}, Bool.and(U32.is_eq(len, h), Bool.and(okv, okd)))

def CColumn.fits(c: CColumn, +s: Skel, +h: U32) -> CColumn & Bool:
  match c:
    case CBool{+len, valid, data}:
      CColumn.fits.w(D.TBool{}, len, h, CValid.fits(valid, s), CW.fits(data, s))
    case CU32{+len, valid, data}:
      CColumn.fits.w(D.TU32{}, len, h, CValid.fits(valid, s), CW.fits(data, s))
    case CI32{+len, valid, data}:
      CColumn.fits.w(D.TI32{}, len, h, CValid.fits(valid, s), CW.fits(data, s))
    case CF32{+len, valid, data}:
      CColumn.fits.f(len, h, CValid.fits(valid, s), CF.fits(data, s))
    case CStr{+len, valid, data}:
      CColumn.fits.s(len, h, CValid.fits(valid, s), CStrs.fits(data, s))

# a's rows then b's rows as one node per tree (O(1) per buffer, plus a Dictionary merge); s = the summed
# rows, already checked against the cap by the caller; the dtypes agree (the caller checked the schema:
# a mismatch keeps a, as Cat.col does)
def CColumn.cat.w(t: D.DType, +s: U32, +ha: U32, va: CValid, vb: CValid, ra: CW & Skel, rb: CW & Skel) -> CColumn:
  (xa, ska) = ra
  (xb, skb) = rb
  CColumn.mk_w(t, s, CValid.cat(va, vb, s, ha, ska, skb), WN{s, ha, xa, xb})

def CColumn.cat.f(+s: U32, +ha: U32, va: CValid, vb: CValid, ra: CF & Skel, rb: CF & Skel) -> CColumn:
  (xa, ska) = ra
  (xb, skb) = rb
  CF32{s, CValid.cat(va, vb, s, ha, ska, skb), FN{s, ha, xa, xb}}

def CColumn.cat.s(+s: U32, +ha: U32, va: CValid, vb: CValid, ra: CStrs & Skel, rb: CStrs & Skel) -> CColumn:
  (xa, ska) = ra
  (xb, skb) = rb
  CStr{s, CValid.cat(va, vb, s, ha, ska, skb), CStrs.cat(s, ha, xa, xb)}

def CColumn.cat(+s: U32, +ha: U32, a: CColumn, b: CColumn) -> CColumn:
  match a b:
    case CBool{la, va, xa} CBool{lb, vb, xb}:
      CColumn.cat.w(D.TBool{}, s, ha, va, vb, CW.skel(xa), CW.skel(xb))
    case CU32{la, va, xa} CU32{lb, vb, xb}:
      CColumn.cat.w(D.TU32{}, s, ha, va, vb, CW.skel(xa), CW.skel(xb))
    case CI32{la, va, xa} CI32{lb, vb, xb}:
      CColumn.cat.w(D.TI32{}, s, ha, va, vb, CW.skel(xa), CW.skel(xb))
    case CF32{la, va, xa} CF32{lb, vb, xb}:
      CColumn.cat.f(s, ha, va, vb, CF.skel(xa), CF.skel(xb))
    case CStr{la, va, xa} CStr{lb, vb, xb}:
      CColumn.cat.s(s, ha, va, vb, CStrs.skel(xa), CStrs.skel(xb))
    case x y:
      x

def CNamed.of(+g: Nat, nc: C.Named) -> CNamed:
  match nc:
    case C.Named{n, c}:
      CNamed{n, CColumn.of(g, c)}

def CNamed.to(+u: U32, nc: CNamed) -> C.Named:
  match nc:
    case CNamed{n, c}:
      C.Named{n, CColumn.to(c)}

def CNamed.op(+o: COp, nc: CNamed) -> CNamed:
  match nc:
    case CNamed{n, c}:
      CNamed{n, CColumn.op(o, c)}

# ==== a balanced fork over a frame's column list (split in halves, never 1-vs-rest) ====

# the length of a list, as a tail call; the list comes back
def Lst.len(-A: Type, xs: List<&1, A>, +k: U32, acc: List<&1, A>) -> List<&1, A> & U32:
  match xs:
    case Nil{}:
      (List.reverse(&1, A, acc), k)
    case x <> rest:
      Lst.len(A, rest, U32.inc(k), x <> acc)

def Lst.split.k(-A: Type, x: A, r: List<&1, A> & List<&1, A>) -> List<&1, A> & List<&1, A>:
  (a, b) = r
  (x <> a, b)

# the first k elements and the rest (z: k == 0, computed by the caller)
def Lst.split(-A: Type, xs: List<&1, A>, +k: U32, z: Bool) -> List<&1, A> & List<&1, A>:
  match xs z:
    case Nil{} _:
      (Nil{}, Nil{})
    case x <> rest True{}:
      (Nil{}, x <> rest)
    case x <> rest False{}:
      Lst.split.k(A, x, Lst.split(A, rest, U32.sub(k, 1), U32.is_zero(U32.sub(k, 1))))

def Lst.pmap.seq(~A: Type, ~B: Type, ~P: Data, ~f: P -> A -> B, +p: P, xs: List<&1, A>) -> List<&1, B>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      f(p, x) <> Lst.pmap.seq(~A, ~B, ~P, ~f, p, rest)

# r: a list of k elements split at k / 2; the halves go to the two sides of a parallel let
def Lst.pmap.go(~A: Type, ~B: Type, ~P: Data, ~f: P -> A -> B, fl: Nat, small: Bool, +p: P, +k: U32, r: List<&1, A> & List<&1, A>) -> List<&1, B>:
  match fl small:
    case _ True{}:
      (a, b) = r
      List.append(&1, B, Lst.pmap.seq(~A, ~B, ~P, ~f, p, a), Lst.pmap.seq(~A, ~B, ~P, ~f, p, b))
    case 0n False{}:
      (a, b) = r
      List.append(&1, B, Lst.pmap.seq(~A, ~B, ~P, ~f, p, a), Lst.pmap.seq(~A, ~B, ~P, ~f, p, b))
    case 1n++q False{}:
      (a, b) = r
      +h1 = U32.shr(k)
      +h2 = U32.sub(k, h1)
      x y = Lst.pmap.go(~A, ~B, ~P, ~f, q, U32.is_le(h1, 1), p, h1, Lst.split(A, a, U32.shr(h1), U32.is_zero(U32.shr(h1)))) Lst.pmap.go(~A, ~B, ~P, ~f, q, U32.is_le(h2, 1), p, h2, Lst.split(A, b, U32.shr(h2), U32.is_zero(U32.shr(h2))))
      List.append(&1, B, x, y)

def Lst.pmap.k(~A: Type, ~B: Type, ~P: Data, ~f: P -> A -> B, +p: P, r: List<&1, A> & U32) -> List<&1, B>:
  (xs, +k) = r
  Lst.pmap.go(~A, ~B, ~P, ~f, 32n, U32.is_le(k, 1), p, k, Lst.split(A, xs, U32.shr(k), U32.is_zero(U32.shr(k))))

# f(p, x) for every element, in order, the elements forked in a balanced tree
def Lst.pmap(~A: Type, ~B: Type, ~P: Data, ~f: P -> A -> B, +p: P, xs: List<&1, A>) -> List<&1, B>:
  Lst.pmap.k(~A, ~B, ~P, ~f, p, Lst.len(A, xs, 0, Nil{}))

# ==== frames ====

def CFrame.height(f: CFrame) -> CFrame & U32:
  match f:
    case CFrame{+h, cols}:
      (CFrame{h, cols}, h)

# the empty frame (no columns, height 0)
def CFrame.empty() -> CFrame:
  CFrame{0, Nil{}}

# a flat frame chunked at grain g: one builder per column, forked across columns. A frame of at most
# 2^g rows is one leaf per column (the flat buffers moved, nothing copied); height 0 is one empty leaf
# per column; a frame with no columns keeps its height.
def CFrame.of_frame(+g: Nat, f: C.Frame) -> CFrame:
  match f:
    case C.Frame{+h, cols}:
      CFrame{h, Lst.pmap(~C.Named, ~CNamed, ~Nat, ~(g2 => nc => CNamed.of(g2, nc)), g, cols)}

# back to flat columns (flatten per column, forked across columns; one-leaf columns are moved)
def CFrame.to_frame(f: CFrame) -> C.Frame:
  match f:
    case CFrame{+h, cols}:
      C.Frame{h, Lst.pmap(~CNamed, ~C.Named, ~U32, ~(u => nc => CNamed.to(u, nc)), 0, cols)}

def CFrame.op(+o: COp, f: CFrame) -> CFrame:
  match f:
    case CFrame{+h, cols}:
      CFrame{COp.len(o, h), Lst.pmap(~CNamed, ~CNamed, ~COp, ~(o2 => nc => CNamed.op(o2, nc)), o, cols)}

# the first min(n, height) rows: the trees are cut, no row is copied
def CFrame.head(f: CFrame, +n: U32) -> CFrame:
  CFrame.op(OHead{n}, f)

# rows off .. off + len - 1 (clipped): the leaves before off dropped, the boundary leaf re-cut by one
# range copy per tree, the trees past the end cut as head does
def CFrame.slice(f: CFrame, +off: U32, +len: U32) -> CFrame:
  CFrame.op(OHead{len}, CFrame.op(ODrop{off}, f))

# merge sibling leaves whose rows fit 2^g, in every tree of every column (the same row counts, so the
# same new shape everywhere)
def CFrame.rechunk(+g: Nat, f: CFrame) -> CFrame:
  CFrame.op(ORechunk{g}, f)

# the leaf count of the first column's data tree (0 without columns); the frame comes back
def CFrame.leaves.c(+h: U32, nm: String, rest: List<&1, CNamed>, r: CColumn & Skel) -> CFrame & U32:
  (c, +s) = r
  (CFrame{h, CNamed{nm, c} <> rest}, Skel.leaves(s))

def CFrame.leaves(f: CFrame) -> CFrame & U32:
  match f:
    case CFrame{+h, cols}:
      match cols:
        case Nil{}:
          (CFrame{h, Nil{}}, 0)
        case CNamed{nm, c} <> rest:
          CFrame.leaves.c(h, nm, rest, CColumn.skel(c))

def CFrame.rebalance.k(go: Bool, +g: Nat, f: CFrame) -> CFrame:
  match go:
    case True{}:
      CFrame.rechunk(g, f)
    case False{}:
      f

def CFrame.rebalance.b(+g: Nat, +leaves: U32, r: CFrame & U32) -> CFrame:
  (f, +h) = r
  CFrame.rebalance.k(U32.is_lt(U32.shl(h), U32.shln(leaves, g)), g, f)

def CFrame.rebalance.a(+g: Nat, r: CFrame & U32) -> CFrame:
  (f, +leaves) = r
  CFrame.rebalance.b(g, leaves, CFrame.height(f))

# the rechunk policy (DESIGN.md 16.1): after an operator that drops rows, rechunk only when the
# occupancy is under a half (rows < leaves * 2^g / 2); then the total rechunk copying over a chain is
# at most 2x its input rows
def CFrame.rebalance(+g: Nat, f: CFrame) -> CFrame:
  CFrame.rebalance.a(g, CFrame.leaves(f))

# a's rows then b's rows, one node per tree. The schemas agree (checked by the caller as v0.1's concat
# does, before any data work); the summed height is checked against cap first (InvalidOperation, the
# v0.1 text on the saturating sum)
def CCols.cat(+s: U32, +ha: U32, ca: List<&1, CNamed>, cb: List<&1, CNamed>) -> List<&1, CNamed>:
  match ca cb:
    case CNamed{nm, a} <> ta CNamed{nb, b} <> tb:
      CNamed{nm, CColumn.cat(s, ha, a, b)} <> CCols.cat(s, ha, ta, tb)
    case x y:
      Nil{}

def CFrame.concat.k(ok: Bool, +cap: U32, +ha: U32, +hb: U32, ca: List<&1, CNamed>, cb: List<&1, CNamed>) -> E.ResT(CFrame):
  match ok:
    case True{}:
      +s = U32.add(ha, hb)
      Done{CFrame{s, CCols.cat(s, ha, ca, cb)}}
    case False{}:
      Fail{Ch.over(cap, ha, hb)}

def CFrame.concat.cap(+cap: U32, a: CFrame, b: CFrame) -> E.ResT(CFrame):
  match a:
    case CFrame{+ha, ca}:
      match b:
        case CFrame{+hb, cb}:
          CFrame.concat.k(Ch.fits2(cap, ha, hb), cap, ha, hb, ca, cb)

def CFrame.concat(a: CFrame, b: CFrame) -> E.ResT(CFrame):
  CFrame.concat.cap(K.Kernel.max_rows(), a, b)

# ---- WFCFrame: one lockstep walk at the executor boundary ----

def CCols.fits.k(nm: String, uniq: Bool, r: CColumn & Bool, rr: List<&1, CNamed> & Bool) -> List<&1, CNamed> & Bool:
  (c, ok) = r
  (rest, ok2) = rr
  (CNamed{nm, c} <> rest, Bool.and(uniq, Bool.and(ok, ok2)))

def CCols.fits(cols: List<&1, CNamed>, +s: Skel, +h: U32, +seen: List<&2, String>) -> List<&1, CNamed> & Bool:
  match cols:
    case Nil{}:
      (Nil{}, True{})
    case CNamed{+nm, c} <> rest:
      CCols.fits.k(nm, Bool.not(C.Names.has(seen, nm)), CColumn.fits(c, s, h), CCols.fits(rest, s, h, nm <> seen))

def CFrame.check.j(+h: U32, ok0: Bool, r: List<&1, CNamed> & Bool) -> CFrame & Bool:
  (cols, ok) = r
  (CFrame{h, cols}, Bool.and(ok0, ok))

def CFrame.check.k(+h: U32, nm: String, rest: List<&1, CNamed>, r: CColumn & Skel) -> CFrame & Bool:
  (c, +s) = r
  CFrame.check.j(h, U32.is_eq(Skel.rows(s), h), CCols.fits(CNamed{nm, c} <> rest, s, h, Nil{}))

# WFCFrame: every column has the frame's height, every data and mask tree has the first column's shape
# and counts (so every lockstep leaf walk pairs leaves of equal n), the names are unique; a frame with
# no columns holds. O(columns * leaves); the frame comes back.
def CFrame.check(f: CFrame) -> CFrame & Bool:
  match f:
    case CFrame{+h, cols}:
      match cols:
        case Nil{}:
          (CFrame{h, Nil{}}, True{})
        case CNamed{nm, c} <> rest:
          CFrame.check.k(h, nm, rest, CColumn.skel(c))
