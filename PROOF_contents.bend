# PROOF_contents.bend -- proofs of LAWS.bend section 11 (M5, P1): the distinct-paths lemma
# over the production index arithmetic (PROOF_bits.bend), the separation lemma for
# Array.set on a well-formed array, and the full content theorems of the kernels
# (gather, compact, map, zip, iota), slot by slot, against the real loops.
#
# Shape: `sep` walks the tree once with the write and hands back the written array as a
# Sigma witness carrying WFArray and a FORALL over every (index, decision) of what rd now
# answers (v where the paths agree, the old cell elsewhere). `set_other_w` adds the
# masking of Array.set / Array.get (rdN). The kernel loop lemmas thread the output array
# through `set_other_w` and keep "every index written so far holds its value" as a
# forall hypothesis moved into the goal (H -> G) so the array witnesses can be rewritten
# through it.
import Base
import ./src/dtype.bend as D
import ./src/err.bend as E
import ./src/kernels.bend as K
import ./src/column.bend as C
import ./LAWS.bend as Laws
import ./PROOF_lib.bend as L
import ./PROOF_kernels.bend as PK
import ./PROOF_bits.bend as B

# ---- Array.size of a well-formed array: the array back, well formed, with 2^d slots ------------

def wf_size_node(-T: Data, -xs: Array<T>, ys: Array<T>, +p: Nat, wr: Laws.WFArray(T, p, ys), w: &b: Array<T> -> {b == xs : Array<T>} & Laws.WFArray(T, p, b) & {Array.size(T, xs) == (b, U32.shln(1, p)) : Array<T> & U32})
  -> &b2: Array<T> -> {b2 == ANode{xs, ys} : Array<T>} & Laws.WFArray(T, 1n+p, b2) & {Array.size(T, ANode{xs, ys}) == (b2, U32.shln(1, 1n+p)) : Array<T> & U32}:
  (b, eb, wb, es) = w
  (ANode{b, ys}, (%eb : {ANode{b, ys} == ANode{_, ys} : Array<T>}; {==}), (wb, wr), (%Equal.sym(Array<T> & U32, Array.size(T, xs), (b, U32.shln(1, p)), es) : {Array.size.node(T, ys, _) == (ANode{b, ys}, U32.shln(1, 1n+p)) : Array<T> & U32}; {==}))

def wf_size(-T: Data, d: Nat, a: Array<T>, wf: Laws.WFArray(T, d, a)) -> &b: Array<T> -> {b == a : Array<T>} & Laws.WFArray(T, d, b) & {Array.size(T, a) == (b, U32.shln(1, d)) : Array<T> & U32}:
  match d a:
    case 0n ALeaf{+x}:
      (ALeaf{x}, {==}, Unit{}, {==})
    case 1n++p ANode{xs, ys}:
      (wl, wr) = wf
      wf_size_node(T, xs, ys, p, wr, wf_size(T, p, xs, wl))
    case 0n ANode{xs, ys}:
      Empty.absurd(&b: Array<T> -> {b == ANode{xs, ys} : Array<T>} & Laws.WFArray(T, 0n, b) & {Array.size(T, ANode{xs, ys}) == (b, U32.shln(1, 0n)) : Array<T> & U32}, wf)
    case 1n+p ALeaf{x}:
      Empty.absurd(&b: Array<T> -> {b == ALeaf{x} : Array<T>} & Laws.WFArray(T, 1n+p, b) & {Array.size(T, ALeaf{x}) == (b, U32.shln(1, 1n+p)) : Array<T> & U32}, wf)

def rd_at_wf_k(-T: Data, -a: Array<T>, +d: Nat, +k: U32, w: &b: Array<T> -> {b == a : Array<T>} & Laws.WFArray(T, d, b) & {Array.size(T, a) == (b, U32.shln(1, d)) : Array<T> & U32}) -> {Laws.rd_at(T, a, k) == Laws.rdN(T, d, a, k) : T}:
  (b, eb, wb, es) = w
  %Equal.sym(Array<T> & U32, Array.size(T, a), (b, U32.shln(1, d)), es) : {Laws.rd_size(T, k, _) == Laws.rdN(T, d, a, k) : T}
  %eb : {Laws.rd_size(T, k, (b, U32.shln(1, d))) == Laws.rdN(T, d, _, k) : T}
  {==}

def Laws.rd_at_wf(T, d, a, k, wf):
  rd_at_wf_k(T, a, d, k, wf_size(T, d, a, wf))

# ---- the separation lemma: one write through the tree, every read afterwards ------------------

# the left-half write lifted to the node: a read with zj = True goes into the written half
def sep_lo_j(-T: Data, -p: Nat, -c: Array<T>, -xs: Array<T>, -ys: Array<T>, +n: U32, +i: U32, +v: T,
  fj: @j: U32 -> @zj: Bool -> {Laws.rd(T, c, U32.shr(n), j, zj) == Bool.pick(T, Laws.same_d(p, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n))), j, zj), v, Laws.rd(T, xs, U32.shr(n), j, zj)) : T},
  +j: U32, zj: Bool) -> {Laws.rd(T, ANode{c, ys}, n, j, zj) == Bool.pick(T, Laws.same_d(1n+p, n, i, True{}, j, zj), v, Laws.rd(T, ANode{xs, ys}, n, j, zj)) : T}:
  match zj:
    case True{}:
      fj(j, U32.is_lt(j, U32.shr(U32.shr(n))))
    case False{}:
      {==}

def sep_lo(-T: Data, +p: Nat, -xs: Array<T>, ys: Array<T>, +n: U32, +i: U32, +v: T, wr: Laws.WFArray(T, p, ys),
  w: &c: Array<T> -> &o: T -> {Array.swap.go(T, xs, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n)))) == (c, o) : Array<T> & T} & Laws.WFArray(T, p, c) & (@j: U32 -> @zj: Bool -> {Laws.rd(T, c, U32.shr(n), j, zj) == Bool.pick(T, Laws.same_d(p, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n))), j, zj), v, Laws.rd(T, xs, U32.shr(n), j, zj)) : T}))
  -> &c2: Array<T> -> &o2: T -> {Array.swap.go(T, ANode{xs, ys}, n, i, v, True{}) == (c2, o2) : Array<T> & T} & Laws.WFArray(T, 1n+p, c2) & (@j: U32 -> @zj: Bool -> {Laws.rd(T, c2, n, j, zj) == Bool.pick(T, Laws.same_d(1n+p, n, i, True{}, j, zj), v, Laws.rd(T, ANode{xs, ys}, n, j, zj)) : T}):
  (c, o, eq, wc, fj) = w
  (ANode{c, ys}, o, (%Equal.sym(Array<T> & T, Array.swap.go(T, xs, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n)))), (c, o), eq) : {Array.swap.lo(T, ys, _) == (ANode{c, ys}, o) : Array<T> & T}; {==}), (wc, wr), j => zj => sep_lo_j(T, p, c, xs, ys, n, i, v, fj, j, zj))

# the right-half write lifted to the node: a read with zj = False goes into the written half
def sep_hi_j(-T: Data, -p: Nat, -c: Array<T>, -xs: Array<T>, -ys: Array<T>, +n: U32, +i: U32, +v: T,
  fj: @j: U32 -> @zj: Bool -> {Laws.rd(T, c, U32.shr(n), j, zj) == Bool.pick(T, Laws.same_d(p, U32.shr(n), U32.sub(i, U32.shr(n)), U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))), j, zj), v, Laws.rd(T, ys, U32.shr(n), j, zj)) : T},
  +j: U32, zj: Bool) -> {Laws.rd(T, ANode{xs, c}, n, j, zj) == Bool.pick(T, Laws.same_d(1n+p, n, i, False{}, j, zj), v, Laws.rd(T, ANode{xs, ys}, n, j, zj)) : T}:
  match zj:
    case True{}:
      {==}
    case False{}:
      fj(U32.sub(j, U32.shr(n)), U32.is_lt(U32.sub(j, U32.shr(n)), U32.shr(U32.shr(n))))

def sep_hi(-T: Data, +p: Nat, xs: Array<T>, -ys: Array<T>, +n: U32, +i: U32, +v: T, wl: Laws.WFArray(T, p, xs),
  w: &c: Array<T> -> &o: T -> {Array.swap.go(T, ys, U32.shr(n), U32.sub(i, U32.shr(n)), v, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))) == (c, o) : Array<T> & T} & Laws.WFArray(T, p, c) & (@j: U32 -> @zj: Bool -> {Laws.rd(T, c, U32.shr(n), j, zj) == Bool.pick(T, Laws.same_d(p, U32.shr(n), U32.sub(i, U32.shr(n)), U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))), j, zj), v, Laws.rd(T, ys, U32.shr(n), j, zj)) : T}))
  -> &c2: Array<T> -> &o2: T -> {Array.swap.go(T, ANode{xs, ys}, n, i, v, False{}) == (c2, o2) : Array<T> & T} & Laws.WFArray(T, 1n+p, c2) & (@j: U32 -> @zj: Bool -> {Laws.rd(T, c2, n, j, zj) == Bool.pick(T, Laws.same_d(1n+p, n, i, False{}, j, zj), v, Laws.rd(T, ANode{xs, ys}, n, j, zj)) : T}):
  (c, o, eq, wc, fj) = w
  (ANode{xs, c}, o, (%Equal.sym(Array<T> & T, Array.swap.go(T, ys, U32.shr(n), U32.sub(i, U32.shr(n)), v, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))), (c, o), eq) : {Array.swap.hi(T, xs, _) == (ANode{xs, c}, o) : Array<T> & T}; {==}), (wl, wc), j => zj => sep_hi_j(T, p, c, xs, ys, n, i, v, fj, j, zj))

# Array.swap.go on a well-formed tree of depth d: the written array (well formed) and what every
# read answers afterwards: v where the descent agrees with the write's, the old cell elsewhere
def sep(-T: Data, d: Nat, a: Array<T>, +n: U32, +i: U32, +v: T, zi: Bool, wf: Laws.WFArray(T, d, a))
  -> &c: Array<T> -> &o: T -> {Array.swap.go(T, a, n, i, v, zi) == (c, o) : Array<T> & T} & Laws.WFArray(T, d, c) & (@j: U32 -> @zj: Bool -> {Laws.rd(T, c, n, j, zj) == Bool.pick(T, Laws.same_d(d, n, i, zi, j, zj), v, Laws.rd(T, a, n, j, zj)) : T}):
  match d a zi:
    case 0n ALeaf{x} _:
      (ALeaf{v}, x, {==}, Unit{}, j => zj => {==})
    case 1n++p ANode{xs, ys} True{}:
      (wl, wr) = wf
      sep_lo(T, p, xs, ys, n, i, v, wr, sep(T, p, xs, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n))), wl))
    case 1n++p ANode{xs, ys} False{}:
      (wl, wr) = wf
      sep_hi(T, p, xs, ys, n, i, v, wl, sep(T, p, ys, U32.shr(n), U32.sub(i, U32.shr(n)), v, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))), wr))
    case 0n ANode{xs, ys} _:
      Empty.absurd(&c: Array<T> -> &o: T -> {Array.swap.go(T, ANode{xs, ys}, n, i, v, zi) == (c, o) : Array<T> & T} & Laws.WFArray(T, 0n, c) & (@j: U32 -> @zj: Bool -> {Laws.rd(T, c, n, j, zj) == Bool.pick(T, Laws.same_d(0n, n, i, zi, j, zj), v, Laws.rd(T, ANode{xs, ys}, n, j, zj)) : T}), wf)
    case 1n+p ALeaf{x} _:
      Empty.absurd(&c: Array<T> -> &o: T -> {Array.swap.go(T, ALeaf{x}, n, i, v, zi) == (c, o) : Array<T> & T} & Laws.WFArray(T, 1n+p, c) & (@j: U32 -> @zj: Bool -> {Laws.rd(T, c, n, j, zj) == Bool.pick(T, Laws.same_d(1n+p, n, i, zi, j, zj), v, Laws.rd(T, ALeaf{x}, n, j, zj)) : T}), wf)

# ---- Array.set on a well-formed array: the masking of Array.swap.at in place -------------------

def set_other_k2(-T: Data, +d: Nat, -b: Array<T>, +i: U32, +v: T,
  w: &c: Array<T> -> &o: T -> {Array.swap.go(T, b, U32.shln(1, d), U32.and(i, U32.sub(U32.shln(1, d), 1)), v, U32.is_lt(U32.and(i, U32.sub(U32.shln(1, d), 1)), U32.shr(U32.shln(1, d)))) == (c, o) : Array<T> & T} & Laws.WFArray(T, d, c) & (@j: U32 -> @zj: Bool -> {Laws.rd(T, c, U32.shln(1, d), j, zj) == Bool.pick(T, Laws.same_d(d, U32.shln(1, d), U32.and(i, U32.sub(U32.shln(1, d), 1)), U32.is_lt(U32.and(i, U32.sub(U32.shln(1, d), 1)), U32.shr(U32.shln(1, d))), j, zj), v, Laws.rd(T, b, U32.shln(1, d), j, zj)) : T}))
  -> &c2: Array<T> -> {Array.set.fin(T, Array.swap.at(T, i, v, (b, U32.shln(1, d)))) == c2 : Array<T>} & Laws.WFArray(T, d, c2) & (@j: U32 -> {Laws.rdN(T, d, c2, j) == Bool.pick(T, Laws.same_at(d, i, j), v, Laws.rd_size(T, j, (b, U32.shln(1, d)))) : T}):
  (c, o, eq, wc, fj) = w
  (c, (%Equal.sym(Array<T> & T, Array.swap.go(T, b, U32.shln(1, d), U32.and(i, U32.sub(U32.shln(1, d), 1)), v, U32.is_lt(U32.and(i, U32.sub(U32.shln(1, d), 1)), U32.shr(U32.shln(1, d)))), (c, o), eq) : {Array.set.fin(T, _) == c : Array<T>}; {==}), wc, +j => fj(U32.and(j, U32.sub(U32.shln(1, d), 1)), U32.is_lt(U32.and(j, U32.sub(U32.shln(1, d), 1)), U32.shr(U32.shln(1, d)))))

def set_other_k1(-T: Data, +d: Nat, -a: Array<T>, +i: U32, +v: T, w: &b: Array<T> -> {b == a : Array<T>} & Laws.WFArray(T, d, b) & {Array.size(T, a) == (b, U32.shln(1, d)) : Array<T> & U32})
  -> &c: Array<T> -> {Array.set(T, a, i, v) == c : Array<T>} & Laws.WFArray(T, d, c) & (@j: U32 -> {Laws.rdN(T, d, c, j) == Bool.pick(T, Laws.same_at(d, i, j), v, Laws.rd_at(T, a, j)) : T}):
  (b, eb, wb, es) = w
  %Equal.sym(Array<T> & U32, Array.size(T, a), (b, U32.shln(1, d)), es) : &c: Array<T> -> {Array.set.fin(T, Array.swap.at(T, i, v, _)) == c : Array<T>} & Laws.WFArray(T, d, c) & (@j: U32 -> {Laws.rdN(T, d, c, j) == Bool.pick(T, Laws.same_at(d, i, j), v, Laws.rd_size(T, j, _)) : T})
  set_other_k2(T, d, b, i, v, sep(T, d, b, U32.shln(1, d), U32.and(i, U32.sub(U32.shln(1, d), 1)), v, U32.is_lt(U32.and(i, U32.sub(U32.shln(1, d), 1)), U32.shr(U32.shln(1, d))), wb))

# Array.set(a, i, v) on a well-formed array of depth d: the written array (well formed) and every
# cell afterwards: v where the masked paths of i and j agree, the old cell elsewhere
def set_other_w(-T: Data, +d: Nat, a: Array<T>, +i: U32, +v: T, wf: Laws.WFArray(T, d, a))
  -> &c: Array<T> -> {Array.set(T, a, i, v) == c : Array<T>} & Laws.WFArray(T, d, c) & (@j: U32 -> {Laws.rdN(T, d, c, j) == Bool.pick(T, Laws.same_at(d, i, j), v, Laws.rd_at(T, a, j)) : T}):
  set_other_k1(T, d, a, i, v, wf_size(T, d, a, wf))

def wf_set_fin(-T: Data, +d: Nat, -a: Array<T>, +i: U32, +v: T, w: &c: Array<T> -> {Array.set(T, a, i, v) == c : Array<T>} & Laws.WFArray(T, d, c) & (@j: U32 -> {Laws.rdN(T, d, c, j) == Bool.pick(T, Laws.same_at(d, i, j), v, Laws.rd_at(T, a, j)) : T})) -> Laws.WFArray(T, d, Array.set(T, a, i, v)):
  (c, ec, wc, fj) = w
  %Equal.sym(Array<T>, Array.set(T, a, i, v), c, ec) : Laws.WFArray(T, d, _)
  wc

def Laws.wf_array_set(T, d, a, i, v, wf):
  wf_set_fin(T, d, a, i, v, set_other_w(T, d, a, i, v, wf))
