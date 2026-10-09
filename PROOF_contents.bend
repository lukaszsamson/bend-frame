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
  -> &c2: Array<T> -> {Array.set.fin(T, Array.swap.at(T, i, v, (b, U32.shln(1, d)))) == c2 : Array<T>} & Laws.WFArray(T, d, c2) & (@j: U32 -> {Laws.rdN(T, d, c2, j) == Bool.pick(T, Laws.same_at(d, i, j), v, Laws.rdN(T, d, b, j)) : T}) & (@j: U32 -> {Laws.rd_size(T, j, (b, U32.shln(1, d))) == Laws.rdN(T, d, b, j) : T}):
  (c, o, eq, wc, fj) = w
  (c, (%Equal.sym(Array<T> & T, Array.swap.go(T, b, U32.shln(1, d), U32.and(i, U32.sub(U32.shln(1, d), 1)), v, U32.is_lt(U32.and(i, U32.sub(U32.shln(1, d), 1)), U32.shr(U32.shln(1, d)))), (c, o), eq) : {Array.set.fin(T, _) == c : Array<T>}; {==}), wc, +j => fj(U32.and(j, U32.sub(U32.shln(1, d), 1)), U32.is_lt(U32.and(j, U32.sub(U32.shln(1, d), 1)), U32.shr(U32.shln(1, d)))), j => {==})

def set_other_k1(-T: Data, +d: Nat, -a: Array<T>, +i: U32, +v: T, w: &b: Array<T> -> {b == a : Array<T>} & Laws.WFArray(T, d, b) & {Array.size(T, a) == (b, U32.shln(1, d)) : Array<T> & U32})
  -> &c: Array<T> -> {Array.set(T, a, i, v) == c : Array<T>} & Laws.WFArray(T, d, c) & (@j: U32 -> {Laws.rdN(T, d, c, j) == Bool.pick(T, Laws.same_at(d, i, j), v, Laws.rdN(T, d, a, j)) : T}) & (@j: U32 -> {Laws.rd_at(T, a, j) == Laws.rdN(T, d, a, j) : T}):
  (b, eb, wb, es) = w
  %Equal.sym(Array<T> & U32, Array.size(T, a), (b, U32.shln(1, d)), es) : &c: Array<T> -> {Array.set.fin(T, Array.swap.at(T, i, v, _)) == c : Array<T>} & Laws.WFArray(T, d, c) & (@j: U32 -> {Laws.rdN(T, d, c, j) == Bool.pick(T, Laws.same_at(d, i, j), v, Laws.rdN(T, d, a, j)) : T}) & (@j: U32 -> {Laws.rd_size(T, j, _) == Laws.rdN(T, d, a, j) : T})
  %eb : &c: Array<T> -> {Array.set.fin(T, Array.swap.at(T, i, v, (b, U32.shln(1, d)))) == c : Array<T>} & Laws.WFArray(T, d, c) & (@j: U32 -> {Laws.rdN(T, d, c, j) == Bool.pick(T, Laws.same_at(d, i, j), v, Laws.rdN(T, d, _, j)) : T}) & (@j: U32 -> {Laws.rd_size(T, j, (b, U32.shln(1, d))) == Laws.rdN(T, d, _, j) : T})
  set_other_k2(T, d, b, i, v, sep(T, d, b, U32.shln(1, d), U32.and(i, U32.sub(U32.shln(1, d), 1)), v, U32.is_lt(U32.and(i, U32.sub(U32.shln(1, d), 1)), U32.shr(U32.shln(1, d))), wb))

# Array.set(a, i, v) on a well-formed array of depth d: the written array (well formed) and every
# cell afterwards: v where the masked paths of i and j agree, the old cell elsewhere
def set_other_w(-T: Data, +d: Nat, a: Array<T>, +i: U32, +v: T, wf: Laws.WFArray(T, d, a))
  -> &c: Array<T> -> {Array.set(T, a, i, v) == c : Array<T>} & Laws.WFArray(T, d, c) & (@j: U32 -> {Laws.rdN(T, d, c, j) == Bool.pick(T, Laws.same_at(d, i, j), v, Laws.rdN(T, d, a, j)) : T}) & (@j: U32 -> {Laws.rd_at(T, a, j) == Laws.rdN(T, d, a, j) : T}):
  set_other_k1(T, d, a, i, v, wf_size(T, d, a, wf))

def wf_set_fin(-T: Data, +d: Nat, -a: Array<T>, +i: U32, +v: T, w: &c: Array<T> -> {Array.set(T, a, i, v) == c : Array<T>} & Laws.WFArray(T, d, c) & (@j: U32 -> {Laws.rdN(T, d, c, j) == Bool.pick(T, Laws.same_at(d, i, j), v, Laws.rdN(T, d, a, j)) : T}) & (@j: U32 -> {Laws.rd_at(T, a, j) == Laws.rdN(T, d, a, j) : T})) -> Laws.WFArray(T, d, Array.set(T, a, i, v)):
  (c, ec, wc, fj, cv) = w
  %Equal.sym(Array<T>, Array.set(T, a, i, v), c, ec) : Laws.WFArray(T, d, _)
  wc

def Laws.wf_array_set(T, d, a, i, v, wf):
  wf_set_fin(T, d, a, i, v, set_other_w(T, d, a, i, v, wf))

# ---- the distinct-paths lemma (Laws.paths_distinct) -------------------------------------------

# U32.is_lt(U32{x}, U32.shln(1, d)) == True: x is below 2^d
def lt_shln_zabove(+d: Nat, +x: Word(32n)) -> {U32.is_lt(U32{x}, U32.shln(1, d)) == True{} : Bool} -> B.Zabove(d, 32n, x):
  %Equal.sym(U32, U32.shln(1, d), U32{B.bitw(32n, d)}, B.shln_bitw(d)) : {U32.is_lt(U32{x}, _) == True{} : Bool} -> B.Zabove(d, 32n, x)
  h => B.lt_bitw_zabove(32n, d, x, B.is_lt_lt(Word.cmp(32n, x, B.bitw(32n, d)), h))

# ... and NOT below 2^p: Word.cmp(x, bitw(p)) is not LT
def lt_shln_false(+p: Nat, +x: Word(32n)) -> {U32.is_lt(U32{x}, U32.shln(1, p)) == False{} : Bool} -> {Cmp.is_lt(Word.cmp(32n, x, B.bitw(32n, p))) == False{} : Bool}:
  %Equal.sym(U32, U32.shln(1, p), U32{B.bitw(32n, p)}, B.shln_bitw(p)) : {U32.is_lt(U32{x}, _) == False{} : Bool} -> {Cmp.is_lt(Word.cmp(32n, x, B.bitw(32n, p))) == False{} : Bool}
  h => h

# U32.sub(U32{x}, U32.shln(1, p)) as a word subtraction of the single bit
def sub_shln(+p: Nat, +x: Word(32n)) -> {U32.sub(U32{x}, U32.shln(1, p)) == U32{Word.sub(32n, x, B.bitw(32n, p))} : U32}:
  %Equal.sym(U32, U32.shln(1, p), U32{B.bitw(32n, p)}, B.shln_bitw(p)) : {U32.sub(U32{x}, _) == U32{Word.sub(32n, x, B.bitw(32n, p))} : U32}
  {==}

# nothing is below U32.shln(1, d) when it is 0
def shln_nz(+d: Nat, +x: Word(32n)) -> {U32.shln(1, d) == 0 : U32} -> {U32.is_lt(U32{x}, U32.shln(1, d)) == True{} : Bool} -> Empty:
  z =>
    %Equal.sym(U32, U32.shln(1, d), 0, z) : {U32.is_lt(U32{x}, _) == True{} : Bool} -> Empty
    h => B.lt_zero(32n, x, B.is_lt_lt(Word.cmp(32n, x, Word.zero(32n)), h))

# U32.shln(1, p) == 0 gives U32.shln(1, 1+p) == 0
def shl_zero(+p: Nat) -> {U32.shln(1, p) == 0 : U32} -> {U32.shln(1, 1n+p) == 0 : U32}:
  z =>
    %Equal.sym(U32, U32.shln(1, p), 0, z) : {U32.shl(_) == 0 : U32}
    {==}

# the node step of same_inj, by the two halving decisions (bi for x, bj for y), with
# U32.shr(U32.shln(1, 1+p)) == U32.shln(1, p) in hand; the decisions and the same_d
# hypothesis sit in the goal so one rewrite reaches them all
def same_inj_bits(bi: Bool, bj: Bool, +p: Nat, +x: Word(32n), +y: Word(32n), hx: B.Zabove(1n+p, 32n, x), hy: B.Zabove(1n+p, 32n, y), nz: {U32.shln(1, 1n+p) == 0 : U32} -> Empty, spec: {U32.shr(U32.shln(1, 1n+p)) == U32.shln(1, p) : U32},
  ih: @x2: Word(32n) -> @y2: Word(32n) -> B.Zabove(p, 32n, x2) -> B.Zabove(p, 32n, y2) -> ({U32.shln(1, p) == 0 : U32} -> Empty) -> {Laws.same_d(p, U32.shln(1, p), U32{x2}, U32.is_lt(U32{x2}, U32.shr(U32.shln(1, p))), U32{y2}, U32.is_lt(U32{y2}, U32.shr(U32.shln(1, p)))) == True{} : Bool} -> {x2 == y2 : Word(32n)})
  -> {U32.is_lt(U32{x}, U32.shr(U32.shln(1, 1n+p))) == bi : Bool} -> {U32.is_lt(U32{y}, U32.shr(U32.shln(1, 1n+p))) == bj : Bool} -> {Laws.same_d(1n+p, U32.shln(1, 1n+p), U32{x}, bi, U32{y}, bj) == True{} : Bool} -> {x == y : Word(32n)}:
  match bi bj:
    case True{} True{}:
      %Equal.sym(U32, U32.shr(U32.shln(1, 1n+p)), U32.shln(1, p), spec) : {U32.is_lt(U32{x}, _) == True{} : Bool} -> {U32.is_lt(U32{y}, _) == True{} : Bool} -> {Laws.same_d(p, _, U32{x}, U32.is_lt(U32{x}, U32.shr(_)), U32{y}, U32.is_lt(U32{y}, U32.shr(_))) == True{} : Bool} -> {x == y : Word(32n)}
      ex => ey => ih(x, y, lt_shln_zabove(p, x)(ex), lt_shln_zabove(p, y)(ey), z => nz(shl_zero(p)(z)))
    case False{} False{}:
      %Equal.sym(U32, U32.shr(U32.shln(1, 1n+p)), U32.shln(1, p), spec) : {U32.is_lt(U32{x}, _) == False{} : Bool} -> {U32.is_lt(U32{y}, _) == False{} : Bool} -> {Laws.same_d(p, _, U32.sub(U32{x}, _), U32.is_lt(U32.sub(U32{x}, _), U32.shr(_)), U32.sub(U32{y}, _), U32.is_lt(U32.sub(U32{y}, _), U32.shr(_))) == True{} : Bool} -> {x == y : Word(32n)}
      %Equal.sym(U32, U32.sub(U32{x}, U32.shln(1, p)), U32{Word.sub(32n, x, B.bitw(32n, p))}, sub_shln(p, x)) : {U32.is_lt(U32{x}, U32.shln(1, p)) == False{} : Bool} -> {U32.is_lt(U32{y}, U32.shln(1, p)) == False{} : Bool} -> {Laws.same_d(p, U32.shln(1, p), _, U32.is_lt(_, U32.shr(U32.shln(1, p))), U32.sub(U32{y}, U32.shln(1, p)), U32.is_lt(U32.sub(U32{y}, U32.shln(1, p)), U32.shr(U32.shln(1, p)))) == True{} : Bool} -> {x == y : Word(32n)}
      %Equal.sym(U32, U32.sub(U32{y}, U32.shln(1, p)), U32{Word.sub(32n, y, B.bitw(32n, p))}, sub_shln(p, y)) : {U32.is_lt(U32{x}, U32.shln(1, p)) == False{} : Bool} -> {U32.is_lt(U32{y}, U32.shln(1, p)) == False{} : Bool} -> {Laws.same_d(p, U32.shln(1, p), U32{Word.sub(32n, x, B.bitw(32n, p))}, U32.is_lt(U32{Word.sub(32n, x, B.bitw(32n, p))}, U32.shr(U32.shln(1, p))), _, U32.is_lt(_, U32.shr(U32.shln(1, p)))) == True{} : Bool} -> {x == y : Word(32n)}
      ex => ey => h => B.sub_inj(32n, x, y, B.bitw(32n, p), ih(Word.sub(32n, x, B.bitw(32n, p)), Word.sub(32n, y, B.bitw(32n, p)), B.sub_bit(32n, p, x, hx, lt_shln_false(p, x)(ex)), B.sub_bit(32n, p, y, hy, lt_shln_false(p, y)(ey)), z => nz(shl_zero(p)(z)))(h))
    case True{} False{}:
      ex => ey => h => Empty.absurd({x == y : Word(32n)}, L.false_true(h))
    case False{} True{}:
      ex => ey => h => Empty.absurd({x == y : Word(32n)}, L.false_true(h))

# the node step with the shr fact as a Bool-indexed witness (b False: 2^(1+p) is already 0)
def same_inj_case(b: Bool, +p: Nat, +x: Word(32n), +y: Word(32n), hx: B.Zabove(1n+p, 32n, x), hy: B.Zabove(1n+p, 32n, y), nz: {U32.shln(1, 1n+p) == 0 : U32} -> Empty, spec: B.ShrSpec(b, p),
  ih: @x2: Word(32n) -> @y2: Word(32n) -> B.Zabove(p, 32n, x2) -> B.Zabove(p, 32n, y2) -> ({U32.shln(1, p) == 0 : U32} -> Empty) -> {Laws.same_d(p, U32.shln(1, p), U32{x2}, U32.is_lt(U32{x2}, U32.shr(U32.shln(1, p))), U32{y2}, U32.is_lt(U32{y2}, U32.shr(U32.shln(1, p)))) == True{} : Bool} -> {x2 == y2 : Word(32n)})
  -> {Laws.same_d(1n+p, U32.shln(1, 1n+p), U32{x}, U32.is_lt(U32{x}, U32.shr(U32.shln(1, 1n+p))), U32{y}, U32.is_lt(U32{y}, U32.shr(U32.shln(1, 1n+p)))) == True{} : Bool} -> {x == y : Word(32n)}:
  match b:
    case False{}:
      h => Empty.absurd({x == y : Word(32n)}, nz(spec))
    case True{}:
      same_inj_bits(U32.is_lt(U32{x}, U32.shr(U32.shln(1, 1n+p))), U32.is_lt(U32{y}, U32.shr(U32.shln(1, 1n+p))), p, x, y, hx, hy, nz, spec, ih)({==})({==})

def same_inj_step(+p: Nat, +x: Word(32n), +y: Word(32n), hx: B.Zabove(1n+p, 32n, x), hy: B.Zabove(1n+p, 32n, y), nz: {U32.shln(1, 1n+p) == 0 : U32} -> Empty, w: &b: Bool -> B.ShrSpec(b, p),
  ih: @x2: Word(32n) -> @y2: Word(32n) -> B.Zabove(p, 32n, x2) -> B.Zabove(p, 32n, y2) -> ({U32.shln(1, p) == 0 : U32} -> Empty) -> {Laws.same_d(p, U32.shln(1, p), U32{x2}, U32.is_lt(U32{x2}, U32.shr(U32.shln(1, p))), U32{y2}, U32.is_lt(U32{y2}, U32.shr(U32.shln(1, p)))) == True{} : Bool} -> {x2 == y2 : Word(32n)})
  -> {Laws.same_d(1n+p, U32.shln(1, 1n+p), U32{x}, U32.is_lt(U32{x}, U32.shr(U32.shln(1, 1n+p))), U32{y}, U32.is_lt(U32{y}, U32.shr(U32.shln(1, 1n+p)))) == True{} : Bool} -> {x == y : Word(32n)}:
  (b, spec) = w
  same_inj_case(b, p, x, y, hx, hy, nz, spec, ih)

# two words below 2^d whose halving decisions agree all the way down are equal
def same_inj(d: Nat, +x: Word(32n), +y: Word(32n), hx: B.Zabove(d, 32n, x), hy: B.Zabove(d, 32n, y), nz: {U32.shln(1, d) == 0 : U32} -> Empty)
  -> {Laws.same_d(d, U32.shln(1, d), U32{x}, U32.is_lt(U32{x}, U32.shr(U32.shln(1, d))), U32{y}, U32.is_lt(U32{y}, U32.shr(U32.shln(1, d)))) == True{} : Bool} -> {x == y : Word(32n)}:
  match d:
    case 0n:
      h =>
        %Equal.sym(Word(32n), x, Word.zero(32n), hx) : {_ == y : Word(32n)}
        %Equal.sym(Word(32n), y, Word.zero(32n), hy) : {Word.zero(32n) == _ : Word(32n)}
        {==}
    case 1n++p:
      same_inj_step(p, x, y, hx, hy, nz, B.shr_shln(p), x2 => y2 => hx2 => hy2 => nz2 => same_inj(p, x2, y2, hx2, hy2, nz2))

# same_at with the masks removed (both indices below 2^d)
def paths_k(+d: Nat, +x: Word(32n), +y: Word(32n), hx: B.Zabove(d, 32n, x), hx2: B.Zabove(d, 32n, x), hy: B.Zabove(d, 32n, y), hy2: B.Zabove(d, 32n, y), nz: {U32.shln(1, d) == 0 : U32} -> Empty) -> {Laws.same_at(d, U32{x}, U32{y}) == True{} : Bool} -> {U32{x} == U32{y} : U32}:
  %Equal.sym(U32, U32.and(U32{x}, U32.sub(U32.shln(1, d), 1)), U32{x}, B.mask_id(d, x, hx)) : {Laws.same_d(d, U32.shln(1, d), _, U32.is_lt(_, U32.shr(U32.shln(1, d))), U32.and(U32{y}, U32.sub(U32.shln(1, d), 1)), U32.is_lt(U32.and(U32{y}, U32.sub(U32.shln(1, d), 1)), U32.shr(U32.shln(1, d)))) == True{} : Bool} -> {U32{x} == U32{y} : U32}
  %Equal.sym(U32, U32.and(U32{y}, U32.sub(U32.shln(1, d), 1)), U32{y}, B.mask_id(d, y, hy)) : {Laws.same_d(d, U32.shln(1, d), U32{x}, U32.is_lt(U32{x}, U32.shr(U32.shln(1, d))), _, U32.is_lt(_, U32.shr(U32.shln(1, d)))) == True{} : Bool} -> {U32{x} == U32{y} : U32}
  h => Equal.cong(Word(32n), U32, w => U32{w}, x, y, same_inj(d, x, y, hx2, hy2, nz)(h))

def Laws.paths_distinct(d, i, j, hi, hj, h):
  match i j:
    case U32{+x} U32{+y}:
      paths_k(d, x, y, lt_shln_zabove(d, x)(hi), lt_shln_zabove(d, x)(hi), lt_shln_zabove(d, y)(hj), lt_shln_zabove(d, y)(hj), z => shln_nz(d, x)(z)(hi))(h)

# ---- Laws.array_set_other ---------------------------------------------------------------------

# the same leaf for i and i (rd's descent is deterministic)
def same_d_refl(d: Nat, +n: U32, +i: U32, zi: Bool) -> {Laws.same_d(d, n, i, zi, i, zi) == True{} : Bool}:
  match d zi:
    case 0n _:
      {==}
    case 1n+p True{}:
      same_d_refl(p, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n))))
    case 1n+p False{}:
      same_d_refl(p, U32.shr(n), U32.sub(i, U32.shr(n)), U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))

def same_at_refl(+d: Nat, +i: U32) -> {Laws.same_at(d, i, i) == True{} : Bool}:
  same_d_refl(d, U32.shln(1, d), U32.and(i, U32.sub(U32.shln(1, d), 1)), U32.is_lt(U32.and(i, U32.sub(U32.shln(1, d), 1)), U32.shr(U32.shln(1, d))))

# same_at(d, i, j) == False for distinct i, j below 2^d: the value s = same_at(d, i, j) is a parameter
def same_false_k(s: Bool, +d: Nat, +i: U32, +j: U32, +hi: {U32.is_lt(i, U32.shln(1, d)) == True{} : Bool}, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, ne: {i == j : U32} -> Empty, e: {Laws.same_at(d, i, j) == s : Bool}) -> {Laws.same_at(d, i, j) == False{} : Bool}:
  match s:
    case True{}:
      Empty.absurd({Laws.same_at(d, i, j) == False{} : Bool}, ne(Laws.paths_distinct(d, i, j, hi, hj, e)))
    case False{}:
      e

def same_false(+d: Nat, +i: U32, +j: U32, +hi: {U32.is_lt(i, U32.shln(1, d)) == True{} : Bool}, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, ne: {i == j : U32} -> Empty) -> {Laws.same_at(d, i, j) == False{} : Bool}:
  same_false_k(Laws.same_at(d, i, j), d, i, j, hi, hj, ne, {==})

def set_other_fin(-T: Data, +d: Nat, -a: Array<T>, +i: U32, +j: U32, +v: T, +hi: {U32.is_lt(i, U32.shln(1, d)) == True{} : Bool}, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, ne: {i == j : U32} -> Empty,
  w: &c: Array<T> -> {Array.set(T, a, i, v) == c : Array<T>} & Laws.WFArray(T, d, c) & (@j2: U32 -> {Laws.rdN(T, d, c, j2) == Bool.pick(T, Laws.same_at(d, i, j2), v, Laws.rdN(T, d, a, j2)) : T}) & (@j2: U32 -> {Laws.rd_at(T, a, j2) == Laws.rdN(T, d, a, j2) : T}))
  -> {Laws.rd_at(T, Array.set(T, a, i, v), j) == Laws.rd_at(T, a, j) : T}:
  (c, ec, wc, fj, cv) = w
  %Equal.sym(Array<T>, Array.set(T, a, i, v), c, ec) : {Laws.rd_at(T, _, j) == Laws.rd_at(T, a, j) : T}
  %Equal.sym(T, Laws.rd_at(T, c, j), Laws.rdN(T, d, c, j), Laws.rd_at_wf(T, d, c, j, wc)) : {_ == Laws.rd_at(T, a, j) : T}
  %Equal.sym(T, Laws.rdN(T, d, c, j), Bool.pick(T, Laws.same_at(d, i, j), v, Laws.rdN(T, d, a, j)), fj(j)) : {_ == Laws.rd_at(T, a, j) : T}
  %cv(j) : {Bool.pick(T, Laws.same_at(d, i, j), v, _) == Laws.rd_at(T, a, j) : T}
  %Equal.sym(Bool, Laws.same_at(d, i, j), False{}, same_false(d, i, j, hi, hj, ne)) : {Bool.pick(T, _, v, Laws.rd_at(T, a, j)) == Laws.rd_at(T, a, j) : T}
  {==}

def Laws.array_set_other(T, d, a, i, j, v, wf, hi, hj, ne):
  set_other_fin(T, d, a, i, j, v, hi, hj, ne, set_other_w(T, d, a, i, v, wf))

# ---- Array.get handing the array back live (the kernels read src / perm every step) -----------

def get_w_lo(-T: Data, -xs: Array<T>, ys: Array<T>, +n: U32, +i: U32, w: &b: Array<T> -> &x: T -> {b == xs : Array<T>} & {Array.get.go(T, xs, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n)))) == (xs, x) : Array<T> & T} & {x == Laws.rd(T, xs, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n)))) : T})
  -> &b2: Array<T> -> &x2: T -> {b2 == ANode{xs, ys} : Array<T>} & {Array.get.go(T, ANode{xs, ys}, n, i, True{}) == (ANode{xs, ys}, x2) : Array<T> & T} & {x2 == Laws.rd(T, ANode{xs, ys}, n, i, True{}) : T}:
  (b, +x, eb, e1, e2) = w
  (ANode{b, ys}, x, (%eb : {ANode{b, ys} == ANode{_, ys} : Array<T>}; {==}), (%Equal.sym(Array<T> & T, Array.get.go(T, xs, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n)))), (xs, x), e1) : {Array.swap.lo(T, ys, _) == (ANode{xs, ys}, x) : Array<T> & T}; {==}), e2)

def get_w_hi(-T: Data, xs: Array<T>, -ys: Array<T>, +n: U32, +i: U32, w: &b: Array<T> -> &x: T -> {b == ys : Array<T>} & {Array.get.go(T, ys, U32.shr(n), U32.sub(i, U32.shr(n)), U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))) == (ys, x) : Array<T> & T} & {x == Laws.rd(T, ys, U32.shr(n), U32.sub(i, U32.shr(n)), U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))) : T})
  -> &b2: Array<T> -> &x2: T -> {b2 == ANode{xs, ys} : Array<T>} & {Array.get.go(T, ANode{xs, ys}, n, i, False{}) == (ANode{xs, ys}, x2) : Array<T> & T} & {x2 == Laws.rd(T, ANode{xs, ys}, n, i, False{}) : T}:
  (b, +x, eb, e1, e2) = w
  (ANode{xs, b}, x, (%eb : {ANode{xs, b} == ANode{xs, _} : Array<T>}; {==}), (%Equal.sym(Array<T> & T, Array.get.go(T, ys, U32.shr(n), U32.sub(i, U32.shr(n)), U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))), (ys, x), e1) : {Array.swap.hi(T, xs, _) == (ANode{xs, ys}, x) : Array<T> & T}; {==}), e2)

def get_w_go(-T: Data, a: Array<T>, +n: U32, +i: U32, z: Bool) -> &b: Array<T> -> &x: T -> {b == a : Array<T>} & {Array.get.go(T, a, n, i, z) == (a, x) : Array<T> & T} & {x == Laws.rd(T, a, n, i, z) : T}:
  match a z:
    case ALeaf{+x} _:
      (ALeaf{x}, x, {==}, {==}, {==})
    case ANode{xs, ys} True{}:
      get_w_lo(T, xs, ys, n, i, get_w_go(T, xs, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n)))))
    case ANode{xs, ys} False{}:
      get_w_hi(T, xs, ys, n, i, get_w_go(T, ys, U32.shr(n), U32.sub(i, U32.shr(n)), U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))))

def get_w_at(-T: Data, -a: Array<T>, -b: Array<T>, +i: U32, +n: U32, eb: {b == a : Array<T>}, es: {Array.size(T, a) == (b, n) : Array<T> & U32},
  w: &b2: Array<T> -> &x: T -> {b2 == b : Array<T>} & {Array.get.go(T, b, n, U32.and(i, U32.sub(n, 1)), U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))) == (b, x) : Array<T> & T} & {x == Laws.rd(T, b, n, U32.and(i, U32.sub(n, 1)), U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))) : T})
  -> &b3: Array<T> -> &x2: T -> {b3 == a : Array<T>} & {Array.get(T, a, i) == (a, x2) : Array<T> & T} & {x2 == Laws.rd_at(T, a, i) : T}:
  (b2, +x, eb2, e1, e2) = w
  %Equal.sym(Array<T> & U32, Array.size(T, a), (b, n), es) : &b3: Array<T> -> &x2: T -> {b3 == a : Array<T>} & {Array.get.at(T, i, _) == (a, x2) : Array<T> & T} & {x2 == Laws.rd_size(T, i, _) : T}
  %eb : &b3: Array<T> -> &x2: T -> {b3 == _ : Array<T>} & {Array.get.go(T, b, n, U32.and(i, U32.sub(n, 1)), U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))) == (_, x2) : Array<T> & T} & {x2 == Laws.rd_size(T, i, (b, n)) : T}
  (b2, x, eb2, e1, e2)

def get_w_k(-T: Data, -a: Array<T>, +i: U32, w: &b: Array<T> -> &n: U32 -> {b == a : Array<T>} & {Array.size(T, a) == (b, n) : Array<T> & U32} & {Laws.slots(T, b) == n : U32})
  -> &b3: Array<T> -> &x: T -> {b3 == a : Array<T>} & {Array.get(T, a, i) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, i) : T}:
  (b, n0, eb, es, sl) = w
  +n = n0
  get_w_at(T, a, b, i, n, eb, es, get_w_go(T, b, n, U32.and(i, U32.sub(n, 1)), U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))))

# Array.get(a, i): the array back live (equal to a), the pure answer, and its model
def get_w(-T: Data, a: Array<T>, +i: U32) -> &b: Array<T> -> &x: T -> {b == a : Array<T>} & {Array.get(T, a, i) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, i) : T}:
  get_w_k(T, a, i, PK.size_same(T, a))

# ---- U32 comparison helpers for the loop counters --------------------------------------------

def IncLtU(b: Bool, +k: U32, +j: U32) -> Type:
  match b:
    case True{}:
      {U32.is_lt(k, j) == True{} : Bool}
    case False{}:
      {k == j : U32}

def inc_lt_u_k(b: Bool, +x: Word(32n), +y: Word(32n), s: B.IncLt(b, 32n, x, y)) -> IncLtU(b, U32{x}, U32{y}):
  match b:
    case True{}:
      %Equal.sym(Cmp, Word.cmp(32n, x, y), LT{}, s) : {Cmp.is_lt(_) == True{} : Bool}
      {==}
    case False{}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y, s)

def inc_lt_u_fin(+x: Word(32n), +y: Word(32n), w: &b: Bool -> B.IncLt(b, 32n, x, y)) -> &b2: Bool -> IncLtU(b2, U32{x}, U32{y}):
  (+b, s) = w
  (b, inc_lt_u_k(b, x, y, s))

# k < inc(j) is k < j or k == j
def inc_lt_u(k: U32, j: U32, h: {U32.is_lt(k, U32.inc(j)) == True{} : Bool}) -> &b: Bool -> IncLtU(b, k, j):
  match k j:
    case U32{+x} U32{+y}:
      inc_lt_u_fin(x, y, B.inc_lt(32n, x, y, B.is_lt_lt(Word.cmp(32n, x, Word.inc(32n, y)), h)))

def lt_trans_u(k: U32, j: U32, m: U32, h1: {U32.is_lt(k, j) == True{} : Bool}, h2: {U32.is_lt(j, m) == True{} : Bool}) -> {U32.is_lt(k, m) == True{} : Bool}:
  match k j m:
    case U32{+x} U32{+y} U32{+w}:
      %Equal.sym(Cmp, Word.cmp(32n, x, w), LT{}, L.word_lt_trans(32n, x, y, w, B.is_lt_lt(Word.cmp(32n, x, y), h1), B.is_lt_lt(Word.cmp(32n, y, w), h2))) : {Cmp.is_lt(_) == True{} : Bool}
      {==}

def lt_irrefl(k: U32, h: {U32.is_lt(k, k) == True{} : Bool}) -> Empty:
  match k:
    case U32{+x}:
      L.lt_eq(Equal.trans(Cmp, LT{}, Word.cmp(32n, x, x), EQ{}, Equal.sym(Cmp, Word.cmp(32n, x, x), LT{}, B.is_lt_lt(Word.cmp(32n, x, x), h)), L.word_cmp_refl(32n, x)))

# j == k and k < j cannot both hold
def lt_ne(+j: U32, +k: U32) -> {j == k : U32} -> {U32.is_lt(k, j) == True{} : Bool} -> Empty:
  e =>
    %Equal.sym(U32, j, k, e) : {U32.is_lt(k, _) == True{} : Bool} -> Empty
    h => lt_irrefl(k, h)

# nothing is below 0
def lt0(k: U32, h: {U32.is_lt(k, 0) == True{} : Bool}) -> Empty:
  match k:
    case U32{+x}:
      B.lt_zero(32n, x, B.is_lt_lt(Word.cmp(32n, x, Word.zero(32n)), h))

def addn_inc(+j: U32, p: Nat) -> {Laws.addn(U32.inc(j), p) == U32.inc(Laws.addn(j, p)) : U32}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      %Equal.sym(U32, Laws.addn(U32.inc(j), q), U32.inc(Laws.addn(j, q)), addn_inc(j, q)) : {U32.inc(_) == U32.inc(U32.inc(Laws.addn(j, q))) : U32}
      {==}

# same_at(d, j, k) == False for k < j < 2^d
def same_false_lt(+d: Nat, +j: U32, +k: U32, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +lt: {U32.is_lt(k, j) == True{} : Bool}) -> {Laws.same_at(d, j, k) == False{} : Bool}:
  same_false(d, j, k, hj, lt_trans_u(k, j, U32.shln(1, d), lt, hj), e => lt_ne(j, k)(e)(lt))

# ---- the gather loop: goal shapes --------------------------------------------------------------

# every k < j already holds src[perm[k]] in out
def GHyp(+j: U32, +d: Nat, -src: Array<U32>, -out: Array<U32>, -perm: Array<U32>) -> Type:
  @k: U32 -> {U32.is_lt(k, j) == True{} : Bool} -> {Laws.rdN(U32, d, out, k) == Laws.rd_at(U32, src, Laws.rd_at(U32, perm, k)) : U32}

# the result: perm back, the output well formed, every k < bound holding src[perm[k]]
def GRes(+d: Nat, -src: Array<U32>, -perm: Array<U32>, o: Array<U32>, -pm: Array<U32>, +bound: U32) -> Type:
  {pm == perm : Array<U32>} & Laws.WFArray(U32, d, o) & (@k: U32 -> {U32.is_lt(k, bound) == True{} : Bool} -> {Laws.rdN(U32, d, o, k) == Laws.rd_at(U32, src, Laws.rd_at(U32, perm, k)) : U32})

# the loop with f steps left at counter j and the pending read r of perm[j]
def GGoal(f: Nat, +j: U32, +d: Nat, -src: Array<U32>, -out: Array<U32>, -perm: Array<U32>, -r: Array<U32> & U32) -> Type:
  GHyp(j, d, src, out, perm) -> &o: Array<U32> -> &pm: Array<U32> -> {K.Kernel.gather.go(~U32, f, j, (src, out), r) == (o, pm) : Array<U32> & Array<U32>} & GRes(d, src, perm, o, pm, Laws.addn(j, f))

# ... after one step, with the read rs of src[perm[j]] pending
def GMid(p: Nat, +j: U32, +d: Nat, -src: Array<U32>, -out: Array<U32>, -perm: Array<U32>, -rs: Array<U32> & U32) -> Type:
  GHyp(j, d, src, out, perm) -> &o: Array<U32> -> &pm: Array<U32> -> {K.Kernel.gather.go(~U32, p, U32.inc(j), K.Kernel.gather.put(~U32, out, j, rs), Array.get(U32, perm, U32.inc(j))) == (o, pm) : Array<U32> & Array<U32>} & GRes(d, src, perm, o, pm, Laws.addn(j, 1n+p))

# ... with the cell y written at j
def GSet(p: Nat, +j: U32, +d: Nat, -src: Array<U32>, -out: Array<U32>, -perm: Array<U32>, +y: U32) -> Type:
  GHyp(j, d, src, out, perm) -> &o: Array<U32> -> &pm: Array<U32> -> {K.Kernel.gather.go(~U32, p, U32.inc(j), (src, Array.set(U32, out, j, y)), Array.get(U32, perm, U32.inc(j))) == (o, pm) : Array<U32> & Array<U32>} & GRes(d, src, perm, o, pm, Laws.addn(j, 1n+p))

# ... with the written array c in place and the bound as a parameter
def GC(p: Nat, +j: U32, +d: Nat, -src: Array<U32>, -out: Array<U32>, -c: Array<U32>, -perm: Array<U32>, +bound: U32) -> Type:
  GHyp(j, d, src, out, perm) -> &o: Array<U32> -> &pm: Array<U32> -> {K.Kernel.gather.go(~U32, p, U32.inc(j), (src, c), Array.get(U32, perm, U32.inc(j))) == (o, pm) : Array<U32> & Array<U32>} & GRes(d, src, perm, o, pm, bound)

# ---- the invariant after a write at j ----------------------------------------------------------

# k < j: the slot k is untouched (distinct paths) and already right
def gnext_lt(+d: Nat, +j: U32, +k: U32, -src: Array<U32>, -perm: Array<U32>, -out: Array<U32>, -c: Array<U32>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +y: U32, g: GHyp(j, d, src, out, perm),
  fj: @k2: U32 -> {Laws.rdN(U32, d, c, k2) == Bool.pick(U32, Laws.same_at(d, j, k2), y, Laws.rdN(U32, d, out, k2)) : U32}, +lt: {U32.is_lt(k, j) == True{} : Bool})
  -> {Laws.rdN(U32, d, c, k) == Laws.rd_at(U32, src, Laws.rd_at(U32, perm, k)) : U32}:
  %Equal.sym(U32, Laws.rdN(U32, d, c, k), Bool.pick(U32, Laws.same_at(d, j, k), y, Laws.rdN(U32, d, out, k)), fj(k)) : {_ == Laws.rd_at(U32, src, Laws.rd_at(U32, perm, k)) : U32}
  %Equal.sym(Bool, Laws.same_at(d, j, k), False{}, same_false_lt(d, j, k, hj, lt)) : {Bool.pick(U32, _, y, Laws.rdN(U32, d, out, k)) == Laws.rd_at(U32, src, Laws.rd_at(U32, perm, k)) : U32}
  g(k, lt)

def gnext_b(b: Bool, +d: Nat, +j: U32, +k: U32, -src: Array<U32>, -perm: Array<U32>, -out: Array<U32>, -c: Array<U32>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +y: U32, ey: {y == Laws.rd_at(U32, src, Laws.rd_at(U32, perm, j)) : U32}, g: GHyp(j, d, src, out, perm),
  fj: @k2: U32 -> {Laws.rdN(U32, d, c, k2) == Bool.pick(U32, Laws.same_at(d, j, k2), y, Laws.rdN(U32, d, out, k2)) : U32}, s: IncLtU(b, k, j))
  -> {Laws.rdN(U32, d, c, k) == Laws.rd_at(U32, src, Laws.rd_at(U32, perm, k)) : U32}:
  match b:
    case True{}:
      gnext_lt(d, j, k, src, perm, out, c, hj, y, g, fj, s)
    case False{}:
      %Equal.sym(U32, k, j, s) : {Laws.rdN(U32, d, c, _) == Laws.rd_at(U32, src, Laws.rd_at(U32, perm, _)) : U32}
      %Equal.sym(U32, Laws.rdN(U32, d, c, j), Bool.pick(U32, Laws.same_at(d, j, j), y, Laws.rdN(U32, d, out, j)), fj(j)) : {_ == Laws.rd_at(U32, src, Laws.rd_at(U32, perm, j)) : U32}
      %Equal.sym(Bool, Laws.same_at(d, j, j), True{}, same_at_refl(d, j)) : {Bool.pick(U32, _, y, Laws.rdN(U32, d, out, j)) == Laws.rd_at(U32, src, Laws.rd_at(U32, perm, j)) : U32}
      ey

def gnext_k(+d: Nat, +j: U32, +k: U32, -src: Array<U32>, -perm: Array<U32>, -out: Array<U32>, -c: Array<U32>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +y: U32, ey: {y == Laws.rd_at(U32, src, Laws.rd_at(U32, perm, j)) : U32}, g: GHyp(j, d, src, out, perm),
  fj: @k2: U32 -> {Laws.rdN(U32, d, c, k2) == Bool.pick(U32, Laws.same_at(d, j, k2), y, Laws.rdN(U32, d, out, k2)) : U32}, w: &b: Bool -> IncLtU(b, k, j))
  -> {Laws.rdN(U32, d, c, k) == Laws.rd_at(U32, src, Laws.rd_at(U32, perm, k)) : U32}:
  (b, s) = w
  gnext_b(b, d, j, k, src, perm, out, c, hj, y, ey, g, fj, s)

# the invariant moves from j to inc(j) once slot j holds src[perm[j]]
def gnext(+d: Nat, +j: U32, -src: Array<U32>, -perm: Array<U32>, -out: Array<U32>, -c: Array<U32>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +y: U32, +ey: {y == Laws.rd_at(U32, src, Laws.rd_at(U32, perm, j)) : U32}, g: GHyp(j, d, src, out, perm),
  fj: @k2: U32 -> {Laws.rdN(U32, d, c, k2) == Bool.pick(U32, Laws.same_at(d, j, k2), y, Laws.rdN(U32, d, out, k2)) : U32})
  -> GHyp(U32.inc(j), d, src, c, perm):
  +k => hk => gnext_k(d, j, k, src, perm, out, c, hj, y, ey, g, fj, inc_lt_u(k, j, hk))

# ---- the gather loop -----------------------------------------------------------------------------

def gather_step3(p: Nat, +j: U32, +d: Nat, src: Array<U32>, -out: Array<U32>, perm: Array<U32>, +y: U32, +ey: {y == Laws.rd_at(U32, src, Laws.rd_at(U32, perm, j)) : U32}, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, room: Laws.Room(d, U32.inc(j), p),
  ih: @src2: Array<U32> -> @c: Array<U32> -> @perm2: Array<U32> -> Laws.WFArray(U32, d, c) -> Laws.Room(d, U32.inc(j), p) -> GGoal(p, U32.inc(j), d, src2, c, perm2, Array.get(U32, perm2, U32.inc(j))),
  w: &c: Array<U32> -> {Array.set(U32, out, j, y) == c : Array<U32>} & Laws.WFArray(U32, d, c) & (@k2: U32 -> {Laws.rdN(U32, d, c, k2) == Bool.pick(U32, Laws.same_at(d, j, k2), y, Laws.rdN(U32, d, out, k2)) : U32}) & (@k2: U32 -> {Laws.rd_at(U32, out, k2) == Laws.rdN(U32, d, out, k2) : U32}))
  -> GSet(p, j, d, src, out, perm, y):
  (c, ec, wc, fj, cv) = w
  %Equal.sym(Array<U32>, Array.set(U32, out, j, y), c, ec) : GC(p, j, d, src, out, _, perm, Laws.addn(j, 1n+p))
  %addn_inc(j, p) : GC(p, j, d, src, out, c, perm, _)
  g => ih(src, c, perm, wc, room)(gnext(d, j, src, perm, out, c, hj, y, ey, g, fj))

def gather_step2(p: Nat, +j: U32, +d: Nat, -src: Array<U32>, out: Array<U32>, perm: Array<U32>, wf: Laws.WFArray(U32, d, out), +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, room: Laws.Room(d, U32.inc(j), p),
  ih: @src2: Array<U32> -> @c: Array<U32> -> @perm2: Array<U32> -> Laws.WFArray(U32, d, c) -> Laws.Room(d, U32.inc(j), p) -> GGoal(p, U32.inc(j), d, src2, c, perm2, Array.get(U32, perm2, U32.inc(j))),
  +x: U32, ex: {x == Laws.rd_at(U32, perm, j) : U32},
  w: &b: Array<U32> -> &y: U32 -> {b == src : Array<U32>} & {Array.get(U32, src, x) == (src, y) : Array<U32> & U32} & {y == Laws.rd_at(U32, src, x) : U32})
  -> GMid(p, j, d, src, out, perm, Array.get(U32, src, x)):
  (src2, +y, +es, e2, ey) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, src, x), (src, y), e2) : GMid(p, j, d, src, out, perm, _)
  %es : GSet(p, j, d, _, out, perm, y)
  gather_step3(p, j, d, src2, out, perm, y, Equal.trans(U32, y, Laws.rd_at(U32, src2, x), Laws.rd_at(U32, src2, Laws.rd_at(U32, perm, j)), Equal.trans(U32, y, Laws.rd_at(U32, src, x), Laws.rd_at(U32, src2, x), ey, Equal.sym(U32, Laws.rd_at(U32, src2, x), Laws.rd_at(U32, src, x), Equal.cong(Array<U32>, U32, a => Laws.rd_at(U32, a, x), src2, src, es))), Equal.cong(U32, U32, a => Laws.rd_at(U32, src2, a), x, Laws.rd_at(U32, perm, j), ex)), hj, room, ih, set_other_w(U32, d, out, j, y, wf))

def gather_step1(p: Nat, +j: U32, +d: Nat, src: Array<U32>, out: Array<U32>, -perm: Array<U32>, wf: Laws.WFArray(U32, d, out), room: Laws.Room(d, j, 1n+p),
  ih: @src2: Array<U32> -> @c: Array<U32> -> @perm2: Array<U32> -> Laws.WFArray(U32, d, c) -> Laws.Room(d, U32.inc(j), p) -> GGoal(p, U32.inc(j), d, src2, c, perm2, Array.get(U32, perm2, U32.inc(j))),
  w: &b: Array<U32> -> &x: U32 -> {b == perm : Array<U32>} & {Array.get(U32, perm, j) == (perm, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, perm, j) : U32})
  -> GGoal(1n+p, j, d, src, out, perm, Array.get(U32, perm, j)):
  (hj, room2) = room
  (perm2, +x, +ep, e1, ex) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, perm, j), (perm, x), e1) : GGoal(1n+p, j, d, src, out, perm, _)
  %ep : GGoal(1n+p, j, d, src, out, _, (_, x))
  gather_step2(p, j, d, src, out, perm2, wf, hj, room2, ih, x, Equal.trans(U32, x, Laws.rd_at(U32, perm, j), Laws.rd_at(U32, perm2, j), ex, Equal.sym(U32, Laws.rd_at(U32, perm2, j), Laws.rd_at(U32, perm, j), Equal.cong(Array<U32>, U32, a => Laws.rd_at(U32, a, j), perm2, perm, ep))), get_w(U32, src, x))

def gather_zero(+j: U32, +d: Nat, src: Array<U32>, out: Array<U32>, -perm: Array<U32>, wf: Laws.WFArray(U32, d, out),
  w: &b: Array<U32> -> &x: U32 -> {b == perm : Array<U32>} & {Array.get(U32, perm, j) == (perm, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, perm, j) : U32})
  -> GGoal(0n, j, d, src, out, perm, Array.get(U32, perm, j)):
  (perm2, +x, ep, e1, ex) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, perm, j), (perm, x), e1) : GGoal(0n, j, d, src, out, perm, _)
  %ep : GGoal(0n, j, d, src, out, _, (_, x))
  g => (out, perm2, {==}, {==}, wf, g)

# Kernel.gather.go with f steps left at counter j, every k < j already right, the next f indices
# fitting the output: afterwards every k < addn(j, f) holds src[perm[k]]; perm comes back
def gather_go(f: Nat, +j: U32, +d: Nat, src: Array<U32>, out: Array<U32>, perm: Array<U32>, wf: Laws.WFArray(U32, d, out), room: Laws.Room(d, j, f)) -> GGoal(f, j, d, src, out, perm, Array.get(U32, perm, j)):
  match f:
    case 0n:
      gather_zero(j, d, src, out, perm, wf, get_w(U32, perm, j))
    case 1n++p:
      gather_step1(p, j, d, src, out, perm, wf, room, src2 => c => perm2 => wc => room2 => gather_go(p, U32.inc(j), d, src2, c, perm2, wc, room2), get_w(U32, perm, j))

# ---- Laws.gather_contents / Laws.gather_keeps_perm --------------------------------------------------

# the vacuous invariant at counter 0
def ghyp0(+d: Nat, -src: Array<U32>, -out: Array<U32>, -perm: Array<U32>) -> GHyp(0, d, src, out, perm):
  +k => hk => Empty.absurd({Laws.rdN(U32, d, out, k) == Laws.rd_at(U32, src, Laws.rd_at(U32, perm, k)) : U32}, lt0(k, hk))

def gather_fin(+d: Nat, +n: U32, -src: Array<U32>, -perm: Array<U32>, +z: U32, +k: U32, hk: {U32.is_lt(k, n) == True{} : Bool},
  w: &o: Array<U32> -> &pm: Array<U32> -> {K.Kernel.gather.go(~U32, U32.to_nat(n), 0, (src, Array.new(U32, d, z)), Array.get(U32, perm, 0)) == (o, pm) : Array<U32> & Array<U32>} & GRes(d, src, perm, o, pm, Laws.addn(0, U32.to_nat(n))))
  -> {Laws.rd_at(U32, Pair.fst(Array<U32>, Array<U32>, K.Kernel.gather(~U32, n, d, src, perm, z)), k) == Laws.rd_at(U32, src, Laws.rd_at(U32, perm, k)) : U32}:
  (o, pm, eq, epm, wo, spec) = w
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.gather.go(~U32, U32.to_nat(n), 0, (src, Array.new(U32, d, z)), Array.get(U32, perm, 0)), (o, pm), eq) : {Laws.rd_at(U32, Pair.fst(Array<U32>, Array<U32>, _), k) == Laws.rd_at(U32, src, Laws.rd_at(U32, perm, k)) : U32}
  %Equal.sym(U32, Laws.rd_at(U32, o, k), Laws.rdN(U32, d, o, k), Laws.rd_at_wf(U32, d, o, k, wo)) : {_ == Laws.rd_at(U32, src, Laws.rd_at(U32, perm, k)) : U32}
  spec(k, (%Equal.sym(U32, Laws.addn(0, U32.to_nat(n)), n, B.addn_to_nat(n)) : {U32.is_lt(k, _) == True{} : Bool}; hk))

def Laws.gather_contents(d, n, src, perm, z, k, fits, hk):
  gather_fin(d, n, src, perm, z, k, hk, gather_go(U32.to_nat(n), 0, d, src, Array.new(U32, d, z), perm, Laws.wf_new(U32, d, z), B.room_from(d, n, fits))(ghyp0(d, src, Array.new(U32, d, z), perm)))

def gather_perm_fin(+d: Nat, +n: U32, -src: Array<U32>, -perm: Array<U32>, +z: U32,
  w: &o: Array<U32> -> &pm: Array<U32> -> {K.Kernel.gather.go(~U32, U32.to_nat(n), 0, (src, Array.new(U32, d, z)), Array.get(U32, perm, 0)) == (o, pm) : Array<U32> & Array<U32>} & GRes(d, src, perm, o, pm, Laws.addn(0, U32.to_nat(n))))
  -> {Pair.snd(Array<U32>, Array<U32>, K.Kernel.gather(~U32, n, d, src, perm, z)) == perm : Array<U32>}:
  (o, pm, eq, epm, wo, spec) = w
  %Equal.sym(Array<U32> & Array<U32>, K.Kernel.gather.go(~U32, U32.to_nat(n), 0, (src, Array.new(U32, d, z)), Array.get(U32, perm, 0)), (o, pm), eq) : {Pair.snd(Array<U32>, Array<U32>, _) == perm : Array<U32>}
  epm

def Laws.gather_keeps_perm(d, n, src, perm, z, fits):
  gather_perm_fin(d, n, src, perm, z, gather_go(U32.to_nat(n), 0, d, src, Array.new(U32, d, z), perm, Laws.wf_new(U32, d, z), B.room_from(d, n, fits))(ghyp0(d, src, Array.new(U32, d, z), perm)))

# ---- Kernel.map: out[k] == f(a[k]) (template proofs; the laws are stated at the mask instances) ----

def MHyp(~T: Data, ~U: Data, ~f: T -> U, +j: U32, +d: Nat, -a: Array<T>, -out: Array<U>) -> Type:
  @k: U32 -> {U32.is_lt(k, j) == True{} : Bool} -> {Laws.rdN(U, d, out, k) == f(Laws.rd_at(T, a, k)) : U}

def MRes(~T: Data, ~U: Data, ~f: T -> U, +d: Nat, -a: Array<T>, o: Array<U>, +bound: U32) -> Type:
  Laws.WFArray(U, d, o) & (@k: U32 -> {U32.is_lt(k, bound) == True{} : Bool} -> {Laws.rdN(U, d, o, k) == f(Laws.rd_at(T, a, k)) : U})

def MGoal(~T: Data, ~U: Data, ~f: T -> U, fl: Nat, +j: U32, +d: Nat, -a: Array<T>, -out: Array<U>, -r: Array<T> & T) -> Type:
  MHyp(~T, ~U, ~f, j, d, a, out) -> &o: Array<U> -> {K.Kernel.map.go(~T, ~U, ~f, fl, j, out, r) == o : Array<U>} & MRes(~T, ~U, ~f, d, a, o, Laws.addn(j, fl))

def MSet(~T: Data, ~U: Data, ~f: T -> U, p: Nat, +j: U32, +d: Nat, -a: Array<T>, -out: Array<U>, +y: U) -> Type:
  MHyp(~T, ~U, ~f, j, d, a, out) -> &o: Array<U> -> {K.Kernel.map.go(~T, ~U, ~f, p, U32.inc(j), Array.set(U, out, j, y), Array.get(T, a, U32.inc(j))) == o : Array<U>} & MRes(~T, ~U, ~f, d, a, o, Laws.addn(j, 1n+p))

def MC(~T: Data, ~U: Data, ~f: T -> U, p: Nat, +j: U32, +d: Nat, -a: Array<T>, -out: Array<U>, -c: Array<U>, +bound: U32) -> Type:
  MHyp(~T, ~U, ~f, j, d, a, out) -> &o: Array<U> -> {K.Kernel.map.go(~T, ~U, ~f, p, U32.inc(j), c, Array.get(T, a, U32.inc(j))) == o : Array<U>} & MRes(~T, ~U, ~f, d, a, o, bound)

def mnext_lt(~T: Data, ~U: Data, ~f: T -> U, +d: Nat, +j: U32, +k: U32, -a: Array<T>, -out: Array<U>, -c: Array<U>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +y: U, g: MHyp(~T, ~U, ~f, j, d, a, out),
  fj: @k2: U32 -> {Laws.rdN(U, d, c, k2) == Bool.pick(U, Laws.same_at(d, j, k2), y, Laws.rdN(U, d, out, k2)) : U}, +lt: {U32.is_lt(k, j) == True{} : Bool})
  -> {Laws.rdN(U, d, c, k) == f(Laws.rd_at(T, a, k)) : U}:
  %Equal.sym(U, Laws.rdN(U, d, c, k), Bool.pick(U, Laws.same_at(d, j, k), y, Laws.rdN(U, d, out, k)), fj(k)) : {_ == f(Laws.rd_at(T, a, k)) : U}
  %Equal.sym(Bool, Laws.same_at(d, j, k), False{}, same_false_lt(d, j, k, hj, lt)) : {Bool.pick(U, _, y, Laws.rdN(U, d, out, k)) == f(Laws.rd_at(T, a, k)) : U}
  g(k, lt)

def mnext_b(~T: Data, ~U: Data, ~f: T -> U, b: Bool, +d: Nat, +j: U32, +k: U32, -a: Array<T>, -out: Array<U>, -c: Array<U>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +x: T, ex: {x == Laws.rd_at(T, a, j) : T}, +y: U, ey: {y == f(x) : U}, g: MHyp(~T, ~U, ~f, j, d, a, out),
  fj: @k2: U32 -> {Laws.rdN(U, d, c, k2) == Bool.pick(U, Laws.same_at(d, j, k2), y, Laws.rdN(U, d, out, k2)) : U}, s: IncLtU(b, k, j))
  -> {Laws.rdN(U, d, c, k) == f(Laws.rd_at(T, a, k)) : U}:
  match b:
    case True{}:
      mnext_lt(~T, ~U, ~f, d, j, k, a, out, c, hj, y, g, fj, s)
    case False{}:
      %Equal.sym(U32, k, j, s) : {Laws.rdN(U, d, c, _) == f(Laws.rd_at(T, a, _)) : U}
      %Equal.sym(U, Laws.rdN(U, d, c, j), Bool.pick(U, Laws.same_at(d, j, j), y, Laws.rdN(U, d, out, j)), fj(j)) : {_ == f(Laws.rd_at(T, a, j)) : U}
      %Equal.sym(Bool, Laws.same_at(d, j, j), True{}, same_at_refl(d, j)) : {Bool.pick(U, _, y, Laws.rdN(U, d, out, j)) == f(Laws.rd_at(T, a, j)) : U}
      Equal.trans(U, y, f(x), f(Laws.rd_at(T, a, j)), ey, Equal.cong(T, U, v => f(v), x, Laws.rd_at(T, a, j), ex))

def mnext_k(~T: Data, ~U: Data, ~f: T -> U, +d: Nat, +j: U32, +k: U32, -a: Array<T>, -out: Array<U>, -c: Array<U>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +x: T, ex: {x == Laws.rd_at(T, a, j) : T}, +y: U, ey: {y == f(x) : U}, g: MHyp(~T, ~U, ~f, j, d, a, out),
  fj: @k2: U32 -> {Laws.rdN(U, d, c, k2) == Bool.pick(U, Laws.same_at(d, j, k2), y, Laws.rdN(U, d, out, k2)) : U}, w: &b: Bool -> IncLtU(b, k, j))
  -> {Laws.rdN(U, d, c, k) == f(Laws.rd_at(T, a, k)) : U}:
  (b, s) = w
  mnext_b(~T, ~U, ~f, b, d, j, k, a, out, c, hj, x, ex, y, ey, g, fj, s)

def mnext(~T: Data, ~U: Data, ~f: T -> U, +d: Nat, +j: U32, -a: Array<T>, -out: Array<U>, -c: Array<U>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +x: T, +ex: {x == Laws.rd_at(T, a, j) : T}, +y: U, +ey: {y == f(x) : U}, g: MHyp(~T, ~U, ~f, j, d, a, out),
  fj: @k2: U32 -> {Laws.rdN(U, d, c, k2) == Bool.pick(U, Laws.same_at(d, j, k2), y, Laws.rdN(U, d, out, k2)) : U})
  -> MHyp(~T, ~U, ~f, U32.inc(j), d, a, c):
  +k => hk => mnext_k(~T, ~U, ~f, d, j, k, a, out, c, hj, x, ex, y, ey, g, fj, inc_lt_u(k, j, hk))

def map_step2(~T: Data, ~U: Data, ~f: T -> U, p: Nat, +j: U32, +d: Nat, a: Array<T>, -out: Array<U>, +x: T, +ex: {x == Laws.rd_at(T, a, j) : T}, +y: U, +ey: {y == f(x) : U}, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, room: Laws.Room(d, U32.inc(j), p),
  ih: @a2: Array<T> -> @c: Array<U> -> Laws.WFArray(U, d, c) -> Laws.Room(d, U32.inc(j), p) -> MGoal(~T, ~U, ~f, p, U32.inc(j), d, a2, c, Array.get(T, a2, U32.inc(j))),
  w: &c: Array<U> -> {Array.set(U, out, j, y) == c : Array<U>} & Laws.WFArray(U, d, c) & (@k2: U32 -> {Laws.rdN(U, d, c, k2) == Bool.pick(U, Laws.same_at(d, j, k2), y, Laws.rdN(U, d, out, k2)) : U}) & (@k2: U32 -> {Laws.rd_at(U, out, k2) == Laws.rdN(U, d, out, k2) : U}))
  -> MSet(~T, ~U, ~f, p, j, d, a, out, y):
  (c, ec, wc, fj, cv) = w
  %Equal.sym(Array<U>, Array.set(U, out, j, y), c, ec) : MC(~T, ~U, ~f, p, j, d, a, out, _, Laws.addn(j, 1n+p))
  %addn_inc(j, p) : MC(~T, ~U, ~f, p, j, d, a, out, c, _)
  g => ih(a, c, wc, room)(mnext(~T, ~U, ~f, d, j, a, out, c, hj, x, ex, y, ey, g, fj))

def map_step1(~T: Data, ~U: Data, ~f: T -> U, p: Nat, +j: U32, +d: Nat, -a: Array<T>, out: Array<U>, wf: Laws.WFArray(U, d, out), room: Laws.Room(d, j, 1n+p),
  ih: @a2: Array<T> -> @c: Array<U> -> Laws.WFArray(U, d, c) -> Laws.Room(d, U32.inc(j), p) -> MGoal(~T, ~U, ~f, p, U32.inc(j), d, a2, c, Array.get(T, a2, U32.inc(j))),
  w: &b: Array<T> -> &x: T -> {b == a : Array<T>} & {Array.get(T, a, j) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, j) : T})
  -> MGoal(~T, ~U, ~f, 1n+p, j, d, a, out, Array.get(T, a, j)):
  (hj, room2) = room
  (a2, +x, +ea, e1, ex) = w
  %Equal.sym(Array<T> & T, Array.get(T, a, j), (a, x), e1) : MGoal(~T, ~U, ~f, 1n+p, j, d, a, out, _)
  %ea : MGoal(~T, ~U, ~f, 1n+p, j, d, _, out, (_, x))
  map_step2(~T, ~U, ~f, p, j, d, a2, out, x, Equal.trans(T, x, Laws.rd_at(T, a, j), Laws.rd_at(T, a2, j), ex, Equal.sym(T, Laws.rd_at(T, a2, j), Laws.rd_at(T, a, j), Equal.cong(Array<T>, T, q => Laws.rd_at(T, q, j), a2, a, ea))), f(x), {==}, hj, room2, ih, set_other_w(U, d, out, j, f(x), wf))

def map_zero(~T: Data, ~U: Data, ~f: T -> U, +j: U32, +d: Nat, -a: Array<T>, out: Array<U>, wf: Laws.WFArray(U, d, out),
  w: &b: Array<T> -> &x: T -> {b == a : Array<T>} & {Array.get(T, a, j) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, j) : T})
  -> MGoal(~T, ~U, ~f, 0n, j, d, a, out, Array.get(T, a, j)):
  (a2, +x, ea, e1, ex) = w
  %Equal.sym(Array<T> & T, Array.get(T, a, j), (a, x), e1) : MGoal(~T, ~U, ~f, 0n, j, d, a, out, _)
  g => (out, {==}, wf, g)

# Kernel.map.go: every k < addn(j, fl) holds f(a[k]) afterwards
def map_go(~T: Data, ~U: Data, ~f: T -> U, fl: Nat, +j: U32, +d: Nat, a: Array<T>, out: Array<U>, wf: Laws.WFArray(U, d, out), room: Laws.Room(d, j, fl)) -> MGoal(~T, ~U, ~f, fl, j, d, a, out, Array.get(T, a, j)):
  match fl:
    case 0n:
      map_zero(~T, ~U, ~f, j, d, a, out, wf, get_w(T, a, j))
    case 1n++p:
      map_step1(~T, ~U, ~f, p, j, d, a, out, wf, room, a2 => c => wc => room2 => map_go(~T, ~U, ~f, p, U32.inc(j), d, a2, c, wc, room2), get_w(T, a, j))

def mhyp0(~T: Data, ~U: Data, ~f: T -> U, +d: Nat, -a: Array<T>, -out: Array<U>) -> MHyp(~T, ~U, ~f, 0, d, a, out):
  +k => hk => Empty.absurd({Laws.rdN(U, d, out, k) == f(Laws.rd_at(T, a, k)) : U}, lt0(k, hk))

# Kernel.map(n, d, a, z): out[k] == f(a[k]) for k < n when n <= 2^d
def map_fin(~T: Data, ~U: Data, ~f: T -> U, +d: Nat, +n: U32, -a: Array<T>, +z: U, +k: U32, hk: {U32.is_lt(k, n) == True{} : Bool},
  w: &o: Array<U> -> {K.Kernel.map.go(~T, ~U, ~f, U32.to_nat(n), 0, Array.new(U, d, z), Array.get(T, a, 0)) == o : Array<U>} & MRes(~T, ~U, ~f, d, a, o, Laws.addn(0, U32.to_nat(n))))
  -> {Laws.rd_at(U, K.Kernel.map.go(~T, ~U, ~f, U32.to_nat(n), 0, Array.new(U, d, z), Array.get(T, a, 0)), k) == f(Laws.rd_at(T, a, k)) : U}:
  (o, eq, wo, spec) = w
  %Equal.sym(Array<U>, K.Kernel.map.go(~T, ~U, ~f, U32.to_nat(n), 0, Array.new(U, d, z), Array.get(T, a, 0)), o, eq) : {Laws.rd_at(U, _, k) == f(Laws.rd_at(T, a, k)) : U}
  %Equal.sym(U, Laws.rd_at(U, o, k), Laws.rdN(U, d, o, k), Laws.rd_at_wf(U, d, o, k, wo)) : {_ == f(Laws.rd_at(T, a, k)) : U}
  spec(k, (%Equal.sym(U32, Laws.addn(0, U32.to_nat(n)), n, B.addn_to_nat(n)) : {U32.is_lt(k, _) == True{} : Bool}; hk))

def map_cell(~T: Data, ~U: Data, ~f: T -> U, +d: Nat, +n: U32, a: Array<T>, +z: U, +k: U32, fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, hk: {U32.is_lt(k, n) == True{} : Bool}) -> {Laws.rd_at(U, K.Kernel.map.go(~T, ~U, ~f, U32.to_nat(n), 0, Array.new(U, d, z), Array.get(T, a, 0)), k) == f(Laws.rd_at(T, a, k)) : U}:
  map_fin(~T, ~U, ~f, d, n, a, z, k, hk, map_go(~T, ~U, ~f, U32.to_nat(n), 0, d, a, Array.new(U, d, z), Laws.wf_new(U, d, z), B.room_from(d, n, fits))(mhyp0(~T, ~U, ~f, d, a, Array.new(U, d, z))))

def Laws.mask_not_cell(d, n, a, k, fits, hk):
  map_cell(~U32, ~U32, ~(x => U32.xor(x, 1)), d, n, a, 0, k, fits, hk)

# ---- Kernel.zip: out[k] == f(a[k], b[k]) ---------------------------------------------------------

def ZHyp(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +j: U32, +d: Nat, -a: Array<T>, -b: Array<U>, -out: Array<V>) -> Type:
  @k: U32 -> {U32.is_lt(k, j) == True{} : Bool} -> {Laws.rdN(V, d, out, k) == f(Laws.rd_at(T, a, k), Laws.rd_at(U, b, k)) : V}

def ZRes(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +d: Nat, -a: Array<T>, -b: Array<U>, o: Array<V>, +bound: U32) -> Type:
  Laws.WFArray(V, d, o) & (@k: U32 -> {U32.is_lt(k, bound) == True{} : Bool} -> {Laws.rdN(V, d, o, k) == f(Laws.rd_at(T, a, k), Laws.rd_at(U, b, k)) : V})

def ZGoal(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, fl: Nat, +j: U32, +d: Nat, -a: Array<T>, -b: Array<U>, -out: Array<V>, -ra: Array<T> & T, -rb: Array<U> & U) -> Type:
  ZHyp(~T, ~U, ~V, ~f, j, d, a, b, out) -> &o: Array<V> -> {K.Kernel.zip.go(~T, ~U, ~V, ~f, fl, j, out, ra, rb) == o : Array<V>} & ZRes(~T, ~U, ~V, ~f, d, a, b, o, Laws.addn(j, fl))

def ZSet(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, p: Nat, +j: U32, +d: Nat, -a: Array<T>, -b: Array<U>, -out: Array<V>, +y: V) -> Type:
  ZHyp(~T, ~U, ~V, ~f, j, d, a, b, out) -> &o: Array<V> -> {K.Kernel.zip.go(~T, ~U, ~V, ~f, p, U32.inc(j), Array.set(V, out, j, y), Array.get(T, a, U32.inc(j)), Array.get(U, b, U32.inc(j))) == o : Array<V>} & ZRes(~T, ~U, ~V, ~f, d, a, b, o, Laws.addn(j, 1n+p))

def ZC(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, p: Nat, +j: U32, +d: Nat, -a: Array<T>, -b: Array<U>, -out: Array<V>, -c: Array<V>, +bound: U32) -> Type:
  ZHyp(~T, ~U, ~V, ~f, j, d, a, b, out) -> &o: Array<V> -> {K.Kernel.zip.go(~T, ~U, ~V, ~f, p, U32.inc(j), c, Array.get(T, a, U32.inc(j)), Array.get(U, b, U32.inc(j))) == o : Array<V>} & ZRes(~T, ~U, ~V, ~f, d, a, b, o, bound)

def znext_lt(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +d: Nat, +j: U32, +k: U32, -a: Array<T>, -b: Array<U>, -out: Array<V>, -c: Array<V>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +y: V, g: ZHyp(~T, ~U, ~V, ~f, j, d, a, b, out),
  fj: @k2: U32 -> {Laws.rdN(V, d, c, k2) == Bool.pick(V, Laws.same_at(d, j, k2), y, Laws.rdN(V, d, out, k2)) : V}, +lt: {U32.is_lt(k, j) == True{} : Bool})
  -> {Laws.rdN(V, d, c, k) == f(Laws.rd_at(T, a, k), Laws.rd_at(U, b, k)) : V}:
  %Equal.sym(V, Laws.rdN(V, d, c, k), Bool.pick(V, Laws.same_at(d, j, k), y, Laws.rdN(V, d, out, k)), fj(k)) : {_ == f(Laws.rd_at(T, a, k), Laws.rd_at(U, b, k)) : V}
  %Equal.sym(Bool, Laws.same_at(d, j, k), False{}, same_false_lt(d, j, k, hj, lt)) : {Bool.pick(V, _, y, Laws.rdN(V, d, out, k)) == f(Laws.rd_at(T, a, k), Laws.rd_at(U, b, k)) : V}
  g(k, lt)

def znext_b(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, bb: Bool, +d: Nat, +j: U32, +k: U32, -a: Array<T>, -b: Array<U>, -out: Array<V>, -c: Array<V>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +x: T, +y: U, ex: {x == Laws.rd_at(T, a, j) : T}, ey: {y == Laws.rd_at(U, b, j) : U}, +v: V, ev: {v == f(x, y) : V}, g: ZHyp(~T, ~U, ~V, ~f, j, d, a, b, out),
  fj: @k2: U32 -> {Laws.rdN(V, d, c, k2) == Bool.pick(V, Laws.same_at(d, j, k2), v, Laws.rdN(V, d, out, k2)) : V}, s: IncLtU(bb, k, j))
  -> {Laws.rdN(V, d, c, k) == f(Laws.rd_at(T, a, k), Laws.rd_at(U, b, k)) : V}:
  match bb:
    case True{}:
      znext_lt(~T, ~U, ~V, ~f, d, j, k, a, b, out, c, hj, v, g, fj, s)
    case False{}:
      %Equal.sym(U32, k, j, s) : {Laws.rdN(V, d, c, _) == f(Laws.rd_at(T, a, _), Laws.rd_at(U, b, _)) : V}
      %Equal.sym(V, Laws.rdN(V, d, c, j), Bool.pick(V, Laws.same_at(d, j, j), v, Laws.rdN(V, d, out, j)), fj(j)) : {_ == f(Laws.rd_at(T, a, j), Laws.rd_at(U, b, j)) : V}
      %Equal.sym(Bool, Laws.same_at(d, j, j), True{}, same_at_refl(d, j)) : {Bool.pick(V, _, v, Laws.rdN(V, d, out, j)) == f(Laws.rd_at(T, a, j), Laws.rd_at(U, b, j)) : V}
      Equal.trans(V, v, f(x, y), f(Laws.rd_at(T, a, j), Laws.rd_at(U, b, j)), ev, Equal.trans(V, f(x, y), f(Laws.rd_at(T, a, j), y), f(Laws.rd_at(T, a, j), Laws.rd_at(U, b, j)), Equal.cong(T, V, q => f(q, y), x, Laws.rd_at(T, a, j), ex), Equal.cong(U, V, q => f(Laws.rd_at(T, a, j), q), y, Laws.rd_at(U, b, j), ey)))

def znext_k(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +d: Nat, +j: U32, +k: U32, -a: Array<T>, -b: Array<U>, -out: Array<V>, -c: Array<V>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +x: T, +y: U, ex: {x == Laws.rd_at(T, a, j) : T}, ey: {y == Laws.rd_at(U, b, j) : U}, +v: V, ev: {v == f(x, y) : V}, g: ZHyp(~T, ~U, ~V, ~f, j, d, a, b, out),
  fj: @k2: U32 -> {Laws.rdN(V, d, c, k2) == Bool.pick(V, Laws.same_at(d, j, k2), v, Laws.rdN(V, d, out, k2)) : V}, w: &bb: Bool -> IncLtU(bb, k, j))
  -> {Laws.rdN(V, d, c, k) == f(Laws.rd_at(T, a, k), Laws.rd_at(U, b, k)) : V}:
  (bb, s) = w
  znext_b(~T, ~U, ~V, ~f, bb, d, j, k, a, b, out, c, hj, x, y, ex, ey, v, ev, g, fj, s)

def znext(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +d: Nat, +j: U32, -a: Array<T>, -b: Array<U>, -out: Array<V>, -c: Array<V>, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, +x: T, +y: U, +ex: {x == Laws.rd_at(T, a, j) : T}, +ey: {y == Laws.rd_at(U, b, j) : U}, +v: V, +ev: {v == f(x, y) : V}, g: ZHyp(~T, ~U, ~V, ~f, j, d, a, b, out),
  fj: @k2: U32 -> {Laws.rdN(V, d, c, k2) == Bool.pick(V, Laws.same_at(d, j, k2), v, Laws.rdN(V, d, out, k2)) : V})
  -> ZHyp(~T, ~U, ~V, ~f, U32.inc(j), d, a, b, c):
  +k => hk => znext_k(~T, ~U, ~V, ~f, d, j, k, a, b, out, c, hj, x, y, ex, ey, v, ev, g, fj, inc_lt_u(k, j, hk))

def zip_step3(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, p: Nat, +j: U32, +d: Nat, a: Array<T>, b: Array<U>, -out: Array<V>, +x: T, +y: U, +ex: {x == Laws.rd_at(T, a, j) : T}, +ey: {y == Laws.rd_at(U, b, j) : U}, +v: V, +ev: {v == f(x, y) : V}, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, room: Laws.Room(d, U32.inc(j), p),
  ih: @a2: Array<T> -> @b2: Array<U> -> @c: Array<V> -> Laws.WFArray(V, d, c) -> Laws.Room(d, U32.inc(j), p) -> ZGoal(~T, ~U, ~V, ~f, p, U32.inc(j), d, a2, b2, c, Array.get(T, a2, U32.inc(j)), Array.get(U, b2, U32.inc(j))),
  w: &c: Array<V> -> {Array.set(V, out, j, v) == c : Array<V>} & Laws.WFArray(V, d, c) & (@k2: U32 -> {Laws.rdN(V, d, c, k2) == Bool.pick(V, Laws.same_at(d, j, k2), v, Laws.rdN(V, d, out, k2)) : V}) & (@k2: U32 -> {Laws.rd_at(V, out, k2) == Laws.rdN(V, d, out, k2) : V}))
  -> ZSet(~T, ~U, ~V, ~f, p, j, d, a, b, out, v):
  (c, ec, wc, fj, cv) = w
  %Equal.sym(Array<V>, Array.set(V, out, j, v), c, ec) : ZC(~T, ~U, ~V, ~f, p, j, d, a, b, out, _, Laws.addn(j, 1n+p))
  %addn_inc(j, p) : ZC(~T, ~U, ~V, ~f, p, j, d, a, b, out, c, _)
  g => ih(a, b, c, wc, room)(znext(~T, ~U, ~V, ~f, d, j, a, b, out, c, hj, x, y, ex, ey, v, ev, g, fj))

def zip_step2(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, p: Nat, +j: U32, +d: Nat, a: Array<T>, -b: Array<U>, out: Array<V>, wf: Laws.WFArray(V, d, out), +x: T, +ex: {x == Laws.rd_at(T, a, j) : T}, +hj: {U32.is_lt(j, U32.shln(1, d)) == True{} : Bool}, room: Laws.Room(d, U32.inc(j), p),
  ih: @a2: Array<T> -> @b2: Array<U> -> @c: Array<V> -> Laws.WFArray(V, d, c) -> Laws.Room(d, U32.inc(j), p) -> ZGoal(~T, ~U, ~V, ~f, p, U32.inc(j), d, a2, b2, c, Array.get(T, a2, U32.inc(j)), Array.get(U, b2, U32.inc(j))),
  w: &b3: Array<U> -> &y: U -> {b3 == b : Array<U>} & {Array.get(U, b, j) == (b, y) : Array<U> & U} & {y == Laws.rd_at(U, b, j) : U})
  -> ZGoal(~T, ~U, ~V, ~f, 1n+p, j, d, a, b, out, (a, x), Array.get(U, b, j)):
  (b2, +y, +eb, e2, ey) = w
  %Equal.sym(Array<U> & U, Array.get(U, b, j), (b, y), e2) : ZGoal(~T, ~U, ~V, ~f, 1n+p, j, d, a, b, out, (a, x), _)
  %eb : ZGoal(~T, ~U, ~V, ~f, 1n+p, j, d, a, _, out, (a, x), (_, y))
  zip_step3(~T, ~U, ~V, ~f, p, j, d, a, b2, out, x, y, ex, Equal.trans(U, y, Laws.rd_at(U, b, j), Laws.rd_at(U, b2, j), ey, Equal.sym(U, Laws.rd_at(U, b2, j), Laws.rd_at(U, b, j), Equal.cong(Array<U>, U, q => Laws.rd_at(U, q, j), b2, b, eb))), f(x, y), {==}, hj, room, ih, set_other_w(V, d, out, j, f(x, y), wf))

def zip_step1(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, p: Nat, +j: U32, +d: Nat, -a: Array<T>, b: Array<U>, out: Array<V>, wf: Laws.WFArray(V, d, out), room: Laws.Room(d, j, 1n+p),
  ih: @a2: Array<T> -> @b2: Array<U> -> @c: Array<V> -> Laws.WFArray(V, d, c) -> Laws.Room(d, U32.inc(j), p) -> ZGoal(~T, ~U, ~V, ~f, p, U32.inc(j), d, a2, b2, c, Array.get(T, a2, U32.inc(j)), Array.get(U, b2, U32.inc(j))),
  w: &a3: Array<T> -> &x: T -> {a3 == a : Array<T>} & {Array.get(T, a, j) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, j) : T})
  -> ZGoal(~T, ~U, ~V, ~f, 1n+p, j, d, a, b, out, Array.get(T, a, j), Array.get(U, b, j)):
  (hj, room2) = room
  (a2, +x, +ea, e1, ex) = w
  %Equal.sym(Array<T> & T, Array.get(T, a, j), (a, x), e1) : ZGoal(~T, ~U, ~V, ~f, 1n+p, j, d, a, b, out, _, Array.get(U, b, j))
  %ea : ZGoal(~T, ~U, ~V, ~f, 1n+p, j, d, _, b, out, (_, x), Array.get(U, b, j))
  zip_step2(~T, ~U, ~V, ~f, p, j, d, a2, b, out, wf, x, Equal.trans(T, x, Laws.rd_at(T, a, j), Laws.rd_at(T, a2, j), ex, Equal.sym(T, Laws.rd_at(T, a2, j), Laws.rd_at(T, a, j), Equal.cong(Array<T>, T, q => Laws.rd_at(T, q, j), a2, a, ea))), hj, room2, ih, get_w(U, b, j))

def zip_zero(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +j: U32, +d: Nat, -a: Array<T>, -b: Array<U>, out: Array<V>, wf: Laws.WFArray(V, d, out),
  wa: &a3: Array<T> -> &x: T -> {a3 == a : Array<T>} & {Array.get(T, a, j) == (a, x) : Array<T> & T} & {x == Laws.rd_at(T, a, j) : T},
  wb: &b3: Array<U> -> &y: U -> {b3 == b : Array<U>} & {Array.get(U, b, j) == (b, y) : Array<U> & U} & {y == Laws.rd_at(U, b, j) : U})
  -> ZGoal(~T, ~U, ~V, ~f, 0n, j, d, a, b, out, Array.get(T, a, j), Array.get(U, b, j)):
  (a2, +x, ea, e1, ex) = wa
  (b2, +y, eb, e2, ey) = wb
  %Equal.sym(Array<T> & T, Array.get(T, a, j), (a, x), e1) : ZGoal(~T, ~U, ~V, ~f, 0n, j, d, a, b, out, _, Array.get(U, b, j))
  %Equal.sym(Array<U> & U, Array.get(U, b, j), (b, y), e2) : ZGoal(~T, ~U, ~V, ~f, 0n, j, d, a, b, out, (a, x), _)
  g => (out, {==}, wf, g)

def zip_go(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, fl: Nat, +j: U32, +d: Nat, a: Array<T>, b: Array<U>, out: Array<V>, wf: Laws.WFArray(V, d, out), room: Laws.Room(d, j, fl)) -> ZGoal(~T, ~U, ~V, ~f, fl, j, d, a, b, out, Array.get(T, a, j), Array.get(U, b, j)):
  match fl:
    case 0n:
      zip_zero(~T, ~U, ~V, ~f, j, d, a, b, out, wf, get_w(T, a, j), get_w(U, b, j))
    case 1n++p:
      zip_step1(~T, ~U, ~V, ~f, p, j, d, a, b, out, wf, room, a2 => b2 => c => wc => room2 => zip_go(~T, ~U, ~V, ~f, p, U32.inc(j), d, a2, b2, c, wc, room2), get_w(T, a, j))

def zhyp0(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +d: Nat, -a: Array<T>, -b: Array<U>, -out: Array<V>) -> ZHyp(~T, ~U, ~V, ~f, 0, d, a, b, out):
  +k => hk => Empty.absurd({Laws.rdN(V, d, out, k) == f(Laws.rd_at(T, a, k), Laws.rd_at(U, b, k)) : V}, lt0(k, hk))

def zip_fin(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +d: Nat, +n: U32, -a: Array<T>, -b: Array<U>, +z: V, +k: U32, hk: {U32.is_lt(k, n) == True{} : Bool},
  w: &o: Array<V> -> {K.Kernel.zip.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, Array.new(V, d, z), Array.get(T, a, 0), Array.get(U, b, 0)) == o : Array<V>} & ZRes(~T, ~U, ~V, ~f, d, a, b, o, Laws.addn(0, U32.to_nat(n))))
  -> {Laws.rd_at(V, K.Kernel.zip.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, Array.new(V, d, z), Array.get(T, a, 0), Array.get(U, b, 0)), k) == f(Laws.rd_at(T, a, k), Laws.rd_at(U, b, k)) : V}:
  (o, eq, wo, spec) = w
  %Equal.sym(Array<V>, K.Kernel.zip.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, Array.new(V, d, z), Array.get(T, a, 0), Array.get(U, b, 0)), o, eq) : {Laws.rd_at(V, _, k) == f(Laws.rd_at(T, a, k), Laws.rd_at(U, b, k)) : V}
  %Equal.sym(V, Laws.rd_at(V, o, k), Laws.rdN(V, d, o, k), Laws.rd_at_wf(V, d, o, k, wo)) : {_ == f(Laws.rd_at(T, a, k), Laws.rd_at(U, b, k)) : V}
  spec(k, (%Equal.sym(U32, Laws.addn(0, U32.to_nat(n)), n, B.addn_to_nat(n)) : {U32.is_lt(k, _) == True{} : Bool}; hk))

def zip_cell(~T: Data, ~U: Data, ~V: Data, ~f: T -> U -> V, +d: Nat, +n: U32, a: Array<T>, b: Array<U>, +z: V, +k: U32, fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}, hk: {U32.is_lt(k, n) == True{} : Bool}) -> {Laws.rd_at(V, K.Kernel.zip.go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, Array.new(V, d, z), Array.get(T, a, 0), Array.get(U, b, 0)), k) == f(Laws.rd_at(T, a, k), Laws.rd_at(U, b, k)) : V}:
  zip_fin(~T, ~U, ~V, ~f, d, n, a, b, z, k, hk, zip_go(~T, ~U, ~V, ~f, U32.to_nat(n), 0, d, a, b, Array.new(V, d, z), Laws.wf_new(V, d, z), B.room_from(d, n, fits))(zhyp0(~T, ~U, ~V, ~f, d, a, b, Array.new(V, d, z))))

def Laws.mask_and_cell(d, n, a, b, k, fits, hk):
  zip_cell(~U32, ~U32, ~U32, ~(x => y => U32.and(x, y)), d, n, a, b, 0, k, fits, hk)

def Laws.mask_or_cell(d, n, a, b, k, fits, hk):
  zip_cell(~U32, ~U32, ~U32, ~(x => y => U32.or(x, y)), d, n, a, b, 0, k, fits, hk)

# ---- Kernel.iota_from: out[k] == off + k ----------------------------------------------------------

def IHyp(+i: U32, +d: Nat, +off: U32, -out: Array<U32>) -> Type:
  @k: U32 -> {U32.is_lt(k, i) == True{} : Bool} -> {Laws.rdN(U32, d, out, k) == U32.add(off, k) : U32}

def IRes(+d: Nat, +off: U32, o: Array<U32>, +bound: U32) -> Type:
  Laws.WFArray(U32, d, o) & (@k: U32 -> {U32.is_lt(k, bound) == True{} : Bool} -> {Laws.rdN(U32, d, o, k) == U32.add(off, k) : U32})

def IGoal(fl: Nat, +i: U32, +d: Nat, +off: U32, -out: Array<U32>) -> Type:
  IHyp(i, d, off, out) -> &o: Array<U32> -> {K.Kernel.iota.go(fl, i, off, out) == o : Array<U32>} & IRes(d, off, o, Laws.addn(i, fl))

def IC(p: Nat, +i: U32, +d: Nat, +off: U32, -out: Array<U32>, -c: Array<U32>, +bound: U32) -> Type:
  IHyp(i, d, off, out) -> &o: Array<U32> -> {K.Kernel.iota.go(p, U32.inc(i), off, c) == o : Array<U32>} & IRes(d, off, o, bound)

def inext_lt(+d: Nat, +i: U32, +k: U32, +off: U32, -out: Array<U32>, -c: Array<U32>, +hi: {U32.is_lt(i, U32.shln(1, d)) == True{} : Bool}, g: IHyp(i, d, off, out),
  fj: @k2: U32 -> {Laws.rdN(U32, d, c, k2) == Bool.pick(U32, Laws.same_at(d, i, k2), U32.add(off, i), Laws.rdN(U32, d, out, k2)) : U32}, +lt: {U32.is_lt(k, i) == True{} : Bool})
  -> {Laws.rdN(U32, d, c, k) == U32.add(off, k) : U32}:
  %Equal.sym(U32, Laws.rdN(U32, d, c, k), Bool.pick(U32, Laws.same_at(d, i, k), U32.add(off, i), Laws.rdN(U32, d, out, k)), fj(k)) : {_ == U32.add(off, k) : U32}
  %Equal.sym(Bool, Laws.same_at(d, i, k), False{}, same_false_lt(d, i, k, hi, lt)) : {Bool.pick(U32, _, U32.add(off, i), Laws.rdN(U32, d, out, k)) == U32.add(off, k) : U32}
  g(k, lt)

def inext_b(b: Bool, +d: Nat, +i: U32, +k: U32, +off: U32, -out: Array<U32>, -c: Array<U32>, +hi: {U32.is_lt(i, U32.shln(1, d)) == True{} : Bool}, g: IHyp(i, d, off, out),
  fj: @k2: U32 -> {Laws.rdN(U32, d, c, k2) == Bool.pick(U32, Laws.same_at(d, i, k2), U32.add(off, i), Laws.rdN(U32, d, out, k2)) : U32}, s: IncLtU(b, k, i))
  -> {Laws.rdN(U32, d, c, k) == U32.add(off, k) : U32}:
  match b:
    case True{}:
      inext_lt(d, i, k, off, out, c, hi, g, fj, s)
    case False{}:
      %Equal.sym(U32, k, i, s) : {Laws.rdN(U32, d, c, _) == U32.add(off, _) : U32}
      %Equal.sym(U32, Laws.rdN(U32, d, c, i), Bool.pick(U32, Laws.same_at(d, i, i), U32.add(off, i), Laws.rdN(U32, d, out, i)), fj(i)) : {_ == U32.add(off, i) : U32}
      %Equal.sym(Bool, Laws.same_at(d, i, i), True{}, same_at_refl(d, i)) : {Bool.pick(U32, _, U32.add(off, i), Laws.rdN(U32, d, out, i)) == U32.add(off, i) : U32}
      {==}

def inext_k(+d: Nat, +i: U32, +k: U32, +off: U32, -out: Array<U32>, -c: Array<U32>, +hi: {U32.is_lt(i, U32.shln(1, d)) == True{} : Bool}, g: IHyp(i, d, off, out),
  fj: @k2: U32 -> {Laws.rdN(U32, d, c, k2) == Bool.pick(U32, Laws.same_at(d, i, k2), U32.add(off, i), Laws.rdN(U32, d, out, k2)) : U32}, w: &b: Bool -> IncLtU(b, k, i))
  -> {Laws.rdN(U32, d, c, k) == U32.add(off, k) : U32}:
  (b, s) = w
  inext_b(b, d, i, k, off, out, c, hi, g, fj, s)

def inext(+d: Nat, +i: U32, +off: U32, -out: Array<U32>, -c: Array<U32>, +hi: {U32.is_lt(i, U32.shln(1, d)) == True{} : Bool}, g: IHyp(i, d, off, out),
  fj: @k2: U32 -> {Laws.rdN(U32, d, c, k2) == Bool.pick(U32, Laws.same_at(d, i, k2), U32.add(off, i), Laws.rdN(U32, d, out, k2)) : U32})
  -> IHyp(U32.inc(i), d, off, c):
  +k => hk => inext_k(d, i, k, off, out, c, hi, g, fj, inc_lt_u(k, i, hk))

def iota_step(p: Nat, +i: U32, +d: Nat, +off: U32, -out: Array<U32>, room: Laws.Room(d, i, 1n+p),
  ih: @c: Array<U32> -> Laws.WFArray(U32, d, c) -> Laws.Room(d, U32.inc(i), p) -> IGoal(p, U32.inc(i), d, off, c),
  w: &c: Array<U32> -> {Array.set(U32, out, i, U32.add(off, i)) == c : Array<U32>} & Laws.WFArray(U32, d, c) & (@k2: U32 -> {Laws.rdN(U32, d, c, k2) == Bool.pick(U32, Laws.same_at(d, i, k2), U32.add(off, i), Laws.rdN(U32, d, out, k2)) : U32}) & (@k2: U32 -> {Laws.rd_at(U32, out, k2) == Laws.rdN(U32, d, out, k2) : U32}))
  -> IGoal(1n+p, i, d, off, out):
  (hi, room2) = room
  (c, ec, wc, fj, cv) = w
  %Equal.sym(Array<U32>, Array.set(U32, out, i, U32.add(off, i)), c, ec) : IC(p, i, d, off, out, _, Laws.addn(i, 1n+p))
  %addn_inc(i, p) : IC(p, i, d, off, out, c, _)
  g => ih(c, wc, room2)(inext(d, i, off, out, c, hi, g, fj))

def iota_go(fl: Nat, +i: U32, +d: Nat, +off: U32, out: Array<U32>, wf: Laws.WFArray(U32, d, out), room: Laws.Room(d, i, fl)) -> IGoal(fl, i, d, off, out):
  match fl:
    case 0n:
      g => (out, {==}, wf, g)
    case 1n++p:
      iota_step(p, i, d, off, out, room, c => wc => room2 => iota_go(p, U32.inc(i), d, off, c, wc, room2), set_other_w(U32, d, out, i, U32.add(off, i), wf))

def ihyp0(+d: Nat, +off: U32, -out: Array<U32>) -> IHyp(0, d, off, out):
  +k => hk => Empty.absurd({Laws.rdN(U32, d, out, k) == U32.add(off, k) : U32}, lt0(k, hk))

def iota_fin(+d: Nat, +n: U32, +off: U32, +k: U32, hk: {U32.is_lt(k, n) == True{} : Bool},
  w: &o: Array<U32> -> {K.Kernel.iota.go(U32.to_nat(n), 0, off, Array.new(U32, d, 0)) == o : Array<U32>} & IRes(d, off, o, Laws.addn(0, U32.to_nat(n))))
  -> {Laws.rd_at(U32, K.Kernel.iota_from(n, d, off), k) == U32.add(off, k) : U32}:
  (o, eq, wo, spec) = w
  %Equal.sym(Array<U32>, K.Kernel.iota.go(U32.to_nat(n), 0, off, Array.new(U32, d, 0)), o, eq) : {Laws.rd_at(U32, _, k) == U32.add(off, k) : U32}
  %Equal.sym(U32, Laws.rd_at(U32, o, k), Laws.rdN(U32, d, o, k), Laws.rd_at_wf(U32, d, o, k, wo)) : {_ == U32.add(off, k) : U32}
  spec(k, (%Equal.sym(U32, Laws.addn(0, U32.to_nat(n)), n, B.addn_to_nat(n)) : {U32.is_lt(k, _) == True{} : Bool}; hk))

def Laws.iota_cell(d, n, off, k, fits, hk):
  iota_fin(d, n, off, k, hk, iota_go(U32.to_nat(n), 0, d, off, Array.new(U32, d, 0), Laws.wf_new(U32, d, 0), B.room_from(d, n, fits))(ihyp0(d, off, Array.new(U32, d, 0))))

# ---- Kernel.fold: the running sum (U32.add instance; Laws.FSum is the Type-level spec) -----------

def FAdd(x: U32, y: U32) -> U32:
  U32.add(x, y)

# the fold with fl steps left at index i and accumulator acc, pending read r of a[i]
def FGoal(fl: Nat, +i: U32, +acc: U32, -a: Array<U32>, -r: Array<U32> & U32) -> Type:
  &a2: Array<U32> -> &res: U32 -> {K.Kernel.fold.go(~U32, ~U32, ~(acc => x => U32.add(acc, x)), fl, i, acc, r) == (a2, res) : Array<U32> & U32} & {a2 == a : Array<U32>} & Laws.FSum(fl, i, acc, a, res)

def fold_zero(+i: U32, +acc: U32, -a: Array<U32>, w: &b: Array<U32> -> &x: U32 -> {b == a : Array<U32>} & {Array.get(U32, a, i) == (a, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, a, i) : U32}) -> FGoal(0n, i, acc, a, Array.get(U32, a, i)):
  (a2, +x, ea, e1, ex) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, a, i), (a, x), e1) : FGoal(0n, i, acc, a, _)
  %ea : FGoal(0n, i, acc, _, (_, x))
  (a2, acc, {==}, {==}, {==})

# the induction hypothesis repackaged: the cell x read at i names the step of FSum
def fold_step(p: Nat, +i: U32, +acc: U32, -a: Array<U32>, +x: U32, ex: {x == Laws.rd_at(U32, a, i) : U32},
  w: &a3: Array<U32> -> &res: U32 -> {K.Kernel.fold.go(~U32, ~U32, ~(acc => x => U32.add(acc, x)), p, U32.inc(i), U32.add(acc, x), Array.get(U32, a, U32.inc(i))) == (a3, res) : Array<U32> & U32} & {a3 == a : Array<U32>} & Laws.FSum(p, U32.inc(i), U32.add(acc, x), a, res))
  -> FGoal(1n+p, i, acc, a, (a, x)):
  (a3, +res, eq, ea3, spec) = w
  (a3, res, eq, ea3, (x, ex, spec))

def fold_cons(p: Nat, +i: U32, +acc: U32, -a: Array<U32>, w: &b: Array<U32> -> &x: U32 -> {b == a : Array<U32>} & {Array.get(U32, a, i) == (a, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, a, i) : U32},
  ih: @a2: Array<U32> -> @x: U32 -> FGoal(p, U32.inc(i), U32.add(acc, x), a2, Array.get(U32, a2, U32.inc(i))))
  -> FGoal(1n+p, i, acc, a, Array.get(U32, a, i)):
  (a2, +x, +ea, e1, ex) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, a, i), (a, x), e1) : FGoal(1n+p, i, acc, a, _)
  %ea : FGoal(1n+p, i, acc, _, (_, x))
  fold_step(p, i, acc, a2, x, Equal.trans(U32, x, Laws.rd_at(U32, a, i), Laws.rd_at(U32, a2, i), ex, Equal.sym(U32, Laws.rd_at(U32, a2, i), Laws.rd_at(U32, a, i), Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, i), a2, a, ea))), ih(a2, x))

def fold_go(fl: Nat, +i: U32, +acc: U32, a: Array<U32>) -> FGoal(fl, i, acc, a, Array.get(U32, a, i)):
  match fl:
    case 0n:
      fold_zero(i, acc, a, get_w(U32, a, i))
    case 1n++p:
      fold_cons(p, i, acc, a, get_w(U32, a, i), a2 => x => fold_go(p, U32.inc(i), U32.add(acc, x), a2))

def fold_sum_fin(+n: U32, -a: Array<U32>, +z: U32, w: FGoal(U32.to_nat(n), 0, z, a, Array.get(U32, a, 0))) -> Laws.FSum(U32.to_nat(n), 0, z, a, Pair.snd(Array<U32>, U32, K.Kernel.fold.go(~U32, ~U32, ~(acc => x => U32.add(acc, x)), U32.to_nat(n), 0, z, Array.get(U32, a, 0)))):
  (a2, res, eq, ea, spec) = w
  %Equal.sym(Array<U32> & U32, K.Kernel.fold.go(~U32, ~U32, ~(acc => x => U32.add(acc, x)), U32.to_nat(n), 0, z, Array.get(U32, a, 0)), (a2, res), eq) : Laws.FSum(U32.to_nat(n), 0, z, a, Pair.snd(Array<U32>, U32, _))
  spec

def Laws.u32_fold_sum(n, a, z):
  fold_sum_fin(n, a, z, fold_go(U32.to_nat(n), 0, z, a))

def fold_keeps_fin(+n: U32, -a: Array<U32>, +z: U32, w: FGoal(U32.to_nat(n), 0, z, a, Array.get(U32, a, 0))) -> {Pair.fst(Array<U32>, U32, K.Kernel.fold.go(~U32, ~U32, ~(acc => x => U32.add(acc, x)), U32.to_nat(n), 0, z, Array.get(U32, a, 0))) == a : Array<U32>}:
  (a2, res, eq, ea, spec) = w
  %Equal.sym(Array<U32> & U32, K.Kernel.fold.go(~U32, ~U32, ~(acc => x => U32.add(acc, x)), U32.to_nat(n), 0, z, Array.get(U32, a, 0)), (a2, res), eq) : {Pair.fst(Array<U32>, U32, _) == a : Array<U32>}
  ea

def Laws.u32_fold_keeps(n, a, z):
  fold_keeps_fin(n, a, z, fold_go(U32.to_nat(n), 0, z, a))

def Laws.popcount_sum(n, mask):
  fold_sum_fin(n, mask, 0, fold_go(U32.to_nat(n), 0, 0, mask))
