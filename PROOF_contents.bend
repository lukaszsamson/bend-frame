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

# ---- compaction (Kernel.compact_keep): clones, the cursor, the keep-one-position lemma, the spec ------
#
# A forall hypothesis is affine (it cannot be used twice), so the invariant "every kept row so far
# sits at its position" cannot be transported across a write row by row. Instead: an array can be
# copied (clone_eq / clone_wf rebuild two live copies with equations to the original) and a finite
# Type-level chain (CRoom) can be duplicated by induction; so the remaining run is analysed twice,
# once for the row just written (ckeep: later writes land above its position) and once for the
# rows to come (cspec_run), on separate copies of the state.

# two live copies of an array, both equal to it
def clone_node(-T: Data, -xs: Array<T>, -ys: Array<T>, wx: &x1: Array<T> -> &x2: Array<T> -> {x1 == xs : Array<T>} & {x2 == xs : Array<T>}, wy: &y1: Array<T> -> &y2: Array<T> -> {y1 == ys : Array<T>} & {y2 == ys : Array<T>})
  -> &a1: Array<T> -> &a2: Array<T> -> {a1 == ANode{xs, ys} : Array<T>} & {a2 == ANode{xs, ys} : Array<T>}:
  (x1, x2, ex1, ex2) = wx
  (y1, y2, ey1, ey2) = wy
  (ANode{x1, y1}, ANode{x2, y2}, (%ey1 : {ANode{x1, y1} == ANode{xs, _} : Array<T>}; %ex1 : {ANode{x1, y1} == ANode{_, y1} : Array<T>}; {==}), (%ey2 : {ANode{x2, y2} == ANode{xs, _} : Array<T>}; %ex2 : {ANode{x2, y2} == ANode{_, y2} : Array<T>}; {==}))

def clone_eq(-T: Data, a: Array<T>) -> &a1: Array<T> -> &a2: Array<T> -> {a1 == a : Array<T>} & {a2 == a : Array<T>}:
  match a:
    case ALeaf{+x}:
      (ALeaf{x}, ALeaf{x}, {==}, {==})
    case ANode{xs, ys}:
      clone_node(T, xs, ys, clone_eq(T, xs), clone_eq(T, ys))

# the same for a well-formed array: both copies well formed
def clone_wf_node(-T: Data, -xs: Array<T>, -ys: Array<T>, +p: Nat,
  wx: &x1: Array<T> -> &x2: Array<T> -> {x1 == xs : Array<T>} & {x2 == xs : Array<T>} & Laws.WFArray(T, p, x1) & Laws.WFArray(T, p, x2),
  wy: &y1: Array<T> -> &y2: Array<T> -> {y1 == ys : Array<T>} & {y2 == ys : Array<T>} & Laws.WFArray(T, p, y1) & Laws.WFArray(T, p, y2))
  -> &a1: Array<T> -> &a2: Array<T> -> {a1 == ANode{xs, ys} : Array<T>} & {a2 == ANode{xs, ys} : Array<T>} & Laws.WFArray(T, 1n+p, a1) & Laws.WFArray(T, 1n+p, a2):
  (x1, x2, ex1, ex2, wx1, wx2) = wx
  (y1, y2, ey1, ey2, wy1, wy2) = wy
  (ANode{x1, y1}, ANode{x2, y2}, (%ey1 : {ANode{x1, y1} == ANode{xs, _} : Array<T>}; %ex1 : {ANode{x1, y1} == ANode{_, y1} : Array<T>}; {==}), (%ey2 : {ANode{x2, y2} == ANode{xs, _} : Array<T>}; %ex2 : {ANode{x2, y2} == ANode{_, y2} : Array<T>}; {==}), (wx1, wy1), (wx2, wy2))

def clone_wf(-T: Data, d: Nat, a: Array<T>, wf: Laws.WFArray(T, d, a)) -> &a1: Array<T> -> &a2: Array<T> -> {a1 == a : Array<T>} & {a2 == a : Array<T>} & Laws.WFArray(T, d, a1) & Laws.WFArray(T, d, a2):
  match d a:
    case 0n ALeaf{+x}:
      (ALeaf{x}, ALeaf{x}, {==}, {==}, Unit{}, Unit{})
    case 1n++p ANode{xs, ys}:
      (wl, wr) = wf
      clone_wf_node(T, xs, ys, p, clone_wf(T, p, xs, wl), clone_wf(T, p, ys, wr))
    case 0n ANode{xs, ys}:
      Empty.absurd(&a1: Array<T> -> &a2: Array<T> -> {a1 == ANode{xs, ys} : Array<T>} & {a2 == ANode{xs, ys} : Array<T>} & Laws.WFArray(T, 0n, a1) & Laws.WFArray(T, 0n, a2), wf)
    case 1n+p ALeaf{x}:
      Empty.absurd(&a1: Array<T> -> &a2: Array<T> -> {a1 == ALeaf{x} : Array<T>} & {a2 == ALeaf{x} : Array<T>} & Laws.WFArray(T, 1n+p, a1) & Laws.WFArray(T, 1n+p, a2), wf)

# a CRoom chain, twice
def croom_dup_k(p: Nat, +i: U32, +k: U32, +d: Nat, -mask: Array<U32>, +b: U32, +eb: {b == Laws.rd_at(U32, mask, i) : U32}, +hb: {U32.is_le(b, 1) == True{} : Bool}, +hk: {U32.is_lt(k, U32.shln(1, d)) == True{} : Bool},
  w: Laws.CRoom(p, U32.inc(i), U32.add(k, b), d, mask) & Laws.CRoom(p, U32.inc(i), U32.add(k, b), d, mask)) -> Laws.CRoom(1n+p, i, k, d, mask) & Laws.CRoom(1n+p, i, k, d, mask):
  (r1, r2) = w
  ((b, eb, hb, hk, r1), (b, eb, hb, hk, r2))

def croom_dup(f: Nat, +i: U32, +k: U32, +d: Nat, -mask: Array<U32>, room: Laws.CRoom(f, i, k, d, mask)) -> Laws.CRoom(f, i, k, d, mask) & Laws.CRoom(f, i, k, d, mask):
  match f:
    case 0n:
      (Unit{}, Unit{})
    case 1n++p:
      (+b, +eb, +hb, +hk, rest) = room
      croom_dup_k(p, i, k, d, mask, b, eb, hb, hk, croom_dup(p, U32.inc(i), U32.add(k, b), d, mask, rest))

# ---- the cursor: a 0/1 word moves it by inc or not at all --------------------------------------------

def Bit01(c: Bool, +b: U32) -> Type:
  match c:
    case True{}:
      {b == 1 : U32}
    case False{}:
      {b == 0 : U32}

def le1_k(c: Cmp, +x: Word(32n), e: {Word.cmp(32n, x, B.bitw(32n, 0n)) == c : Cmp}, h: {Cmp.is_le(c) == True{} : Bool}) -> &c2: Bool -> Bit01(c2, U32{x}):
  match c:
    case LT{}:
      (False{}, Equal.cong(Word(32n), U32, w => U32{w}, x, Word.zero(32n), B.lt_bitw_zabove(32n, 0n, x, e)))
    case EQ{}:
      (True{}, Equal.cong(Word(32n), U32, w => U32{w}, x, B.bitw(32n, 0n), L.word_cmp_eq(32n, x, B.bitw(32n, 0n), e)))
    case GT{}:
      Empty.absurd(&c2: Bool -> Bit01(c2, U32{x}), L.false_true(h))

# a word <= 1 is 0 or 1
def le1_cases(b: U32, h: {U32.is_le(b, 1) == True{} : Bool}) -> &c: Bool -> Bit01(c, b):
  match b:
    case U32{+x}:
      le1_k(Word.cmp(32n, x, B.bitw(32n, 0n)), x, {==}, h)

# x + 0 == x, x + 0 with a carry in == inc x, x + 1 == inc x
def add_zero_r(n: Nat, x: Word(n)) -> {Word.adc(n, x, Word.zero(n), False{}, False{}) == x : Word(n)}:
  match n:
    case 0n:
      match x:
        case WNil{}:
          {==}
    case 1n++p:
      match x:
        case WCon{False{}, +t}:
          %Equal.sym(Word(p), Word.adc(p, t, Word.zero(p), False{}, False{}), t, add_zero_r(p, t)) : {WCon{False{}, _} == WCon{False{}, t} : Word(1n+p)}
          {==}
        case WCon{True{}, +t}:
          %Equal.sym(Word(p), Word.adc(p, t, Word.zero(p), False{}, False{}), t, add_zero_r(p, t)) : {WCon{True{}, _} == WCon{True{}, t} : Word(1n+p)}
          {==}

def add_zero_c(n: Nat, x: Word(n)) -> {Word.adc(n, x, Word.zero(n), False{}, True{}) == Word.inc(n, x) : Word(n)}:
  match n:
    case 0n:
      match x:
        case WNil{}:
          {==}
    case 1n++p:
      match x:
        case WCon{False{}, +t}:
          %Equal.sym(Word(p), Word.adc(p, t, Word.zero(p), False{}, False{}), t, add_zero_r(p, t)) : {WCon{True{}, _} == WCon{True{}, t} : Word(1n+p)}
          {==}
        case WCon{True{}, +t}:
          %Equal.sym(Word(p), Word.adc(p, t, Word.zero(p), False{}, True{}), Word.inc(p, t), add_zero_c(p, t)) : {WCon{False{}, _} == WCon{False{}, Word.inc(p, t)} : Word(1n+p)}
          {==}

def add_one(n: Nat, x: Word(n)) -> {Word.adc(n, x, B.bitw(n, 0n), False{}, False{}) == Word.inc(n, x) : Word(n)}:
  match n:
    case 0n:
      match x:
        case WNil{}:
          {==}
    case 1n++p:
      match x:
        case WCon{False{}, +t}:
          %Equal.sym(Word(p), Word.adc(p, t, Word.zero(p), False{}, False{}), t, add_zero_r(p, t)) : {WCon{True{}, _} == WCon{True{}, t} : Word(1n+p)}
          {==}
        case WCon{True{}, +t}:
          %Equal.sym(Word(p), Word.adc(p, t, Word.zero(p), False{}, True{}), Word.inc(p, t), add_zero_c(p, t)) : {WCon{False{}, _} == WCon{False{}, Word.inc(p, t)} : Word(1n+p)}
          {==}

def u_add0(k: U32) -> {U32.add(k, 0) == k : U32}:
  match k:
    case U32{x}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.adc(32n, x, Word.zero(32n), False{}, False{}), x, add_zero_r(32n, x))

def u_add1(k: U32) -> {U32.add(k, 1) == U32.inc(k) : U32}:
  match k:
    case U32{x}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.adc(32n, x, B.bitw(32n, 0n), False{}, False{}), Word.inc(32n, x), add_one(32n, x))

# Nat.cmp(a, 1 + a) == LT
def nat_lt_succ(a: Nat) -> {Nat.cmp(a, 1n+a) == LT{} : Cmp}:
  match a:
    case 0n:
      {==}
    case 1n+q:
      nat_lt_succ(q)

# a word below 2^d is below its increment (inc does not wrap: the word is not maximal)
def lt_inc_k(bb: Bool, +k: U32, +d: Nat, s: B.IncSpecU(bb, k), hk: {U32.is_lt(k, U32.shln(1, d)) == True{} : Bool}) -> {U32.is_lt(k, U32.inc(k)) == True{} : Bool}:
  match bb:
    case True{}:
      B.lt_of_nat_u(k, U32.inc(k), (%Equal.sym(Nat, U32.to_nat(U32.inc(k)), 1n+U32.to_nat(k), s) : {Cmp.is_lt(Nat.cmp(U32.to_nat(k), _)) == True{} : Bool}; %Equal.sym(Cmp, Nat.cmp(U32.to_nat(k), 1n+U32.to_nat(k)), LT{}, nat_lt_succ(U32.to_nat(k))) : {Cmp.is_lt(_) == True{} : Bool}; {==}))
    case False{}:
      Empty.absurd({U32.is_lt(k, U32.inc(k)) == True{} : Bool}, s(U32.shln(1, d))(B.gt_of_lt_u(k, U32.shln(1, d), hk)))

def lt_inc_fin(+k: U32, +d: Nat, w: &bb: Bool -> B.IncSpecU(bb, k), hk: {U32.is_lt(k, U32.shln(1, d)) == True{} : Bool}) -> {U32.is_lt(k, U32.inc(k)) == True{} : Bool}:
  (bb, s) = w
  lt_inc_k(bb, k, d, s, hk)

def lt_inc_u(+k: U32, +d: Nat, hk: {U32.is_lt(k, U32.shln(1, d)) == True{} : Bool}) -> {U32.is_lt(k, U32.inc(k)) == True{} : Bool}:
  lt_inc_fin(k, d, B.inc_nat_u(k), hk)

# a position below the cursor stays below it after a 0/1 step
def cursor_step_k(c: Bool, +k: U32, +b: U32, +d: Nat, s: Bit01(c, b), hk: {U32.is_lt(k, U32.shln(1, d)) == True{} : Bool}, +pos: U32, hpos: {U32.is_lt(pos, k) == True{} : Bool}) -> {U32.is_lt(pos, U32.add(k, b)) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(U32, b, 1, s) : {U32.is_lt(pos, U32.add(k, _)) == True{} : Bool}
      %Equal.sym(U32, U32.add(k, 1), U32.inc(k), u_add1(k)) : {U32.is_lt(pos, _) == True{} : Bool}
      lt_trans_u(pos, k, U32.inc(k), hpos, lt_inc_u(k, d, hk))
    case False{}:
      %Equal.sym(U32, b, 0, s) : {U32.is_lt(pos, U32.add(k, _)) == True{} : Bool}
      %Equal.sym(U32, U32.add(k, 0), k, u_add0(k)) : {U32.is_lt(pos, _) == True{} : Bool}
      hpos

def cursor_step_fin(+k: U32, +b: U32, +d: Nat, w: &c: Bool -> Bit01(c, b), hk: {U32.is_lt(k, U32.shln(1, d)) == True{} : Bool}, +pos: U32, hpos: {U32.is_lt(pos, k) == True{} : Bool}) -> {U32.is_lt(pos, U32.add(k, b)) == True{} : Bool}:
  (c, s) = w
  cursor_step_k(c, k, b, d, s, hk, pos, hpos)

def cursor_step(+k: U32, +b: U32, +d: Nat, hb: {U32.is_le(b, 1) == True{} : Bool}, hk: {U32.is_lt(k, U32.shln(1, d)) == True{} : Bool}, +pos: U32, hpos: {U32.is_lt(pos, k) == True{} : Bool}) -> {U32.is_lt(pos, U32.add(k, b)) == True{} : Bool}:
  cursor_step_fin(k, b, d, le1_cases(b, hb), hk, pos, hpos)

# a kept row (word 1) moves the cursor strictly up
def cursor_set_k(c: Bool, +k: U32, +b: U32, +d: Nat, s: Bit01(c, b), hk: {U32.is_lt(k, U32.shln(1, d)) == True{} : Bool}) -> {U32.is_ne(b, 0) == True{} : Bool} -> {U32.is_lt(k, U32.add(k, b)) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(U32, b, 1, s) : {U32.is_ne(_, 0) == True{} : Bool} -> {U32.is_lt(k, U32.add(k, _)) == True{} : Bool}
      %Equal.sym(U32, U32.add(k, 1), U32.inc(k), u_add1(k)) : {U32.is_ne(1, 0) == True{} : Bool} -> {U32.is_lt(k, _) == True{} : Bool}
      nz => lt_inc_u(k, d, hk)
    case False{}:
      %Equal.sym(U32, b, 0, s) : {U32.is_ne(_, 0) == True{} : Bool} -> {U32.is_lt(k, U32.add(k, _)) == True{} : Bool}
      nz => Empty.absurd({U32.is_lt(k, U32.add(k, 0)) == True{} : Bool}, L.false_true(nz))

def cursor_set_fin(+k: U32, +b: U32, +d: Nat, w: &c: Bool -> Bit01(c, b), hk: {U32.is_lt(k, U32.shln(1, d)) == True{} : Bool}) -> {U32.is_ne(b, 0) == True{} : Bool} -> {U32.is_lt(k, U32.add(k, b)) == True{} : Bool}:
  (c, s) = w
  cursor_set_k(c, k, b, d, s, hk)

def cursor_set(+k: U32, +b: U32, +d: Nat, hb: {U32.is_le(b, 1) == True{} : Bool}, hk: {U32.is_lt(k, U32.shln(1, d)) == True{} : Bool}) -> {U32.is_ne(b, 0) == True{} : Bool} -> {U32.is_lt(k, U32.add(k, b)) == True{} : Bool}:
  cursor_set_fin(k, b, d, le1_cases(b, hb), hk)

# ---- keep one position: later writes of the compaction land above it -------------------------------

# the cell at pos of the output of the remaining run (pending read r of mask[i])
def CK(~T: Data, f: Nat, +i: U32, +k: U32, +d: Nat, -a: Array<T>, -out: Array<T>, -mask: Array<U32>, -r: Array<U32> & U32, +pos: U32, +val: T) -> Type:
  {Laws.rdN(T, d, Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep.go(~T, f, i, k, (a, out), r)), pos) == val : T}

# ... after the step's cursor move, with the read ra of a[i] pending inside compact.put
def CKmid(~T: Data, p: Nat, +i: U32, +k: U32, +b: U32, +d: Nat, -out: Array<T>, -mask: Array<U32>, -ra: Array<T> & T, +pos: U32, +val: T) -> Type:
  {Laws.rdN(T, d, Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep.go(~T, p, U32.inc(i), U32.add(k, b), K.Kernel.compact.put(~T, out, k, ra), Array.get(U32, mask, U32.inc(i)))), pos) == val : T}

def ckeep_s3(~T: Data, p: Nat, +i: U32, +k: U32, +b: U32, +d: Nat, a: Array<T>, -out: Array<T>, mask: Array<U32>, -maskR: Array<U32>, +em: {mask == maskR : Array<U32>}, room: Laws.CRoom(p, U32.inc(i), U32.add(k, b), d, maskR), +hb: {U32.is_le(b, 1) == True{} : Bool}, +hk: {U32.is_lt(k, U32.shln(1, d)) == True{} : Bool}, +pos: U32, +val: T, +hpos: {U32.is_lt(pos, k) == True{} : Bool}, hval: {Laws.rdN(T, d, out, pos) == val : T}, +y: T,
  ih: @a2: Array<T> -> @c: Array<T> -> @m2: Array<U32> -> Laws.WFArray(T, d, c) -> {m2 == maskR : Array<U32>} -> Laws.CRoom(p, U32.inc(i), U32.add(k, b), d, maskR) -> {U32.is_lt(pos, U32.add(k, b)) == True{} : Bool} -> {Laws.rdN(T, d, c, pos) == val : T} -> CK(~T, p, U32.inc(i), U32.add(k, b), d, a2, c, m2, Array.get(U32, m2, U32.inc(i)), pos, val),
  w: &c: Array<T> -> {Array.set(T, out, k, y) == c : Array<T>} & Laws.WFArray(T, d, c) & (@k2: U32 -> {Laws.rdN(T, d, c, k2) == Bool.pick(T, Laws.same_at(d, k, k2), y, Laws.rdN(T, d, out, k2)) : T}) & (@k2: U32 -> {Laws.rd_at(T, out, k2) == Laws.rdN(T, d, out, k2) : T}))
  -> CK(~T, p, U32.inc(i), U32.add(k, b), d, a, Array.set(T, out, k, y), mask, Array.get(U32, mask, U32.inc(i)), pos, val):
  (c, ec, wc, fj, cv) = w
  %Equal.sym(Array<T>, Array.set(T, out, k, y), c, ec) : CK(~T, p, U32.inc(i), U32.add(k, b), d, a, _, mask, Array.get(U32, mask, U32.inc(i)), pos, val)
  ih(a, c, mask, wc, em, room, cursor_step(k, b, d, hb, hk, pos, hpos), (%Equal.sym(T, Laws.rdN(T, d, c, pos), Bool.pick(T, Laws.same_at(d, k, pos), y, Laws.rdN(T, d, out, pos)), fj(pos)) : {_ == val : T}; %Equal.sym(Bool, Laws.same_at(d, k, pos), False{}, same_false_lt(d, k, pos, hk, hpos)) : {Bool.pick(T, _, y, Laws.rdN(T, d, out, pos)) == val : T}; hval))

def ckeep_s2(~T: Data, p: Nat, +i: U32, +k: U32, +b: U32, +d: Nat, -a: Array<T>, out: Array<T>, mask: Array<U32>, wf: Laws.WFArray(T, d, out), -maskR: Array<U32>, +em: {mask == maskR : Array<U32>}, room: Laws.CRoom(p, U32.inc(i), U32.add(k, b), d, maskR), +hb: {U32.is_le(b, 1) == True{} : Bool}, +hk: {U32.is_lt(k, U32.shln(1, d)) == True{} : Bool}, +pos: U32, +val: T, +hpos: {U32.is_lt(pos, k) == True{} : Bool}, hval: {Laws.rdN(T, d, out, pos) == val : T},
  ih: @a2: Array<T> -> @c: Array<T> -> @m2: Array<U32> -> Laws.WFArray(T, d, c) -> {m2 == maskR : Array<U32>} -> Laws.CRoom(p, U32.inc(i), U32.add(k, b), d, maskR) -> {U32.is_lt(pos, U32.add(k, b)) == True{} : Bool} -> {Laws.rdN(T, d, c, pos) == val : T} -> CK(~T, p, U32.inc(i), U32.add(k, b), d, a2, c, m2, Array.get(U32, m2, U32.inc(i)), pos, val),
  w: &a3: Array<T> -> &y: T -> {a3 == a : Array<T>} & {Array.get(T, a, i) == (a, y) : Array<T> & T} & {y == Laws.rd_at(T, a, i) : T})
  -> CKmid(~T, p, i, k, b, d, out, mask, Array.get(T, a, i), pos, val):
  (a2, +y, ea, e2, ey) = w
  %Equal.sym(Array<T> & T, Array.get(T, a, i), (a, y), e2) : CKmid(~T, p, i, k, b, d, out, mask, _, pos, val)
  %ea : CK(~T, p, U32.inc(i), U32.add(k, b), d, _, Array.set(T, out, k, y), mask, Array.get(U32, mask, U32.inc(i)), pos, val)
  ckeep_s3(~T, p, i, k, b, d, a2, out, mask, maskR, em, room, hb, hk, pos, val, hpos, hval, y, ih, set_other_w(T, d, out, k, y, wf))

def ckeep_s1(~T: Data, p: Nat, +i: U32, +k: U32, +d: Nat, a: Array<T>, out: Array<T>, -mask: Array<U32>, wf: Laws.WFArray(T, d, out), -maskR: Array<U32>, +em: {mask == maskR : Array<U32>}, room: Laws.CRoom(1n+p, i, k, d, maskR), +pos: U32, +val: T, +hpos: {U32.is_lt(pos, k) == True{} : Bool}, hval: {Laws.rdN(T, d, out, pos) == val : T},
  ih: @b: U32 -> @a2: Array<T> -> @c: Array<T> -> @m2: Array<U32> -> Laws.WFArray(T, d, c) -> {m2 == maskR : Array<U32>} -> Laws.CRoom(p, U32.inc(i), U32.add(k, b), d, maskR) -> {U32.is_lt(pos, U32.add(k, b)) == True{} : Bool} -> {Laws.rdN(T, d, c, pos) == val : T} -> CK(~T, p, U32.inc(i), U32.add(k, b), d, a2, c, m2, Array.get(U32, m2, U32.inc(i)), pos, val),
  w: &m3: Array<U32> -> &x: U32 -> {m3 == mask : Array<U32>} & {Array.get(U32, mask, i) == (mask, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, mask, i) : U32})
  -> CK(~T, 1n+p, i, k, d, a, out, mask, Array.get(U32, mask, i), pos, val):
  (+b, eb, +hb, +hk, room2) = room
  (mask2, +x, +em2, e1, ex) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, mask, i), (mask, x), e1) : CK(~T, 1n+p, i, k, d, a, out, mask, _, pos, val)
  %em2 : CK(~T, 1n+p, i, k, d, a, out, _, (_, x), pos, val)
  %Equal.sym(U32, x, b, Equal.trans(U32, x, Laws.rd_at(U32, mask, i), b, ex, Equal.trans(U32, Laws.rd_at(U32, mask, i), Laws.rd_at(U32, maskR, i), b, Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, i), mask, maskR, em), Equal.sym(U32, b, Laws.rd_at(U32, maskR, i), eb)))) : CK(~T, 1n+p, i, k, d, a, out, mask2, (mask2, _), pos, val)
  ckeep_s2(~T, p, i, k, b, d, a, out, mask2, wf, maskR, Equal.trans(Array<U32>, mask2, mask, maskR, em2, em), room2, hb, hk, pos, val, hpos, hval, ih(b), get_w(T, a, i))

def ckeep_zero(~T: Data, +i: U32, +k: U32, +d: Nat, a: Array<T>, out: Array<T>, -mask: Array<U32>, +pos: U32, +val: T, hval: {Laws.rdN(T, d, out, pos) == val : T},
  w: &m3: Array<U32> -> &x: U32 -> {m3 == mask : Array<U32>} & {Array.get(U32, mask, i) == (mask, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, mask, i) : U32})
  -> CK(~T, 0n, i, k, d, a, out, mask, Array.get(U32, mask, i), pos, val):
  (mask2, +x, em2, e1, ex) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, mask, i), (mask, x), e1) : CK(~T, 0n, i, k, d, a, out, mask, _, pos, val)
  hval

# the remaining run never writes below the cursor: a cell at pos < k keeps its value
def ckeep(~T: Data, f: Nat, +i: U32, +k: U32, +d: Nat, a: Array<T>, out: Array<T>, mask: Array<U32>, wf: Laws.WFArray(T, d, out), -maskR: Array<U32>, +em: {mask == maskR : Array<U32>}, room: Laws.CRoom(f, i, k, d, maskR), +pos: U32, +val: T, +hpos: {U32.is_lt(pos, k) == True{} : Bool}, hval: {Laws.rdN(T, d, out, pos) == val : T})
  -> CK(~T, f, i, k, d, a, out, mask, Array.get(U32, mask, i), pos, val):
  match f:
    case 0n:
      ckeep_zero(~T, i, k, d, a, out, mask, pos, val, hval, get_w(U32, mask, i))
    case 1n++p:
      ckeep_s1(~T, p, i, k, d, a, out, mask, wf, maskR, em, room, pos, val, hpos, hval, b => a2 => c => m2 => wc => em3 => room2 => hp => hv => ckeep(~T, p, U32.inc(i), U32.add(k, b), d, a2, c, m2, wc, maskR, em3, room2, pos, val, hp, hv), get_w(U32, mask, i))

# ---- the spec of the whole run -----------------------------------------------------------------------

# CSpec over the output of the remaining run (pending read r of mask[i]); aR / maskR are the arrays the
# spec names, equal to the live ones
def CS(~T: Data, f: Nat, +i: U32, +k: U32, +d: Nat, -a: Array<T>, -out: Array<T>, -mask: Array<U32>, -r: Array<U32> & U32, -aR: Array<T>, -maskR: Array<U32>) -> Type:
  Laws.CSpec(T, f, i, k, d, aR, maskR, Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep.go(~T, f, i, k, (a, out), r)))

def CSmid(~T: Data, p: Nat, +i: U32, +k: U32, +b: U32, +d: Nat, -out: Array<T>, -mask: Array<U32>, -ra: Array<T> & T, -aR: Array<T>, -maskR: Array<U32>) -> Type:
  Laws.CSpec(T, 1n+p, i, k, d, aR, maskR, Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep.go(~T, p, U32.inc(i), U32.add(k, b), K.Kernel.compact.put(~T, out, k, ra), Array.get(U32, mask, U32.inc(i)))))

def CSfin(~T: Data, p: Nat, +i: U32, +k: U32, +b: U32, +d: Nat, -a: Array<T>, -out2: Array<T>, -mask: Array<U32>, -aR: Array<T>, -maskR: Array<U32>) -> Type:
  Laws.CSpec(T, 1n+p, i, k, d, aR, maskR, Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep.go(~T, p, U32.inc(i), U32.add(k, b), (a, out2), Array.get(U32, mask, U32.inc(i)))))

# the clause of the row just written, restated from the ckeep copies to the spec's copies
def row_clause(~T: Data, +p: Nat, +i: U32, +k: U32, +b: U32, +d: Nat, -a3: Array<T>, -a4: Array<T>, -c1: Array<T>, -c2: Array<T>, -m3: Array<U32>, -m4: Array<U32>, -aR: Array<T>, +y: T,
  ea: {a3 == a4 : Array<T>}, ec: {c1 == c2 : Array<T>}, em: {m3 == m4 : Array<U32>}, ey: {y == Laws.rd_at(T, aR, i) : T},
  fact: CK(~T, p, U32.inc(i), U32.add(k, b), d, a3, c1, m3, Array.get(U32, m3, U32.inc(i)), k, y))
  -> {Laws.rdN(T, d, Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep.go(~T, p, U32.inc(i), U32.add(k, b), (a4, c2), Array.get(U32, m4, U32.inc(i)))), k) == Laws.rd_at(T, aR, i) : T}:
  %ea : {Laws.rdN(T, d, Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep.go(~T, p, U32.inc(i), U32.add(k, b), (_, c2), Array.get(U32, m4, U32.inc(i)))), k) == Laws.rd_at(T, aR, i) : T}
  %ec : {Laws.rdN(T, d, Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep.go(~T, p, U32.inc(i), U32.add(k, b), (a3, _), Array.get(U32, m4, U32.inc(i)))), k) == Laws.rd_at(T, aR, i) : T}
  %em : {Laws.rdN(T, d, Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep.go(~T, p, U32.inc(i), U32.add(k, b), (a3, c1), Array.get(U32, _, U32.inc(i)))), k) == Laws.rd_at(T, aR, i) : T}
  %ey : {Laws.rdN(T, d, Pair.fst(Array<T>, Array<U32>, K.Kernel.compact_keep.go(~T, p, U32.inc(i), U32.add(k, b), (a3, c1), Array.get(U32, m3, U32.inc(i)))), k) == _ : T}
  fact

# the written cell at k on the written array's copy
def wrote_k(~T: Data, +k: U32, +d: Nat, -out: Array<T>, -c: Array<T>, -c1: Array<T>, +y: T, ec1: {c1 == c : Array<T>}, e: {Laws.rdN(T, d, c, k) == Bool.pick(T, Laws.same_at(d, k, k), y, Laws.rdN(T, d, out, k)) : T}) -> {Laws.rdN(T, d, c1, k) == y : T}:
  %Equal.sym(Array<T>, c1, c, ec1) : {Laws.rdN(T, d, _, k) == y : T}
  %Equal.sym(T, Laws.rdN(T, d, c, k), Bool.pick(T, Laws.same_at(d, k, k), y, Laws.rdN(T, d, out, k)), e) : {_ == y : T}
  %Equal.sym(Bool, Laws.same_at(d, k, k), True{}, same_at_refl(d, k)) : {Bool.pick(T, _, y, Laws.rdN(T, d, out, k)) == y : T}
  {==}

def cspec_s4(~T: Data, +p: Nat, +i: U32, +k: U32, +b: U32, +d: Nat, -a2: Array<T>, -out: Array<T>, -c: Array<T>, -mask2: Array<U32>, -aR: Array<T>, -maskR: Array<U32>, +ea2: {a2 == aR : Array<T>}, +em2: {mask2 == maskR : Array<U32>}, +eb: {b == Laws.rd_at(U32, maskR, i) : U32}, +hb: {U32.is_le(b, 1) == True{} : Bool}, +hk: {U32.is_lt(k, U32.shln(1, d)) == True{} : Bool}, +y: T, +ey: {y == Laws.rd_at(T, aR, i) : T},
  fj: @k2: U32 -> {Laws.rdN(T, d, c, k2) == Bool.pick(T, Laws.same_at(d, k, k2), y, Laws.rdN(T, d, out, k2)) : T},
  rooms: Laws.CRoom(p, U32.inc(i), U32.add(k, b), d, maskR) & Laws.CRoom(p, U32.inc(i), U32.add(k, b), d, maskR),
  wa: &a3: Array<T> -> &a4: Array<T> -> {a3 == a2 : Array<T>} & {a4 == a2 : Array<T>},
  wc: &c1: Array<T> -> &c2: Array<T> -> {c1 == c : Array<T>} & {c2 == c : Array<T>} & Laws.WFArray(T, d, c1) & Laws.WFArray(T, d, c2),
  wm: &m3: Array<U32> -> &m4: Array<U32> -> {m3 == mask2 : Array<U32>} & {m4 == mask2 : Array<U32>},
  ih: @a4: Array<T> -> @c2: Array<T> -> @m4: Array<U32> -> Laws.WFArray(T, d, c2) -> {a4 == aR : Array<T>} -> {m4 == maskR : Array<U32>} -> Laws.CRoom(p, U32.inc(i), U32.add(k, b), d, maskR) -> CS(~T, p, U32.inc(i), U32.add(k, b), d, a4, c2, m4, Array.get(U32, m4, U32.inc(i)), aR, maskR))
  -> CSfin(~T, p, i, k, b, d, a2, c, mask2, aR, maskR):
  (r1, r2) = rooms
  (a3, a4, +ea3, +ea4) = wa
  (c1, c2, +ec1, +ec2, wc1, wc2) = wc
  (m3, m4, +em3, +em4) = wm
  %ea4 : CSfin(~T, p, i, k, b, d, _, c, mask2, aR, maskR)
  %ec2 : CSfin(~T, p, i, k, b, d, a4, _, mask2, aR, maskR)
  %em4 : CSfin(~T, p, i, k, b, d, a4, c2, _, aR, maskR)
  (b, eb, nz => row_clause(~T, p, i, k, b, d, a3, a4, c1, c2, m3, m4, aR, y, Equal.trans(Array<T>, a3, a2, a4, ea3, Equal.sym(Array<T>, a4, a2, ea4)), Equal.trans(Array<T>, c1, c, c2, ec1, Equal.sym(Array<T>, c2, c, ec2)), Equal.trans(Array<U32>, m3, mask2, m4, em3, Equal.sym(Array<U32>, m4, mask2, em4)), ey, ckeep(~T, p, U32.inc(i), U32.add(k, b), d, a3, c1, m3, wc1, maskR, Equal.trans(Array<U32>, m3, mask2, maskR, em3, em2), r1, k, y, cursor_set(k, b, d, hb, hk)(nz), wrote_k(~T, k, d, out, c, c1, y, ec1, fj(k)))), ih(a4, c2, m4, wc2, Equal.trans(Array<T>, a4, a2, aR, ea4, ea2), Equal.trans(Array<U32>, m4, mask2, maskR, em4, em2), r2))

def cspec_s3(~T: Data, +p: Nat, +i: U32, +k: U32, +b: U32, +d: Nat, a2: Array<T>, -out: Array<T>, mask2: Array<U32>, -aR: Array<T>, -maskR: Array<U32>, +ea2: {a2 == aR : Array<T>}, +em2: {mask2 == maskR : Array<U32>}, +eb: {b == Laws.rd_at(U32, maskR, i) : U32}, +hb: {U32.is_le(b, 1) == True{} : Bool}, +hk: {U32.is_lt(k, U32.shln(1, d)) == True{} : Bool}, +y: T, +ey: {y == Laws.rd_at(T, aR, i) : T}, room: Laws.CRoom(p, U32.inc(i), U32.add(k, b), d, maskR),
  ih: @a4: Array<T> -> @c2: Array<T> -> @m4: Array<U32> -> Laws.WFArray(T, d, c2) -> {a4 == aR : Array<T>} -> {m4 == maskR : Array<U32>} -> Laws.CRoom(p, U32.inc(i), U32.add(k, b), d, maskR) -> CS(~T, p, U32.inc(i), U32.add(k, b), d, a4, c2, m4, Array.get(U32, m4, U32.inc(i)), aR, maskR),
  w: &c: Array<T> -> {Array.set(T, out, k, y) == c : Array<T>} & Laws.WFArray(T, d, c) & (@k2: U32 -> {Laws.rdN(T, d, c, k2) == Bool.pick(T, Laws.same_at(d, k, k2), y, Laws.rdN(T, d, out, k2)) : T}) & (@k2: U32 -> {Laws.rd_at(T, out, k2) == Laws.rdN(T, d, out, k2) : T}))
  -> CSfin(~T, p, i, k, b, d, a2, Array.set(T, out, k, y), mask2, aR, maskR):
  (c, ec, wc, fj, cv) = w
  %Equal.sym(Array<T>, Array.set(T, out, k, y), c, ec) : CSfin(~T, p, i, k, b, d, a2, _, mask2, aR, maskR)
  cspec_s4(~T, p, i, k, b, d, a2, out, c, mask2, aR, maskR, ea2, em2, eb, hb, hk, y, ey, fj, croom_dup(p, U32.inc(i), U32.add(k, b), d, maskR, room), clone_eq(T, a2), clone_wf(T, d, c, wc), clone_eq(U32, mask2), ih)

def cspec_s2(~T: Data, +p: Nat, +i: U32, +k: U32, +b: U32, +d: Nat, -a: Array<T>, out: Array<T>, mask2: Array<U32>, wf: Laws.WFArray(T, d, out), -aR: Array<T>, -maskR: Array<U32>, +ea: {a == aR : Array<T>}, +em2: {mask2 == maskR : Array<U32>}, +eb: {b == Laws.rd_at(U32, maskR, i) : U32}, +hb: {U32.is_le(b, 1) == True{} : Bool}, +hk: {U32.is_lt(k, U32.shln(1, d)) == True{} : Bool}, room: Laws.CRoom(p, U32.inc(i), U32.add(k, b), d, maskR),
  ih: @a4: Array<T> -> @c2: Array<T> -> @m4: Array<U32> -> Laws.WFArray(T, d, c2) -> {a4 == aR : Array<T>} -> {m4 == maskR : Array<U32>} -> Laws.CRoom(p, U32.inc(i), U32.add(k, b), d, maskR) -> CS(~T, p, U32.inc(i), U32.add(k, b), d, a4, c2, m4, Array.get(U32, m4, U32.inc(i)), aR, maskR),
  w: &a3: Array<T> -> &y: T -> {a3 == a : Array<T>} & {Array.get(T, a, i) == (a, y) : Array<T> & T} & {y == Laws.rd_at(T, a, i) : T})
  -> CSmid(~T, p, i, k, b, d, out, mask2, Array.get(T, a, i), aR, maskR):
  (a2, +y, +ea2, e2, ey) = w
  %Equal.sym(Array<T> & T, Array.get(T, a, i), (a, y), e2) : CSmid(~T, p, i, k, b, d, out, mask2, _, aR, maskR)
  %ea2 : CSfin(~T, p, i, k, b, d, _, Array.set(T, out, k, y), mask2, aR, maskR)
  cspec_s3(~T, p, i, k, b, d, a2, out, mask2, aR, maskR, Equal.trans(Array<T>, a2, a, aR, ea2, ea), em2, eb, hb, hk, y, Equal.trans(T, y, Laws.rd_at(T, a, i), Laws.rd_at(T, aR, i), ey, Equal.cong(Array<T>, T, q => Laws.rd_at(T, q, i), a, aR, ea)), room, ih, set_other_w(T, d, out, k, y, wf))

def cspec_s1(~T: Data, +p: Nat, +i: U32, +k: U32, +d: Nat, a: Array<T>, out: Array<T>, -mask: Array<U32>, wf: Laws.WFArray(T, d, out), -aR: Array<T>, -maskR: Array<U32>, +ea: {a == aR : Array<T>}, +em: {mask == maskR : Array<U32>}, room: Laws.CRoom(1n+p, i, k, d, maskR),
  ih: @b: U32 -> @a4: Array<T> -> @c2: Array<T> -> @m4: Array<U32> -> Laws.WFArray(T, d, c2) -> {a4 == aR : Array<T>} -> {m4 == maskR : Array<U32>} -> Laws.CRoom(p, U32.inc(i), U32.add(k, b), d, maskR) -> CS(~T, p, U32.inc(i), U32.add(k, b), d, a4, c2, m4, Array.get(U32, m4, U32.inc(i)), aR, maskR),
  w: &m3: Array<U32> -> &x: U32 -> {m3 == mask : Array<U32>} & {Array.get(U32, mask, i) == (mask, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, mask, i) : U32})
  -> CS(~T, 1n+p, i, k, d, a, out, mask, Array.get(U32, mask, i), aR, maskR):
  (+b, +eb, +hb, +hk, room2) = room
  (mask2, +x, +em2, e1, ex) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, mask, i), (mask, x), e1) : CS(~T, 1n+p, i, k, d, a, out, mask, _, aR, maskR)
  %em2 : CS(~T, 1n+p, i, k, d, a, out, _, (_, x), aR, maskR)
  %Equal.sym(U32, x, b, Equal.trans(U32, x, Laws.rd_at(U32, mask, i), b, ex, Equal.trans(U32, Laws.rd_at(U32, mask, i), Laws.rd_at(U32, maskR, i), b, Equal.cong(Array<U32>, U32, q => Laws.rd_at(U32, q, i), mask, maskR, em), Equal.sym(U32, b, Laws.rd_at(U32, maskR, i), eb)))) : CS(~T, 1n+p, i, k, d, a, out, mask2, (mask2, _), aR, maskR)
  cspec_s2(~T, p, i, k, b, d, a, out, mask2, wf, aR, maskR, ea, Equal.trans(Array<U32>, mask2, mask, maskR, em2, em), eb, hb, hk, room2, ih(b), get_w(T, a, i))

# the compaction's contract for the remaining run
def cspec_run(~T: Data, f: Nat, +i: U32, +k: U32, +d: Nat, a: Array<T>, out: Array<T>, mask: Array<U32>, wf: Laws.WFArray(T, d, out), -aR: Array<T>, -maskR: Array<U32>, +ea: {a == aR : Array<T>}, +em: {mask == maskR : Array<U32>}, room: Laws.CRoom(f, i, k, d, maskR))
  -> CS(~T, f, i, k, d, a, out, mask, Array.get(U32, mask, i), aR, maskR):
  match f:
    case 0n:
      Unit{}
    case 1n++p:
      cspec_s1(~T, p, i, k, d, a, out, mask, wf, aR, maskR, ea, em, room, b => a4 => c2 => m4 => wc2 => ea4 => em4 => room2 => cspec_run(~T, p, U32.inc(i), U32.add(k, b), d, a4, c2, m4, wc2, aR, maskR, ea4, em4, room2), get_w(U32, mask, i))

def Laws.compact_contents(d, n, a, mask, z, room):
  cspec_run(~U32, U32.to_nat(n), 0, 0, d, a, Array.new(U32, d, z), mask, Laws.wf_new(U32, d, z), a, mask, {==}, {==}, room)

# ---- the mask comes back ------------------------------------------------------------------------------

def CM(~T: Data, f: Nat, +i: U32, +k: U32, -a: Array<T>, -out: Array<T>, -mask: Array<U32>, -r: Array<U32> & U32) -> Type:
  {Pair.snd(Array<T>, Array<U32>, K.Kernel.compact_keep.go(~T, f, i, k, (a, out), r)) == mask : Array<U32>}

def CMmid(~T: Data, p: Nat, +i: U32, +k: U32, +x: U32, -out: Array<T>, -mask: Array<U32>, -ra: Array<T> & T) -> Type:
  {Pair.snd(Array<T>, Array<U32>, K.Kernel.compact_keep.go(~T, p, U32.inc(i), U32.add(k, x), K.Kernel.compact.put(~T, out, k, ra), Array.get(U32, mask, U32.inc(i)))) == mask : Array<U32>}

def cmask_s2(~T: Data, +p: Nat, +i: U32, +k: U32, +x: U32, -a: Array<T>, out: Array<T>, mask2: Array<U32>,
  ih: @a2: Array<T> -> @c: Array<T> -> @m2: Array<U32> -> CM(~T, p, U32.inc(i), U32.add(k, x), a2, c, m2, Array.get(U32, m2, U32.inc(i))),
  w: &a3: Array<T> -> &y: T -> {a3 == a : Array<T>} & {Array.get(T, a, i) == (a, y) : Array<T> & T} & {y == Laws.rd_at(T, a, i) : T})
  -> CMmid(~T, p, i, k, x, out, mask2, Array.get(T, a, i)):
  (a2, +y, ea, e2, ey) = w
  %Equal.sym(Array<T> & T, Array.get(T, a, i), (a, y), e2) : CMmid(~T, p, i, k, x, out, mask2, _)
  %ea : CM(~T, p, U32.inc(i), U32.add(k, x), _, Array.set(T, out, k, y), mask2, Array.get(U32, mask2, U32.inc(i)))
  ih(a2, Array.set(T, out, k, y), mask2)

def cmask_s1(~T: Data, +p: Nat, +i: U32, +k: U32, a: Array<T>, out: Array<T>, -mask: Array<U32>,
  ih: @x: U32 -> @a2: Array<T> -> @c: Array<T> -> @m2: Array<U32> -> CM(~T, p, U32.inc(i), U32.add(k, x), a2, c, m2, Array.get(U32, m2, U32.inc(i))),
  w: &m3: Array<U32> -> &x: U32 -> {m3 == mask : Array<U32>} & {Array.get(U32, mask, i) == (mask, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, mask, i) : U32})
  -> CM(~T, 1n+p, i, k, a, out, mask, Array.get(U32, mask, i)):
  (mask2, +x, em2, e1, ex) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, mask, i), (mask, x), e1) : CM(~T, 1n+p, i, k, a, out, mask, _)
  %em2 : CM(~T, 1n+p, i, k, a, out, _, (_, x))
  cmask_s2(~T, p, i, k, x, a, out, mask2, ih(x), get_w(T, a, i))

def cmask_zero(~T: Data, +i: U32, +k: U32, -a: Array<T>, -out: Array<T>, -mask: Array<U32>, w: &m3: Array<U32> -> &x: U32 -> {m3 == mask : Array<U32>} & {Array.get(U32, mask, i) == (mask, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, mask, i) : U32}) -> CM(~T, 0n, i, k, a, out, mask, Array.get(U32, mask, i)):
  (mask2, +x, em2, e1, ex) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, mask, i), (mask, x), e1) : CM(~T, 0n, i, k, a, out, mask, _)
  {==}

def cmask(~T: Data, f: Nat, +i: U32, +k: U32, a: Array<T>, out: Array<T>, mask: Array<U32>) -> CM(~T, f, i, k, a, out, mask, Array.get(U32, mask, i)):
  match f:
    case 0n:
      cmask_zero(~T, i, k, a, out, mask, get_w(U32, mask, i))
    case 1n++p:
      cmask_s1(~T, p, i, k, a, out, mask, x => a2 => c => m2 => cmask(~T, p, U32.inc(i), U32.add(k, x), a2, c, m2), get_w(U32, mask, i))

def Laws.compact_keeps_mask(d, n, a, mask, z):
  cmask(~U32, U32.to_nat(n), 0, 0, a, Array.new(U32, d, z), mask)

# ---- Column.cell is pure and reads the model ccell (LAWS.bend section 12) ---------------------------

# the data part: Column.data_cell on a CBool column answers the modelled scalar
def dcell_cbool(+len: U32, +depth: Nat, -valid: C.Valid, -data: Array<U32>, +i: U32, w: &x: U32 -> {Array.get(U32, data, i) == (data, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, data, i) : U32}) -> {C.Column.data_cell(C.CBool{len, depth, valid, data}, i) == (C.CBool{len, depth, valid, data}, D.SBool{U32.is_ne(Laws.rd_at(U32, data, i), 0)}) : C.Column & D.Scalar}:
  (+x, e1, e2) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, data, i), (data, x), e1) : {C.Column.cell.w(D.TBool{}, len, depth, valid, _) == (C.CBool{len, depth, valid, data}, D.SBool{U32.is_ne(Laws.rd_at(U32, data, i), 0)}) : C.Column & D.Scalar}
  %e2 : {C.Column.cell.w(D.TBool{}, len, depth, valid, (data, x)) == (C.CBool{len, depth, valid, data}, D.SBool{U32.is_ne(_, 0)}) : C.Column & D.Scalar}
  {==}

# the validity decision ok = (mask word != 0) as a parameter
def cp_mask_cbool_ok(ok: Bool, +len: U32, +depth: Nat, -m: Array<U32>, data: Array<U32>, +i: U32) -> {C.Column.cell.c(ok, i, C.CBool{len, depth, C.Mask{m}, data}) == (C.CBool{len, depth, C.Mask{m}, data}, Bool.pick(D.Scalar, ok, D.SBool{U32.is_ne(Laws.rd_at(U32, data, i), 0)}, D.SNull{})) : C.Column & D.Scalar}:
  match ok:
    case True{}:
      dcell_cbool(len, depth, C.Mask{m}, data, i, PK.get_at_w(U32, data, i))
    case False{}:
      {==}

def cp_mask_cbool_k(+len: U32, +depth: Nat, -m: Array<U32>, data: Array<U32>, +i: U32, w: &x: U32 -> {Array.get(U32, m, i) == (m, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, m, i) : U32}) -> {C.Column.cell(C.CBool{len, depth, C.Mask{m}, data}, i) == (C.CBool{len, depth, C.Mask{m}, data}, Laws.ccell(C.CBool{len, depth, C.Mask{m}, data}, i)) : C.Column & D.Scalar}:
  (+x, e1, e2) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, m, i), (m, x), e1) : {C.Column.cell.b(i, C.CBool{len, depth, C.AllValid{}, data}, C.Valid.get.k(_)) == (C.CBool{len, depth, C.Mask{m}, data}, Laws.ccell(C.CBool{len, depth, C.Mask{m}, data}, i)) : C.Column & D.Scalar}
  %e2 : {C.Column.cell.b(i, C.CBool{len, depth, C.AllValid{}, data}, C.Valid.get.k((m, x))) == (C.CBool{len, depth, C.Mask{m}, data}, Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SBool{U32.is_ne(Laws.rd_at(U32, data, i), 0)}, D.SNull{})) : C.Column & D.Scalar}
  cp_mask_cbool_ok(U32.is_ne(x, 0), len, depth, m, data, i)

def cp_cbool(+len: U32, +depth: Nat, valid: C.Valid, data: Array<U32>, +i: U32) -> {C.Column.cell(C.CBool{len, depth, valid, data}, i) == (C.CBool{len, depth, valid, data}, Laws.ccell(C.CBool{len, depth, valid, data}, i)) : C.Column & D.Scalar}:
  match valid:
    case C.AllValid{}:
      dcell_cbool(len, depth, C.AllValid{}, data, i, PK.get_at_w(U32, data, i))
    case C.Mask{m}:
      cp_mask_cbool_k(len, depth, m, data, i, PK.get_at_w(U32, m, i))

# the data part: Column.data_cell on a CU32 column answers the modelled scalar
def dcell_cu32(+len: U32, +depth: Nat, -valid: C.Valid, -data: Array<U32>, +i: U32, w: &x: U32 -> {Array.get(U32, data, i) == (data, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, data, i) : U32}) -> {C.Column.data_cell(C.CU32{len, depth, valid, data}, i) == (C.CU32{len, depth, valid, data}, D.SU32{Laws.rd_at(U32, data, i)}) : C.Column & D.Scalar}:
  (+x, e1, e2) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, data, i), (data, x), e1) : {C.Column.cell.w(D.TU32{}, len, depth, valid, _) == (C.CU32{len, depth, valid, data}, D.SU32{Laws.rd_at(U32, data, i)}) : C.Column & D.Scalar}
  %e2 : {C.Column.cell.w(D.TU32{}, len, depth, valid, (data, x)) == (C.CU32{len, depth, valid, data}, D.SU32{_}) : C.Column & D.Scalar}
  {==}

# the validity decision ok = (mask word != 0) as a parameter
def cp_mask_cu32_ok(ok: Bool, +len: U32, +depth: Nat, -m: Array<U32>, data: Array<U32>, +i: U32) -> {C.Column.cell.c(ok, i, C.CU32{len, depth, C.Mask{m}, data}) == (C.CU32{len, depth, C.Mask{m}, data}, Bool.pick(D.Scalar, ok, D.SU32{Laws.rd_at(U32, data, i)}, D.SNull{})) : C.Column & D.Scalar}:
  match ok:
    case True{}:
      dcell_cu32(len, depth, C.Mask{m}, data, i, PK.get_at_w(U32, data, i))
    case False{}:
      {==}

def cp_mask_cu32_k(+len: U32, +depth: Nat, -m: Array<U32>, data: Array<U32>, +i: U32, w: &x: U32 -> {Array.get(U32, m, i) == (m, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, m, i) : U32}) -> {C.Column.cell(C.CU32{len, depth, C.Mask{m}, data}, i) == (C.CU32{len, depth, C.Mask{m}, data}, Laws.ccell(C.CU32{len, depth, C.Mask{m}, data}, i)) : C.Column & D.Scalar}:
  (+x, e1, e2) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, m, i), (m, x), e1) : {C.Column.cell.b(i, C.CU32{len, depth, C.AllValid{}, data}, C.Valid.get.k(_)) == (C.CU32{len, depth, C.Mask{m}, data}, Laws.ccell(C.CU32{len, depth, C.Mask{m}, data}, i)) : C.Column & D.Scalar}
  %e2 : {C.Column.cell.b(i, C.CU32{len, depth, C.AllValid{}, data}, C.Valid.get.k((m, x))) == (C.CU32{len, depth, C.Mask{m}, data}, Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SU32{Laws.rd_at(U32, data, i)}, D.SNull{})) : C.Column & D.Scalar}
  cp_mask_cu32_ok(U32.is_ne(x, 0), len, depth, m, data, i)

def cp_cu32(+len: U32, +depth: Nat, valid: C.Valid, data: Array<U32>, +i: U32) -> {C.Column.cell(C.CU32{len, depth, valid, data}, i) == (C.CU32{len, depth, valid, data}, Laws.ccell(C.CU32{len, depth, valid, data}, i)) : C.Column & D.Scalar}:
  match valid:
    case C.AllValid{}:
      dcell_cu32(len, depth, C.AllValid{}, data, i, PK.get_at_w(U32, data, i))
    case C.Mask{m}:
      cp_mask_cu32_k(len, depth, m, data, i, PK.get_at_w(U32, m, i))

# the data part: Column.data_cell on a CI32 column answers the modelled scalar
def dcell_ci32(+len: U32, +depth: Nat, -valid: C.Valid, -data: Array<U32>, +i: U32, w: &x: U32 -> {Array.get(U32, data, i) == (data, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, data, i) : U32}) -> {C.Column.data_cell(C.CI32{len, depth, valid, data}, i) == (C.CI32{len, depth, valid, data}, D.SI32{D.I32{Laws.rd_at(U32, data, i)}}) : C.Column & D.Scalar}:
  (+x, e1, e2) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, data, i), (data, x), e1) : {C.Column.cell.w(D.TI32{}, len, depth, valid, _) == (C.CI32{len, depth, valid, data}, D.SI32{D.I32{Laws.rd_at(U32, data, i)}}) : C.Column & D.Scalar}
  %e2 : {C.Column.cell.w(D.TI32{}, len, depth, valid, (data, x)) == (C.CI32{len, depth, valid, data}, D.SI32{D.I32{_}}) : C.Column & D.Scalar}
  {==}

# the validity decision ok = (mask word != 0) as a parameter
def cp_mask_ci32_ok(ok: Bool, +len: U32, +depth: Nat, -m: Array<U32>, data: Array<U32>, +i: U32) -> {C.Column.cell.c(ok, i, C.CI32{len, depth, C.Mask{m}, data}) == (C.CI32{len, depth, C.Mask{m}, data}, Bool.pick(D.Scalar, ok, D.SI32{D.I32{Laws.rd_at(U32, data, i)}}, D.SNull{})) : C.Column & D.Scalar}:
  match ok:
    case True{}:
      dcell_ci32(len, depth, C.Mask{m}, data, i, PK.get_at_w(U32, data, i))
    case False{}:
      {==}

def cp_mask_ci32_k(+len: U32, +depth: Nat, -m: Array<U32>, data: Array<U32>, +i: U32, w: &x: U32 -> {Array.get(U32, m, i) == (m, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, m, i) : U32}) -> {C.Column.cell(C.CI32{len, depth, C.Mask{m}, data}, i) == (C.CI32{len, depth, C.Mask{m}, data}, Laws.ccell(C.CI32{len, depth, C.Mask{m}, data}, i)) : C.Column & D.Scalar}:
  (+x, e1, e2) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, m, i), (m, x), e1) : {C.Column.cell.b(i, C.CI32{len, depth, C.AllValid{}, data}, C.Valid.get.k(_)) == (C.CI32{len, depth, C.Mask{m}, data}, Laws.ccell(C.CI32{len, depth, C.Mask{m}, data}, i)) : C.Column & D.Scalar}
  %e2 : {C.Column.cell.b(i, C.CI32{len, depth, C.AllValid{}, data}, C.Valid.get.k((m, x))) == (C.CI32{len, depth, C.Mask{m}, data}, Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SI32{D.I32{Laws.rd_at(U32, data, i)}}, D.SNull{})) : C.Column & D.Scalar}
  cp_mask_ci32_ok(U32.is_ne(x, 0), len, depth, m, data, i)

def cp_ci32(+len: U32, +depth: Nat, valid: C.Valid, data: Array<U32>, +i: U32) -> {C.Column.cell(C.CI32{len, depth, valid, data}, i) == (C.CI32{len, depth, valid, data}, Laws.ccell(C.CI32{len, depth, valid, data}, i)) : C.Column & D.Scalar}:
  match valid:
    case C.AllValid{}:
      dcell_ci32(len, depth, C.AllValid{}, data, i, PK.get_at_w(U32, data, i))
    case C.Mask{m}:
      cp_mask_ci32_k(len, depth, m, data, i, PK.get_at_w(U32, m, i))

# the data part: Column.data_cell on a CF32 column answers the modelled scalar
def dcell_cf32(+len: U32, +depth: Nat, -valid: C.Valid, -data: Array<F32>, +i: U32, w: &x: F32 -> {Array.get(F32, data, i) == (data, x) : Array<F32> & F32} & {x == Laws.rd_at(F32, data, i) : F32}) -> {C.Column.data_cell(C.CF32{len, depth, valid, data}, i) == (C.CF32{len, depth, valid, data}, D.SF32{Laws.rd_at(F32, data, i)}) : C.Column & D.Scalar}:
  (+x, e1, e2) = w
  %Equal.sym(Array<F32> & F32, Array.get(F32, data, i), (data, x), e1) : {C.Column.cell.f(len, depth, valid, _) == (C.CF32{len, depth, valid, data}, D.SF32{Laws.rd_at(F32, data, i)}) : C.Column & D.Scalar}
  %e2 : {C.Column.cell.f(len, depth, valid, (data, x)) == (C.CF32{len, depth, valid, data}, D.SF32{_}) : C.Column & D.Scalar}
  {==}

# the validity decision ok = (mask word != 0) as a parameter
def cp_mask_cf32_ok(ok: Bool, +len: U32, +depth: Nat, -m: Array<U32>, data: Array<F32>, +i: U32) -> {C.Column.cell.c(ok, i, C.CF32{len, depth, C.Mask{m}, data}) == (C.CF32{len, depth, C.Mask{m}, data}, Bool.pick(D.Scalar, ok, D.SF32{Laws.rd_at(F32, data, i)}, D.SNull{})) : C.Column & D.Scalar}:
  match ok:
    case True{}:
      dcell_cf32(len, depth, C.Mask{m}, data, i, PK.get_at_w(F32, data, i))
    case False{}:
      {==}

def cp_mask_cf32_k(+len: U32, +depth: Nat, -m: Array<U32>, data: Array<F32>, +i: U32, w: &x: U32 -> {Array.get(U32, m, i) == (m, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, m, i) : U32}) -> {C.Column.cell(C.CF32{len, depth, C.Mask{m}, data}, i) == (C.CF32{len, depth, C.Mask{m}, data}, Laws.ccell(C.CF32{len, depth, C.Mask{m}, data}, i)) : C.Column & D.Scalar}:
  (+x, e1, e2) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, m, i), (m, x), e1) : {C.Column.cell.b(i, C.CF32{len, depth, C.AllValid{}, data}, C.Valid.get.k(_)) == (C.CF32{len, depth, C.Mask{m}, data}, Laws.ccell(C.CF32{len, depth, C.Mask{m}, data}, i)) : C.Column & D.Scalar}
  %e2 : {C.Column.cell.b(i, C.CF32{len, depth, C.AllValid{}, data}, C.Valid.get.k((m, x))) == (C.CF32{len, depth, C.Mask{m}, data}, Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SF32{Laws.rd_at(F32, data, i)}, D.SNull{})) : C.Column & D.Scalar}
  cp_mask_cf32_ok(U32.is_ne(x, 0), len, depth, m, data, i)

def cp_cf32(+len: U32, +depth: Nat, valid: C.Valid, data: Array<F32>, +i: U32) -> {C.Column.cell(C.CF32{len, depth, valid, data}, i) == (C.CF32{len, depth, valid, data}, Laws.ccell(C.CF32{len, depth, valid, data}, i)) : C.Column & D.Scalar}:
  match valid:
    case C.AllValid{}:
      dcell_cf32(len, depth, C.AllValid{}, data, i, PK.get_at_w(F32, data, i))
    case C.Mask{m}:
      cp_mask_cf32_k(len, depth, m, data, i, PK.get_at_w(U32, m, i))

# the data part: Column.data_cell on a CStr column answers the modelled scalar
def dcell_cstr(+len: U32, +depth: Nat, -valid: C.Valid, -data: Array<String>, +i: U32, w: &x: String -> {Array.get(String, data, i) == (data, x) : Array<String> & String} & {x == Laws.rd_at(String, data, i) : String}) -> {C.Column.data_cell(C.CStr{len, depth, valid, data}, i) == (C.CStr{len, depth, valid, data}, D.SStr{Laws.rd_at(String, data, i)}) : C.Column & D.Scalar}:
  (+x, e1, e2) = w
  %Equal.sym(Array<String> & String, Array.get(String, data, i), (data, x), e1) : {C.Column.cell.s(len, depth, valid, _) == (C.CStr{len, depth, valid, data}, D.SStr{Laws.rd_at(String, data, i)}) : C.Column & D.Scalar}
  %e2 : {C.Column.cell.s(len, depth, valid, (data, x)) == (C.CStr{len, depth, valid, data}, D.SStr{_}) : C.Column & D.Scalar}
  {==}

# the validity decision ok = (mask word != 0) as a parameter
def cp_mask_cstr_ok(ok: Bool, +len: U32, +depth: Nat, -m: Array<U32>, data: Array<String>, +i: U32) -> {C.Column.cell.c(ok, i, C.CStr{len, depth, C.Mask{m}, data}) == (C.CStr{len, depth, C.Mask{m}, data}, Bool.pick(D.Scalar, ok, D.SStr{Laws.rd_at(String, data, i)}, D.SNull{})) : C.Column & D.Scalar}:
  match ok:
    case True{}:
      dcell_cstr(len, depth, C.Mask{m}, data, i, PK.get_at_w(String, data, i))
    case False{}:
      {==}

def cp_mask_cstr_k(+len: U32, +depth: Nat, -m: Array<U32>, data: Array<String>, +i: U32, w: &x: U32 -> {Array.get(U32, m, i) == (m, x) : Array<U32> & U32} & {x == Laws.rd_at(U32, m, i) : U32}) -> {C.Column.cell(C.CStr{len, depth, C.Mask{m}, data}, i) == (C.CStr{len, depth, C.Mask{m}, data}, Laws.ccell(C.CStr{len, depth, C.Mask{m}, data}, i)) : C.Column & D.Scalar}:
  (+x, e1, e2) = w
  %Equal.sym(Array<U32> & U32, Array.get(U32, m, i), (m, x), e1) : {C.Column.cell.b(i, C.CStr{len, depth, C.AllValid{}, data}, C.Valid.get.k(_)) == (C.CStr{len, depth, C.Mask{m}, data}, Laws.ccell(C.CStr{len, depth, C.Mask{m}, data}, i)) : C.Column & D.Scalar}
  %e2 : {C.Column.cell.b(i, C.CStr{len, depth, C.AllValid{}, data}, C.Valid.get.k((m, x))) == (C.CStr{len, depth, C.Mask{m}, data}, Bool.pick(D.Scalar, U32.is_ne(_, 0), D.SStr{Laws.rd_at(String, data, i)}, D.SNull{})) : C.Column & D.Scalar}
  cp_mask_cstr_ok(U32.is_ne(x, 0), len, depth, m, data, i)

def cp_cstr(+len: U32, +depth: Nat, valid: C.Valid, data: Array<String>, +i: U32) -> {C.Column.cell(C.CStr{len, depth, valid, data}, i) == (C.CStr{len, depth, valid, data}, Laws.ccell(C.CStr{len, depth, valid, data}, i)) : C.Column & D.Scalar}:
  match valid:
    case C.AllValid{}:
      dcell_cstr(len, depth, C.AllValid{}, data, i, PK.get_at_w(String, data, i))
    case C.Mask{m}:
      cp_mask_cstr_k(len, depth, m, data, i, PK.get_at_w(U32, m, i))

def Laws.cell_pure(c, i):
  match c:
    case C.CBool{+len, +depth, valid, data}:
      cp_cbool(len, depth, valid, data, i)
    case C.CU32{+len, +depth, valid, data}:
      cp_cu32(len, depth, valid, data, i)
    case C.CI32{+len, +depth, valid, data}:
      cp_ci32(len, depth, valid, data, i)
    case C.CF32{+len, +depth, valid, data}:
      cp_cf32(len, depth, valid, data, i)
    case C.CStr{+len, +depth, valid, data}:
      cp_cstr(len, depth, valid, data, i)

def Laws.head_cell(c, n, k):
  match c:
    case C.CBool{len, depth, valid, data}:
      {==}
    case C.CU32{len, depth, valid, data}:
      {==}
    case C.CI32{len, depth, valid, data}:
      {==}
    case C.CF32{len, depth, valid, data}:
      {==}
    case C.CStr{len, depth, valid, data}:
      {==}

# ---- Kernel.depth_for gives at least n slots for n <= 2^31 -------------------------------------------

# the loop with 1+f fuel left at depth d, the exit test c = (n <= 2^d) as a parameter, and n <= 2^(f+d)
def dff_go(f: Nat, +n: U32, +d: Nat, c: Bool, e: {U32.is_le(n, U32.shln(1, d)) == c : Bool}, h: {U32.is_le(n, U32.shln(1, Nat.add(f, d))) == True{} : Bool}) -> {U32.is_le(n, U32.shln(1, K.Kernel.depth_for.go(1n+f, n, d, c))) == True{} : Bool}:
  match f c:
    case _ True{}:
      e
    case 0n False{}:
      Empty.absurd({U32.is_le(n, U32.shln(1, K.Kernel.depth_for.go(0n, n, 1n+d, U32.is_le(n, U32.shln(1, 1n+d))))) == True{} : Bool}, L.true_false(Equal.trans(Bool, True{}, U32.is_le(n, U32.shln(1, d)), False{}, Equal.sym(Bool, U32.is_le(n, U32.shln(1, d)), True{}, h), e)))
    case 1n++q False{}:
      dff_go(q, n, 1n+d, U32.is_le(n, U32.shln(1, 1n+d)), {==}, (%Equal.sym(Nat, Nat.add(q, 1n+d), 1n+Nat.add(q, d), B.add_succ(q, d)) : {U32.is_le(n, U32.shln(1, _)) == True{} : Bool}; h))

def Laws.depth_for_fits(n, h):
  dff_go(31n, n, 0n, U32.is_le(n, 1), {==}, h)
