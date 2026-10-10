# S5 (W0 engine spike, disposable): proof feasibility for chunked kernels.
#
# A chunk tree over owned U32 leaves with LOGICAL cell addressing:
#   CL{n, d, a}             n rows in the 2^d slots of a
#   CN{rows, lrows, l, r}   rows = lrows + rows(r), lrows = rows(l): the node stores its left child's row
#                           count so a logical row k is addressed without reading the children twice
# Models: crows (the row count), ccell (the logical cell at k), the Type-valued WFChunks and ShapeWF.
# Kernels: cmap_not (the chunked Kernel.mask_not, one parallel let per node), ccompact (per-leaf
# Kernel.compact_keep with one mask tree, ragged leaves kept, counts carried out as Data).
#
# PROVEN here (bend and --verdict; the file imports LAWS.bend, so its 149 statements are reported as the
# baseline TODO count, and PROOF_contents.bend for the leaf lemma map_cell):
#   (a') cmap_leafwise: the chunked map is, leaf by leaf, the flat map (Leafwise): a pure node congruence
#        whose leaf lemma is PROOF_contents' map_cell (the term behind the production law mask_not_cell)
#   (c)  cmap_shape: the chunked map keeps the row counts and the shape half of WFChunks (ShapeWF)
# STATED, left open (the measured gap; see the README for the budget):
#   (a)  cmap_not_cell: the same at a LOGICAL cell k, which needs sub_lt_of_lt_add (word arithmetic:
#        k < a + b, not k < a, no wrap => k - a < b); the toolkit has the U32<->Nat bridges (B.cmp_nat_u,
#        B.le_nat_u, PST.lt_nat_of_u) but no to_nat of U32.add / U32.sub, so this is new word work
#   (b)  ccompact_rows / ccompact_leafwise: per-leaf compaction; the leaf lemma is the production
#        compact_contents under CRoom, and CRoom itself must come from the leaf capacity (croom_of_cap:
#        0/1 words and n <= 2^d give the cursor k <= i < n < 2^d: the "cursor capacity" proof D1 asks for)
#   wf_map_out: WFArray of Kernel.mask_not's output (PROOF_contents proves it inside MC; not exposed)
# Check: ~/.bend/bin/bend bench/spikes/w0_engine/laws_spike.bend (expects "N TODOs": the imported open laws + 5 open here)
#        ~/.bend/bin/bend bench/spikes/w0_engine/laws_spike.bend --verdict
import Base
import ./../../../src/kernels.bend as K
import ./../../../LAWS.bend as Laws
import ./../../../PROOF_contents.bend as PC

# ---- the type and the models ---------------------------------------------------------------------------------

type CU is Type:
  CL{n: U32, d: Nat, a: Array<U32>}
  CN{rows: U32, lrows: U32, l: CU, r: CU}

def crows(t: CU) -> U32:
  match t:
    case CL{n, d, a}:
      n
    case CN{rows, lrows, l, r}:
      rows

# the logical cell k: the left child below lrows, else the right child at k - lrows (each child consumed
# once: one per arm; a model function, used only in claims)
def ccell(t: CU, +k: U32) -> U32:
  match t:
    case CL{n, d, a}:
      Laws.rd_at(U32, a, k)
    case CN{rows, +lrows, l, r}:
      Bool.pick(U32, U32.is_lt(k, lrows), ccell(l, k), ccell(r, U32.sub(k, lrows)))

# well-formed chunks: leaves fit their slots and are well-formed arrays; nodes carry the true counts and
# the sum does not wrap (lrows <= rows as words)
def WFChunks(t: CU) -> Type:
  match t:
    case CL{n, d, a}:
      {U32.is_le(n, U32.shln(1, d)) == True{} : Bool} & Laws.WFArray(U32, d, a)
    case CN{rows, lrows, l, r}:
      {lrows == crows(l) : U32} & {rows == U32.add(lrows, crows(r)) : U32} & {U32.is_le(lrows, rows) == True{} : Bool} & WFChunks(l) & WFChunks(r)

# the shape half of WFChunks (counts and fits, no WFArray of the leaves)
def ShapeWF(t: CU) -> Type:
  match t:
    case CL{n, d, a}:
      {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
    case CN{rows, lrows, l, r}:
      {lrows == crows(l) : U32} & {rows == U32.add(lrows, crows(r)) : U32} & {U32.is_le(lrows, rows) == True{} : Bool} & ShapeWF(l) & ShapeWF(r)

# ---- the chunked map (Kernel.mask_not at every leaf, one balanced fork per node) --------------------------------

def cmap_not(t: CU) -> CU:
  match t:
    case CL{+n, +d, a}:
      CL{n, d, K.Kernel.mask_not(n, d, a)}
    case CN{rows, lrows, l, r}:
      x y = cmap_not(l) cmap_not(r)
      CN{rows, lrows, x, y}

# ---- (c) counts and shape: one bundled induction (a live child can go to ONE lemma, so the facts a node
#      needs about a child come back together) ----------------------------------------------------------------

law cmap_shape:
  for t: CU
  for wf: WFChunks(t)
  {crows(cmap_not(t)) == crows(t) : U32} & ShapeWF(cmap_not(t))

def cmap_shape_node(+rows: U32, +lrows: U32, -l: CU, -r: CU, e1: {lrows == crows(l) : U32}, e2: {rows == U32.add(lrows, crows(r)) : U32}, e3: {U32.is_le(lrows, rows) == True{} : Bool}, x: {crows(cmap_not(l)) == crows(l) : U32} & ShapeWF(cmap_not(l)), y: {crows(cmap_not(r)) == crows(r) : U32} & ShapeWF(cmap_not(r))) -> {rows == rows : U32} & ({lrows == crows(cmap_not(l)) : U32} & {rows == U32.add(lrows, crows(cmap_not(r))) : U32} & {U32.is_le(lrows, rows) == True{} : Bool} & ShapeWF(cmap_not(l)) & ShapeWF(cmap_not(r))):
  (el, sl) = x
  (er, sr) = y
  ({==}, (Equal.trans(U32, lrows, crows(l), crows(cmap_not(l)), e1, Equal.sym(U32, crows(cmap_not(l)), crows(l), el)), (%Equal.sym(U32, crows(cmap_not(r)), crows(r), er) : {rows == U32.add(lrows, _) : U32}; e2), e3, sl, sr))

def cmap_shape(t, wf):
  match t:
    case CL{+n, +d, a}:
      (fits, wfa) = wf
      ({==}, fits)
    case CN{+rows, +lrows, l, r}:
      (e1, e2, e3, wl, wr) = wf
      cmap_shape_node(rows, lrows, l, r, e1, e2, e3, cmap_shape(l, wl), cmap_shape(r, wr))

# ---- (a') the chunked map is the flat map leaf by leaf (a node congruence; no arithmetic) ----------------------

# the output t2 reads, at every leaf, as the flat mask_not of t1's leaf, with the same shape and counts
def Leafwise(t1: CU, t2: CU) -> Type:
  match t1 t2:
    case CL{n1, d1, a1} CL{n2, d2, a2}:
      {n2 == n1 : U32} & {d2 == d1 : Nat} & (@k: U32 -> {U32.is_lt(k, n1) == True{} : Bool} -> {Laws.rd_at(U32, a2, k) == U32.xor(Laws.rd_at(U32, a1, k), 1) : U32})
    case CN{r1, l1, x1, y1} CN{r2, l2, x2, y2}:
      {r2 == r1 : U32} & {l2 == l1 : U32} & Leafwise(x1, x2) & Leafwise(y1, y2)
    case _ _:
      Empty

law cmap_leafwise:
  for t: CU
  for wf: WFChunks(t)
  Leafwise(t, cmap_not(t))

# the leaf lemma is PROOF_contents.map_cell at the mask_not instance (the production law mask_not_cell's term);
# the template lambda is spelled exactly as kernels.bend spells it (BendTT compares templates by their text)
def cmap_leafwise(t, wf):
  match t:
    case CL{+n, +d, a}:
      (fits, wfa) = wf
      ({==}, {==}, k => hk => PC.map_cell(~U32, ~U32, ~(x => U32.xor(x, 1)), d, n, a, 0, k, fits, hk))
    case CN{+rows, +lrows, l, r}:
      (e1, e2, e3, wl, wr) = wf
      ({==}, {==}, cmap_leafwise(l, wl), cmap_leafwise(r, wr))

# ---- (a) the same at a LOGICAL cell: stated; needs the word-arithmetic lemma below ----------------------------

# the node case needs: k < a + b and not (k < a) give k - a < b (words, no wrap)
law sub_lt_of_lt_add:
  for +k: U32
  for +a: U32
  for +b: U32
  for nowrap: {U32.is_le(a, U32.add(a, b)) == True{} : Bool}
  for hk: {U32.is_lt(k, U32.add(a, b)) == True{} : Bool}
  for hge: {U32.is_lt(k, a) == False{} : Bool}
  {U32.is_lt(U32.sub(k, a), b) == True{} : Bool}

law cmap_not_cell:
  for t: CU
  for +k: U32
  for wf: WFChunks(t)
  for hk: {U32.is_lt(k, crows(t)) == True{} : Bool}
  {ccell(cmap_not(t), k) == U32.xor(ccell(t, k), 1) : U32}

# ---- (b) per-leaf compaction with one mask tree, ragged leaves kept ------------------------------------------
# ccompact(t, m): at a leaf, Kernel.compact_keep(n, d, a, m, 0) into a leaf of the SAME capacity whose n is the
# popcount of the mask the kernel hands back (the cursor k <= i < n <= 2^d: no kept+1 slot); at a node, both
# halves and the new counts, carried out of the recursion as Data, FIRST in the pair (a node cannot read its
# children's counts twice, and a Sigma's last component cannot be reused).

def ccompact.leaf2(+d: Nat, out: Array<U32>, r: Array<U32> & U32) -> U32 & CU:
  (m, +kept) = r
  (kept, CL{kept, d, out})

def ccompact.leaf(+n: U32, +d: Nat, r: Array<U32> & Array<U32>) -> U32 & CU:
  (out, m) = r
  ccompact.leaf2(d, out, K.Kernel.popcount(n, m))

def ccompact.join(x: U32 & CU, y: U32 & CU) -> U32 & CU:
  (+rl, l) = x
  (+rr, r) = y
  +s = U32.add(rl, rr)
  (s, CN{s, rl, l, r})

def ccompact.go(t: CU, m: CU) -> U32 & CU:
  match t m:
    case CL{+n, +d, a} CL{n2, d2, ma}:
      ccompact.leaf(n, d, K.Kernel.compact_keep(~U32, n, d, a, ma, 0))
    case CN{rows, lrows, l, r} CN{r2, l2, ml, mr}:
      x y = ccompact.go(l, ml) ccompact.go(r, mr)
      ccompact.join(x, y)
    case _ _:
      (0, CL{0, 0n, Array.new(U32, 0n, 0)})

def ccompact(t: CU, m: CU) -> CU:
  Pair.snd(U32, CU, ccompact.go(t, m))

# the number of set mask words among the first n (Kernel.popcount's answer)
def cnt(+n: U32, m: Array<U32>) -> U32:
  Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, m))

# the logical "kept index" model: kidx(t, m, k) = the number of set mask words among logical rows < k
# (min arithmetic instead of a pick, so each child is read once: for k < lrows the right term is kidx at 0 = 0)
def kidx(t: CU, m: CU, +k: U32) -> U32:
  match t m:
    case CL{+n, d, a} CL{n2, d2, ma}:
      cnt(U32.min(k, n), ma)
    case CN{rows, +lrows, l, r} CN{r2, l2, ml, mr}:
      U32.add(kidx(l, ml, U32.min(k, lrows)), kidx(r, mr, U32.sub(k, U32.min(k, lrows))))
    case _ _:
      0

# the missing LEAF lemma: a 0/1 mask over a leaf that fits its slots gives the compaction precondition
# (the cursor after i rows is at most i < n <= 2^d); LAWS section 11 states CRoom as a hypothesis only
law croom_of_cap:
  for +n: U32
  for +d: Nat
  for mask: Array<U32>
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  for bits: @i: U32 -> {U32.is_lt(i, n) == True{} : Bool} -> {U32.is_le(Laws.rd_at(U32, mask, i), 1) == True{} : Bool}
  Laws.CRoom(U32.to_nat(n), 0, 0, d, mask)

# the leaf-wise statement of (b): the output's leaf is the production compaction's output (CSpec, the kept
# rows in order at the cursor positions) with the popcount as its row count; nodes: counts and recursion
def CompactLeafwise(t: CU, m: CU, o: CU) -> Type:
  match t m o:
    case CL{n1, d1, a1} CL{n2, d2, ma} CL{n3, d3, a3}:
      {n3 == cnt(n1, ma) : U32} & {d3 == d1 : Nat} & Laws.CSpec(U32, U32.to_nat(n1), 0, 0, d1, a1, ma, a3)
    case CN{r1, l1, x1, y1} CN{r2, l2, x2, y2} CN{r3, l3, x3, y3}:
      {l3 == crows(x3) : U32} & {r3 == U32.add(l3, crows(y3)) : U32} & CompactLeafwise(x1, x2, x3) & CompactLeafwise(y1, y2, y3)
    case _ _ _:
      Empty

law ccompact_leafwise:
  for t: CU
  for m: CU
  for wf: WFChunks(t)
  for wfm: WFChunks(m)
  for bits: @i: U32 -> {U32.is_le(ccell(m, i), 1) == True{} : Bool}
  CompactLeafwise(t, m, ccompact(t, m))

# the LOGICAL statement of (b): the output's row count is the kept count (and, by a concatenation lemma over
# kidx, its logical cells are the kept cells in order); stated only
law ccompact_rows:
  for t: CU
  for m: CU
  for wf: WFChunks(t)
  for wfm: WFChunks(m)
  for same: {crows(m) == crows(t) : U32}
  {crows(ccompact(t, m)) == kidx(t, m, crows(t)) : U32}

# WFArray of the map's output (proven inside PROOF_contents' MC invariant, not exposed as a lemma)
law wf_map_out:
  for +n: U32
  for +d: Nat
  for a: Array<U32>
  for wf: Laws.WFArray(U32, d, a)
  for fits: {U32.is_le(n, U32.shln(1, d)) == True{} : Bool}
  Laws.WFArray(U32, d, K.Kernel.mask_not(n, d, a))
