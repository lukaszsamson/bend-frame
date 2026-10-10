# S1 (W0 engine spike, disposable): chunk layout and grain.
#
# A user-defined chunk tree over owned flat leaves (CU over Array<U32>, CF over Array<F32>):
#   UL{n, d, a} | UN{rows, l, r}      n rows live in 2^d slots; a node's rows = l.rows + r.rows
# Build: a tail-recursive leaf loop (range copy out of the flat column) folding leaves into a
# balanced tree with a binary-counter stack (US.merge: leaf i merges tz(i+1) times), because a
# recursive build cannot open the left child's result and recurse into the right one (R3/R4).
# Flatten: an explicit work stack (UF.go), one copy_into per leaf. Kernels fork at every UN with
# one balanced parallel let and run flat loops at the leaves.
#
# Modes (build/s1 --threads T <mode> <grain log2> <reps>), 2^20 rows:
#   build      chunk 5 U32 + 2 F32 columns at 2^grain, then flatten one back (per rep)
#   q1today    today's q1 pipeline, flat: clone ok, clone qty, broadcast 50, zip gt, zip and,
#              popcount, 7 compactions (every column of the frame: no projection pushdown)
#   q1today3   the same with 3 compactions (projection pushdown assumed)
#   q1fused    fused flat (no chunks): predicate+count in one in-place loop (the mask lands in ok's
#              dead buffer), the 3 selected columns compacted in one loop with one cursor
#   q1chunk    the fused leaf loops forked over the chunk tree (grain matters)
#   q2today    today's q2' (qty.cast(f32) * price * (1 - discount), discount nullable): 4 clones,
#              cast, mul, broadcast 1.0, sub, mul, fix (mask_data): 10 passes
#   q2fused    one 4-input loop (qty, price, discount, its validity) writing value + validity, flat
#   q2chunk    the same per leaf, forked
# The timed window runs `reps` repetitions whose outputs are dropped (the root row count is kept as
# the data dependency); one untimed run after the clock prints a checksum (kept rows and the wrapping
# sum of the id column, or the valid count and the wrapping sum of the f32 bits) that the flat and
# chunked variants must agree on. Build/run:
#   ~/.bend/bin/bend bench/spikes/w0_engine/s1_chunks.bend -o build/s1 && build/s1 --threads 12 q1chunk 14 20
import Base
import ./../../../src/kernels.bend as K

# ---- chunk trees -----------------------------------------------------------------------------------

type CU is Type:
  UL{n: U32, d: Nat, a: Array<U32>}
  UN{rows: U32, l: CU, r: CU}

type CF is Type:
  FL{n: U32, d: Nat, a: Array<F32>}
  FN{rows: U32, l: CF, r: CF}

# a build / flatten stack of subtrees (binary counter: merge equal-level tops)
type US is Type:
  USNil{}
  USCons{rows: U32, c: CU, next: US}

type FS is Type:
  FSNil{}
  FSCons{rows: U32, c: CF, next: FS}

# the q1 output: three compacted columns per leaf, aligned by construction (ragged leaves)
type T3 is Type:
  T3L{n: U32, d: Nat, id: Array<U32>, rg: Array<U32>, pr: Array<F32>}
  T3N{rows: U32, l: T3, r: T3}

# the q2 output: a F32 column with validity
type TR is Type:
  TRL{n: U32, d: Nat, v: Array<U32>, x: Array<F32>}
  TRN{rows: U32, l: TR, r: TR}

# ---- small helpers --------------------------------------------------------------------------------

# trailing zeros of x > 0
def Tz.go(f: Nat, +x: U32, +acc: Nat, odd: Bool) -> Nat:
  match f odd:
    case _ True{}:
      acc
    case 0n False{}:
      acc
    case 1n+p False{}:
      +y = U32.shr(x)
      Tz.go(p, y, 1n+acc, U32.is_ne(U32.and(y, 1), 0))

def Tz(+x: U32) -> Nat:
  Tz.go(32n, x, 0n, U32.is_ne(U32.and(x, 1), 0))

# out[i] = a[off + i] for i < n (a range copy: the chunk builder's leaf); a comes back
def RngU.go(n: Nat, +i: U32, +off: U32, out: Array<U32>, r: Array<U32> & U32) -> Array<U32> & Array<U32>:
  match n:
    case 0n:
      (a, x) = r
      (a, out)
    case 1n+p:
      (a, x) = r
      +j = U32.inc(i)
      RngU.go(p, j, off, Array.set(U32, out, i, x), Array.get(U32, a, U32.add(off, j)))

def RngU(+n: U32, +d: Nat, +off: U32, a: Array<U32>) -> Array<U32> & Array<U32>:
  RngU.go(U32.to_nat(n), 0, off, Array.new(U32, d, 0), Array.get(U32, a, off))

def RngF.go(n: Nat, +i: U32, +off: U32, out: Array<F32>, r: Array<F32> & F32) -> Array<F32> & Array<F32>:
  match n:
    case 0n:
      (a, x) = r
      (a, out)
    case 1n+p:
      (a, x) = r
      +j = U32.inc(i)
      RngF.go(p, j, off, Array.set(F32, out, i, x), Array.get(F32, a, U32.add(off, j)))

def RngF(+n: U32, +d: Nat, +off: U32, a: Array<F32>) -> Array<F32> & Array<F32>:
  RngF.go(U32.to_nat(n), 0, off, Array.new(F32, d, 0.0), Array.get(F32, a, off))

# the wrapping sum of the first n words (consumes the array)
def Sum.go(n: Nat, +i: U32, +acc: U32, r: Array<U32> & U32) -> U32:
  match n:
    case 0n:
      (a, x) = r
      acc
    case 1n+p:
      (a, x) = r
      +j = U32.inc(i)
      Sum.go(p, j, U32.add(acc, x), Array.get(U32, a, j))

def Sum(+n: U32, a: Array<U32>) -> U32:
  Sum.go(U32.to_nat(n), 0, 0, Array.get(U32, a, 0))

# the wrapping sum of the bit patterns of the first n floats (bit-exact check)
def SumB.go(n: Nat, +i: U32, +acc: U32, r: Array<F32> & F32) -> U32:
  match n:
    case 0n:
      (a, x) = r
      acc
    case 1n+p:
      (a, x) = r
      +j = U32.inc(i)
      SumB.go(p, j, U32.add(acc, F32.bits(x)), Array.get(F32, a, j))

def SumB(+n: U32, a: Array<F32>) -> U32:
  SumB.go(U32.to_nat(n), 0, 0, Array.get(F32, a, 0))

# ---- build: flat column -> 2^k leaves of 2^g rows ---------------------------------------------------

def US.merge(m: Nat, +rows: U32, c: CU, s: US) -> US:
  match m s:
    case 0n USNil{}:
      USCons{rows, c, USNil{}}
    case 0n USCons{r2, c2, nx}:
      USCons{rows, c, USCons{r2, c2, nx}}
    case 1n+p USNil{}:
      USCons{rows, c, USNil{}}
    case 1n+p USCons{+r2, c2, nx}:
      +t = U32.add(r2, rows)
      US.merge(p, t, UN{t, c2, c}, nx)

def UB.step(+i: U32, +g: Nat, s: US, out: Array<U32>) -> US:
  US.merge(Tz(U32.inc(i)), U32.shln(1, g), UL{U32.shln(1, g), g, out}, s)

def UB.go(f: Nat, +i: U32, +g: Nat, s: US, r: Array<U32> & Array<U32>) -> Array<U32> & US:
  match f:
    case 0n:
      (a, out) = r
      (a, UB.step(i, g, s, out))
    case 1n+p:
      (a, out) = r
      +j = U32.inc(i)
      UB.go(p, j, g, UB.step(i, g, s, out), RngU(U32.shln(1, g), g, U32.shln(j, g), a))

def UB.fin2(a: Array<U32>, s: US) -> Array<U32> & CU:
  match s:
    case USCons{rows, c, nx}:
      (a, c)
    case USNil{}:
      (a, UL{0, 0n, Array.new(U32, 0n, 0)})

def UB.fin(r: Array<U32> & US) -> Array<U32> & CU:
  (a, s) = r
  UB.fin2(a, s)

# chunk the first 2^(g+k) rows of a (the flat column comes back)
def UB(+k: Nat, +g: Nat, a: Array<U32>) -> Array<U32> & CU:
  UB.fin(UB.go(Nat.sub(U32.to_nat(U32.shln(1, k)), 1n), 0, g, USNil{}, RngU(U32.shln(1, g), g, 0, a)))

def FS.merge(m: Nat, +rows: U32, c: CF, s: FS) -> FS:
  match m s:
    case 0n FSNil{}:
      FSCons{rows, c, FSNil{}}
    case 0n FSCons{r2, c2, nx}:
      FSCons{rows, c, FSCons{r2, c2, nx}}
    case 1n+p FSNil{}:
      FSCons{rows, c, FSNil{}}
    case 1n+p FSCons{+r2, c2, nx}:
      +t = U32.add(r2, rows)
      FS.merge(p, t, FN{t, c2, c}, nx)

def FB.step(+i: U32, +g: Nat, s: FS, out: Array<F32>) -> FS:
  FS.merge(Tz(U32.inc(i)), U32.shln(1, g), FL{U32.shln(1, g), g, out}, s)

def FB.go(f: Nat, +i: U32, +g: Nat, s: FS, r: Array<F32> & Array<F32>) -> Array<F32> & FS:
  match f:
    case 0n:
      (a, out) = r
      (a, FB.step(i, g, s, out))
    case 1n+p:
      (a, out) = r
      +j = U32.inc(i)
      FB.go(p, j, g, FB.step(i, g, s, out), RngF(U32.shln(1, g), g, U32.shln(j, g), a))

def FB.fin2(a: Array<F32>, s: FS) -> Array<F32> & CF:
  match s:
    case FSCons{rows, c, nx}:
      (a, c)
    case FSNil{}:
      (a, FL{0, 0n, Array.new(F32, 0n, 0.0)})

def FB.fin(r: Array<F32> & FS) -> Array<F32> & CF:
  (a, s) = r
  FB.fin2(a, s)

def FB(+k: Nat, +g: Nat, a: Array<F32>) -> Array<F32> & CF:
  FB.fin(FB.go(Nat.sub(U32.to_nat(U32.shln(1, k)), 1n), 0, g, FSNil{}, RngF(U32.shln(1, g), g, 0, a)))

# ---- flatten: the leaves in order into one array (the sort / join boundary) -------------------------------

def UF.go(f: Nat, +off: U32, out: Array<U32>, s: US) -> Array<U32>:
  match f s:
    case 0n USNil{}:
      out
    case 0n USCons{r, c, nx}:
      out
    case 1n+p USNil{}:
      out
    case 1n+p USCons{rows, UL{+n, d, a}, nx}:
      UF.go(p, U32.add(off, n), K.Kernel.copy_into(~U32, n, off, out, a), nx)
    case 1n+p USCons{rows, UN{r2, l, r}, nx}:
      UF.go(p, off, out, USCons{0, l, USCons{0, r, nx}})

def CU.rows(c: CU) -> CU & U32:
  match c:
    case UL{+n, d, a}:
      (UL{n, d, a}, n)
    case UN{+rows, l, r}:
      (UN{rows, l, r}, rows)

# fuel: a bound on nodes + leaves (leaves hold >= 1024 rows here)
def UF.k(+d: Nat, r: CU & U32) -> Array<U32>:
  (c, +rows) = r
  UF.go(U32.to_nat(U32.add(U32.shl(U32.add(U32.shrn(rows, 10n), 1)), 2)), 0, Array.new(U32, d, 0), USCons{rows, c, USNil{}})

# flatten into 2^d slots
def UF(+d: Nat, c: CU) -> Array<U32>:
  UF.k(d, CU.rows(c))

# ---- data: 2^20 rows ------------------------------------------------------------------------------------

def Gen.ok(+i: U32) -> U32:
  Bool.to_u32(U32.is_gt(U32.mod(U32.mul(i, 7919), 13), 4))

def Gen.qty(+i: U32) -> U32:
  U32.mod(U32.mul(i, 2654435761), 100)

def Gen.rg(+i: U32) -> U32:
  U32.and(i, 7)

def Gen.price(+i: U32) -> F32:
  F32.div(U32.to_f32(U32.mod(U32.mul(i, 31), 1000)), 10.0)

# discount: null (slot 0.0) every 10th row
def Gen.disc(+i: U32) -> F32:
  Bool.pick(F32, U32.is_zero(U32.mod(i, 10)), 0.0, F32.div(U32.to_f32(U32.mod(U32.mul(i, 17), 100)), 100.0))

def Gen.vdisc(+i: U32) -> U32:
  Bool.to_u32(U32.is_ne(U32.mod(i, 10), 0))

def GenU.go(~f: U32 -> U32, n: Nat, +i: U32, out: Array<U32>) -> Array<U32>:
  match n:
    case 0n:
      out
    case 1n+p:
      GenU.go(~f, p, U32.inc(i), Array.set(U32, out, i, f(i)))

def GenU(~f: U32 -> U32, +d: Nat) -> Array<U32>:
  GenU.go(~f, U32.to_nat(U32.shln(1, d)), 0, Array.new(U32, d, 0))

def GenF.go(~f: U32 -> F32, n: Nat, +i: U32, out: Array<F32>) -> Array<F32>:
  match n:
    case 0n:
      out
    case 1n+p:
      GenF.go(~f, p, U32.inc(i), Array.set(F32, out, i, f(i)))

def GenF(~f: U32 -> F32, +d: Nat) -> Array<F32>:
  GenF.go(~f, U32.to_nat(U32.shln(1, d)), 0, Array.new(F32, d, 0.0))

# the flat frame: ok, qty, id, region, vdisc (U32 words) and price, disc (F32)
type Flat is Type:
  Flat{ok: Array<U32>, qty: Array<U32>, id: Array<U32>, rg: Array<U32>, vd: Array<U32>, pr: Array<F32>, ds: Array<F32>}

def Flat.gen(+d: Nat) -> Flat:
  Flat{GenU(~(i => Gen.ok(i)), d), GenU(~(i => Gen.qty(i)), d), K.Kernel.iota(U32.shln(1, d), d), GenU(~(i => Gen.rg(i)), d), GenU(~(i => Gen.vdisc(i)), d), GenF(~(i => Gen.price(i)), d), GenF(~(i => Gen.disc(i)), d)}

# the chunked frame: every column a tree of the SAME shape (the frame's partition)
type Chunked is Type:
  Chunked{ok: CU, qty: CU, id: CU, rg: CU, vd: CU, pr: CF, ds: CF}

def Flat.chunk.k7(r1: Array<U32> & CU, r2: Array<U32> & CU, r3: Array<U32> & CU, r4: Array<U32> & CU, r5: Array<U32> & CU, r6: Array<F32> & CF, r7: Array<F32> & CF) -> Flat & Chunked:
  (a1, c1) = r1
  (a2, c2) = r2
  (a3, c3) = r3
  (a4, c4) = r4
  (a5, c5) = r5
  (a6, c6) = r6
  (a7, c7) = r7
  (Flat{a1, a2, a3, a4, a5, a6, a7}, Chunked{c1, c2, c3, c4, c5, c6, c7})

# chunk every column (sequential: each flat column has one owner); the flat frame comes back
def Flat.chunk(+k: Nat, +g: Nat, f: Flat) -> Flat & Chunked:
  match f:
    case Flat{ok, qty, id, rg, vd, pr, ds}:
      Flat.chunk.k7(UB(k, g, ok), UB(k, g, qty), UB(k, g, id), UB(k, g, rg), UB(k, g, vd), FB(k, g, pr), FB(k, g, ds))

# ---- q1 leaf kernels -----------------------------------------------------------------------------------

# fused predicate ok & (qty > 50), written IN PLACE into ok's buffer (a dead operand), with the kept
# count in the same loop; qty comes back (the frame still holds it)
type P1 is Type:
  P1{m: Array<U32>, q: Array<U32>, k: U32}

def P1.go(n: Nat, +i: U32, +k: U32, ro: Array<U32> & U32, rq: Array<U32> & U32) -> P1:
  match n:
    case 0n:
      (o, x) = ro
      (q, y) = rq
      P1{o, q, k}
    case 1n+p:
      (o, x) = ro
      (q, y) = rq
      +j = U32.inc(i)
      +b = U32.and(x, Bool.to_u32(U32.is_gt(y, 50)))
      P1.go(p, j, U32.add(k, b), Array.get(U32, Array.set(U32, o, i, b), j), Array.get(U32, q, j))

def P1.run(+n: U32, ok: Array<U32>, qty: Array<U32>) -> P1:
  P1.go(U32.to_nat(n), 0, 0, Array.get(U32, ok, 0), Array.get(U32, qty, 0))

# three aligned columns compacted by one mask in ONE loop with one cursor (legacy branchless write:
# every dropped row lands at slot k; k <= i < n <= 2^d, so the cursor fits the leaf's own capacity
# and no kept+1 scratch slot is needed). The inputs come back.
type C3 is Type:
  C3{o1: Array<U32>, o2: Array<U32>, o3: Array<F32>, m: Array<U32>, a1: Array<U32>, a2: Array<U32>, a3: Array<F32>, k: U32}

def C3.go(n: Nat, +i: U32, +k: U32, o1: Array<U32>, o2: Array<U32>, o3: Array<F32>, rm: Array<U32> & U32, r1: Array<U32> & U32, r2: Array<U32> & U32, r3: Array<F32> & F32) -> C3:
  match n:
    case 0n:
      (m, b) = rm
      (a1, x1) = r1
      (a2, x2) = r2
      (a3, x3) = r3
      C3{o1, o2, o3, m, a1, a2, a3, k}
    case 1n+p:
      (m, b) = rm
      (a1, x1) = r1
      (a2, x2) = r2
      (a3, x3) = r3
      +j = U32.inc(i)
      C3.go(p, j, U32.add(k, b), Array.set(U32, o1, k, x1), Array.set(U32, o2, k, x2), Array.set(F32, o3, k, x3), Array.get(U32, m, j), Array.get(U32, a1, j), Array.get(U32, a2, j), Array.get(F32, a3, j))

def C3.run(+n: U32, +d: Nat, m: Array<U32>, a1: Array<U32>, a2: Array<U32>, a3: Array<F32>) -> C3:
  C3.go(U32.to_nat(n), 0, 0, Array.new(U32, d, 0), Array.new(U32, d, 0), Array.new(F32, d, 0.0), Array.get(U32, m, 0), Array.get(U32, a1, 0), Array.get(U32, a2, 0), Array.get(F32, a3, 0))

# one leaf of q1: the fused predicate, then the fused compaction; the inputs come back
type Q1L is Type:
  Q1L{out: T3, ok: Array<U32>, qty: Array<U32>, id: Array<U32>, rg: Array<U32>, pr: Array<F32>}

def Q1.leaf.c(+d: Nat, qty: Array<U32>, r: C3) -> Q1L:
  match r:
    case C3{o1, o2, o3, m, a1, a2, a3, +k}:
      Q1L{T3L{k, d, o1, o2, o3}, m, qty, a1, a2, a3}

def Q1.leaf.p(+n: U32, +d: Nat, id: Array<U32>, rg: Array<U32>, pr: Array<F32>, r: P1) -> Q1L:
  match r:
    case P1{m, q, k}:
      Q1.leaf.c(d, q, C3.run(n, d, m, id, rg, pr))

def Q1.leaf(+n: U32, +d: Nat, ok: Array<U32>, qty: Array<U32>, id: Array<U32>, rg: Array<U32>, pr: Array<F32>) -> Q1L:
  Q1.leaf.p(n, d, id, rg, pr, P1.run(n, ok, qty))

# ---- q1 over the tree: one balanced fork per node, the leaf kernels at the leaves -------------------------

type Q1T is Type:
  Q1T{out: T3, ok: CU, qty: CU, id: CU, rg: CU, pr: CF}

def Q1.node(+rows: U32, l: Q1T, r: Q1T) -> Q1T:
  match l r:
    case Q1T{o1, a1, b1, c1, d1, e1} Q1T{o2, a2, b2, c2, d2, e2}:
      Q1T{T3N{rows, o1, o2}, UN{rows, a1, a2}, UN{rows, b1, b2}, UN{rows, c1, c2}, UN{rows, d1, d2}, FN{rows, e1, e2}}

def Q1.leaf.t(+n: U32, +d: Nat, r: Q1L) -> Q1T:
  match r:
    case Q1L{out, ok, qty, id, rg, pr}:
      Q1T{out, UL{n, d, ok}, UL{n, d, qty}, UL{n, d, id}, UL{n, d, rg}, FL{n, d, pr}}

def Q1.tree(ok: CU, qty: CU, id: CU, rg: CU, pr: CF) -> Q1T:
  match ok qty id rg pr:
    case UL{+n, +d, a} UL{n2, d2, b} UL{n3, d3, c} UL{n4, d4, e} FL{n5, d5, f}:
      Q1.leaf.t(n, d, Q1.leaf(n, d, a, b, c, e, f))
    case UN{+rows, l1, r1} UN{w2, l2, r2} UN{w3, l3, r3} UN{w4, l4, r4} FN{w5, l5, r5}:
      x y = Q1.tree(l1, l2, l3, l4, l5) Q1.tree(r1, r2, r3, r4, r5)
      Q1.node(rows, x, y)
    case _ _ _ _ _:
      Q1T{T3L{0, 0n, Array.new(U32, 0n, 0), Array.new(U32, 0n, 0), Array.new(F32, 0n, 0.0)}, UL{0, 0n, Array.new(U32, 0n, 0)}, UL{0, 0n, Array.new(U32, 0n, 0)}, UL{0, 0n, Array.new(U32, 0n, 0)}, UL{0, 0n, Array.new(U32, 0n, 0)}, FL{0, 0n, Array.new(F32, 0n, 0.0)}}

# the output's root row count (forces the whole fork tree; drops the buffers)
def T3.rows(t: T3) -> U32:
  match t:
    case T3L{n, d, id, rg, pr}:
      n
    case T3N{rows, l, r}:
      rows

# the checksum, forked like a kernel (U32 modular sums combine at the nodes): (kept rows, sum of id)
def T3.check.k(+n: U32, +s: U32) -> U32 & U32:
  (n, s)

def T3.check.j(l: U32 & U32, r: U32 & U32) -> U32 & U32:
  (k1, s1) = l
  (k2, s2) = r
  (U32.add(k1, k2), U32.add(s1, s2))

def T3.check(t: T3) -> U32 & U32:
  match t:
    case T3L{+n, d, id, rg, pr}:
      T3.check.k(n, Sum(n, id))
    case T3N{rows, l, r}:
      x y = T3.check(l) T3.check(r)
      T3.check.j(x, y)

# reps of q1 over the chunked frame: the frame comes back each time, the output is dropped
type CSt is Type:
  CSt{c: Chunked, acc: U32}

def Q1C.s1(+acc: U32, vd: CU, ds: CF, r: Q1T) -> CSt:
  match r:
    case Q1T{out, ok, qty, id, rg, pr}:
      CSt{Chunked{ok, qty, id, rg, vd, pr, ds}, U32.add(acc, T3.rows(out))}

def Q1C.rep(f: Nat, st: CSt) -> CSt:
  match f st:
    case 0n CSt{c, acc}:
      CSt{c, acc}
    case 1n+p CSt{Chunked{ok, qty, id, rg, vd, pr, ds}, acc}:
      Q1C.rep(p, Q1C.s1(acc, vd, ds, Q1.tree(ok, qty, id, rg, pr)))

# the untimed verification run
def Q1C.verify.k(r: Q1T) -> U32 & U32:
  match r:
    case Q1T{out, ok, qty, id, rg, pr}:
      T3.check(out)

def Q1C.verify(c: Chunked) -> U32 & U32:
  match c:
    case Chunked{ok, qty, id, rg, vd, pr, ds}:
      Q1C.verify.k(Q1.tree(ok, qty, id, rg, pr))

# ---- q1 flat variants ------------------------------------------------------------------------------------

type FSt is Type:
  FSt{f: Flat, acc: U32}

# compact_keep that also hands its input back (same loop as Kernel.compact_keep, so "today's" 7 column
# compactions can repeat without consuming the frame)
type CK is Type:
  CKU{a: Array<U32>, o: Array<U32>, m: Array<U32>}

def CKU.go(n: Nat, +i: U32, +k: U32, o: Array<U32>, ra: Array<U32> & U32, rm: Array<U32> & U32) -> CK:
  match n:
    case 0n:
      (a, x) = ra
      (m, b) = rm
      CKU{a, o, m}
    case 1n+p:
      (a, x) = ra
      (m, b) = rm
      +j = U32.inc(i)
      CKU.go(p, j, U32.add(k, b), Array.set(U32, o, k, x), Array.get(U32, a, j), Array.get(U32, m, j))

def CKU.run(+n: U32, +d: Nat, a: Array<U32>, m: Array<U32>) -> CK:
  CKU.go(U32.to_nat(n), 0, 0, Array.new(U32, d, 0), Array.get(U32, a, 0), Array.get(U32, m, 0))

# `cols` compactions of the same column with the same mask (every column is a 32-bit buffer of n rows:
# the cost of compacting 7 different columns); the last output survives
def Q1F.cmp.go(cols: Nat, +n: U32, +d: Nat, r: CK) -> CK:
  match cols r:
    case 0n CKU{a, o, m}:
      CKU{a, o, m}
    case 1n+p CKU{a, o, m}:
      Q1F.cmp.go(p, n, d, CKU.run(n, d, a, m))

# today's predicate: (cloned) ok AND (cloned) qty > broadcast(50), then popcount: (mask, kept)
def Q1F.pred(+n: U32, +d: Nat, ok: Array<U32>, qty: Array<U32>) -> Array<U32> & U32:
  K.Kernel.popcount(n, K.Kernel.mask_and(n, d, ok, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, qty, Array.new(U32, d, 50), 0)))

def Q1F.t4(+acc: U32, +kept: U32, ok1: Array<U32>, q1: Array<U32>, rg: Array<U32>, vd: Array<U32>, pr: Array<F32>, ds: Array<F32>, r: CK) -> FSt:
  match r:
    case CKU{a, o, m}:
      FSt{Flat{ok1, q1, a, rg, vd, pr, ds}, U32.add(acc, kept)}

def Q1F.t3(+n: U32, +cols: Nat, +acc: U32, ok1: Array<U32>, q1: Array<U32>, id: Array<U32>, rg: Array<U32>, vd: Array<U32>, pr: Array<F32>, ds: Array<F32>, r: Array<U32> & U32) -> FSt:
  (m, +kept) = r
  Q1F.t4(acc, kept, ok1, q1, rg, vd, pr, ds, Q1F.cmp.go(cols, n, K.Kernel.depth_for(U32.add(kept, 1)), CKU{id, Array.new(U32, 0n, 0), m}))

def Q1F.t2(+n: U32, +d: Nat, +cols: Nat, +acc: U32, ok1: Array<U32>, ok2: Array<U32>, id: Array<U32>, rg: Array<U32>, vd: Array<U32>, pr: Array<F32>, ds: Array<F32>, rq: Array<U32> & Array<U32>) -> FSt:
  (q1, q2) = rq
  Q1F.t3(n, cols, acc, ok1, q1, id, rg, vd, pr, ds, Q1F.pred(n, d, ok2, q2))

def Q1F.t1(+n: U32, +d: Nat, +cols: Nat, +acc: U32, qty: Array<U32>, id: Array<U32>, rg: Array<U32>, vd: Array<U32>, pr: Array<F32>, ds: Array<F32>, rok: Array<U32> & Array<U32>) -> FSt:
  (ok1, ok2) = rok
  Q1F.t2(n, d, cols, acc, ok1, ok2, id, rg, vd, pr, ds, Array.clone(U32, qty))

def Q1F.today.rep(reps: Nat, +n: U32, +d: Nat, +cols: Nat, st: FSt) -> FSt:
  match reps st:
    case 0n FSt{f, acc}:
      FSt{f, acc}
    case 1n+p FSt{Flat{ok, qty, id, rg, vd, pr, ds}, acc}:
      Q1F.today.rep(p, n, d, cols, Q1F.t1(n, d, cols, acc, qty, id, rg, vd, pr, ds, Array.clone(U32, ok)))

# verification of today's: (kept, sum of the compacted id)
def Q1F.today.v2(+kept: U32, r: CK) -> U32 & U32:
  match r:
    case CKU{a, o, m}:
      T3.check.k(kept, Sum(kept, o))

def Q1F.today.v1(+n: U32, id: Array<U32>, r: Array<U32> & U32) -> U32 & U32:
  (m, +kept) = r
  Q1F.today.v2(kept, CKU.run(n, K.Kernel.depth_for(U32.add(kept, 1)), id, m))

def Q1F.today.verify(+n: U32, +d: Nat, f: Flat) -> U32 & U32:
  match f:
    case Flat{ok, qty, id, rg, vd, pr, ds}:
      Q1F.today.v1(n, id, Q1F.pred(n, d, ok, qty))

# fused flat: the leaf kernels over the whole column (no chunks, no fork)
def Q1F.f1(+acc: U32, vd: Array<U32>, ds: Array<F32>, r: Q1L) -> FSt:
  match r:
    case Q1L{out, m, qty, id, rg, pr}:
      FSt{Flat{m, qty, id, rg, vd, pr, ds}, U32.add(acc, T3.rows(out))}

def Q1F.fused.rep(reps: Nat, +n: U32, +d: Nat, st: FSt) -> FSt:
  match reps st:
    case 0n FSt{f, acc}:
      FSt{f, acc}
    case 1n+p FSt{Flat{ok, qty, id, rg, vd, pr, ds}, acc}:
      Q1F.fused.rep(p, n, d, Q1F.f1(acc, vd, ds, Q1.leaf(n, d, ok, qty, id, rg, pr)))

def Q1F.fused.v(r: Q1L) -> U32 & U32:
  match r:
    case Q1L{out, m, qty, id, rg, pr}:
      T3.check(out)

def Q1F.fused.verify(+n: U32, +d: Nat, f: Flat) -> U32 & U32:
  match f:
    case Flat{ok, qty, id, rg, vd, pr, ds}:
      Q1F.fused.v(Q1.leaf(n, d, ok, qty, id, rg, pr))

# ---- q2' ------------------------------------------------------------------------------------------------
# rev = f32(qty) * price * (1 - disc) with disc nullable: the output's validity is disc's and null slots are
# reset to 0.0 in the same pass (the fused "validity/reset"). With fill_null(disc, 0.0) the loop would drop
# the two validity arrays (the null slot holds the default already) and answer AllValid.

type R4 is Type:
  R4{v: Array<U32>, x: Array<F32>, q: Array<U32>, p: Array<F32>, vd: Array<U32>, ds: Array<F32>}

def R4.go(n: Nat, +i: U32, ov: Array<U32>, ox: Array<F32>, rq: Array<U32> & U32, rp: Array<F32> & F32, rv: Array<U32> & U32, rd: Array<F32> & F32) -> R4:
  match n:
    case 0n:
      (q, a) = rq
      (pa, b) = rp
      (v, c) = rv
      (d, e) = rd
      R4{ov, ox, q, pa, v, d}
    case 1n+p:
      (q, a) = rq
      (pa, b) = rp
      (v, +c) = rv
      (d, e) = rd
      +j = U32.inc(i)
      R4.go(p, j, Array.set(U32, ov, i, c), Array.set(F32, ox, i, Bool.pick(F32, U32.is_ne(c, 0), F32.mul(F32.mul(U32.to_f32(a), b), F32.sub(1.0, e)), 0.0)), Array.get(U32, q, j), Array.get(F32, pa, j), Array.get(U32, v, j), Array.get(F32, d, j))

def R4.run(+n: U32, +d: Nat, q: Array<U32>, p: Array<F32>, v: Array<U32>, ds: Array<F32>) -> R4:
  R4.go(U32.to_nat(n), 0, Array.new(U32, d, 0), Array.new(F32, d, 0.0), Array.get(U32, q, 0), Array.get(F32, p, 0), Array.get(U32, v, 0), Array.get(F32, ds, 0))

type Q2T is Type:
  Q2T{out: TR, qty: CU, vd: CU, pr: CF, ds: CF}

def Q2.leaf.t(+n: U32, +d: Nat, r: R4) -> Q2T:
  match r:
    case R4{v, x, q, p, vd, ds}:
      Q2T{TRL{n, d, v, x}, UL{n, d, q}, UL{n, d, vd}, FL{n, d, p}, FL{n, d, ds}}

def Q2.node(+rows: U32, l: Q2T, r: Q2T) -> Q2T:
  match l r:
    case Q2T{o1, a1, b1, c1, d1} Q2T{o2, a2, b2, c2, d2}:
      Q2T{TRN{rows, o1, o2}, UN{rows, a1, a2}, UN{rows, b1, b2}, FN{rows, c1, c2}, FN{rows, d1, d2}}

def Q2.tree(qty: CU, vd: CU, pr: CF, ds: CF) -> Q2T:
  match qty vd pr ds:
    case UL{+n, +d, a} UL{n2, d2, b} FL{n3, d3, c} FL{n4, d4, e}:
      Q2.leaf.t(n, d, R4.run(n, d, a, c, b, e))
    case UN{+rows, l1, r1} UN{w2, l2, r2} FN{w3, l3, r3} FN{w4, l4, r4}:
      x y = Q2.tree(l1, l2, l3, l4) Q2.tree(r1, r2, r3, r4)
      Q2.node(rows, x, y)
    case _ _ _ _:
      Q2T{TRL{0, 0n, Array.new(U32, 0n, 0), Array.new(F32, 0n, 0.0)}, UL{0, 0n, Array.new(U32, 0n, 0)}, UL{0, 0n, Array.new(U32, 0n, 0)}, FL{0, 0n, Array.new(F32, 0n, 0.0)}, FL{0, 0n, Array.new(F32, 0n, 0.0)}}

def TR.rows(t: TR) -> U32:
  match t:
    case TRL{n, d, v, x}:
      n
    case TRN{rows, l, r}:
      rows

# (valid count, wrapping sum of the f32 bits), forked
def TR.check(t: TR) -> U32 & U32:
  match t:
    case TRL{+n, d, v, x}:
      T3.check.k(Sum(n, v), SumB(n, x))
    case TRN{rows, l, r}:
      a b = TR.check(l) TR.check(r)
      T3.check.j(a, b)

def Q2C.s1(+acc: U32, ok: CU, id: CU, rg: CU, r: Q2T) -> CSt:
  match r:
    case Q2T{out, qty, vd, pr, ds}:
      CSt{Chunked{ok, qty, id, rg, vd, pr, ds}, U32.add(acc, TR.rows(out))}

def Q2C.rep(f: Nat, st: CSt) -> CSt:
  match f st:
    case 0n CSt{c, acc}:
      CSt{c, acc}
    case 1n+p CSt{Chunked{ok, qty, id, rg, vd, pr, ds}, acc}:
      Q2C.rep(p, Q2C.s1(acc, ok, id, rg, Q2.tree(qty, vd, pr, ds)))

def Q2C.verify.k(r: Q2T) -> U32 & U32:
  match r:
    case Q2T{out, qty, vd, pr, ds}:
      TR.check(out)

def Q2C.verify(c: Chunked) -> U32 & U32:
  match c:
    case Chunked{ok, qty, id, rg, vd, pr, ds}:
      Q2C.verify.k(Q2.tree(qty, vd, pr, ds))

# flat fused
def Q2F.f1(+n: U32, +d: Nat, +acc: U32, ok: Array<U32>, id: Array<U32>, rg: Array<U32>, r: R4) -> FSt:
  match r:
    case R4{v, x, q, p, vd, ds}:
      FSt{Flat{ok, q, id, rg, vd, p, ds}, U32.add(acc, TR.rows(TRL{n, d, v, x}))}

def Q2F.fused.rep(reps: Nat, +n: U32, +d: Nat, st: FSt) -> FSt:
  match reps st:
    case 0n FSt{f, acc}:
      FSt{f, acc}
    case 1n+p FSt{Flat{ok, qty, id, rg, vd, pr, ds}, acc}:
      Q2F.fused.rep(p, n, d, Q2F.f1(n, d, acc, ok, id, rg, R4.run(n, d, qty, pr, vd, ds)))

def Q2F.fused.v(+n: U32, +d: Nat, r: R4) -> U32 & U32:
  match r:
    case R4{v, x, q, p, vd, ds}:
      TR.check(TRL{n, d, v, x})

def Q2F.fused.verify(+n: U32, +d: Nat, f: Flat) -> U32 & U32:
  match f:
    case Flat{ok, qty, id, rg, vd, pr, ds}:
      Q2F.fused.v(n, d, R4.run(n, d, qty, pr, vd, ds))

# today's q2' (eval.bend): ICol clones of qty, price and disc (data + validity: 4 array clones), cast map,
# zip mul, broadcast 1.0, zip sub, zip mul, then Eval.fix = mask_data over the validity: 10 passes
def Q2F.today.expr(+n: U32, +d: Nat, q: Array<U32>, p: Array<F32>, vd: Array<U32>, ds: Array<F32>) -> Array<F32> & Array<U32>:
  K.Kernel.mask_data(~F32, n, K.Kernel.zip(~F32, ~F32, ~F32, ~(a => b => F32.mul(a, b)), n, d, K.Kernel.zip(~F32, ~F32, ~F32, ~(a => b => F32.mul(a, b)), n, d, K.Kernel.map(~U32, ~F32, ~(a => U32.to_f32(a)), n, d, q, 0.0), p, 0.0), K.Kernel.zip(~F32, ~F32, ~F32, ~(a => b => F32.sub(a, b)), n, d, Array.new(F32, d, 1.0), ds, 0.0), 0.0), vd, 0.0)

def Q2F.t5(+n: U32, +d: Nat, +acc: U32, f: Flat, r: Array<F32> & Array<U32>) -> FSt:
  (x, m) = r
  FSt{f, U32.add(acc, TR.rows(TRL{n, d, m, x}))}

def Q2F.t4(+n: U32, +d: Nat, +acc: U32, ok: Array<U32>, q1: Array<U32>, id: Array<U32>, rg: Array<U32>, p1: Array<F32>, d1: Array<F32>, q2: Array<U32>, p2: Array<F32>, d2: Array<F32>, rv: Array<U32> & Array<U32>) -> FSt:
  (v1, v2) = rv
  Q2F.t5(n, d, acc, Flat{ok, q1, id, rg, v1, p1, d1}, Q2F.today.expr(n, d, q2, p2, v2, d2))

def Q2F.t3(+n: U32, +d: Nat, +acc: U32, ok: Array<U32>, q1: Array<U32>, id: Array<U32>, rg: Array<U32>, vd: Array<U32>, p1: Array<F32>, q2: Array<U32>, p2: Array<F32>, rd: Array<F32> & Array<F32>) -> FSt:
  (d1, d2) = rd
  Q2F.t4(n, d, acc, ok, q1, id, rg, p1, d1, q2, p2, d2, Array.clone(U32, vd))

def Q2F.t2(+n: U32, +d: Nat, +acc: U32, ok: Array<U32>, q1: Array<U32>, id: Array<U32>, rg: Array<U32>, vd: Array<U32>, ds: Array<F32>, q2: Array<U32>, rp: Array<F32> & Array<F32>) -> FSt:
  (p1, p2) = rp
  Q2F.t3(n, d, acc, ok, q1, id, rg, vd, p1, q2, p2, Array.clone(F32, ds))

def Q2F.t1(+n: U32, +d: Nat, +acc: U32, ok: Array<U32>, id: Array<U32>, rg: Array<U32>, vd: Array<U32>, pr: Array<F32>, ds: Array<F32>, rq: Array<U32> & Array<U32>) -> FSt:
  (q1, q2) = rq
  Q2F.t2(n, d, acc, ok, q1, id, rg, vd, ds, q2, Array.clone(F32, pr))

def Q2F.today.rep(reps: Nat, +n: U32, +d: Nat, st: FSt) -> FSt:
  match reps st:
    case 0n FSt{f, acc}:
      FSt{f, acc}
    case 1n+p FSt{Flat{ok, qty, id, rg, vd, pr, ds}, acc}:
      Q2F.today.rep(p, n, d, Q2F.t1(n, d, acc, ok, id, rg, vd, pr, ds, Array.clone(U32, qty)))

def Q2F.today.v(+n: U32, +d: Nat, r: Array<F32> & Array<U32>) -> U32 & U32:
  (x, m) = r
  TR.check(TRL{n, d, m, x})

def Q2F.today.verify(+n: U32, +d: Nat, f: Flat) -> U32 & U32:
  match f:
    case Flat{ok, qty, id, rg, vd, pr, ds}:
      Q2F.today.v(n, d, Q2F.today.expr(n, d, qty, pr, vd, ds))

# ---- build / flatten timing -------------------------------------------------------------------------------

type BSt is Type:
  BSt{f: Flat, acc: U32}

# chunk the 7 columns, flatten one back (reads one cell of the flat result); the other trees are dropped
def Build.step2(+k: Nat, +g: Nat, +acc: U32, f: Flat, c: Chunked) -> BSt:
  match c:
    case Chunked{ok, qty, id, rg, vd, pr, ds}:
      BSt{f, U32.add(acc, Sum.go(1n, 0, 0, Array.get(U32, UF(Nat.add(g, k), id), 1023)))}

def Build.step(+k: Nat, +g: Nat, +acc: U32, r: Flat & Chunked) -> BSt:
  (f, c) = r
  Build.step2(k, g, acc, f, c)

def Build.rep(reps: Nat, +k: Nat, +g: Nat, st: BSt) -> BSt:
  match reps st:
    case 0n BSt{f, acc}:
      BSt{f, acc}
    case 1n+p BSt{f, acc}:
      Build.rep(p, k, g, Build.step(k, g, acc, Flat.chunk(k, g, f)))

# ---- driver -------------------------------------------------------------------------------------------

def D() -> Nat:
  20n

def show(+label: String, +g: Nat, +reps: U32, +ms: U32, +acc: U32, r: U32 & U32) -> String:
  (k, s) = r
  "{\"mode\":\"" ++ label ++ "\",\"rows\":1048576,\"grain_log2\":" ++ Nat.show(g) ++ ",\"reps\":" ++ U32.show(reps) ++ ",\"ms_total\":" ++ U32.show(ms) ++ ",\"acc\":" ++ U32.show(acc) ++ ",\"check_k\":" ++ U32.show(k) ++ ",\"check_s\":" ++ U32.show(s) ++ "}"

def run.chunked(+mode: String, reps: Nat, c: Chunked) -> CSt:
  match mode:
    case "q1chunk":
      Q1C.rep(reps, CSt{c, 0})
    case _:
      Q2C.rep(reps, CSt{c, 0})

def verify.chunked(+mode: String, c: Chunked) -> U32 & U32:
  match mode:
    case "q1chunk":
      Q1C.verify(c)
    case _:
      Q2C.verify(c)

def run.flat(+mode: String, +n: U32, +d: Nat, reps: Nat, f: Flat) -> FSt:
  match mode:
    case "q1today":
      Q1F.today.rep(reps, n, d, 7n, FSt{f, 0})
    case "q1today3":
      Q1F.today.rep(reps, n, d, 3n, FSt{f, 0})
    case "q1fused":
      Q1F.fused.rep(reps, n, d, FSt{f, 0})
    case "q2today":
      Q2F.today.rep(reps, n, d, FSt{f, 0})
    case _:
      Q2F.fused.rep(reps, n, d, FSt{f, 0})

def verify.flat(+mode: String, +n: U32, +d: Nat, f: Flat) -> U32 & U32:
  match mode:
    case "q1today":
      Q1F.today.verify(n, d, f)
    case "q1today3":
      Q1F.today.verify(n, d, f)
    case "q1fused":
      Q1F.fused.verify(n, d, f)
    case "q2today":
      Q2F.today.verify(n, d, f)
    case _:
      Q2F.fused.verify(n, d, f)

def fin.chunked(+mode: String, +g: Nat, +reps: U32, +t0: Nat, +t1: Nat, st: CSt) -> String:
  match st:
    case CSt{c, acc}:
      show(mode, g, reps, U32.from_nat(Nat.sub(t1, t0)), acc, verify.chunked(mode, c))

def timed.chunked(+mode: String, +g: Nat, +reps: U32, r: Flat & Chunked) -> IO(Unit):
  (f, c) = r
  do IO<Unit>:
    t0 : Nat <- IO.now()
    st : CSt <- IO.pure(CSt, run.chunked(mode, U32.to_nat(reps), c))
    t1 : Nat <- IO.now()
    IO.print(fin.chunked(mode, g, reps, t0, t1, st))

def fin.flat(+mode: String, +reps: U32, +t0: Nat, +t1: Nat, st: FSt) -> String:
  match st:
    case FSt{f, acc}:
      show(mode, 20n, reps, U32.from_nat(Nat.sub(t1, t0)), acc, verify.flat(mode, U32.shln(1, D()), D(), f))

def timed.flat(+mode: String, +reps: U32, f: Flat) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    st : FSt <- IO.pure(FSt, run.flat(mode, U32.shln(1, D()), D(), U32.to_nat(reps), f))
    t1 : Nat <- IO.now()
    IO.print(fin.flat(mode, reps, t0, t1, st))

def fin.build(+g: Nat, +reps: U32, +t0: Nat, +t1: Nat, st: BSt) -> String:
  match st:
    case BSt{f, acc}:
      show("build7+flatten1", g, reps, U32.from_nat(Nat.sub(t1, t0)), acc, (0, 0))

def timed.build(+g: Nat, +reps: U32, f: Flat) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    st : BSt <- IO.pure(BSt, Build.rep(U32.to_nat(reps), Nat.sub(D(), g), g, BSt{f, 0}))
    t1 : Nat <- IO.now()
    IO.print(fin.build(g, reps, t0, t1, st))

def dispatch(build: Bool, chunked: Bool, +mode: String, +g: Nat, +reps: U32, f: Flat) -> IO(Unit):
  match build chunked:
    case True{} _:
      timed.build(g, reps, f)
    case False{} True{}:
      timed.chunked(mode, g, reps, Flat.chunk(Nat.sub(D(), g), g, f))
    case False{} False{}:
      timed.flat(mode, reps, f)

def nat_of.k(m: Maybe<&2, Nat>, +dflt: Nat) -> Nat:
  match m:
    case Some{v}:
      v
    case None{}:
      dflt

def nat_of(+s: String, +dflt: Nat) -> Nat:
  nat_of.k(Nat.read(s), dflt)

def go(args: List<String>) -> IO(Unit):
  match args:
    case exe <> +mode <> g <> reps <> Nil{}:
      dispatch(String.eq(mode, "build"), Bool.or(String.eq(mode, "q1chunk"), String.eq(mode, "q2chunk")), mode, nat_of(g, 14n), U32.from_nat(nat_of(reps, 10n)), Flat.gen(D()))
    case _:
      IO.print("usage: s1 <build|q1today|q1today3|q1fused|q1chunk|q2today|q2fused|q2chunk> <grain_log2> <reps>")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
