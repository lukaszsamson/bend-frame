# S3 (W0 engine spike, disposable): reductions and coarse-grain forks.
#
# Modes (build/s3 --threads T <mode> <grain log2> <reps>), 2^20 rows:
#   usum      U32 modular sum: flat Kernel.fold vs the chunk tree (per-leaf fold, U32.add at the nodes)
#   fsum      F32 Neumaier (DESIGN 15.5.3): flat Kernel.fsum vs a SEQUENTIAL in-order walk over the
#             leaves carrying the (s, c) state (no fork; the contract's ascending-i order is kept):
#             what the chunk layout costs the serial F32 reduction (should be ~0)
#   aggs      q3-like group_by aggregates over gids with 8 groups: sum F32 (Neumaier scatter), mean F32
#             (Neumaier scatter + count), count, max U32: sequential vs forked across the 4 aggregates
#             (2 x 2 balanced; each lane gets its own clone of gids: 3 clones, charged)
#   gathers   q4-like: 7 columns gathered by one permutation: sequential vs forked over a balanced tree
#             of the columns (perm cloned at every node: 2 clones per node, charged)
# Build/run: ~/.bend/bin/bend bench/spikes/w0_engine/s3_reduce.bend -o build/s3 && build/s3 --threads 12 usum 14 20
import Base
import ./../../../src/kernels.bend as K
import ./s1_chunks.bend as S

# ---- U32 sum: flat vs tree ------------------------------------------------------------------------------------

def USum.flat(+n: U32, a: Array<U32>) -> Array<U32> & U32:
  K.Kernel.fold(~U32, ~U32, ~(acc => x => U32.add(acc, x)), n, a, 0)

# per-leaf fold (the array comes back), U32.add at the nodes
def USum.leaf(+n: U32, +d: Nat, r: Array<U32> & U32) -> S.CU & U32:
  (a, s) = r
  (S.UL{n, d, a}, s)

def USum.node(+rows: U32, x: S.CU & U32, y: S.CU & U32) -> S.CU & U32:
  (a, s1) = x
  (b, s2) = y
  (S.UN{rows, a, b}, U32.add(s1, s2))

def USum.tree(t: S.CU) -> S.CU & U32:
  match t:
    case S.UL{+n, +d, a}:
      USum.leaf(n, d, K.Kernel.fold(~U32, ~U32, ~(acc => x => U32.add(acc, x)), n, a, 0))
    case S.UN{+rows, l, r}:
      x y = USum.tree(l) USum.tree(r)
      USum.node(rows, x, y)

type ASt is Type:
  ASt{a: Array<U32>, acc: U32}

def USum.flat.step(+acc: U32, r: Array<U32> & U32) -> ASt:
  (a, s) = r
  ASt{a, U32.add(acc, s)}

def USum.flat.rep(f: Nat, +n: U32, st: ASt) -> ASt:
  match f st:
    case 0n ASt{a, acc}:
      ASt{a, acc}
    case 1n+p ASt{a, acc}:
      USum.flat.rep(p, n, USum.flat.step(acc, USum.flat(n, a)))

type TSt is Type:
  TSt{t: S.CU, acc: U32}

def USum.tree.step(+acc: U32, r: S.CU & U32) -> TSt:
  (t, s) = r
  TSt{t, U32.add(acc, s)}

def USum.tree.rep(f: Nat, st: TSt) -> TSt:
  match f st:
    case 0n TSt{t, acc}:
      TSt{t, acc}
    case 1n+p TSt{t, acc}:
      USum.tree.rep(p, USum.tree.step(acc, USum.tree(t)))

# ---- F32 Neumaier: flat vs the sequential in-order leaf walk -------------------------------------------------

# Kernel.fsum.go restated so the array comes back and the state is threaded across leaves
def FSum.go(n: Nat, +i: U32, acc: K.NS, r: Array<F32> & F32) -> Array<F32> & K.NS:
  match n:
    case 0n:
      (a, x) = r
      (a, acc)
    case 1n+p:
      (a, x) = r
      +j = U32.inc(i)
      FSum.go(p, j, K.Kernel.nm.step(acc, x), Array.get(F32, a, j))

def FSum.flat(+n: U32, a: Array<F32>, acc: K.NS) -> Array<F32> & K.NS:
  FSum.go(U32.to_nat(n), 0, acc, Array.get(F32, a, 0))

# the leaves in order by an explicit work stack (a recursive in-order walk would need the left child's
# state to recurse into the right one: a helper that recurses back, R4); the folded leaves are rebuilt
# into a tree by the binary counter (FS.merge) and collapsed at the end
def FS.collapse(f: Nat, s: S.FS) -> S.CF:
  match f s:
    case _ S.FSNil{}:
      S.FL{0, 0n, Array.new(F32, 0n, 0.0)}
    case _ S.FSCons{r, c, S.FSNil{}}:
      c
    case 0n S.FSCons{r, c, S.FSCons{r2, c2, nx}}:
      S.FN{U32.add(r, r2), c2, c}
    case 1n+p S.FSCons{+r, c, S.FSCons{+r2, c2, nx}}:
      FS.collapse(p, S.FSCons{U32.add(r, r2), S.FN{U32.add(r, r2), c2, c}, nx})

# the walk carries the PREVIOUS leaf's fold result r (pend = 1n) and makes the next leaf's fold in its own
# argument list (the read-ahead idiom: no helper has to recurse back); i counts pushed leaves
def FSum.walk(f: Nat, pend: Nat, +i: U32, +n: U32, +d: Nat, s: S.FS, out: S.FS, r: Array<F32> & K.NS) -> S.FS & K.NS:
  match f pend s:
    case 0n 0n S.FSNil{}:
      (a, acc) = r
      (out, acc)
    case 0n 1n+q S.FSNil{}:
      (a, acc) = r
      (S.FS.merge(S.Tz(U32.inc(i)), n, S.FL{n, d, a}, out), acc)
    case 0n 0n S.FSCons{rows, c, nx}:
      (a, acc) = r
      (out, acc)
    case 0n 1n+q S.FSCons{rows, c, nx}:
      (a, acc) = r
      (S.FS.merge(S.Tz(U32.inc(i)), n, S.FL{n, d, a}, out), acc)
    case 1n+p 0n S.FSNil{}:
      (a, acc) = r
      (out, acc)
    case 1n+p 1n+q S.FSNil{}:
      (a, acc) = r
      (S.FS.merge(S.Tz(U32.inc(i)), n, S.FL{n, d, a}, out), acc)
    case 1n+p 0n S.FSCons{rows, S.FL{+n2, +d2, a2}, nx}:
      (a, acc) = r
      FSum.walk(p, 1n, 0, n2, d2, nx, out, FSum.flat(n2, a2, acc))
    case 1n+p 1n+q S.FSCons{rows, S.FL{+n2, +d2, a2}, nx}:
      (a, acc) = r
      FSum.walk(p, 1n, U32.inc(i), n2, d2, nx, S.FS.merge(S.Tz(U32.inc(i)), n, S.FL{n, d, a}, out), FSum.flat(n2, a2, acc))
    case 1n+p 0n S.FSCons{rows, S.FN{r2, l, rr}, nx}:
      FSum.walk(p, 0n, i, n, d, S.FSCons{0, l, S.FSCons{0, rr, nx}}, out, r)
    case 1n+p 1n+q S.FSCons{rows, S.FN{r2, l, rr}, nx}:
      FSum.walk(p, 1n+q, i, n, d, S.FSCons{0, l, S.FSCons{0, rr, nx}}, out, r)

def FSum.tree.k(r: S.FS & K.NS) -> S.CF & K.NS:
  (out, acc) = r
  (FS.collapse(4096n, out), acc)

def FSum.tree(t: S.CF) -> S.CF & K.NS:
  FSum.tree.k(FSum.walk(4096n, 0n, 0, 0, 0n, S.FSCons{0, t, S.FSNil{}}, S.FSNil{}, (Array.new(F32, 0n, 0.0), K.NS{0.0, 0.0})))

type FASt is Type:
  FASt{a: Array<F32>, acc: U32}

def FSum.flat.step(+acc: U32, r: Array<F32> & K.NS) -> FASt:
  (a, s) = r
  FASt{a, U32.add(acc, F32.bits(K.Kernel.nm.fin(s)))}

def FSum.flat.rep(f: Nat, +n: U32, st: FASt) -> FASt:
  match f st:
    case 0n FASt{a, acc}:
      FASt{a, acc}
    case 1n+p FASt{a, acc}:
      FSum.flat.rep(p, n, FSum.flat.step(acc, FSum.flat(n, a, K.NS{0.0, 0.0})))

type FTSt is Type:
  FTSt{t: S.CF, acc: U32}

def FSum.tree.step(+acc: U32, r: S.CF & K.NS) -> FTSt:
  (t, s) = r
  FTSt{t, U32.add(acc, F32.bits(K.Kernel.nm.fin(s)))}

def FSum.tree.rep(f: Nat, st: FTSt) -> FTSt:
  match f st:
    case 0n FTSt{t, acc}:
      FTSt{t, acc}
    case 1n+p FTSt{t, acc}:
      FSum.tree.rep(p, FSum.tree.step(acc, FSum.tree(t)))

# ---- q3-like aggregates over gids (8 groups) -------------------------------------------------------------------

# the scatters as groupby.bend does them (Kernel.scatter), with the inputs handed back
def Sc.f.put(+g: U32, +x: F32, r: Array<K.NS> & K.NS) -> Array<K.NS>:
  (acc, old) = r
  Array.set(K.NS, acc, g, K.Kernel.nm.step(old, x))

def Sc.f.go(n: Nat, +i: U32, acc: Array<K.NS>, rg: Array<U32> & U32, rv: Array<F32> & F32) -> Array<K.NS> & Array<U32> & Array<F32>:
  match n:
    case 0n:
      (gs, g) = rg
      (vs, x) = rv
      (acc, gs, vs)
    case 1n+p:
      (gs, +g) = rg
      (vs, x) = rv
      +j = U32.inc(i)
      Sc.f.go(p, j, Sc.f.put(g, x, Array.get(K.NS, acc, g)), Array.get(U32, gs, j), Array.get(F32, vs, j))

# F32 Neumaier per group, in row order (the contract)
def Sc.f(+n: U32, gids: Array<U32>, vals: Array<F32>) -> Array<K.NS> & Array<U32> & Array<F32>:
  Sc.f.go(U32.to_nat(n), 0, Array.new(K.NS, 3n, K.NS{0.0, 0.0}), Array.get(U32, gids, 0), Array.get(F32, vals, 0))

def Sc.u.put(~f: U32 -> U32 -> U32, +g: U32, +x: U32, r: Array<U32> & U32) -> Array<U32>:
  (acc, old) = r
  Array.set(U32, acc, g, f(old, x))

def Sc.u.go(~f: U32 -> U32 -> U32, n: Nat, +i: U32, acc: Array<U32>, rg: Array<U32> & U32, rv: Array<U32> & U32) -> Array<U32> & Array<U32> & Array<U32>:
  match n:
    case 0n:
      (gs, g) = rg
      (vs, x) = rv
      (acc, gs, vs)
    case 1n+p:
      (gs, +g) = rg
      (vs, x) = rv
      +j = U32.inc(i)
      Sc.u.go(~f, p, j, Sc.u.put(~f, g, x, Array.get(U32, acc, g)), Array.get(U32, gs, j), Array.get(U32, vs, j))

def Sc.u(~f: U32 -> U32 -> U32, +n: U32, gids: Array<U32>, vals: Array<U32>) -> Array<U32> & Array<U32> & Array<U32>:
  Sc.u.go(~f, U32.to_nat(n), 0, Array.new(U32, 3n, 0), Array.get(U32, gids, 0), Array.get(U32, vals, 0))

# a scatter's answer reduced to one word (group 1's result) plus the inputs
def Agg.w3b(gs: Array<U32>, vs: Array<F32>, r: Array<K.NS> & K.NS) -> Array<U32> & Array<F32> & U32:
  (acc, s) = r
  (gs, vs, F32.bits(K.Kernel.nm.fin(s)))

def Agg.w3(r: Array<K.NS> & Array<U32> & Array<F32>) -> Array<U32> & Array<F32> & U32:
  (acc, gs, vs) = r
  Agg.w3b(gs, vs, Array.get(K.NS, acc, 1))

def Agg.u3b(gs: Array<U32>, vs: Array<U32>, r: Array<U32> & U32) -> Array<U32> & Array<U32> & U32:
  (acc, s) = r
  (gs, vs, s)

def Agg.u3(r: Array<U32> & Array<U32> & Array<U32>) -> Array<U32> & Array<U32> & U32:
  (acc, gs, vs) = r
  Agg.u3b(gs, vs, Array.get(U32, acc, 1))

# the four aggregates' inputs: gids, revenue (F32), price (F32), qty (U32); results folded into acc
type Agg is Type:
  Agg{gids: Array<U32>, rev: Array<F32>, pr: Array<F32>, qty: Array<U32>, acc: U32}

# sequential: sum(rev), mean(price) = fsum + count, count, max(qty); the inputs come back
def Agg.sd(rev: Array<F32>, pr: Array<F32>, +acc: U32, r: Array<U32> & Array<U32> & U32) -> Agg:
  (gs, qty, m) = r
  Agg{gs, rev, pr, qty, U32.add(acc, m)}

def Agg.sc(+n: U32, rev: Array<F32>, pr: Array<F32>, qty: Array<U32>, +acc: U32, r: Array<U32> & Array<U32> & U32) -> Agg:
  (gs, ones, c) = r
  Agg.sd(rev, pr, U32.add(acc, c), Agg.u3(Sc.u(~(a => b => U32.max(a, b)), n, gs, qty)))

def Agg.sb(+n: U32, rev: Array<F32>, qty: Array<U32>, +acc: U32, r: Array<U32> & Array<F32> & U32) -> Agg:
  (gs, pr, s2) = r
  Agg.sc(n, rev, pr, qty, U32.add(acc, s2), Agg.u3(Sc.u(~(a => b => U32.add(a, b)), n, gs, K.Kernel.const(~U32, 20n, 1))))

def Agg.sa(+n: U32, pr: Array<F32>, qty: Array<U32>, +acc: U32, r: Array<U32> & Array<F32> & U32) -> Agg:
  (gs, rev, s1) = r
  Agg.sb(n, rev, qty, U32.add(acc, s1), Agg.w3(Sc.f(n, gs, pr)))

def Agg.seq(+n: U32, a: Agg) -> Agg:
  match a:
    case Agg{gids, rev, pr, qty, acc}:
      Agg.sa(n, pr, qty, acc, Agg.w3(Sc.f(n, gids, rev)))

# forked: 2 x 2 over the aggregates; lanes need their own gids: three clones (charged inside the timing)
def Agg.par.lj(x: Array<U32> & Array<F32> & U32, y: Array<U32> & Array<F32> & U32) -> Array<U32> & Array<F32> & U32 & Array<F32> & U32:
  (g1, rev, s1) = x
  (g2, pr, s2) = y
  (g1, rev, s1, pr, s2)

def Agg.par.l(+n: U32, rev: Array<F32>, pr: Array<F32>, rg2: Array<U32> & Array<U32>) -> Array<U32> & Array<F32> & U32 & Array<F32> & U32:
  (g1, g2) = rg2
  x y = Agg.w3(Sc.f(n, g1, rev)) Agg.w3(Sc.f(n, g2, pr))
  Agg.par.lj(x, y)

def Agg.par.rj(x: Array<U32> & Array<U32> & U32, y: Array<U32> & Array<U32> & U32) -> U32 & Array<U32> & U32:
  (g3, ones, c) = x
  (g4, qty, m) = y
  (c, qty, m)

def Agg.par.r(+n: U32, qty: Array<U32>, rg2: Array<U32> & Array<U32>) -> U32 & Array<U32> & U32:
  (g3, g4) = rg2
  x y = Agg.u3(Sc.u(~(a => b => U32.add(a, b)), n, g3, K.Kernel.const(~U32, 20n, 1))) Agg.u3(Sc.u(~(a => b => U32.max(a, b)), n, g4, qty))
  Agg.par.rj(x, y)

def Agg.par.j(+acc: U32, x: Array<U32> & Array<F32> & U32 & Array<F32> & U32, y: U32 & Array<U32> & U32) -> Agg:
  (g1, rev, s1, pr, s2) = x
  (c, qty, m) = y
  Agg{g1, rev, pr, qty, U32.add(acc, U32.add(U32.add(s1, s2), U32.add(c, m)))}

def Agg.par.k(+n: U32, +acc: U32, rev: Array<F32>, pr: Array<F32>, qty: Array<U32>, r12: Array<U32> & Array<U32>, r34: Array<U32> & Array<U32>) -> Agg:
  x y = Agg.par.l(n, rev, pr, r12) Agg.par.r(n, qty, r34)
  Agg.par.j(acc, x, y)

def Agg.par.c(+n: U32, +acc: U32, rev: Array<F32>, pr: Array<F32>, qty: Array<U32>, r: Array<U32> & Array<U32>) -> Agg:
  (ga, gb) = r
  Agg.par.k(n, acc, rev, pr, qty, Array.clone(U32, ga), Array.clone(U32, gb))

def Agg.par(+n: U32, a: Agg) -> Agg:
  match a:
    case Agg{gids, rev, pr, qty, acc}:
      Agg.par.c(n, acc, rev, pr, qty, Array.clone(U32, gids))

def Agg.rep(f: Nat, par: Bool, +n: U32, a: Agg) -> Agg:
  match f par:
    case 0n _:
      a
    case 1n+p True{}:
      Agg.rep(p, True{}, n, Agg.par(n, a))
    case 1n+p False{}:
      Agg.rep(p, False{}, n, Agg.seq(n, a))

# ---- q4-like: 7 columns gathered by one permutation ------------------------------------------------------------

# a reversed permutation (a cheap stand-in for a sort's permutation)
def Perm(+n: U32, +d: Nat) -> Array<U32>:
  K.Kernel.map(~U32, ~U32, ~(i => U32.sub(1048575, i)), n, d, K.Kernel.iota(n, d), 0)

# the columns as a balanced tree (built untimed by the binary counter)
type CT is Type:
  CTL{a: Array<U32>}
  CTN{l: CT, r: CT}

type CTS is Type:
  CTSNil{}
  CTSCons{c: CT, next: CTS}

def CTS.merge(m: Nat, c: CT, s: CTS) -> CTS:
  match m s:
    case 0n CTSNil{}:
      CTSCons{c, CTSNil{}}
    case 0n CTSCons{c2, nx}:
      CTSCons{c, CTSCons{c2, nx}}
    case 1n+p CTSNil{}:
      CTSCons{c, CTSNil{}}
    case 1n+p CTSCons{c2, nx}:
      CTS.merge(p, CTN{c2, c}, nx)

def CTS.collapse(f: Nat, s: CTS) -> CT:
  match f s:
    case _ CTSNil{}:
      CTL{Array.new(U32, 0n, 0)}
    case _ CTSCons{c, CTSNil{}}:
      c
    case 0n CTSCons{c, CTSCons{c2, nx}}:
      CTN{c2, c}
    case 1n+p CTSCons{c, CTSCons{c2, nx}}:
      CTS.collapse(p, CTSCons{CTN{c2, c}, nx})

def CT.gen(k: Nat, +i: U32, +n: U32, +d: Nat, s: CTS) -> CT:
  match k:
    case 0n:
      CTS.collapse(64n, s)
    case 1n+p:
      CT.gen(p, U32.inc(i), n, d, CTS.merge(S.Tz(U32.inc(i)), CTL{K.Kernel.iota_from(n, d, i)}, s))

def CT.count.j(x: CT & U32, y: CT & U32) -> CT & U32:
  (l, a) = x
  (r, b) = y
  (CTN{l, r}, U32.add(a, b))

# sequential: every column gathered in turn (an in-order walk; perm comes back)
def CT.count(t: CT) -> CT & U32:
  match t:
    case CTL{a}:
      (CTL{a}, 1)
    case CTN{l, r}:
      CT.count.j(CT.count(l), CT.count(r))

def G.seq.walk(f: Nat, pend: Nat, +i: U32, +n: U32, +d: Nat, s: CTS, out: CTS, r: Array<U32> & Array<U32>) -> CTS & Array<U32>:
  match f pend s:
    case 0n 0n CTSNil{}:
      (o, perm) = r
      (out, perm)
    case 0n 1n+q CTSNil{}:
      (o, perm) = r
      (CTS.merge(S.Tz(U32.inc(i)), CTL{o}, out), perm)
    case 0n 0n CTSCons{c, nx}:
      (o, perm) = r
      (out, perm)
    case 0n 1n+q CTSCons{c, nx}:
      (o, perm) = r
      (CTS.merge(S.Tz(U32.inc(i)), CTL{o}, out), perm)
    case 1n+p 0n CTSNil{}:
      (o, perm) = r
      (out, perm)
    case 1n+p 1n+q CTSNil{}:
      (o, perm) = r
      (CTS.merge(S.Tz(U32.inc(i)), CTL{o}, out), perm)
    case 1n+p 0n CTSCons{CTL{a}, nx}:
      (o, perm) = r
      G.seq.walk(p, 1n, 0, n, d, nx, out, K.Kernel.gather(~U32, n, d, a, perm, 0))
    case 1n+p 1n+q CTSCons{CTL{a}, nx}:
      (o, perm) = r
      G.seq.walk(p, 1n, U32.inc(i), n, d, nx, CTS.merge(S.Tz(U32.inc(i)), CTL{o}, out), K.Kernel.gather(~U32, n, d, a, perm, 0))
    case 1n+p 0n CTSCons{CTN{l, rr}, nx}:
      G.seq.walk(p, 0n, i, n, d, CTSCons{l, CTSCons{rr, nx}}, out, r)
    case 1n+p 1n+q CTSCons{CTN{l, rr}, nx}:
      G.seq.walk(p, 1n+q, i, n, d, CTSCons{l, CTSCons{rr, nx}}, out, r)

def G.seq.fin(r: CTS & Array<U32>) -> CT & Array<U32>:
  (out, perm) = r
  (CTS.collapse(64n, out), perm)

def G.seq(+n: U32, +d: Nat, t: CT, perm: Array<U32>) -> CT & Array<U32>:
  G.seq.fin(G.seq.walk(64n, 0n, 0, n, d, CTSCons{t, CTSNil{}}, CTSNil{}, (Array.new(U32, 0n, 0), perm)))

# forked over the column tree: every call receives a PAIR of perms (opened as a parameter, no helper has to
# recurse back); a node clones one for each child, a leaf gathers with one and drops the other
def G.par.leaf(r: Array<U32> & Array<U32>) -> CT & Array<U32>:
  (out, perm) = r
  (CTL{out}, perm)

def G.par.j(x: CT & Array<U32>, y: CT & Array<U32>) -> CT & Array<U32>:
  (l, p1) = x
  (r, p2) = y
  (CTN{l, r}, p1)

def G.par(t: CT, pp: Array<U32> & Array<U32>, +n: U32, +d: Nat) -> CT & Array<U32>:
  match t:
    case CTL{a}:
      (p1, p2) = pp
      G.par.leaf(K.Kernel.gather(~U32, n, d, a, p1, 0))
    case CTN{l, r}:
      (p1, p2) = pp
      x y = G.par(l, Array.clone(U32, p1), n, d) G.par(r, Array.clone(U32, p2), n, d)
      G.par.j(x, y)

type GSt is Type:
  GSt{c: CT, perm: Array<U32>, acc: U32}

def G.step(+acc: U32, r: CT & Array<U32>) -> GSt:
  (c, perm) = r
  GSt{c, perm, U32.inc(acc)}

def G.rep(f: Nat, par: Bool, +n: U32, +d: Nat, st: GSt) -> GSt:
  match f par st:
    case 0n _ GSt{c, perm, acc}:
      GSt{c, perm, acc}
    case 1n+p True{} GSt{c, perm, acc}:
      G.rep(p, True{}, n, d, G.step(acc, G.par(c, Array.clone(U32, perm), n, d)))
    case 1n+p False{} GSt{c, perm, acc}:
      G.rep(p, False{}, n, d, G.step(acc, G.seq(n, d, c, perm)))

# ---- driver -------------------------------------------------------------------------------------------------

def D() -> Nat:
  20n

def show(+mode: String, +g: Nat, +reps: U32, +ms: U32, +k: U32, +s: U32) -> String:
  "{\"mode\":\"" ++ mode ++ "\",\"rows\":1048576,\"grain_log2\":" ++ Nat.show(g) ++ ",\"reps\":" ++ U32.show(reps) ++ ",\"ms_total\":" ++ U32.show(ms) ++ ",\"check_k\":" ++ U32.show(k) ++ ",\"check_s\":" ++ U32.show(s) ++ "}"

def fin.usum.flat(+reps: U32, +t0: Nat, +t1: Nat, st: ASt) -> String:
  match st:
    case ASt{a, acc}:
      show("usum_flat", 20n, reps, U32.from_nat(Nat.sub(t1, t0)), acc, 0)

def fin.usum.tree(+g: Nat, +reps: U32, +t0: Nat, +t1: Nat, st: TSt) -> String:
  match st:
    case TSt{t, acc}:
      show("usum_tree", g, reps, U32.from_nat(Nat.sub(t1, t0)), acc, 0)

def run.usum.flat(+reps: U32, a: Array<U32>) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    st : ASt <- IO.pure(ASt, USum.flat.rep(U32.to_nat(reps), U32.shln(1, D()), ASt{a, 0}))
    t1 : Nat <- IO.now()
    IO.print(fin.usum.flat(reps, t0, t1, st))

def run.usum.tree(+g: Nat, +reps: U32, r: Array<U32> & S.CU) -> IO(Unit):
  (a, t) = r
  do IO<Unit>:
    t0 : Nat <- IO.now()
    st : TSt <- IO.pure(TSt, USum.tree.rep(U32.to_nat(reps), TSt{t, 0}))
    t1 : Nat <- IO.now()
    IO.print(fin.usum.tree(g, reps, t0, t1, st))

def fin.fsum.flat(+reps: U32, +t0: Nat, +t1: Nat, st: FASt) -> String:
  match st:
    case FASt{a, acc}:
      show("fsum_flat", 20n, reps, U32.from_nat(Nat.sub(t1, t0)), acc, 0)

def fin.fsum.tree(+g: Nat, +reps: U32, +t0: Nat, +t1: Nat, st: FTSt) -> String:
  match st:
    case FTSt{t, acc}:
      show("fsum_leafwalk", g, reps, U32.from_nat(Nat.sub(t1, t0)), acc, 0)

def run.fsum.flat(+reps: U32, a: Array<F32>) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    st : FASt <- IO.pure(FASt, FSum.flat.rep(U32.to_nat(reps), U32.shln(1, D()), FASt{a, 0}))
    t1 : Nat <- IO.now()
    IO.print(fin.fsum.flat(reps, t0, t1, st))

def run.fsum.tree(+g: Nat, +reps: U32, r: Array<F32> & S.CF) -> IO(Unit):
  (a, t) = r
  do IO<Unit>:
    t0 : Nat <- IO.now()
    st : FTSt <- IO.pure(FTSt, FSum.tree.rep(U32.to_nat(reps), FTSt{t, 0}))
    t1 : Nat <- IO.now()
    IO.print(fin.fsum.tree(g, reps, t0, t1, st))

def fin.aggs(+par: Bool, +reps: U32, +t0: Nat, +t1: Nat, a: Agg) -> String:
  match a:
    case Agg{gids, rev, pr, qty, acc}:
      show(Bool.pick(String, par, "aggs_forked4", "aggs_seq"), 20n, reps, U32.from_nat(Nat.sub(t1, t0)), acc, 0)

def run.aggs(+par: Bool, +reps: U32, a: Agg) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    st : Agg <- IO.pure(Agg, Agg.rep(U32.to_nat(reps), par, U32.shln(1, D()), a))
    t1 : Nat <- IO.now()
    IO.print(fin.aggs(par, reps, t0, t1, st))

def fin.gathers.k(+par: Bool, +reps: U32, +t0: Nat, +t1: Nat, +acc: U32, r: CT & U32) -> String:
  (c, k) = r
  show(Bool.pick(String, par, "gathers7_forked", "gathers7_seq"), 20n, reps, U32.from_nat(Nat.sub(t1, t0)), acc, k)

def fin.gathers(+par: Bool, +reps: U32, +t0: Nat, +t1: Nat, st: GSt) -> String:
  match st:
    case GSt{c, perm, acc}:
      fin.gathers.k(par, reps, t0, t1, acc, CT.count(c))

def run.gathers(+par: Bool, +reps: U32, c: CT) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    st : GSt <- IO.pure(GSt, G.rep(U32.to_nat(reps), par, U32.shln(1, D()), D(), GSt{c, Perm(U32.shln(1, D()), D()), 0}))
    t1 : Nat <- IO.now()
    IO.print(fin.gathers(par, reps, t0, t1, st))

def agg.gen() -> Agg:
  Agg{S.GenU(~(i => S.Gen.rg(i)), D()), S.GenF(~(i => S.Gen.price(i)), D()), S.GenF(~(i => S.Gen.disc(i)), D()), S.GenU(~(i => S.Gen.qty(i)), D()), 0}

def dispatch(+mode: String, +g: Nat, +reps: U32) -> IO(Unit):
  match mode:
    case "usum":
      do IO<Unit>:
        run.usum.flat(reps, S.GenU(~(i => S.Gen.qty(i)), D()))
        run.usum.tree(g, reps, S.UB(Nat.sub(D(), g), g, S.GenU(~(i => S.Gen.qty(i)), D())))
    case "fsum":
      do IO<Unit>:
        run.fsum.flat(reps, S.GenF(~(i => S.Gen.price(i)), D()))
        run.fsum.tree(g, reps, S.FB(Nat.sub(D(), g), g, S.GenF(~(i => S.Gen.price(i)), D())))
    case "fsumr":
      do IO<Unit>:
        run.fsum.tree(g, reps, S.FB(Nat.sub(D(), g), g, S.GenF(~(i => S.Gen.price(i)), D())))
        run.fsum.flat(reps, S.GenF(~(i => S.Gen.price(i)), D()))
    case "aggs":
      do IO<Unit>:
        run.aggs(False{}, reps, agg.gen())
        run.aggs(True{}, reps, agg.gen())
    case _:
      do IO<Unit>:
        run.gathers(False{}, reps, CT.gen(7n, 0, U32.shln(1, D()), D(), CTSNil{}))
        run.gathers(True{}, reps, CT.gen(7n, 0, U32.shln(1, D()), D(), CTSNil{}))

def go(args: List<String>) -> IO(Unit):
  match args:
    case exe <> mode <> g <> reps <> Nil{}:
      dispatch(mode, S.nat_of(g, 14n), U32.from_nat(S.nat_of(reps, 10n)))
    case _:
      IO.print("usage: s3 <usum|fsum|fsumr|aggs|gathers> <grain_log2> <reps>")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
