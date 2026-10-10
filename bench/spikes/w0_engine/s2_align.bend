# S2 (W0 engine spike, disposable): aligned zip / filter over chunk trees with different partitions.
#
# Imports the S1 chunk tree (S.CU: UL{n, d, a} | UN{rows, l, r}) and its fused filter. Shows:
#   ragged     filter (S1's fused predicate + 3-column compaction) gives RAGGED leaves that stay ALIGNED
#              across the frame's columns (one mask per leaf); a zip over two ragged aligned trees walks
#              them in lockstep (per-leaf n) and forks at the nodes; no alignment work
#   concat     concat_vertical is one node over the two inputs (O(1), partitions compose)
#   misaligned two trees of the same height but different partitions (grain 2^14 vs 2^13): the lockstep
#              zip reports `aligned=false`; the normalisation re-cuts B to A's partition: flatten B (one
#              pass) + chunk by the partition (one pass); its cost is timed
#   rechunk    after a selective filter the leaves are small: Rechunk merges sibling leaves whose rows
#              fit one leaf (bottom-up, forked, decision by row counts only, so every column of the frame
#              takes the same shape without a shared plan); timed, leaf counts before / after
# Build/run: ~/.bend/bin/bend bench/spikes/w0_engine/s2_align.bend -o build/s2 && build/s2 --threads 12 ragged 14 20
import Base
import ./../../../src/kernels.bend as K
import ./s1_chunks.bend as S

# ---- a zip that hands its inputs back (so reps can repeat it) ----------------------------------------------

type Z3 is Type:
  Z3{out: Array<U32>, a: Array<U32>, b: Array<U32>}

def ZK.go(n: Nat, +i: U32, out: Array<U32>, ra: Array<U32> & U32, rb: Array<U32> & U32) -> Z3:
  match n:
    case 0n:
      (a, x) = ra
      (b, y) = rb
      Z3{out, a, b}
    case 1n+p:
      (a, x) = ra
      (b, y) = rb
      +j = U32.inc(i)
      ZK.go(p, j, Array.set(U32, out, i, U32.add(x, y)), Array.get(U32, a, j), Array.get(U32, b, j))

def ZK(+n: U32, +d: Nat, a: Array<U32>, b: Array<U32>) -> Z3:
  ZK.go(U32.to_nat(n), 0, Array.new(U32, d, 0), Array.get(U32, a, 0), Array.get(U32, b, 0))

# the lockstep zip over two trees: aligned when every leaf pair has the same n and the shapes agree
type ZT is Type:
  ZT{out: S.CU, a: S.CU, b: S.CU, aligned: Bool}

def ZipT.leaf(+n: U32, +d: Nat, +n2: U32, +d2: Nat, r: Z3) -> ZT:
  match r:
    case Z3{out, a, b}:
      ZT{S.UL{n, d, out}, S.UL{n, d, a}, S.UL{n2, d2, b}, U32.is_eq(n, n2)}

def ZipT.join(+rows: U32, +rows2: U32, x: ZT, y: ZT) -> ZT:
  match x y:
    case ZT{o1, a1, b1, k1} ZT{o2, a2, b2, k2}:
      ZT{S.UN{rows, o1, o2}, S.UN{rows, a1, a2}, S.UN{rows2, b1, b2}, Bool.and(k1, k2)}

def ZipT(a: S.CU, b: S.CU) -> ZT:
  match a b:
    case S.UL{+n, +d, x} S.UL{+n2, +d2, y}:
      ZipT.leaf(n, d, n2, d2, ZK(n, d, x, y))
    case S.UN{+rows, l1, r1} S.UN{+rows2, l2, r2}:
      x y = ZipT(l1, l2) ZipT(r1, r2)
      ZipT.join(rows, rows2, x, y)
    case S.UL{n, d, x} S.UN{rows2, l2, r2}:
      ZT{S.UL{0, 0n, Array.new(U32, 0n, 0)}, S.UL{n, d, x}, S.UN{rows2, l2, r2}, False{}}
    case S.UN{rows, l1, r1} S.UL{n2, d2, y}:
      ZT{S.UL{0, 0n, Array.new(U32, 0n, 0)}, S.UN{rows, l1, r1}, S.UL{n2, d2, y}, False{}}

# ---- tree queries (consuming; used untimed) ---------------------------------------------------------------

def CU.leaves(t: S.CU) -> U32:
  match t:
    case S.UL{n, d, a}:
      1
    case S.UN{rows, l, r}:
      U32.add(CU.leaves(l), CU.leaves(r))

def CU.sum(t: S.CU) -> U32:
  match t:
    case S.UL{+n, d, a}:
      S.Sum(n, a)
    case S.UN{rows, l, r}:
      x y = CU.sum(l) CU.sum(r)
      U32.add(x, y)

# the partition (leaf sizes in order), by a stack walk; the tree is consumed
def Part.go(f: Nat, acc: List<&2, U32>, s: S.US) -> List<&2, U32>:
  match f s:
    case 0n S.USNil{}:
      acc
    case 0n S.USCons{r, c, nx}:
      acc
    case 1n+p S.USNil{}:
      acc
    case 1n+p S.USCons{rows, S.UL{n, d, a}, nx}:
      Part.go(p, n <> acc, nx)
    case 1n+p S.USCons{rows, S.UN{r2, l, r}, nx}:
      Part.go(p, acc, S.USCons{0, l, S.USCons{0, r, nx}})

def Part(t: S.CU) -> List<&2, U32>:
  List.reverse(&2, U32, Part.go(4096n, Nil{}, S.USCons{0, t, S.USNil{}}))

# ---- chunk by a partition (ragged leaf sizes) ---------------------------------------------------------------

# collapse a binary-counter stack into one tree (merge the top two until one is left)
def US.collapse(f: Nat, s: S.US) -> S.CU:
  match f s:
    case _ S.USNil{}:
      S.UL{0, 0n, Array.new(U32, 0n, 0)}
    case _ S.USCons{r, c, S.USNil{}}:
      c
    case 0n S.USCons{r, c, S.USCons{r2, c2, nx}}:
      S.UN{U32.add(r, r2), c2, c}
    case 1n+p S.USCons{+r, c, S.USCons{+r2, c2, nx}}:
      US.collapse(p, S.USCons{U32.add(r, r2), S.UN{U32.add(r, r2), c2, c}, nx})

def UBP.step(+i: U32, +n: U32, s: S.US, out: Array<U32>) -> S.US:
  S.US.merge(S.Tz(U32.inc(i)), n, S.UL{n, K.Kernel.depth_for(U32.max(n, 1)), out}, s)

# r is the range copy of leaf i (n rows, taken at off - n); the next leaf's copy is made in the argument list
def UBP.go(part: List<&2, U32>, +i: U32, +off: U32, +n: U32, s: S.US, r: Array<U32> & Array<U32>) -> Array<U32> & S.US:
  match part:
    case Nil{}:
      (a, out) = r
      (a, UBP.step(i, n, s, out))
    case +n2 <> rest:
      (a, out) = r
      UBP.go(rest, U32.inc(i), U32.add(off, n2), n2, UBP.step(i, n, s, out), S.RngU(n2, K.Kernel.depth_for(U32.max(n2, 1)), off, a))

def UBP.fin(r: Array<U32> & S.US) -> Array<U32> & S.CU:
  (a, s) = r
  (a, US.collapse(4096n, s))

# chunk the flat column a by the partition (leaf sizes in order); a comes back
def UBP(part: List<&2, U32>, a: Array<U32>) -> Array<U32> & S.CU:
  match part:
    case Nil{}:
      (a, S.UL{0, 0n, Array.new(U32, 0n, 0)})
    case +n0 <> rest:
      UBP.fin(UBP.go(rest, 0, n0, n0, S.USNil{}, S.RngU(n0, K.Kernel.depth_for(U32.max(n0, 1)), 0, a)))

# ---- re-cut B to A's partition: flatten (one pass) + chunk by the partition (one pass) ----------------------

def Realign.k2(r: Array<U32> & S.CU) -> S.CU:
  (a, c) = r
  c

def Realign.k(part: List<&2, U32>, flat: Array<U32>) -> S.CU:
  Realign.k2(UBP(part, flat))

# ---- rechunk: merge sibling leaves that fit one leaf of 2^g rows -------------------------------------------

def RC.leaf(fits: Bool, +g: Nat, +rows: U32, +n1: U32, +d1: Nat, a1: Array<U32>, +n2: U32, +d2: Nat, a2: Array<U32>) -> S.CU:
  match fits:
    case True{}:
      S.UL{rows, g, K.Kernel.append(~U32, n1, n2, g, a1, a2, 0)}
    case False{}:
      S.UN{rows, S.UL{n1, d1, a1}, S.UL{n2, d2, a2}}

def RC.join(+g: Nat, +rows: U32, x: S.CU, y: S.CU) -> S.CU:
  match x y:
    case S.UL{+n1, d1, a1} S.UL{+n2, d2, a2}:
      RC.leaf(U32.is_le(U32.add(n1, n2), U32.shln(1, g)), g, rows, n1, d1, a1, n2, d2, a2)
    case S.UL{n1, d1, a1} S.UN{r2, l2, rr2}:
      S.UN{rows, S.UL{n1, d1, a1}, S.UN{r2, l2, rr2}}
    case S.UN{r1, l1, rr1} S.UL{n2, d2, a2}:
      S.UN{rows, S.UN{r1, l1, rr1}, S.UL{n2, d2, a2}}
    case S.UN{r1, l1, rr1} S.UN{r2, l2, rr2}:
      S.UN{rows, S.UN{r1, l1, rr1}, S.UN{r2, l2, rr2}}

def Rechunk(+g: Nat, t: S.CU) -> S.CU:
  match t:
    case S.UL{n, d, a}:
      S.UL{n, d, a}
    case S.UN{+rows, l, r}:
      x y = Rechunk(g, l) Rechunk(g, r)
      RC.join(g, rows, x, y)

# ---- the filtered (ragged, aligned) id and region trees out of S1's fused filter --------------------------------

def T3.split.j(+rows: U32, x: S.CU & S.CU, y: S.CU & S.CU) -> S.CU & S.CU:
  (a1, b1) = x
  (a2, b2) = y
  (S.UN{rows, a1, a2}, S.UN{rows, b1, b2})

def T3.split(t: S.T3) -> S.CU & S.CU:
  match t:
    case S.T3L{+n, +d, id, rg, pr}:
      (S.UL{n, d, id}, S.UL{n, d, rg})
    case S.T3N{+rows, l, r}:
      T3.split.j(rows, T3.split(l), T3.split(r))

def Ragged.k(r: S.Q1T) -> S.CU & S.CU:
  match r:
    case S.Q1T{out, ok, qty, id, rg, pr}:
      T3.split(out)

# the filtered id and region trees (the S1 frame's other columns are dropped)
def Ragged(c: S.Chunked) -> S.CU & S.CU:
  match c:
    case S.Chunked{ok, qty, id, rg, vd, pr, ds}:
      Ragged.k(S.Q1.tree(ok, qty, id, rg, pr))

# ---- reps -------------------------------------------------------------------------------------------------

type ZSt is Type:
  ZSt{a: S.CU, b: S.CU, acc: U32, aligned: Bool}

def Zip.rep.k(+acc: U32, r: ZT) -> ZSt:
  match r:
    case ZT{out, a, b, k}:
      ZSt{a, b, U32.add(acc, CU.leaves(out)), k}

def Zip.rep(f: Nat, st: ZSt) -> ZSt:
  match f st:
    case 0n ZSt{a, b, acc, k}:
      ZSt{a, b, acc, k}
    case 1n+p ZSt{a, b, acc, k}:
      Zip.rep(p, Zip.rep.k(acc, ZipT(a, b)))

type RSt is Type:
  RSt{t: S.CU, acc: U32}

def RC.rep.k(+acc: U32, +g: Nat, t: S.CU) -> RSt:
  RSt{t, U32.add(acc, 1)}

# rechunk reps: each rep re-chunks the previous result (idempotent after the first; the copy happens once)
def RC.rep(f: Nat, +g: Nat, st: RSt) -> RSt:
  match f st:
    case 0n RSt{t, acc}:
      RSt{t, acc}
    case 1n+p RSt{t, acc}:
      RC.rep(p, g, RC.rep.k(acc, g, Rechunk(g, t)))

# ---- driver -------------------------------------------------------------------------------------------------

def D() -> Nat:
  20n

def show(+mode: String, +g: Nat, +reps: U32, +ms: U32, +k: U32, +s: U32, +extra: String) -> String:
  "{\"mode\":\"" ++ mode ++ "\",\"rows\":1048576,\"grain_log2\":" ++ Nat.show(g) ++ ",\"reps\":" ++ U32.show(reps) ++ ",\"ms_total\":" ++ U32.show(ms) ++ ",\"check_k\":" ++ U32.show(k) ++ ",\"check_s\":" ++ U32.show(s) ++ extra ++ "}"

def fin.zip(+mode: String, +g: Nat, +reps: U32, +t0: Nat, +t1: Nat, st: ZSt) -> String:
  match st:
    case ZSt{a, b, acc, k}:
      show(mode, g, reps, U32.from_nat(Nat.sub(t1, t0)), CU.leaves(a), CU.sum(b), ",\"aligned\":" ++ Bool.show(k) ++ ",\"acc\":" ++ U32.show(acc))

# ragged: the filtered id and region trees zipped `reps` times
def run.ragged(+g: Nat, +reps: U32, r: S.CU & S.CU) -> IO(Unit):
  (a, b) = r
  do IO<Unit>:
    t0 : Nat <- IO.now()
    st : ZSt <- IO.pure(ZSt, Zip.rep(U32.to_nat(reps), ZSt{a, b, 0, True{}}))
    t1 : Nat <- IO.now()
    IO.print(fin.zip("ragged_zip", g, reps, t0, t1, st))

# concat: UN over two filtered frames' trees, then the lockstep zip (aligned by construction)
def run.concat(+g: Nat, +reps: U32, r1: S.CU & S.CU, r2: S.CU & S.CU) -> IO(Unit):
  (a1, b1) = r1
  (a2, b2) = r2
  do IO<Unit>:
    t0 : Nat <- IO.now()
    st : ZSt <- IO.pure(ZSt, Zip.rep(U32.to_nat(reps), ZSt{S.UN{0, a1, a2}, S.UN{0, b1, b2}, 0, True{}}))
    t1 : Nat <- IO.now()
    IO.print(fin.zip("concat_zip", g, reps, t0, t1, st))

def chunk1(r: Array<U32> & S.CU) -> S.CU:
  (a, c) = r
  c

def fin.mis(+g: Nat, +t0: Nat, +t1: Nat, +t2: Nat, +t3: Nat, +k0: Bool, st: ZSt) -> String:
  match st:
    case ZSt{a, b, acc, k}:
      show("misaligned", g, 1, U32.from_nat(Nat.sub(t3, t2)), CU.leaves(a), CU.leaves(b), ",\"lockstep_aligned_before\":" ++ Bool.show(k0) ++ ",\"aligned_after\":" ++ Bool.show(k) ++ ",\"lockstep_ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"realign_ms\":" ++ Nat.show(Nat.sub(t2, t1)))

def mis.c(+g: Nat, +t0: Nat, +t1: Nat, +t2: Nat, +k0: Bool, st: ZSt) -> IO(Unit):
  do IO<Unit>:
    t3 : Nat <- IO.now()
    IO.print(fin.mis(g, t0, t1, t2, t3, k0, st))

def mis.b(+g: Nat, +t0: Nat, +t1: Nat, +k0: Bool, a: S.CU, part: List<&2, U32>, b: S.CU) -> IO(Unit):
  do IO<Unit>:
    b2 : S.CU <- IO.pure(S.CU, Realign.k(part, S.UF(D(), b)))
    t2 : Nat <- IO.now()
    st : ZSt <- IO.pure(ZSt, Zip.rep(1n, ZSt{a, b2, 0, True{}}))
    mis.c(g, t0, t1, t2, k0, st)

def mis.a(+g: Nat, +t0: Nat, part: List<&2, U32>, zt: ZT) -> IO(Unit):
  match zt:
    case ZT{out, a, b, k}:
      do IO<Unit>:
        t1 : Nat <- IO.now()
        mis.b(g, t0, t1, k, a, part, b)

# misaligned: A at grain g, B at grain g-1 (same rows); the lockstep zip reports aligned=false (an O(shape)
# walk); then B is re-cut to A's partition (read off a third tree built like A) and the zip runs aligned
def run.misaligned(+g: Nat, a: S.CU, b: S.CU, part: List<&2, U32>) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    zt : ZT <- IO.pure(ZT, ZipT(a, b))
    mis.a(g, t0, part, zt)

def fin.rc(+g: Nat, +reps: U32, +t0: Nat, +t1: Nat, +before: U32, st: RSt) -> String:
  match st:
    case RSt{t, acc}:
      show("rechunk", g, reps, U32.from_nat(Nat.sub(t1, t0)), before, CU.leaves(t), ",\"acc\":" ++ U32.show(acc))

def rc.k(+g: Nat, +reps: U32, +before: U32, t: S.CU) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    st : RSt <- IO.pure(RSt, RC.rep(U32.to_nat(reps), g, RSt{t, 0}))
    t1 : Nat <- IO.now()
    IO.print(fin.rc(g, reps, t0, t1, before, st))

# rechunk: the filtered id tree (ragged) merged bottom-up; check_k = leaves before, check_s = leaves after
def run.rechunk(+g: Nat, +reps: U32, r: S.CU & S.CU) -> IO(Unit):
  (a, b) = r
  rc.k(g, reps, CU.leaves(b), a)

def chunk7.k(r: S.Flat & S.Chunked) -> S.Chunked:
  (f, c) = r
  c

def chunk7(+k: Nat, +g: Nat, f: S.Flat) -> S.Chunked:
  chunk7.k(S.Flat.chunk(k, g, f))

def dispatch(+mode: String, +g: Nat, +reps: U32, f: S.Flat) -> IO(Unit):
  match mode:
    case "ragged":
      run.ragged(g, reps, Ragged(chunk7(Nat.sub(D(), g), g, f)))
    case "concat":
      run.concat(g, reps, Ragged(chunk7(Nat.sub(D(), g), g, f)), Ragged(chunk7(Nat.sub(D(), g), g, S.Flat.gen(D()))))
    case "rechunk":
      run.rechunk(g, reps, Ragged(chunk7(Nat.sub(D(), g), g, f)))
    case _:
      run.misaligned(g, chunk1(S.UB(Nat.sub(D(), g), g, K.Kernel.iota(U32.shln(1, D()), D()))), chunk1(S.UB(Nat.sub(D(), Nat.sub(g, 1n)), Nat.sub(g, 1n), K.Kernel.iota(U32.shln(1, D()), D()))), Part(chunk1(S.UB(Nat.sub(D(), g), g, K.Kernel.iota(U32.shln(1, D()), D())))))

def go(args: List<String>) -> IO(Unit):
  match args:
    case exe <> mode <> g <> reps <> Nil{}:
      dispatch(mode, S.nat_of(g, 14n), U32.from_nat(S.nat_of(reps, 10n)), S.Flat.gen(D()))
    case _:
      IO.print("usage: s2 <ragged|concat|misaligned|rechunk> <grain_log2> <reps>")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
