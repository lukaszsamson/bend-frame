# W0 spike T3 (disposable): parallel string coding with OWNED HASH PARTITIONS, against the
# sequential borrowed coder (coder.bend Hc.code). Same output: first-appearance ids identical.
#   ~/.bend/bin/bend bench/spikes/w0_strings/probe.bend -o bench/spikes/w0_strings/build/probe
#   ./build/probe [--threads N] <shape> <n> <seq|part> [L]
# part, 2^L partitions:
#  1. hashes: a balanced fork over the ANode spine of the rows (L levels; matching ANode copies the
#     pointer blocks down and up: measured, the string walk dominates)
#  2. partition id = top L bits of h * 2246822519 (independent of the table's slot bits, which use
#     h * 2654435769): one stable Radix.sort of the ids gives the rows grouped by partition, in
#     row order inside each partition
#  3. sequential: each partition's rows MOVED (Array.swap) out of the column into its own arrays
#     (strings, hashes, global rows): no string is copied or shared
#  4. ONE fork over the partition tree: each lane codes its own rows with its own presized table
#     (local first-appearance ids, the global first row of each local entry)
#  5. sequential: global first-appearance order from the entries' first rows (one flat scan over
#     the rows), codes scattered back to row order, strings moved back into the column
# stdout: one JSON line with every phase's ms and the codes' checksum.
import Base
import ./../../../src/kernels.bend as K
import ./../../../src/strs.bend as ST
import ./../../../src/sort.bend as SO
import ./coder.bend as C

# ---- 1. hashes -----------------------------------------------------------------------------------

type HP is Type:
  HP{a: Array<String>, h: Array<U32>}

def Hp.flat.go(f: Nat, +i: U32, h: Array<U32>, r: Array<String> & String) -> HP:
  match f:
    case 0n:
      (a, s) = r
      HP{a, h}
    case 1n+p:
      (a, s) = r
      +j = U32.inc(i)
      Hp.flat.go(p, j, Array.set(U32, h, i, ST.Str.hash(s)), Array.get(String, a, j))

def Hp.flat(+n: U32, +d: Nat, a: Array<String>) -> HP:
  Hp.flat.go(U32.to_nat(n), 0, Array.new(U32, d, 0), Array.get(String, a, 0))

def Hp.join(l: HP, r: HP) -> HP:
  match l r:
    case HP{a1, h1} HP{a2, h2}:
      HP{ANode{a1, a2}, ANode{h1, h2}}

def Hp.fork(f: Nat, +n: U32, +d: Nat, a: Array<String>) -> HP:
  match f a:
    case 0n a2:
      Hp.flat(n, d, a2)
    case 1n+p ALeaf{x}:
      Hp.flat(n, d, ALeaf{x})
    case 1n++p ANode{xs, ys}:
      +dr = Nat.sub(d, 1n)
      +nl = U32.min(n, U32.shln(1, dr))
      +nr = U32.sub(n, nl)
      l r = Hp.fork(p, nl, dr, xs) Hp.fork(p, nr, dr, ys)
      Hp.join(l, r)

# ---- 2. partition ids, rows grouped by partition ----------------------------------------------------

def Pt.id(+h: U32, +l: Nat) -> U32:
  U32.shrn(U32.mul(h, 2246822519), Nat.sub(32n, l))

def Pt.fst(r: Array<U32> & Array<U32>) -> Array<U32>:
  (a, b) = r
  a

def Pt.snd(r: Array<U32> & Array<U32>) -> Array<U32>:
  (a, b) = r
  b

# counts per partition (2^l of them)
def Pt.inc.k(+g: U32, r: Array<U32> & U32) -> Array<U32>:
  (c, +x) = r
  Array.set(U32, c, g, U32.inc(x))

def Pt.inc(+g: U32, c: Array<U32>) -> Array<U32>:
  Pt.inc.k(g, Array.get(U32, c, g))

def Pt.cnt.go(f: Nat, +i: U32, +l: Nat, cnt: Array<U32>, r: Array<U32> & U32) -> Array<U32> & Array<U32>:
  match f:
    case 0n:
      (h, x) = r
      (h, cnt)
    case 1n+p:
      (h, +x) = r
      +j = U32.inc(i)
      Pt.cnt.go(p, j, l, Pt.inc(Pt.id(x, l), cnt), Array.get(U32, h, j))

# ---- 3. partitions: rows moved out of the column ------------------------------------------------------

# one partition: m rows, their strings, hashes, global rows
type PL is Type:
  PL{m: U32, s: Array<String>, h: Array<U32>, rows: Array<U32>}

type MV is Type:
  MV{a: Array<String>, h: Array<U32>, perm: Array<U32>, s: Array<String>, hp: Array<U32>, rows: Array<U32>}

def Mv.s(+j: U32, +row: U32, perm: Array<U32>, s: Array<String>, hp: Array<U32>, rows: Array<U32>, rs: Array<String> & String, rh: Array<U32> & U32) -> MV:
  (a, x) = rs
  (h2, +hx) = rh
  MV{a, h2, perm, Array.set(String, s, j, x), Array.set(U32, hp, j, hx), Array.set(U32, rows, j, row)}

def Mv.r(+j: U32, a: Array<String>, h: Array<U32>, s: Array<String>, hp: Array<U32>, rows: Array<U32>, rp: Array<U32> & U32) -> MV:
  (perm, +row) = rp
  Mv.s(j, row, perm, s, hp, rows, Array.swap(String, a, row, ""), Array.get(U32, h, row))

def Mv.go(f: Nat, +j: U32, +off: U32, st: MV) -> MV:
  match f st:
    case 0n other:
      other
    case 1n+p MV{a, h, perm, s, hp, rows}:
      Mv.go(p, U32.inc(j), off, Mv.r(j, a, h, s, hp, rows, Array.get(U32, perm, U32.add(off, j))))

type PS is Type:
  PS{a: Array<String>, h: Array<U32>, perm: Array<U32>, off: U32, parts: List<&1, PL>}

def Ps.one.k(+m: U32, +off: U32, parts: List<&1, PL>, mv: MV) -> PS:
  match mv:
    case MV{a, h, perm, s, hp, rows}:
      PS{a, h, perm, U32.add(off, m), PL{m, s, hp, rows} <> parts}

def Ps.one(+m: U32, st: PS) -> PS:
  match st:
    case PS{a, h, perm, +off, parts}:
      +d = K.Kernel.depth_for(U32.max(m, 1))
      Ps.one.k(m, off, parts, Mv.go(U32.to_nat(m), 0, off, MV{a, h, perm, Array.new(String, d, ""), Array.new(U32, d, 0), Array.new(U32, d, 0)}))

def Ps.go(f: Nat, +g: U32, st: PS, rc: Array<U32> & U32) -> Array<U32> & PS:
  match f:
    case 0n:
      (cnt, m) = rc
      (cnt, st)
    case 1n+p:
      (cnt, +m) = rc
      +j = U32.inc(g)
      Ps.go(p, j, Ps.one(m, st), Array.get(U32, cnt, j))

# ---- 4. the lanes ----------------------------------------------------------------------------------

# a lane's coder state: the table, local codes, local entries' first global rows
type LC is Type:
  LC{next: U32, s: Array<String>, h: Array<U32>, rows: Array<U32>, hs: Array<U32>, rp: Array<U32>, ids: Array<U32>, out: Array<U32>, fr: Array<U32>}

def Lc.put(+hh: U32, +i: U32, +next: U32, h: Array<U32>, rows: Array<U32>, out: Array<U32>, fr: Array<U32>, lk: C.LK) -> LC:
  match lk:
    case C.LK{s, hs, rp, ids, more, True{}, id, +j}:
      LC{U32.inc(next), s, h, rows, Array.set(U32, hs, j, hh), Array.set(U32, rp, j, U32.inc(i)), Array.set(U32, ids, j, next), Array.set(U32, out, i, next), Array.set(U32, fr, next, i)}
    case C.LK{s, hs, rp, ids, more, False{}, +id, j}:
      LC{next, s, h, rows, hs, rp, ids, Array.set(U32, out, i, id), fr}

def Lc.row.s(+i: U32, +b: Nat, +mask: U32, +fuel: Nat, +next: U32, +hh: U32, h: Array<U32>, rows: Array<U32>, hs: Array<U32>, rp: Array<U32>, ids: Array<U32>, out: Array<U32>, fr: Array<U32>, r: Array<String> & String) -> LC:
  (s, +x) = r
  Lc.put(hh, i, next, h, rows, out, fr, C.Hc.seek(fuel, C.Hc.look(hh, C.Hc.slot(hh, b), x, s, hs, rp, ids), hh, x, mask))

def Lc.row.h(+i: U32, +b: Nat, +mask: U32, +fuel: Nat, +next: U32, s: Array<String>, rows: Array<U32>, hs: Array<U32>, rp: Array<U32>, ids: Array<U32>, out: Array<U32>, fr: Array<U32>, rh: Array<U32> & U32) -> LC:
  (h, +hh) = rh
  Lc.row.s(i, b, mask, fuel, next, hh, h, rows, hs, rp, ids, out, fr, Array.get(String, s, i))

def Lc.go(f: Nat, +i: U32, +b: Nat, +mask: U32, +fuel: Nat, st: LC) -> LC:
  match f st:
    case 0n other:
      other
    case 1n+p LC{+next, s, h, rows, hs, rp, ids, out, fr}:
      Lc.go(p, U32.inc(i), b, mask, fuel, Lc.row.h(i, b, mask, fuel, next, s, rows, hs, rp, ids, out, fr, Array.get(U32, h, i)))

# a coded partition: rows, entries, strings and global rows back, local codes, first rows (local)
type LO is Type:
  LO{m: U32, k: U32, s: Array<String>, rows: Array<U32>, out: Array<U32>, fr: Array<U32>}

def Lc.fin(+m: U32, st: LC) -> LO:
  match st:
    case LC{+k, s, h, rows, hs, rp, ids, out, fr}:
      LO{m, k, s, rows, out, fr}

def Lc.code(p: PL) -> LO:
  match p:
    case PL{+m, s, h, rows}:
      +b = K.Kernel.depth_for(U32.max(U32.add(m, m), 2))
      +size = U32.shln(1, b)
      +d = K.Kernel.depth_for(U32.max(m, 1))
      Lc.fin(m, Lc.go(U32.to_nat(m), 0, b, U32.sub(size, 1), U32.to_nat(size), LC{0, s, h, rows, Array.new(U32, b, 0), Array.new(U32, b, 0), Array.new(U32, b, 0), Array.new(U32, d, 0), Array.new(U32, d, 0)}))

type PT is Type:
  PE{}
  PLf{p: PL}
  PN{l: PT, r: PT}

type OT is Type:
  OE{}
  OL{o: LO}
  ON{l: OT, r: OT}

def Pt.tree(t: PT) -> OT:
  match t:
    case PE{}:
      OE{}
    case PLf{p}:
      OL{Lc.code(p)}
    case PN{l, r}:
      a b = Pt.tree(l) Pt.tree(r)
      ON{a, b}

def Pt.leaves(xs: List<&1, PL>, acc: List<&1, PT>) -> List<&1, PT>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      Pt.leaves(t, PLf{h} <> acc)

def Pt.pair(xs: List<&1, PT>) -> List<&1, PT>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{a, Nil{}}:
      a <> Nil{}
    case Con{a, Con{b, u}}:
      PN{a, b} <> Pt.pair(u)

def Pt.top(f: Nat, xs: List<&1, PT>) -> PT:
  match f xs:
    case _ Nil{}:
      PE{}
    case _ Con{a, Nil{}}:
      a
    case 0n other:
      PE{}
    case 1n+p other:
      Pt.top(p, Pt.pair(other))

def Ot.list(t: OT, acc: List<&1, LO>) -> List<&1, LO>:
  match t:
    case OE{}:
      acc
    case OL{o}:
      o <> acc
    case ON{l, r}:
      Ot.list(l, Ot.list(r, acc))

# ---- 5. global first-appearance order, assembly ----------------------------------------------------------

# F[global first row] = koff + e + 1 for every local entry e
type GF is Type:
  GF{fr: Array<U32>, rows: Array<U32>, ff: Array<U32>}

def Gf.step.k(+e: U32, +koff: U32, fr: Array<U32>, ff: Array<U32>, r: Array<U32> & U32) -> GF:
  (rows, +g) = r
  GF{fr, rows, Array.set(U32, ff, g, U32.add(U32.add(koff, e), 1))}

def Gf.step.r(+e: U32, +koff: U32, rows: Array<U32>, ff: Array<U32>, r: Array<U32> & U32) -> GF:
  (fr, +li) = r
  Gf.step.k(e, koff, fr, ff, Array.get(U32, rows, li))

def Gf.step(+e: U32, +koff: U32, st: GF) -> GF:
  match st:
    case GF{fr, rows, ff}:
      Gf.step.r(e, koff, rows, ff, Array.get(U32, fr, e))

def Gf.go(f: Nat, +e: U32, +koff: U32, st: GF) -> GF:
  match f:
    case 0n:
      st
    case 1n+p:
      Gf.go(p, U32.inc(e), koff, Gf.step(e, koff, st))

type GA is Type:
  GA{koff: U32, ff: Array<U32>, los: List<&1, LO>}

def Ga.one.k(+m: U32, +k: U32, +koff: U32, s: Array<String>, out: Array<U32>, los: List<&1, LO>, g: GF) -> GA:
  match g:
    case GF{fr, rows, ff}:
      GA{U32.add(koff, k), ff, LO{m, k, s, rows, out, fr} <> los}

def Ga.one(x: LO, st: GA) -> GA:
  match x st:
    case LO{+m, +k, s, rows, out, fr} GA{+koff, ff, los}:
      Ga.one.k(m, k, koff, s, out, los, Gf.go(U32.to_nat(k), 0, koff, GF{fr, rows, ff}))

def Ga.go(xs: List<&1, LO>, st: GA) -> GA:
  match xs:
    case Nil{}:
      st
    case h <> t:
      Ga.go(t, Ga.one(h, st))

# newid[F[r] - 1] = next++ for rows in order with F[r] != 0
def Nw.put(isf: Bool, +x: U32, +next: U32, nw: Array<U32>) -> Array<U32>:
  match isf:
    case True{}:
      Array.set(U32, nw, U32.sub(x, 1), next)
    case False{}:
      nw

def Nw.go(f: Nat, +r: U32, +next: U32, nw: Array<U32>, rf: Array<U32> & U32) -> Array<U32> & U32:
  match f:
    case 0n:
      (ff, x) = rf
      (nw, next)
    case 1n+p:
      (ff, +x) = rf
      +isf = U32.is_ne(x, 0)
      Nw.go(p, U32.inc(r), U32.add(next, Bool.to_u32(isf)), Nw.put(isf, x, next, nw), Array.get(U32, ff, U32.inc(r)))

# codes and strings back to row order (the lanes in their order, koff the entry offset)
type AS is Type:
  AS{koff: U32, a: Array<String>, nw: Array<U32>, out: Array<U32>}

def As.row.n(+g: U32, +k0: U32, s: Array<String>, rows: Array<U32>, lo: Array<U32>, a: Array<String>, out: Array<U32>, r: Array<U32> & U32) -> Array<String> & Array<U32> & Array<U32> & AS:
  (nw, +c) = r
  (s, rows, lo, AS{k0, a, nw, Array.set(U32, out, g, c)})

def As.row.k(+j: U32, +koff: U32, +k0: U32, a: Array<String>, nw: Array<U32>, out: Array<U32>, rs: Array<String> & String, rr: Array<U32> & U32, rl: Array<U32> & U32) -> Array<String> & Array<U32> & Array<U32> & AS:
  (s, x) = rs
  (rows, +g) = rr
  (lo, +lc) = rl
  As.row.n(g, k0, s, rows, lo, Array.set(String, a, g, x), out, Array.get(U32, nw, U32.add(koff, lc)))

def As.row(+j: U32, +koff: U32, s: Array<String>, rows: Array<U32>, lo: Array<U32>, st: AS) -> Array<String> & Array<U32> & Array<U32> & AS:
  match st:
    case AS{k0, a, nw, out}:
      As.row.k(j, koff, k0, a, nw, out, Array.swap(String, s, j, ""), Array.get(U32, rows, j), Array.get(U32, lo, j))

def As.go(f: Nat, +j: U32, +koff: U32, r: Array<String> & Array<U32> & Array<U32> & AS) -> AS:
  match f:
    case 0n:
      (s, rows, lo, st) = r
      st
    case 1n+p:
      (s, rows, lo, st) = r
      As.go(p, U32.inc(j), koff, As.row(j, koff, s, rows, lo, st))

def As.one.k(+k: U32, st: AS) -> AS:
  match st:
    case AS{+koff, a, nw, out}:
      AS{U32.add(koff, k), a, nw, out}

def As.one(x: LO, st: AS) -> AS:
  match x st:
    case LO{+m, +k, s, rows, out, fr} AS{+koff, a, nw, o}:
      As.one.k(k, As.go(U32.to_nat(m), 0, koff, (s, rows, out, AS{koff, a, nw, o})))

def As.lanes(xs: List<&1, LO>, st: AS) -> AS:
  match xs:
    case Nil{}:
      st
    case h <> t:
      As.lanes(t, As.one(h, st))

# ---- drivers --------------------------------------------------------------------------------------------

def out.p(+n: U32, +k: U32, +l: Nat, +t0: Nat, +t1: Nat, +t2: Nat, +t3: Nat, +t4: Nat, +shape: String, a: Array<String>, r: Array<U32> & U32) -> IO(Unit):
  (o, +x) = r
  IO.print("{\"spike\":\"probe\",\"mode\":\"part\",\"L\":" ++ Nat.show(l) ++ ",\"shape\":\"" ++ shape ++ "\",\"n\":" ++ U32.show(n) ++ ",\"k\":" ++ U32.show(k) ++ ",\"hash_ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"part_ms\":" ++ Nat.show(Nat.sub(t2, t1)) ++ ",\"lanes_ms\":" ++ Nat.show(Nat.sub(t3, t2)) ++ ",\"assemble_ms\":" ++ Nat.show(Nat.sub(t4, t3)) ++ ",\"ms\":" ++ Nat.show(Nat.sub(t4, t0)) ++ C.keep(a) ++ ",\"chk\":" ++ U32.show(x) ++ "}")

def run.as(+n: U32, +k: U32, +l: Nat, +t0: Nat, +t1: Nat, +t2: Nat, +t3: Nat, +shape: String, st: AS) -> IO(Unit):
  match st:
    case AS{koff, a, nw, o}:
      do IO<Unit>:
        t4 : Nat <- IO.now()
        out.p(n, k, l, t0, t1, t2, t3, t4, shape, a, C.chk(n, o))

def run.nw(+n: U32, +d: Nat, +l: Nat, +t0: Nat, +t1: Nat, +t2: Nat, +t3: Nat, +shape: String, a: Array<String>, los: List<&1, LO>, r: Array<U32> & U32) -> IO(Unit):
  (nw, +k) = r
  run.as(n, k, l, t0, t1, t2, t3, shape, As.lanes(los, AS{0, a, nw, Array.new(U32, d, 0)}))

def run.ga(+n: U32, +d: Nat, +l: Nat, +t0: Nat, +t1: Nat, +t2: Nat, +t3: Nat, +shape: String, a: Array<String>, ga: GA) -> IO(Unit):
  match ga:
    case GA{+k, ff, los}:
      run.nw(n, d, l, t0, t1, t2, t3, shape, a, List.reverse(&1, LO, los), Nw.go(U32.to_nat(n), 0, 0, Array.new(U32, K.Kernel.depth_for(U32.max(k, 1)), 0), Array.get(U32, ff, 0)))

def run.lanes(+n: U32, +d: Nat, +l: Nat, +t0: Nat, +t1: Nat, +t2: Nat, +shape: String, a: Array<String>, los: List<&1, LO>) -> IO(Unit):
  do IO<Unit>:
    t3 : Nat <- IO.now()
    run.ga(n, d, l, t0, t1, t2, t3, shape, a, Ga.go(los, GA{0, Array.new(U32, d, 0), Nil{}}))

def run.parts(+n: U32, +d: Nat, +l: Nat, +t0: Nat, +t1: Nat, +shape: String, r: Array<U32> & PS) -> IO(Unit):
  (cnt, ps) = r
  match ps:
    case PS{a, h, perm, off, parts}:
      do IO<Unit>:
        t2 : Nat <- IO.now()
        run.lanes(n, d, l, t0, t1, t2, shape, a, Ot.list(Pt.tree(Pt.top(32n, Pt.leaves(parts, Nil{}))), Nil{}))

def run.sorted(+n: U32, +d: Nat, +l: Nat, +t0: Nat, +t1: Nat, +shape: String, a: Array<String>, h: Array<U32>, cnt: Array<U32>, r: Array<U32> & Array<U32>) -> IO(Unit):
  (ws, perm) = r
  run.parts(n, d, l, t0, t1, shape, Ps.go(U32.to_nat(U32.shln(1, l)), 0, PS{a, h, perm, 0, Nil{}}, Array.get(U32, cnt, 0)))

def run.cnt(+n: U32, +d: Nat, +l: Nat, +t0: Nat, +t1: Nat, +shape: String, a: Array<String>, ws: Array<U32>, r: Array<U32> & Array<U32>) -> IO(Unit):
  (h, cnt) = r
  run.sorted(n, d, l, t0, t1, shape, a, h, cnt, SO.Radix.sort(n, d, (ws, K.Kernel.iota(n, d))))

def run.ids(+n: U32, +d: Nat, +l: Nat, +t0: Nat, +t1: Nat, +shape: String, a: Array<String>, r: Array<U32> & Array<U32>) -> IO(Unit):
  (h2, ws) = r
  run.cnt(n, d, l, t0, t1, shape, a, ws, Pt.cnt.go(U32.to_nat(n), 0, l, Array.new(U32, l, 0), Array.get(U32, h2, 0)))

def Pt.map.go(f: Nat, +i: U32, +l: Nat, ws: Array<U32>, r: Array<U32> & U32) -> Array<U32> & Array<U32>:
  match f:
    case 0n:
      (h, x) = r
      (h, ws)
    case 1n+p:
      (h, +x) = r
      +j = U32.inc(i)
      Pt.map.go(p, j, l, Array.set(U32, ws, i, Pt.id(x, l)), Array.get(U32, h, j))

def run.hashed(+n: U32, +d: Nat, +l: Nat, +t0: Nat, +shape: String, hp: HP) -> IO(Unit):
  match hp:
    case HP{a, h}:
      do IO<Unit>:
        t1 : Nat <- IO.now()
        run.ids(n, d, l, t0, t1, shape, a, Pt.map.go(U32.to_nat(n), 0, l, Array.new(U32, d, 0), Array.get(U32, h, 0)))

def run.seq.out(+n: U32, +k: U32, +t0: Nat, +t1: Nat, +shape: String, a: Array<String>, r: Array<U32> & U32) -> IO(Unit):
  (o, +x) = r
  IO.print("{\"spike\":\"probe\",\"mode\":\"seq\",\"shape\":\"" ++ shape ++ "\",\"n\":" ++ U32.show(n) ++ ",\"k\":" ++ U32.show(k) ++ ",\"ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ C.keep(a) ++ ",\"chk\":" ++ U32.show(x) ++ "}")

def run.seq(+n: U32, +t0: Nat, +shape: String, st: C.HS) -> IO(Unit):
  match st:
    case C.HS{+k, a, hs, rp, ids, out, fr}:
      do IO<Unit>:
        t1 : Nat <- IO.now()
        run.seq.out(n, k, t0, t1, shape, a, C.chk(n, out))

def run.mode(seq: Bool, +n: U32, +d: Nat, +l: Nat, +t0: Nat, +shape: String, a: Array<String>) -> IO(Unit):
  match seq:
    case True{}:
      run.seq(n, t0, shape, C.Hc.code(n, d, 0, a))
    case False{}:
      run.hashed(n, d, l, t0, shape, Hp.fork(l, n, d, a))

def run.go(+mode: String, +shape: String, +n: U32, +d: Nat, +l: Nat, r: Array<String> & U32) -> IO(Unit):
  (a, chars) = r
  do IO<Unit>:
    t0 : Nat <- IO.now()
    run.mode(String.eq(mode, "seq"), n, d, l, t0, shape, a)

def run(+shape: String, +n: U32, +mode: String, +l: Nat) -> IO(Unit):
  +d = K.Kernel.depth_for(n)
  run.go(mode, shape, n, d, l, K.Kernel.fold(~String, ~U32, ~(acc => s => U32.add(acc, C.Str.len(s, 0))), n, C.Gen.go(U32.to_nat(n), 0, C.shape_of(shape), Array.new(String, d, "")), 0))

def go(+xs: List<&2, String>) -> IO(Unit):
  run(C.nth(0n, xs, "distinct"), C.num(U32.read(C.nth(1n, xs, "1000"))), C.nth(2n, xs, "part"), U32.to_nat(C.num(U32.read(C.nth(3n, xs, "4")))))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(List.tail(&2, String, C.promote(args)))

