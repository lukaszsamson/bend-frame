# S4 (W0 engine spike, disposable): ownership.
#
# Modes (build/s4 --threads 1 <mode> <reps>), 2^20 rows, 7-column frame from src/column.bend:
#   colclone   today's ICol: C.Frame.get_cloned (an O(n) Column.clone per column reference) vs
#   colmove    borrow-and-return: C.Frame.take then C.Frame.replace (O(columns) list work, no copy)
#   mapfresh   Kernel.map into a fresh output (Array.new + write) vs
#   mapinplace the same map written into the dead operand's own buffer (Array.set on the input)
#   nsboxed    the group F32 sum as a scatter over Array<K.NS> (a boxed record per group, rebuilt per row) vs
#   nsflat     the same Neumaier step over two Array<F32> (s and c): no per-row allocation
# Each prints ms per `reps` and a checksum (the pairs must agree). Build/run:
#   ~/.bend/bin/bend bench/spikes/w0_engine/s4_owner.bend -o build/s4 && build/s4 --threads 1 colclone 64
import Base
import ./../../../src/dtype.bend as D
import ./../../../src/err.bend as E
import ./../../../src/kernels.bend as K
import ./../../../src/column.bend as C
import ./s1_chunks.bend as S

# ---- the frame ------------------------------------------------------------------------------------------

def col.u(+d: Nat, a: Array<U32>) -> C.Column:
  C.CU32{U32.shln(1, d), d, C.AllValid{}, a}

def col.f(+d: Nat, a: Array<F32>) -> C.Column:
  C.CF32{U32.shln(1, d), d, C.AllValid{}, a}

def frame.gen(+d: Nat) -> C.Frame:
  C.Frame{U32.shln(1, d), [C.Named{"ok", col.u(d, S.GenU(~(i => S.Gen.ok(i)), d))}, C.Named{"qty", col.u(d, S.GenU(~(i => S.Gen.qty(i)), d))}, C.Named{"id", col.u(d, K.Kernel.iota(U32.shln(1, d), d))}, C.Named{"region", col.u(d, S.GenU(~(i => S.Gen.rg(i)), d))}, C.Named{"vd", col.u(d, S.GenU(~(i => S.Gen.vdisc(i)), d))}, C.Named{"price", col.f(d, S.GenF(~(i => S.Gen.price(i)), d))}, C.Named{"disc", col.f(d, S.GenF(~(i => S.Gen.disc(i)), d))}]}

# a cheap "use" of the referenced column (its length); the column comes back
def peek(c: C.Column) -> C.Column & U32:
  C.Column.len(c)

# ---- colclone: get_cloned per reference ---------------------------------------------------------------

type FSt is Type:
  FSt{f: C.Frame, acc: U32}

def clone.k2(f: C.Frame, +acc: U32, r: C.Column & U32) -> FSt:
  (c, w) = r
  FSt{f, U32.add(acc, w)}

def clone.k(+acc: U32, r: C.Frame & E.ResT(C.Column)) -> FSt:
  (f, rc) = r
  match rc:
    case Fail{e}:
      FSt{f, acc}
    case Done{c}:
      clone.k2(f, acc, peek(c))

def clone.rep(reps: Nat, st: FSt) -> FSt:
  match reps st:
    case 0n FSt{f, acc}:
      FSt{f, acc}
    case 1n+p FSt{f, acc}:
      clone.rep(p, clone.k(acc, C.Frame.get_cloned(f, "price")))

# ---- colmove: take, use, put back ------------------------------------------------------------------------

def move.k3(+acc: U32, r: E.ResT(C.Frame)) -> FSt:
  match r:
    case Fail{e}:
      FSt{C.Frame.empty(), acc}
    case Done{f}:
      FSt{f, acc}

def move.k2(f: C.Frame, +acc: U32, r: C.Column & U32) -> FSt:
  (c, w) = r
  move.k3(U32.add(acc, w), C.Frame.replace(f, "price", c))

def move.k(+acc: U32, r: C.Frame & Maybe<&1, C.Column>) -> FSt:
  (f, m) = r
  match m:
    case None{}:
      FSt{f, acc}
    case Some{c}:
      move.k2(f, acc, peek(c))

def move.rep(reps: Nat, st: FSt) -> FSt:
  match reps st:
    case 0n FSt{f, acc}:
      FSt{f, acc}
    case 1n+p FSt{f, acc}:
      move.rep(p, move.k(acc, C.Frame.take(f, "price")))

# ---- mapfresh / mapinplace -------------------------------------------------------------------------------

def inc.go(n: Nat, +i: U32, r: Array<U32> & U32) -> Array<U32>:
  match n:
    case 0n:
      (a, x) = r
      a
    case 1n+p:
      (a, x) = r
      +j = U32.inc(i)
      inc.go(p, j, Array.get(U32, Array.set(U32, a, i, U32.add(x, 1)), j))

def inc.inplace(+n: U32, a: Array<U32>) -> Array<U32>:
  inc.go(U32.to_nat(n), 0, Array.get(U32, a, 0))

def inc.fresh(+n: U32, +d: Nat, a: Array<U32>) -> Array<U32>:
  K.Kernel.map(~U32, ~U32, ~(x => U32.add(x, 1)), n, d, a, 0)

type ASt is Type:
  ASt{a: Array<U32>, acc: U32}

def map.rep(reps: Nat, inplace: Bool, +n: U32, +d: Nat, st: ASt) -> ASt:
  match reps inplace st:
    case 0n _ ASt{a, acc}:
      ASt{a, acc}
    case 1n+p True{} ASt{a, acc}:
      map.rep(p, True{}, n, d, ASt{inc.inplace(n, a), U32.inc(acc)})
    case 1n+p False{} ASt{a, acc}:
      map.rep(p, False{}, n, d, ASt{inc.fresh(n, d, a), U32.inc(acc)})

# ---- nsboxed / nsflat ----------------------------------------------------------------------------------------

def nsb.put(+g: U32, +x: F32, r: Array<K.NS> & K.NS) -> Array<K.NS>:
  (acc, old) = r
  Array.set(K.NS, acc, g, K.Kernel.nm.step(old, x))

def nsb.go(n: Nat, +i: U32, acc: Array<K.NS>, rg: Array<U32> & U32, rv: Array<F32> & F32) -> Array<K.NS> & Array<U32> & Array<F32>:
  match n:
    case 0n:
      (gs, g) = rg
      (vs, x) = rv
      (acc, gs, vs)
    case 1n+p:
      (gs, +g) = rg
      (vs, x) = rv
      +j = U32.inc(i)
      nsb.go(p, j, nsb.put(g, x, Array.get(K.NS, acc, g)), Array.get(U32, gs, j), Array.get(F32, vs, j))

def nsb.fin(r: Array<K.NS> & K.NS) -> U32:
  (acc, s) = r
  F32.bits(K.Kernel.nm.fin(s))

def nsb.k(r: Array<K.NS> & Array<U32> & Array<F32>) -> Array<U32> & Array<F32> & U32:
  (acc, gs, vs) = r
  (gs, vs, nsb.fin(Array.get(K.NS, acc, 1)))

def nsb(+n: U32, gs: Array<U32>, vs: Array<F32>) -> Array<U32> & Array<F32> & U32:
  nsb.k(nsb.go(U32.to_nat(n), 0, Array.new(K.NS, 3n, K.NS{0.0, 0.0}), Array.get(U32, gs, 0), Array.get(F32, vs, 0)))

# the same step over two F32 arrays: s[g], c[g]; nothing boxed per row
def nsf.put2(+g: U32, +x: F32, +s: F32, ss: Array<F32>, rc: Array<F32> & F32) -> Array<F32> & Array<F32>:
  (cs, c) = rc
  +t = F32.add(s, x)
  (Array.set(F32, ss, g, t), Array.set(F32, cs, g, K.Kernel.nm.c(K.Kernel.is_finite(t), s, x, t, c)))

def nsf.put(+g: U32, +x: F32, cs: Array<F32>, rs: Array<F32> & F32) -> Array<F32> & Array<F32>:
  (ss, s) = rs
  nsf.put2(g, x, s, ss, Array.get(F32, cs, g))

def nsf.go(n: Nat, +i: U32, sc: Array<F32> & Array<F32>, rg: Array<U32> & U32, rv: Array<F32> & F32) -> Array<F32> & Array<F32> & Array<U32> & Array<F32>:
  match n:
    case 0n:
      (ss, cs) = sc
      (gs, g) = rg
      (vs, x) = rv
      (ss, cs, gs, vs)
    case 1n+p:
      (ss, cs) = sc
      (gs, +g) = rg
      (vs, x) = rv
      +j = U32.inc(i)
      nsf.go(p, j, nsf.put(g, x, cs, Array.get(F32, ss, g)), Array.get(U32, gs, j), Array.get(F32, vs, j))

def nsf.fin2(+s: F32, r: Array<F32> & F32) -> U32:
  (cs, c) = r
  F32.bits(K.Kernel.nm.result(s, c))

def nsf.fin(cs: Array<F32>, r: Array<F32> & F32) -> U32:
  (ss, s) = r
  nsf.fin2(s, Array.get(F32, cs, 1))

def nsf.k(r: Array<F32> & Array<F32> & Array<U32> & Array<F32>) -> Array<U32> & Array<F32> & U32:
  (ss, cs, gs, vs) = r
  (gs, vs, nsf.fin(cs, Array.get(F32, ss, 1)))

def nsf(+n: U32, gs: Array<U32>, vs: Array<F32>) -> Array<U32> & Array<F32> & U32:
  nsf.k(nsf.go(U32.to_nat(n), 0, (Array.new(F32, 3n, 0.0), Array.new(F32, 3n, 0.0)), Array.get(U32, gs, 0), Array.get(F32, vs, 0)))

type NSt is Type:
  NSt{gs: Array<U32>, vs: Array<F32>, acc: U32}

def ns.step(+acc: U32, r: Array<U32> & Array<F32> & U32) -> NSt:
  (gs, vs, w) = r
  NSt{gs, vs, U32.add(acc, w)}

def ns.rep(reps: Nat, boxed: Bool, +n: U32, st: NSt) -> NSt:
  match reps boxed st:
    case 0n _ NSt{gs, vs, acc}:
      NSt{gs, vs, acc}
    case 1n+p True{} NSt{gs, vs, acc}:
      ns.rep(p, True{}, n, ns.step(acc, nsb(n, gs, vs)))
    case 1n+p False{} NSt{gs, vs, acc}:
      ns.rep(p, False{}, n, ns.step(acc, nsf(n, gs, vs)))

# ---- driver ---------------------------------------------------------------------------------------------------

def D() -> Nat:
  20n

def show(+mode: String, +reps: U32, +ms: U32, +k: U32) -> String:
  "{\"mode\":\"" ++ mode ++ "\",\"rows\":1048576,\"grain_log2\":20,\"reps\":" ++ U32.show(reps) ++ ",\"ms_total\":" ++ U32.show(ms) ++ ",\"check_k\":" ++ U32.show(k) ++ ",\"check_s\":0}"

def fin.f(+mode: String, +reps: U32, +t0: Nat, +t1: Nat, st: FSt) -> String:
  match st:
    case FSt{f, acc}:
      show(mode, reps, U32.from_nat(Nat.sub(t1, t0)), acc)

def run.col(+mode: String, clone: Bool, +reps: U32, f: C.Frame) -> IO(Unit):
  match clone:
    case True{}:
      do IO<Unit>:
        t0 : Nat <- IO.now()
        st : FSt <- IO.pure(FSt, clone.rep(U32.to_nat(reps), FSt{f, 0}))
        t1 : Nat <- IO.now()
        IO.print(fin.f(mode, reps, t0, t1, st))
    case False{}:
      do IO<Unit>:
        t0 : Nat <- IO.now()
        st : FSt <- IO.pure(FSt, move.rep(U32.to_nat(reps), FSt{f, 0}))
        t1 : Nat <- IO.now()
        IO.print(fin.f(mode, reps, t0, t1, st))

def fin.a(+mode: String, +reps: U32, +t0: Nat, +t1: Nat, st: ASt) -> String:
  match st:
    case ASt{a, acc}:
      show(mode, reps, U32.from_nat(Nat.sub(t1, t0)), U32.add(acc, S.Sum(1024, a)))

def run.map(+mode: String, inplace: Bool, +reps: U32) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    st : ASt <- IO.pure(ASt, map.rep(U32.to_nat(reps), inplace, U32.shln(1, D()), D(), ASt{K.Kernel.iota(U32.shln(1, D()), D()), 0}))
    t1 : Nat <- IO.now()
    IO.print(fin.a(mode, reps, t0, t1, st))

def fin.n(+mode: String, +reps: U32, +t0: Nat, +t1: Nat, st: NSt) -> String:
  match st:
    case NSt{gs, vs, acc}:
      show(mode, reps, U32.from_nat(Nat.sub(t1, t0)), acc)

def run.ns(+mode: String, boxed: Bool, +reps: U32) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    st : NSt <- IO.pure(NSt, ns.rep(U32.to_nat(reps), boxed, U32.shln(1, D()), NSt{S.GenU(~(i => S.Gen.rg(i)), D()), S.GenF(~(i => S.Gen.price(i)), D()), 0}))
    t1 : Nat <- IO.now()
    IO.print(fin.n(mode, reps, t0, t1, st))

def dispatch(+mode: String, +reps: U32) -> IO(Unit):
  match mode:
    case "colclone":
      run.col(mode, True{}, reps, frame.gen(D()))
    case "colmove":
      run.col(mode, False{}, reps, frame.gen(D()))
    case "mapfresh":
      run.map(mode, False{}, reps)
    case "mapinplace":
      run.map(mode, True{}, reps)
    case "nsboxed":
      run.ns(mode, True{}, reps)
    case _:
      run.ns("nsflat", False{}, reps)

def go(args: List<String>) -> IO(Unit):
  match args:
    case exe <> mode <> reps <> Nil{}:
      dispatch(mode, U32.from_nat(S.nat_of(reps, 10n)))
    case _:
      IO.print("usage: s4 <colclone|colmove|mapfresh|mapinplace|nsboxed|nsflat> <reps>")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
