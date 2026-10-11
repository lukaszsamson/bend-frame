# T5.2 probe (provisional numbers; plans/M_02.txt W5, DESIGN.md 16.3 / 16.4 / 16.8): the chunked kernel
# wrappers of src/ckernels.bend over 2^20-row chunk trees at grain 2^14 (64 leaves) against the flat fused
# kernels of src/kernels.bend (T4.1's q1 / q2 cells), and the in-situ measurement of the F32 in-order walk
# (DESIGN 16.4 OPEN ISSUE) against its flatten-then-fold fallback. Run at 1 / 4 / 12 threads.
#
#   q1flat     Kernel.pred_count (ok & qty > 50, AllValid: 1-slot ones) + Kernel.compact3 (id, region,
#              price into depth_for(kept + 1)): T4.1's q1fused, flat
#   q1chunk    CK.pc.ww over the trees (AllValid: CK.ones1) + CK.c3.wwf by the mask tree (per-leaf
#              compaction into each leaf's own capacity): one fork tree per wrapper, inputs borrowed
#   q2flat     Kernel.zipb (f32(qty) * price) + Kernel.map_pb (1.0 - discount) + Kernel.zip (product):
#              T4.1's q2fused, flat
#   q2chunk    the same three kernels as three wrapper walks (CK.zipb.wff, CK.mappb.ff, CK.zip.fff)
#   q2chunk1   the same three kernels chained per leaf in ONE tree walk (a local wrapper: F9's "fuse the
#              walks"), to price the fork tree per wrapper
#   q2nflat    q2 with a nullable discount (F2): Kernel.zipb, Kernel.zipv (1.0 as a 1-slot array,
#              discount with its mask), Kernel.zipv of the two temporaries (AllValid: 1-slot ones)
#   q2nchunk   the same as wrapper walks (CK.zipb.wff, CK.zipv.fff, CK.zipv.fff; 1-slot constant trees)
#   sumflat    Kernel.fold U32.add over the flat 1M words (borrowed)
#   sumchunk   CK.sum.w (per-leaf fold, U32.add at the nodes, one fork per node)
#   fsum cells (F32 Neumaier, row order; D4):
#     fclone   Array.clone of the flat price column (the baseline of the next one)
#     fsumflat fclone + Kernel.fsum (consuming: today's loop)
#     ffold    Kernel.fold with Kernel.nm.step over the flat column, borrowed (the same loop, no clone)
#     tclone   a leaf-by-leaf clone of the 64-leaf tree (the baseline of the next two)
#     twalk    tclone + CK.fsum.f (the in-order walk threading NS through f(r, f(l, acc)), consuming)
#     tflat    tclone + CK.fsumflat.f (flatten into one buffer, then Kernel.fsum)
#     twalkr   tclone + the RECURSIVE in-order walk (f(r, f(l, acc)) with Kernel.fold at each leaf: the W0
#              spike's shape, kept here to measure the anomaly; CK.fsum.f lists the leaves and folds them
#              in one tail loop instead)
#   gather cells (outputs built fresh from a flat permutation, perm[j] = (j * 2654435761) mod 2^20, a
#   bijection; the source tree consumed, so each rep clones it first):
#     gclone   tclone of the u32 tree (baseline)
#     gfused   gclone + CK.gather.w (flatten the source, gather each output leaf straight from it)
#     gflat    gclone + CK.gatherf.w (flatten, Kernel.gather into a flat buffer, then CW.of)
#
# The timed window runs `reps` repetitions (inputs come back each rep; a word of each output is kept as
# the data dependency); one untimed run after the clock prints a checksum the flat and chunked cells of a
# query must agree on (q1: kept rows + the wrapping sum of the compacted id, region and price bits; q2: the
# wrapping sum of the output's f32 bits; sums: the result's bits; gathers: the wrapping sum of the output).
#   ~/.bend/bin/bend bench/w5/ckernels.bend -o build/w5/ckernels && build/w5/ckernels --threads 12 q1chunk 40
#   python3 -I bench/w5/run_t52.py build/w5/ckernels bench/w5/results/t52.jsonl 5 40
import Base
import ./../../src/kernels.bend as K
import ./../../src/chunks.bend as CH
import ./../../src/ckernels.bend as KC

def D() -> Nat:
  20n

def N() -> U32:
  1048576

def G() -> Nat:
  14n

# ---- data (T4.1's generators) ---------------------------------------------------------------------

def Gen.ok(+i: U32) -> U32:
  Bool.to_u32(U32.is_gt(U32.mod(U32.mul(i, 7919), 13), 4))

def Gen.qty(+i: U32) -> U32:
  U32.mod(U32.mul(i, 2654435761), 100)

def Gen.rg(+i: U32) -> U32:
  U32.and(i, 7)

def Gen.price(+i: U32) -> F32:
  F32.div(U32.to_f32(U32.mod(U32.mul(i, 31), 1000)), 10.0)

def Gen.disc(+i: U32) -> F32:
  Bool.pick(F32, U32.is_zero(U32.mod(i, 10)), 0.0, F32.div(U32.to_f32(U32.mod(U32.mul(i, 17), 31)), 100.0))

def Gen.vdisc(+i: U32) -> U32:
  Bool.to_u32(U32.is_ne(U32.mod(i, 10), 0))

def Gen.perm(+i: U32) -> U32:
  U32.and(U32.mul(i, 2654435761), 1048575)

def GenU.go(~f: U32 -> U32, n: Nat, +i: U32, out: Array<U32>) -> Array<U32>:
  match n:
    case 0n:
      out
    case 1n+p:
      GenU.go(~f, p, U32.inc(i), Array.set(U32, out, i, f(i)))

def GenU(~f: U32 -> U32) -> Array<U32>:
  GenU.go(~f, U32.to_nat(N()), 0, Array.new(U32, D(), 0))

def GenF.go(~f: U32 -> F32, n: Nat, +i: U32, out: Array<F32>) -> Array<F32>:
  match n:
    case 0n:
      out
    case 1n+p:
      GenF.go(~f, p, U32.inc(i), Array.set(F32, out, i, f(i)))

def GenF(~f: U32 -> F32) -> Array<F32>:
  GenF.go(~f, U32.to_nat(N()), 0, Array.new(F32, D(), 0.0))

def tw(a: Array<U32>) -> CH.CW:
  CH.CW.of(N(), D(), G(), a)

def tf(a: Array<F32>) -> CH.CF:
  CH.CF.of(N(), D(), G(), a)

# a 1-slot constant leaf per leaf of the skeleton (an AllValid side / a literal operand, never written)

def fconst1(s: CH.Skel, +v: F32) -> CH.CF:
  match s:
    case CH.KLeaf{n}:
      CH.FL{n, 0n, Array.new(F32, 0n, v)}
    case CH.KNode{rows, lrows, l, r}:
      CH.FN{rows, lrows, fconst1(l, v), fconst1(r, v)}

def skel() -> CH.Skel:
  Pair.snd(CH.CW, CH.Skel, CH.CW.skel(tw(GenU(~(i => i)))))

# ---- checksums ------------------------------------------------------------------------------------

def Sum.go(n: Nat, +i: U32, +acc: U32, r: Array<U32> & U32) -> U32:
  match n:
    case 0n:
      acc
    case 1n+p:
      (a, x) = r
      +j = U32.inc(i)
      Sum.go(p, j, U32.add(acc, x), Array.get(U32, a, j))

def Sum(+n: U32, a: Array<U32>) -> U32:
  Sum.go(U32.to_nat(n), 0, 0, Array.get(U32, a, 0))

def SumB.go(n: Nat, +i: U32, +acc: U32, r: Array<F32> & F32) -> U32:
  match n:
    case 0n:
      acc
    case 1n+p:
      (a, x) = r
      +j = U32.inc(i)
      SumB.go(p, j, U32.add(acc, F32.bits(x)), Array.get(F32, a, j))

def SumB(+n: U32, a: Array<F32>) -> U32:
  SumB.go(U32.to_nat(n), 0, 0, Array.get(F32, a, 0))

def TSum.k(r: CH.CW & U32) -> U32:
  (t, +n) = r
  Sum(n, CH.CW.flatten(K.Kernel.depth_for(U32.max(n, 1)), t))

def TSum(t: CH.CW) -> U32:
  TSum.k(CH.CW.rows(t))

def TSumB.k(r: CH.CF & U32) -> U32:
  (t, +n) = r
  SumB(n, CH.CF.flatten(K.Kernel.depth_for(U32.max(n, 1)), t))

def TSumB(t: CH.CF) -> U32:
  TSumB.k(CH.CF.rows(t))

def firstb(r: CH.CF & F32) -> U32:
  (t, +x) = r
  F32.bits(x)

def first(a: Array<F32>) -> U32:
  F32.bits(Pair.snd(Array<F32>, F32, Array.get(F32, a, 0)))

# ---- q1 ------------------------------------------------------------------------------------------

type Q1F is Type:
  Q1F{ok: Array<U32>, qty: Array<U32>, id: Array<U32>, rg: Array<U32>, pr: Array<F32>, acc: U32}

def q1f.c(+acc: U32, ok: Array<U32>, qty: Array<U32>, r: K.C3<U32, U32, F32>) -> Q1F:
  match r:
    case K.C3{o1, o2, o3, m, a1, a2, a3, +k}:
      Q1F{ok, qty, a1, a2, a3, U32.add(acc, k)}

def q1f.p(+acc: U32, id: Array<U32>, rg: Array<U32>, pr: Array<F32>, r: K.PC<U32, U32>) -> Q1F:
  match r:
    case K.PC{m, +kept, ok, v1, qty, v2}:
      q1f.c(acc, ok, qty, K.Kernel.compact3(~U32, ~U32, ~F32, N(), K.Kernel.depth_for(U32.add(kept, 1)), m, id, rg, pr, 0, 0, 0.0))

def q1f.rep(f: Nat, st: Q1F) -> Q1F:
  match f st:
    case 0n Q1F{ok, qty, id, rg, pr, acc}:
      Q1F{ok, qty, id, rg, pr, acc}
    case 1n+p Q1F{ok, qty, id, rg, pr, +acc}:
      q1f.rep(p, q1f.p(acc, id, rg, pr, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), N(), D(), 50, ok, Array.new(U32, 0n, 1), qty, Array.new(U32, 0n, 1))))

def q1f.v2(r: K.C3<U32, U32, F32>) -> U32:
  match r:
    case K.C3{o1, o2, o3, m, a1, a2, a3, +k}:
      U32.add(k, U32.add(U32.add(Sum(k, o1), Sum(k, o2)), SumB(k, o3)))

def q1f.v1(id: Array<U32>, rg: Array<U32>, pr: Array<F32>, r: K.PC<U32, U32>) -> U32:
  match r:
    case K.PC{m, +kept, ok, v1, qty, v2}:
      q1f.v2(K.Kernel.compact3(~U32, ~U32, ~F32, N(), K.Kernel.depth_for(U32.add(kept, 1)), m, id, rg, pr, 0, 0, 0.0))

def q1f.check(st: Q1F) -> U32:
  match st:
    case Q1F{ok, qty, id, rg, pr, acc}:
      q1f.v1(id, rg, pr, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), N(), D(), 50, ok, Array.new(U32, 0n, 1), qty, Array.new(U32, 0n, 1)))

def q1f.new() -> Q1F:
  Q1F{GenU(~(i => Gen.ok(i))), GenU(~(i => Gen.qty(i))), K.Kernel.iota(N(), D()), GenU(~(i => Gen.rg(i))), GenF(~(i => Gen.price(i))), 0}

type Q1C is Type:
  Q1C{ok: CH.CW, v1: CH.CW, qty: CH.CW, v2: CH.CW, id: CH.CW, rg: CH.CW, pr: CH.CF, acc: U32}

def q1c.c(+acc: U32, ok: CH.CW, v1: CH.CW, qty: CH.CW, v2: CH.CW, r: KC.CC3<CH.CW, CH.CW, CH.CF>) -> Q1C:
  match r:
    case KC.CC3{o1, o2, o3, m, a1, a2, a3, +k}:
      Q1C{ok, v1, qty, v2, a1, a2, a3, U32.add(acc, k)}

def q1c.p(+acc: U32, id: CH.CW, rg: CH.CW, pr: CH.CF, r: KC.CPC<CH.CW, CH.CW>) -> Q1C:
  match r:
    case KC.CPC{m, kept, ok, v1, qty, v2}:
      q1c.c(acc, ok, v1, qty, v2, KC.CK.c3.wwf(m, id, rg, pr))

def q1c.rep(f: Nat, st: Q1C) -> Q1C:
  match f st:
    case 0n Q1C{ok, v1, qty, v2, id, rg, pr, acc}:
      Q1C{ok, v1, qty, v2, id, rg, pr, acc}
    case 1n+p Q1C{ok, v1, qty, v2, id, rg, pr, +acc}:
      q1c.rep(p, q1c.p(acc, id, rg, pr, KC.CK.pc.ww(~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), 50, ok, v1, qty, v2)))

def q1c.v2(r: KC.CC3<CH.CW, CH.CW, CH.CF>) -> U32:
  match r:
    case KC.CC3{o1, o2, o3, m, a1, a2, a3, +k}:
      U32.add(k, U32.add(U32.add(TSum(o1), TSum(o2)), TSumB(o3)))

def q1c.v1(id: CH.CW, rg: CH.CW, pr: CH.CF, r: KC.CPC<CH.CW, CH.CW>) -> U32:
  match r:
    case KC.CPC{m, kept, ok, v1, qty, v2}:
      q1c.v2(KC.CK.c3.wwf(m, id, rg, pr))

def q1c.check(st: Q1C) -> U32:
  match st:
    case Q1C{ok, v1, qty, v2, id, rg, pr, acc}:
      q1c.v1(id, rg, pr, KC.CK.pc.ww(~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), 50, ok, v1, qty, v2))

def q1c.new() -> Q1C:
  Q1C{tw(GenU(~(i => Gen.ok(i)))), KC.CK.ones1(skel()), tw(GenU(~(i => Gen.qty(i)))), KC.CK.ones1(skel()), tw(K.Kernel.iota(N(), D())), tw(GenU(~(i => Gen.rg(i)))), tf(GenF(~(i => Gen.price(i)))), 0}

# ---- q2 ------------------------------------------------------------------------------------------

type Q2F is Type:
  Q2F{qty: Array<U32>, pr: Array<F32>, ds: Array<F32>, vd: Array<U32>, acc: U32}

def q2f.out2(t: Array<F32>, r: Array<F32> & Array<F32>) -> Array<F32> & Array<F32>:
  (s, ds) = r
  (K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), N(), D(), t, s, 0.0), ds)

def q2f.out3(qty: Array<U32>, pr: Array<F32>, r: Array<F32> & Array<F32>) -> Q2F:
  (o, ds) = r
  Q2F{qty, pr, ds, Array.new(U32, 0n, 0), first(o)}

def q2f.out1(ds: Array<F32>, r: K.ZB<U32, F32, F32>) -> Q2F:
  match r:
    case K.ZB{t, qty, pr}:
      q2f.out3(qty, pr, q2f.out2(t, K.Kernel.map_pb(~F32, ~F32, ~F32, ~(p => x => F32.sub(p, x)), N(), D(), ds, 1.0, 0.0)))

def q2f.add(+acc: U32, vd: Array<U32>, st: Q2F) -> Q2F:
  match st:
    case Q2F{qty, pr, ds, v0, +x}:
      Q2F{qty, pr, ds, vd, U32.add(acc, x)}

def q2f.rep(f: Nat, st: Q2F) -> Q2F:
  match f st:
    case 0n Q2F{qty, pr, ds, vd, acc}:
      Q2F{qty, pr, ds, vd, acc}
    case 1n+p Q2F{qty, pr, ds, vd, +acc}:
      q2f.rep(p, q2f.add(acc, vd, q2f.out1(ds, K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), N(), D(), qty, pr, 0.0))))

def q2f.v3(r: Array<F32> & Array<F32>) -> U32:
  (o, ds) = r
  SumB(N(), o)

def q2f.v1(ds: Array<F32>, r: K.ZB<U32, F32, F32>) -> U32:
  match r:
    case K.ZB{t, qty, pr}:
      q2f.v3(q2f.out2(t, K.Kernel.map_pb(~F32, ~F32, ~F32, ~(p => x => F32.sub(p, x)), N(), D(), ds, 1.0, 0.0)))

def q2f.check(st: Q2F) -> U32:
  match st:
    case Q2F{qty, pr, ds, vd, acc}:
      q2f.v1(ds, K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), N(), D(), qty, pr, 0.0))

def q2f.new() -> Q2F:
  Q2F{GenU(~(i => Gen.qty(i))), GenF(~(i => Gen.price(i))), GenF(~(i => Gen.disc(i))), GenU(~(i => Gen.vdisc(i))), 0}

# q2 nullable (F2): zipb, then zipv(1.0 1-slot, discount, vd), then zipv(t, ones, s, vs)

def q2n.e3(r: K.ZV<F32, F32, F32>) -> Array<F32>:
  match r:
    case K.ZV{o, vo, a, va, b, vb}:
      o

def q2n.e2(t: Array<F32>, r: K.ZV<F32, F32, F32>) -> Array<F32> & (Array<F32> & Array<U32>):
  match r:
    case K.ZV{s, vs, one, ones, ds, vd}:
      (q2n.e3(K.Kernel.zipv(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), N(), D(), t, Array.new(U32, 0n, 1), s, vs, 0.0)), (ds, vd))

def q2n.e5(qty: Array<U32>, pr: Array<F32>, +x: U32, r: Array<F32> & Array<U32>) -> Q2F:
  (ds, vd) = r
  Q2F{qty, pr, ds, vd, x}

def q2n.e4(qty: Array<U32>, pr: Array<F32>, r: Array<F32> & (Array<F32> & Array<U32>)) -> Q2F:
  (o, rest) = r
  q2n.e5(qty, pr, first(o), rest)

def q2n.e1(ds: Array<F32>, vd: Array<U32>, r: K.ZB<U32, F32, F32>) -> Q2F:
  match r:
    case K.ZB{t, qty, pr}:
      q2n.e4(qty, pr, q2n.e2(t, K.Kernel.zipv(~F32, ~F32, ~F32, ~(x => y => F32.sub(x, y)), N(), D(), Array.new(F32, 0n, 1.0), Array.new(U32, 0n, 1), ds, vd, 0.0)))

def q2n.add(+acc: U32, st: Q2F) -> Q2F:
  match st:
    case Q2F{qty, pr, ds, vd, +x}:
      Q2F{qty, pr, ds, vd, U32.add(acc, x)}

def q2n.rep(f: Nat, st: Q2F) -> Q2F:
  match f st:
    case 0n Q2F{qty, pr, ds, vd, acc}:
      Q2F{qty, pr, ds, vd, acc}
    case 1n+p Q2F{qty, pr, ds, vd, +acc}:
      q2n.rep(p, q2n.add(acc, q2n.e1(ds, vd, K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), N(), D(), qty, pr, 0.0))))

def q2n.v(r: Array<F32> & (Array<F32> & Array<U32>)) -> U32:
  (o, rest) = r
  SumB(N(), o)

def q2n.v1(ds: Array<F32>, vd: Array<U32>, r: K.ZB<U32, F32, F32>) -> U32:
  match r:
    case K.ZB{t, qty, pr}:
      q2n.v(q2n.e2(t, K.Kernel.zipv(~F32, ~F32, ~F32, ~(x => y => F32.sub(x, y)), N(), D(), Array.new(F32, 0n, 1.0), Array.new(U32, 0n, 1), ds, vd, 0.0)))

def q2n.check(st: Q2F) -> U32:
  match st:
    case Q2F{qty, pr, ds, vd, acc}:
      q2n.v1(ds, vd, K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), N(), D(), qty, pr, 0.0))

type Q2C is Type:
  Q2C{qty: CH.CW, pr: CH.CF, ds: CH.CF, vd: CH.CW, one: CH.CF, ones: CH.CW, acc: U32}

def q2c.out2(t: CH.CF, r: CH.CF & CH.CF) -> CH.CF & CH.CF:
  (s, ds) = r
  (KC.CK.zip.fff(~(x => y => F32.mul(x, y)), t, s, 0.0), ds)

def q2c.out3(qty: CH.CW, pr: CH.CF, vd: CH.CW, one: CH.CF, ones: CH.CW, r: CH.CF & CH.CF) -> Q2C:
  (o, ds) = r
  Q2C{qty, pr, ds, vd, one, ones, firstb(KC.CK.first.f(o))}

def q2c.out1(ds: CH.CF, vd: CH.CW, one: CH.CF, ones: CH.CW, r: KC.CZB<CH.CW, CH.CF, CH.CF>) -> Q2C:
  match r:
    case KC.CZB{t, qty, pr}:
      q2c.out3(qty, pr, vd, one, ones, q2c.out2(t, KC.CK.mappb.ff(~F32, ~(p => x => F32.sub(p, x)), ds, 1.0, 0.0)))

def q2c.add(+acc: U32, st: Q2C) -> Q2C:
  match st:
    case Q2C{qty, pr, ds, vd, one, ones, +x}:
      Q2C{qty, pr, ds, vd, one, ones, U32.add(acc, x)}

def q2c.rep(f: Nat, st: Q2C) -> Q2C:
  match f st:
    case 0n Q2C{qty, pr, ds, vd, one, ones, acc}:
      Q2C{qty, pr, ds, vd, one, ones, acc}
    case 1n+p Q2C{qty, pr, ds, vd, one, ones, +acc}:
      q2c.rep(p, q2c.add(acc, q2c.out1(ds, vd, one, ones, KC.CK.zipb.wff(~(x => y => F32.mul(U32.to_f32(x), y)), qty, pr, 0.0))))

def q2c.v3(r: CH.CF & CH.CF) -> U32:
  (o, ds) = r
  TSumB(o)

def q2c.v1(ds: CH.CF, r: KC.CZB<CH.CW, CH.CF, CH.CF>) -> U32:
  match r:
    case KC.CZB{t, qty, pr}:
      q2c.v3(q2c.out2(t, KC.CK.mappb.ff(~F32, ~(p => x => F32.sub(p, x)), ds, 1.0, 0.0)))

def q2c.check(st: Q2C) -> U32:
  match st:
    case Q2C{qty, pr, ds, vd, one, ones, acc}:
      q2c.v1(ds, KC.CK.zipb.wff(~(x => y => F32.mul(U32.to_f32(x), y)), qty, pr, 0.0))

def q2c.new() -> Q2C:
  Q2C{tw(GenU(~(i => Gen.qty(i)))), tf(GenF(~(i => Gen.price(i)))), tf(GenF(~(i => Gen.disc(i)))), tw(GenU(~(i => Gen.vdisc(i)))), fconst1(skel(), 1.0), KC.CK.ones1(skel()), 0}

# q2 in ONE walk: the three kernels chained per leaf (zipb, map_pb, zip), one fork per node

type W3 is Type:
  W3{o: CH.CF, qty: CH.CW, pr: CH.CF, ds: CH.CF}

def w3.l3(+n: U32, +d: Nat, qty: Array<U32>, pr: Array<F32>, t: Array<F32>, r: Array<F32> & Array<F32>) -> W3:
  (s, ds) = r
  W3{CH.FL{n, d, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, t, s, 0.0)}, CH.WL{n, d, qty}, CH.FL{n, d, pr}, CH.FL{n, d, ds}}

def w3.l2(+n: U32, +d: Nat, ds: Array<F32>, r: K.ZB<U32, F32, F32>) -> W3:
  match r:
    case K.ZB{t, qty, pr}:
      w3.l3(n, d, qty, pr, t, K.Kernel.map_pb(~F32, ~F32, ~F32, ~(p => x => F32.sub(p, x)), n, d, ds, 1.0, 0.0))

def w3.j(+rows: U32, +lrows: U32, x: W3, y: W3) -> W3:
  match x y:
    case W3{o1, q1, p1, d1} W3{o2, q2, p2, d2}:
      W3{CH.FN{rows, lrows, o1, o2}, CH.WN{rows, lrows, q1, q2}, CH.FN{rows, lrows, p1, p2}, CH.FN{rows, lrows, d1, d2}}

def w3(qty: CH.CW, pr: CH.CF, ds: CH.CF) -> W3:
  match qty pr ds:
    case CH.WL{+n, +d, q} CH.FL{n2, d2, p} CH.FL{n3, d3, s}:
      w3.l2(n, d, s, K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), n, d, q, p, 0.0))
    case CH.WN{+rows, +lrows, q1, q2} CH.FN{r2, l2, p1, p2} CH.FN{r3, l3, s1, s2}:
      x y = w3(q1, p1, s1) w3(q2, p2, s2)
      w3.j(rows, lrows, x, y)
    case qty pr ds:
      W3{CH.CF.empty(), qty, pr, ds}

def q21.k(vd: CH.CW, one: CH.CF, ones: CH.CW, +acc: U32, r: W3) -> Q2C:
  match r:
    case W3{o, qty, pr, ds}:
      Q2C{qty, pr, ds, vd, one, ones, U32.add(acc, firstb(KC.CK.first.f(o)))}

def q21.rep(f: Nat, st: Q2C) -> Q2C:
  match f st:
    case 0n Q2C{qty, pr, ds, vd, one, ones, acc}:
      Q2C{qty, pr, ds, vd, one, ones, acc}
    case 1n+p Q2C{qty, pr, ds, vd, one, ones, +acc}:
      q21.rep(p, q21.k(vd, one, ones, acc, w3(qty, pr, ds)))

def q21.v(r: W3) -> U32:
  match r:
    case W3{o, qty, pr, ds}:
      TSumB(o)

def q21.check(st: Q2C) -> U32:
  match st:
    case Q2C{qty, pr, ds, vd, one, ones, acc}:
      q21.v(w3(qty, pr, ds))

# q2 nullable over the trees: CK.zipb.wff, CK.zipv.fff (1.0 as a 1-slot constant tree), CK.zipv.fff

def q2nc.e3(r: KC.CZV<CH.CF, CH.CF, CH.CF>) -> CH.CF & CH.CW:
  match r:
    case KC.CZV{o, vo, a, va, b, vb}:
      (o, va)

def q2nc.e2(t: CH.CF, r: KC.CZV<CH.CF, CH.CF, CH.CF>) -> (CH.CF & CH.CW) & KC.CZV<CH.CF, CH.CF, CH.CF>:
  match r:
    case KC.CZV{s, vs, one, ones, ds, vd}:
      (q2nc.e3(KC.CK.zipv.fff(~(x => y => F32.mul(x, y)), t, ones, s, vs, 0.0)), KC.CZV{CH.CF.empty(), CH.CW.empty(), one, CH.CW.empty(), ds, vd})

def q2nc.e7(qty: CH.CW, pr: CH.CF, o: CH.CF, ones: CH.CW, s: KC.CZV<CH.CF, CH.CF, CH.CF>) -> Q2C:
  match s:
    case KC.CZV{e1, e2, one, e3, ds, vd}:
      Q2C{qty, pr, ds, vd, one, ones, firstb(KC.CK.first.f(o))}

def q2nc.e6(qty: CH.CW, pr: CH.CF, ov: CH.CF & CH.CW, s: KC.CZV<CH.CF, CH.CF, CH.CF>) -> Q2C:
  (o, ones) = ov
  q2nc.e7(qty, pr, o, ones, s)

def q2nc.e4(qty: CH.CW, pr: CH.CF, r: (CH.CF & CH.CW) & KC.CZV<CH.CF, CH.CF, CH.CF>) -> Q2C:
  (ov, s) = r
  q2nc.e6(qty, pr, ov, s)

def q2nc.e1(ds: CH.CF, vd: CH.CW, one: CH.CF, ones: CH.CW, r: KC.CZB<CH.CW, CH.CF, CH.CF>) -> Q2C:
  match r:
    case KC.CZB{t, qty, pr}:
      q2nc.e4(qty, pr, q2nc.e2(t, KC.CK.zipv.fff(~(x => y => F32.sub(x, y)), one, ones, ds, vd, 0.0)))

def q2nc.rep(f: Nat, st: Q2C) -> Q2C:
  match f st:
    case 0n Q2C{qty, pr, ds, vd, one, ones, acc}:
      Q2C{qty, pr, ds, vd, one, ones, acc}
    case 1n+p Q2C{qty, pr, ds, vd, one, ones, +acc}:
      q2nc.rep(p, q2c.add(acc, q2nc.e1(ds, vd, one, ones, KC.CK.zipb.wff(~(x => y => F32.mul(U32.to_f32(x), y)), qty, pr, 0.0))))

def q2nc.v2(ov: CH.CF & CH.CW) -> U32:
  (o, ones) = ov
  TSumB(o)

def q2nc.v(r: (CH.CF & CH.CW) & KC.CZV<CH.CF, CH.CF, CH.CF>) -> U32:
  (ov, s) = r
  q2nc.v2(ov)

def q2nc.v1(ds: CH.CF, vd: CH.CW, one: CH.CF, ones: CH.CW, r: KC.CZB<CH.CW, CH.CF, CH.CF>) -> U32:
  match r:
    case KC.CZB{t, qty, pr}:
      q2nc.v(q2nc.e2(t, KC.CK.zipv.fff(~(x => y => F32.sub(x, y)), one, ones, ds, vd, 0.0)))

def q2nc.check(st: Q2C) -> U32:
  match st:
    case Q2C{qty, pr, ds, vd, one, ones, acc}:
      q2nc.v1(ds, vd, one, ones, KC.CK.zipb.wff(~(x => y => F32.mul(U32.to_f32(x), y)), qty, pr, 0.0))

# ---- U32 sum --------------------------------------------------------------------------------------

type SF is Type:
  SF{a: Array<U32>, acc: U32}

def sf.k(+acc: U32, r: Array<U32> & U32) -> SF:
  (a, +x) = r
  SF{a, U32.add(acc, x)}

def sf.rep(f: Nat, st: SF) -> SF:
  match f st:
    case 0n SF{a, acc}:
      SF{a, acc}
    case 1n+p SF{a, +acc}:
      sf.rep(p, sf.k(acc, K.Kernel.fold(~U32, ~U32, ~(s => x => U32.add(s, x)), N(), a, 0)))

type SC is Type:
  SC{t: CH.CW, acc: U32}

def sc.k(+acc: U32, r: CH.CW & U32) -> SC:
  (t, +x) = r
  SC{t, U32.add(acc, x)}

def sc.rep(f: Nat, st: SC) -> SC:
  match f st:
    case 0n SC{t, acc}:
      SC{t, acc}
    case 1n+p SC{t, +acc}:
      sc.rep(p, sc.k(acc, KC.CK.sum.w(t)))

# ---- F32 sums -------------------------------------------------------------------------------------

type FF is Type:
  FF{a: Array<F32>, acc: U32}

def ff.clone(+acc: U32, r: Array<F32> & Array<F32>) -> FF:
  (a, b) = r
  FF{a, U32.add(acc, first(b))}

def ff.sum(+acc: U32, r: Array<F32> & Array<F32>) -> FF:
  (a, b) = r
  FF{a, U32.add(acc, F32.bits(K.Kernel.fsum(~F32, ~(x => x), N(), b)))}

def ff.fold(+acc: U32, r: Array<F32> & K.NS) -> FF:
  (a, s) = r
  FF{a, U32.add(acc, F32.bits(K.Kernel.nm.fin(s)))}

def ff.step(+mode: U32, +acc: U32, a: Array<F32>) -> FF:
  match mode:
    case 0:
      ff.clone(acc, Array.clone(F32, a))
    case 1:
      ff.sum(acc, Array.clone(F32, a))
    case _:
      ff.fold(acc, K.Kernel.fold(~F32, ~K.NS, ~(s => x => K.Kernel.nm.step(s, x)), N(), a, K.NS{0.0, 0.0}))

# a leaf-by-leaf clone of an F32 tree (sequential; the baseline the consuming cells subtract)

def ff.rep(f: Nat, +mode: U32, st: FF) -> FF:
  match f st:
    case 0n FF{a, acc}:
      FF{a, acc}
    case 1n+p FF{a, +acc}:
      ff.rep(p, mode, ff.step(mode, acc, a))

def tcf.l(+n: U32, +d: Nat, r: Array<F32> & Array<F32>) -> CH.CF & CH.CF:
  (a, b) = r
  (CH.FL{n, d, a}, CH.FL{n, d, b})

def tcf.j(+rows: U32, +lrows: U32, x: CH.CF & CH.CF, y: CH.CF & CH.CF) -> CH.CF & CH.CF:
  (a1, b1) = x
  (a2, b2) = y
  (CH.FN{rows, lrows, a1, a2}, CH.FN{rows, lrows, b1, b2})

def tcf(t: CH.CF) -> CH.CF & CH.CF:
  match t:
    case CH.FL{+n, +d, a}:
      tcf.l(n, d, Array.clone(F32, a))
    case CH.FN{+rows, +lrows, l, r}:
      tcf.j(rows, lrows, tcf(l), tcf(r))

def tcw.l(+n: U32, +d: Nat, r: Array<U32> & Array<U32>) -> CH.CW & CH.CW:
  (a, b) = r
  (CH.WL{n, d, a}, CH.WL{n, d, b})

def tcw.j(+rows: U32, +lrows: U32, x: CH.CW & CH.CW, y: CH.CW & CH.CW) -> CH.CW & CH.CW:
  (a1, b1) = x
  (a2, b2) = y
  (CH.WN{rows, lrows, a1, a2}, CH.WN{rows, lrows, b1, b2})

def tcw(t: CH.CW) -> CH.CW & CH.CW:
  match t:
    case CH.WL{+n, +d, a}:
      tcw.l(n, d, Array.clone(U32, a))
    case CH.WN{+rows, +lrows, l, r}:
      tcw.j(rows, lrows, tcw(l), tcw(r))

type FT is Type:
  FT{t: CH.CF, acc: U32}

def ft.clone(+acc: U32, r: CH.CF & CH.CF) -> FT:
  (t, b) = r
  FT{t, U32.add(acc, firstb(KC.CK.first.f(b)))}

def ft.walk(+acc: U32, r: CH.CF & CH.CF) -> FT:
  (t, b) = r
  FT{t, U32.add(acc, F32.bits(KC.CK.fsum.f(b)))}

def ft.flat(+acc: U32, r: CH.CF & CH.CF) -> FT:
  (t, b) = r
  FT{t, U32.add(acc, F32.bits(KC.CK.fsumflat.f(b)))}

def wr.l(r: Array<F32> & K.NS) -> K.NS:
  (a, acc) = r
  acc

# the recursive in-order walk (the shape CK.walk.f had first; see the header)
def wr(t: CH.CF, acc: K.NS) -> K.NS:
  match t:
    case CH.FL{+n, d, a}:
      wr.l(K.Kernel.fold(~F32, ~K.NS, ~(s => x => K.Kernel.nm.step(s, x)), n, a, acc))
    case CH.FN{rows, lrows, l, r}:
      wr(r, wr(l, acc))

def ft.walkr(+acc: U32, r: CH.CF & CH.CF) -> FT:
  (t, b) = r
  FT{t, U32.add(acc, F32.bits(K.Kernel.nm.fin(wr(b, K.NS{0.0, 0.0}))))}

def ft.step(+mode: U32, +acc: U32, t: CH.CF) -> FT:
  match mode:
    case 0:
      ft.clone(acc, tcf(t))
    case 1:
      ft.walk(acc, tcf(t))
    case 2:
      ft.flat(acc, tcf(t))
    case _:
      ft.walkr(acc, tcf(t))

def ft.rep(f: Nat, +mode: U32, st: FT) -> FT:
  match f st:
    case 0n FT{t, acc}:
      FT{t, acc}
    case 1n+p FT{t, +acc}:
      ft.rep(p, mode, ft.step(mode, acc, t))

# ---- gathers --------------------------------------------------------------------------------------

type GSt is Type:
  GSt{t: CH.CW, perm: Array<U32>, acc: U32}

def gt.k(t: CH.CW, +acc: U32, r: CH.CW & Array<U32>) -> GSt:
  (o, perm) = r
  GSt{t, perm, U32.add(acc, Pair.snd(CH.CW, U32, KC.CK.first.w(o)))}

def gt.clone(+acc: U32, perm: Array<U32>, r: CH.CW & CH.CW) -> GSt:
  (t, b) = r
  GSt{t, perm, U32.add(acc, Pair.snd(CH.CW, U32, KC.CK.first.w(b)))}

def gt.fused(+acc: U32, perm: Array<U32>, r: CH.CW & CH.CW) -> GSt:
  (t, b) = r
  gt.k(t, acc, KC.CK.gather.w(b, perm, N(), G()))

def gt.flat(+acc: U32, perm: Array<U32>, r: CH.CW & CH.CW) -> GSt:
  (t, b) = r
  gt.k(t, acc, KC.CK.gatherf.w(b, perm, N(), G()))

def gt.step(+mode: U32, +acc: U32, t: CH.CW, perm: Array<U32>) -> GSt:
  match mode:
    case 0:
      gt.clone(acc, perm, tcw(t))
    case 1:
      gt.fused(acc, perm, tcw(t))
    case _:
      gt.flat(acc, perm, tcw(t))

def gt.rep(f: Nat, +mode: U32, st: GSt) -> GSt:
  match f st:
    case 0n GSt{t, perm, acc}:
      GSt{t, perm, acc}
    case 1n+p GSt{t, perm, +acc}:
      gt.rep(p, mode, gt.step(mode, acc, t, perm))

def gt.v(r: CH.CW & Array<U32>) -> U32:
  (o, perm) = r
  TSum(o)

def gt.check.k(fl: Bool, t: CH.CW, perm: Array<U32>) -> U32:
  match fl:
    case True{}:
      gt.v(KC.CK.gatherf.w(t, perm, N(), G()))
    case False{}:
      gt.v(KC.CK.gather.w(t, perm, N(), G()))

def gt.check(+mode: U32, st: GSt) -> U32:
  match st:
    case GSt{t, perm, acc}:
      gt.check.k(U32.is_eq(mode, 2), t, perm)

# ---- driver ---------------------------------------------------------------------------------------

def show(+mode: String, +reps: U32, +ms: Nat, +acc: U32, +check: U32) -> String:
  "{\"mode\":\"" ++ mode ++ "\",\"rows\":" ++ U32.show(N()) ++ ",\"grain_log2\":14,\"reps\":" ++ U32.show(reps) ++ ",\"ms_total\":" ++ Nat.show(ms) ++ ",\"acc\":" ++ U32.show(acc) ++ ",\"check\":" ++ U32.show(check) ++ "}"

def acc.q1f(st: Q1F) -> U32 & Q1F:
  match st:
    case Q1F{ok, qty, id, rg, pr, +acc}:
      (acc, Q1F{ok, qty, id, rg, pr, acc})

def acc.q1c(st: Q1C) -> U32 & Q1C:
  match st:
    case Q1C{ok, v1, qty, v2, id, rg, pr, +acc}:
      (acc, Q1C{ok, v1, qty, v2, id, rg, pr, acc})

def acc.q2f(st: Q2F) -> U32 & Q2F:
  match st:
    case Q2F{qty, pr, ds, vd, +acc}:
      (acc, Q2F{qty, pr, ds, vd, acc})

def acc.q2c(st: Q2C) -> U32 & Q2C:
  match st:
    case Q2C{qty, pr, ds, vd, one, ones, +acc}:
      (acc, Q2C{qty, pr, ds, vd, one, ones, acc})

def out.q1f(+mode: String, +reps: U32, +ms: Nat, r: U32 & Q1F) -> String:
  (+acc, st) = r
  show(mode, reps, ms, acc, q1f.check(st))

def out.q1c(+mode: String, +reps: U32, +ms: Nat, r: U32 & Q1C) -> String:
  (+acc, st) = r
  show(mode, reps, ms, acc, q1c.check(st))

def out.q2f.k(+id: U32, st: Q2F) -> U32:
  match id:
    case 2:
      q2f.check(st)
    case _:
      q2n.check(st)

def out.q2f(+mode: String, +id: U32, +reps: U32, +ms: Nat, r: U32 & Q2F) -> String:
  (+acc, st) = r
  show(mode, reps, ms, acc, out.q2f.k(id, st))

def out.q2c.k(+id: U32, st: Q2C) -> U32:
  match id:
    case 3:
      q2c.check(st)
    case 4:
      q21.check(st)
    case _:
      q2nc.check(st)

def out.q2c(+mode: String, +id: U32, +reps: U32, +ms: Nat, r: U32 & Q2C) -> String:
  (+acc, st) = r
  show(mode, reps, ms, acc, out.q2c.k(id, st))

def run.q1f(+mode: String, +reps: U32, st: Q1F) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    s2 : Q1F <- IO.pure(Q1F, q1f.rep(U32.to_nat(reps), st))
    t1 : Nat <- IO.now()
    IO.print(out.q1f(mode, reps, Nat.sub(t1, t0), acc.q1f(s2)))

def run.q1c(+mode: String, +reps: U32, st: Q1C) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    s2 : Q1C <- IO.pure(Q1C, q1c.rep(U32.to_nat(reps), st))
    t1 : Nat <- IO.now()
    IO.print(out.q1c(mode, reps, Nat.sub(t1, t0), acc.q1c(s2)))

def q2f.go(+id: U32, f: Nat, st: Q2F) -> Q2F:
  match id:
    case 2:
      q2f.rep(f, st)
    case _:
      q2n.rep(f, st)

def run.q2f(+mode: String, +id: U32, +reps: U32, st: Q2F) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    s2 : Q2F <- IO.pure(Q2F, q2f.go(id, U32.to_nat(reps), st))
    t1 : Nat <- IO.now()
    IO.print(out.q2f(mode, id, reps, Nat.sub(t1, t0), acc.q2f(s2)))

def q2c.go(+id: U32, f: Nat, st: Q2C) -> Q2C:
  match id:
    case 3:
      q2c.rep(f, st)
    case 4:
      q21.rep(f, st)
    case _:
      q2nc.rep(f, st)

def run.q2c(+mode: String, +id: U32, +reps: U32, st: Q2C) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    s2 : Q2C <- IO.pure(Q2C, q2c.go(id, U32.to_nat(reps), st))
    t1 : Nat <- IO.now()
    IO.print(out.q2c(mode, id, reps, Nat.sub(t1, t0), acc.q2c(s2)))

def fin.sf(+mode: String, +reps: U32, +ms: Nat, st: SF) -> String:
  match st:
    case SF{a, +acc}:
      show(mode, reps, ms, acc, Sum(N(), a))

def fin.sc(+mode: String, +reps: U32, +ms: Nat, st: SC) -> String:
  match st:
    case SC{t, +acc}:
      show(mode, reps, ms, acc, TSum(t))

def run.sf(+mode: String, +reps: U32, st: SF) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    s2 : SF <- IO.pure(SF, sf.rep(U32.to_nat(reps), st))
    t1 : Nat <- IO.now()
    IO.print(fin.sf(mode, reps, Nat.sub(t1, t0), s2))

def run.sc(+mode: String, +reps: U32, st: SC) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    s2 : SC <- IO.pure(SC, sc.rep(U32.to_nat(reps), st))
    t1 : Nat <- IO.now()
    IO.print(fin.sc(mode, reps, Nat.sub(t1, t0), s2))

def fin.ff(+mode: String, +reps: U32, +ms: Nat, st: FF) -> String:
  match st:
    case FF{a, +acc}:
      show(mode, reps, ms, acc, F32.bits(K.Kernel.fsum(~F32, ~(x => x), N(), a)))

def fin.ft(+mode: String, +reps: U32, +ms: Nat, st: FT) -> String:
  match st:
    case FT{t, +acc}:
      show(mode, reps, ms, acc, F32.bits(KC.CK.fsum.f(t)))

def run.ff(+mode: String, +m: U32, +reps: U32, st: FF) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    s2 : FF <- IO.pure(FF, ff.rep(U32.to_nat(reps), m, st))
    t1 : Nat <- IO.now()
    IO.print(fin.ff(mode, reps, Nat.sub(t1, t0), s2))

def run.ft(+mode: String, +m: U32, +reps: U32, st: FT) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    s2 : FT <- IO.pure(FT, ft.rep(U32.to_nat(reps), m, st))
    t1 : Nat <- IO.now()
    IO.print(fin.ft(mode, reps, Nat.sub(t1, t0), s2))

def fin.gt(+mode: String, +m: U32, +reps: U32, +ms: Nat, st: GSt) -> String:
  match st:
    case GSt{t, perm, +acc}:
      show(mode, reps, ms, acc, gt.check(m, GSt{t, perm, acc}))

def run.gt(+mode: String, +m: U32, +reps: U32, st: GSt) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    s2 : GSt <- IO.pure(GSt, gt.rep(U32.to_nat(reps), m, st))
    t1 : Nat <- IO.now()
    IO.print(fin.gt(mode, m, reps, Nat.sub(t1, t0), s2))

def mid.k(hit: Bool, +id: U32, +rest: U32) -> U32:
  match hit:
    case True{}:
      id
    case False{}:
      rest

def mode_id2(+m: String) -> U32:
  mid.k(String.eq(m, "sumflat"), 7, mid.k(String.eq(m, "sumchunk"), 8, mid.k(String.eq(m, "fclone"), 9, mid.k(String.eq(m, "fsumflat"), 10, mid.k(String.eq(m, "ffold"), 11, mid.k(String.eq(m, "tclone"), 12, mid.k(String.eq(m, "twalk"), 13, mid.k(String.eq(m, "tflat"), 14, mid.k(String.eq(m, "twalkr"), 15, mid.k(String.eq(m, "gclone"), 16, mid.k(String.eq(m, "gfused"), 17, mid.k(String.eq(m, "gflat"), 18, 99))))))))))))

def mode_id(+m: String) -> U32:
  mid.k(String.eq(m, "q1flat"), 0, mid.k(String.eq(m, "q1chunk"), 1, mid.k(String.eq(m, "q2flat"), 2, mid.k(String.eq(m, "q2chunk"), 3, mid.k(String.eq(m, "q2chunk1"), 4, mid.k(String.eq(m, "q2nflat"), 5, mid.k(String.eq(m, "q2nchunk"), 6, mode_id2(m))))))))

def dispatch(+mode: String, +id: U32, +reps: U32) -> IO(Unit):
  match id:
    case 0:
      run.q1f(mode, reps, q1f.new())
    case 1:
      run.q1c(mode, reps, q1c.new())
    case 2:
      run.q2f(mode, id, reps, q2f.new())
    case 3:
      run.q2c(mode, id, reps, q2c.new())
    case 4:
      run.q2c(mode, id, reps, q2c.new())
    case 5:
      run.q2f(mode, id, reps, q2f.new())
    case 6:
      run.q2c(mode, id, reps, q2c.new())
    case 7:
      run.sf(mode, reps, SF{GenU(~(i => Gen.qty(i))), 0})
    case 8:
      run.sc(mode, reps, SC{tw(GenU(~(i => Gen.qty(i)))), 0})
    case 9:
      run.ff(mode, 0, reps, FF{GenF(~(i => Gen.price(i))), 0})
    case 10:
      run.ff(mode, 1, reps, FF{GenF(~(i => Gen.price(i))), 0})
    case 11:
      run.ff(mode, 2, reps, FF{GenF(~(i => Gen.price(i))), 0})
    case 12:
      run.ft(mode, 0, reps, FT{tf(GenF(~(i => Gen.price(i)))), 0})
    case 13:
      run.ft(mode, 1, reps, FT{tf(GenF(~(i => Gen.price(i)))), 0})
    case 14:
      run.ft(mode, 2, reps, FT{tf(GenF(~(i => Gen.price(i)))), 0})
    case 15:
      run.ft(mode, 3, reps, FT{tf(GenF(~(i => Gen.price(i)))), 0})
    case 16:
      run.gt(mode, 0, reps, GSt{tw(GenU(~(i => Gen.qty(i)))), GenU(~(i => Gen.perm(i))), 0})
    case 17:
      run.gt(mode, 1, reps, GSt{tw(GenU(~(i => Gen.qty(i)))), GenU(~(i => Gen.perm(i))), 0})
    case 18:
      run.gt(mode, 2, reps, GSt{tw(GenU(~(i => Gen.qty(i)))), GenU(~(i => Gen.perm(i))), 0})
    case _:
      IO.print("unknown mode " ++ mode)

def nat_of.k(m: Maybe<&2, Nat>, +d: Nat) -> Nat:
  match m:
    case Some{n}:
      n
    case None{}:
      d

def nat_of(s: String, +d: Nat) -> Nat:
  nat_of.k(Nat.read(s), d)

def go(args: List<String>) -> IO(Unit):
  match args:
    case exe <> +mode <> reps <> Nil{}:
      dispatch(mode, mode_id(mode), U32.from_nat(nat_of(reps, 10n)))
    case _:
      IO.print("usage: ckernels MODE REPS")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
