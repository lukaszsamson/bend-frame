# T5.2 (DESIGN.md 16.1 / 16.3 / 16.4): every chunked wrapper of src/ckernels.bend against the flat kernel
# it wraps, on trees built by CW.of / CF.of / CS.of at grain 2^2 (many tiny leaves: 0, 1, 3, 4, 5, 13, 17
# rows) and at the production grain 2^14 around the leaf boundary (0, 1, 2^14 - 1, 2^14, 2^14 + 1,
# 3 * 2^14 + 5). Each check flattens the chunked result and compares it with the flat kernel's output on
# the same generated column, row by row (F32 by bits), and the hand-backs with the inputs; `ok` when every
# check of the line holds, else the names of the failing checks. The kept counts are the q1 predicate's
# (tests/lib/ckgen.bend: ok & qty > 50 over the validity patterns), recomputed in Python from the
# generators: n = 0 -> 0, 1 -> 0, 3 -> 1, 4 -> 1, 5 -> 1, 13 -> 3, 17 -> 4; 16383 / 16384 / 16385 -> 4216
# (rows 16383 and 16384 are dropped), 49157 -> 12646. The leaves: ceil(n / 2^g) (1 for n <= 2^g).
import Base
import ./../src/kernels.bend as K
import ./../src/chunks.bend as CH
import ./../src/ckernels.bend as KC
import ./lib/ckgen.bend as G

def n_of(r: U32 & Array<U32>) -> U32:
  (+n, a) = r
  n

# ---- maps -----------------------------------------------------------------------------------------

def c.map(+n: U32, +g: Nat) -> Bool:
  G.sameu(KC.CK.map.ww(~(x => U32.add(U32.mul(x, 3), 1)), G.tw(n, g, G.u1(n)), 0), n, K.Kernel.map(~U32, ~U32, ~(x => U32.add(U32.mul(x, 3), 1)), n, G.dfor(n), G.u1(n), 0))

def c.mapwf(+n: U32, +g: Nat) -> Bool:
  G.samef(KC.CK.map.wf(~(x => U32.to_f32(x)), G.tw(n, g, G.u1(n)), 0.0), n, K.Kernel.map(~U32, ~F32, ~(x => U32.to_f32(x)), n, G.dfor(n), G.u1(n), 0.0))

def c.mapfw(+n: U32, +g: Nat) -> Bool:
  G.sameu(KC.CK.map.fw(~(x => K.Kernel.fword(x)), G.tf(n, g, G.fsp(n)), 0), n, K.Kernel.map(~F32, ~U32, ~(x => K.Kernel.fword(x)), n, G.dfor(n), G.fsp(n), 0))

def c.mapff(+n: U32, +g: Nat) -> Bool:
  G.samef(KC.CK.map.ff(~(x => F32.mul(x, 0.5)), G.tf(n, g, G.fsp(n)), 0.0), n, K.Kernel.map(~F32, ~F32, ~(x => F32.mul(x, 0.5)), n, G.dfor(n), G.fsp(n), 0.0))

def c.mapp(+n: U32, +g: Nat) -> Bool:
  G.sameu(KC.CK.mapp.ww(~U32, ~(p => x => Bool.to_u32(U32.is_gt(x, p))), G.tw(n, g, G.qty(n)), 50, 0), n, K.Kernel.map_p(~U32, ~U32, ~U32, ~(p => x => Bool.to_u32(U32.is_gt(x, p))), n, G.dfor(n), G.qty(n), 50, 0))

def c.mappb.k(+n: U32, r: CH.CW & CH.CW) -> Bool:
  (o, a) = r
  Bool.and(G.sameu(o, n, K.Kernel.map_p(~U32, ~U32, ~U32, ~(p => x => Bool.to_u32(U32.is_gt(x, p))), n, G.dfor(n), G.qty(n), 50, 0)), G.sameu(a, n, G.qty(n)))

def c.mappb(+n: U32, +g: Nat) -> Bool:
  c.mappb.k(n, KC.CK.mappb.ww(~U32, ~(p => x => Bool.to_u32(U32.is_gt(x, p))), G.tw(n, g, G.qty(n)), 50, 0))

def c.mappbf.k(+n: U32, r: CH.CF & CH.CF) -> Bool:
  (o, a) = r
  Bool.and(G.samef(o, n, K.Kernel.map_p(~F32, ~F32, ~F32, ~(p => x => F32.sub(p, x)), n, G.dfor(n), G.fsp(n), 1.0, 0.0)), G.samef(a, n, G.fsp(n)))

def c.mappbf(+n: U32, +g: Nat) -> Bool:
  c.mappbf.k(n, KC.CK.mappb.ff(~F32, ~(p => x => F32.sub(p, x)), G.tf(n, g, G.fsp(n)), 1.0, 0.0))

# ---- zips -----------------------------------------------------------------------------------------

def c.zip(+n: U32, +g: Nat) -> Bool:
  G.sameu(KC.CK.zip.www(~(x => y => U32.add(x, y)), G.tw(n, g, G.u1(n)), G.tw(n, g, G.u2(n)), 0), n, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, G.dfor(n), G.u1(n), G.u2(n), 0))

def c.zipwff(+n: U32, +g: Nat) -> Bool:
  G.samef(KC.CK.zip.wff(~(x => y => F32.mul(U32.to_f32(x), y)), G.tw(n, g, G.qty(n)), G.tf(n, g, G.fsp(n)), 0.0), n, K.Kernel.zip(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), n, G.dfor(n), G.qty(n), G.fsp(n), 0.0))

def c.zipffw(+n: U32, +g: Nat) -> Bool:
  G.sameu(KC.CK.zip.ffw(~(x => y => Bool.to_u32(F32.is_lt(x, y))), G.tf(n, g, G.fsp(n)), G.tf(n, g, G.ffin(n)), 0), n, K.Kernel.zip(~F32, ~F32, ~U32, ~(x => y => Bool.to_u32(F32.is_lt(x, y))), n, G.dfor(n), G.fsp(n), G.ffin(n), 0))

def c.zipb.k(+n: U32, r: KC.CZB<CH.CW, CH.CF, CH.CF>) -> Bool:
  match r:
    case KC.CZB{o, a, b}:
      Bool.and(G.samef(o, n, K.Kernel.zip(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), n, G.dfor(n), G.qty(n), G.fsp(n), 0.0)), Bool.and(G.sameu(a, n, G.qty(n)), G.samef(b, n, G.fsp(n))))

def c.zipb(+n: U32, +g: Nat) -> Bool:
  c.zipb.k(n, KC.CK.zipb.wff(~(x => y => F32.mul(U32.to_f32(x), y)), G.tw(n, g, G.qty(n)), G.tf(n, g, G.fsp(n)), 0.0))

def zvflat(+n: U32) -> K.ZV<U32, U32, U32>:
  K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), n, G.dfor(n), G.u1(n), G.vok(n), G.u2(n), G.vqty(n), 0)

def c.zipv.f(+n: U32, o: CH.CW, vo: CH.CW, f: K.ZV<U32, U32, U32>) -> Bool:
  match f:
    case K.ZV{fo, fvo, a, va, b, vb}:
      Bool.and(G.sameu(o, n, fo), G.sameu(vo, n, fvo))

def c.zipv.k(+n: U32, r: KC.CZV<CH.CW, CH.CW, CH.CW>) -> Bool:
  match r:
    case KC.CZV{o, vo, a, va, b, vb}:
      Bool.and(c.zipv.f(n, o, vo, zvflat(n)), Bool.and(Bool.and(G.sameu(a, n, G.u1(n)), G.sameu(va, n, G.vok(n))), Bool.and(G.sameu(b, n, G.u2(n)), G.sameu(vb, n, G.vqty(n)))))

def c.zipv(+n: U32, +g: Nat) -> Bool:
  c.zipv.k(n, KC.CK.zipv.www(~(x => y => U32.add(x, y)), G.tw(n, g, G.u1(n)), G.tw(n, g, G.vok(n)), G.tw(n, g, G.u2(n)), G.tw(n, g, G.vqty(n)), 0))

# an AllValid side: KC.CK.ones1 of the skeleton, against the flat kernel's 1-slot ones array
def zvflat1(+n: U32) -> K.ZV<F32, F32, F32>:
  K.Kernel.zipv(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, G.dfor(n), G.fsp(n), Array.new(U32, 0n, 1), G.ffin(n), G.vqty(n), 0.0)

def c.zipv1.f(+n: U32, o: CH.CF, vo: CH.CW, f: K.ZV<F32, F32, F32>) -> Bool:
  match f:
    case K.ZV{fo, fvo, a, va, b, vb}:
      Bool.and(G.samef(o, n, fo), G.sameu(vo, n, fvo))

def c.zipv1.k(+n: U32, r: KC.CZV<CH.CF, CH.CF, CH.CF>) -> Bool:
  match r:
    case KC.CZV{o, vo, a, va, b, vb}:
      Bool.and(c.zipv1.f(n, o, vo, zvflat1(n)), Bool.and(G.samef(a, n, G.fsp(n)), G.samef(b, n, G.ffin(n))))

def c.zipv1.s(+n: U32, +g: Nat, r: CH.CW & CH.Skel) -> Bool:
  (vb, s) = r
  c.zipv1.k(n, KC.CK.zipv.fff(~(x => y => F32.mul(x, y)), G.tf(n, g, G.fsp(n)), KC.CK.ones1(s), G.tf(n, g, G.ffin(n)), vb, 0.0))

def c.zipv1(+n: U32, +g: Nat) -> Bool:
  c.zipv1.s(n, g, CH.CW.skel(G.tw(n, g, G.vqty(n))))

# ---- the q1 predicate and the compactions -------------------------------------------------------------

def pcflat(+n: U32) -> K.PC<U32, U32>:
  K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, G.dfor(n), 50, G.ok(n), G.vok(n), G.qty(n), G.vqty(n))

def pcchunk(+n: U32, +g: Nat) -> KC.CPC<CH.CW, CH.CW>:
  KC.CK.pc.ww(~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), 50, G.tw(n, g, G.ok(n)), G.tw(n, g, G.vok(n)), G.tw(n, g, G.qty(n)), G.tw(n, g, G.vqty(n)))

def c.pc.f(+n: U32, m: CH.CW, +k: U32, f: K.PC<U32, U32>) -> Bool:
  match f:
    case K.PC{fm, +fk, a, va, b, vb}:
      Bool.and(U32.is_eq(k, fk), G.sameu(m, n, fm))

# the kept count, then: mask and count equal the flat kernel's, the four hand-backs
def c.pc.k(+n: U32, r: KC.CPC<CH.CW, CH.CW>) -> U32 & Bool:
  match r:
    case KC.CPC{m, +k, a, va, b, vb}:
      (k, Bool.and(c.pc.f(n, m, k, pcflat(n)), Bool.and(Bool.and(G.sameu(a, n, G.ok(n)), G.sameu(va, n, G.vok(n))), Bool.and(G.sameu(b, n, G.qty(n)), G.sameu(vb, n, G.vqty(n))))))

# the flat reference compaction: the first k rows of compact_keep into 2^dfor(n) slots
def cflat.w(+n: U32, a: Array<U32>, m: Array<U32>) -> Array<U32>:
  Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, G.dfor(n), a, m, 0))

def cflat.f(+n: U32, a: Array<F32>, m: Array<U32>) -> Array<F32>:
  Pair.fst(Array<F32>, Array<U32>, K.Kernel.compact_keep(~F32, n, G.dfor(n), a, m, 0.0))

def cflat.s(+n: U32, a: Array<String>, m: Array<U32>) -> Array<String>:
  Pair.fst(Array<String>, Array<U32>, K.Kernel.compact_keep(~String, n, G.dfor(n), a, m, ""))

def pcmask.k(f: K.PC<U32, U32>) -> Array<U32>:
  match f:
    case K.PC{fm, fk, a, va, b, vb}:
      fm

# the pc mask tree, then compact3 (u32, u32, f32) by it: outputs vs the flat compaction, the count, the
# outputs' skeleton counts exact, the mask and inputs handed back
def c.c3.k(+n: U32, +k: U32, r: KC.CC3<CH.CW, CH.CW, CH.CF>) -> Bool:
  match r:
    case KC.CC3{o1, o2, o3, m, a1, a2, a3, +k3}:
      Bool.and(Bool.and(U32.is_eq(k, k3), Bool.and(G.sameu(o1, k, cflat.w(n, G.u1(n), pcmask.k(pcflat(n)))), Bool.and(G.sameu(o2, k, cflat.w(n, G.u2(n), pcmask.k(pcflat(n)))), G.samef(o3, k, cflat.f(n, G.fsp(n), pcmask.k(pcflat(n))))))), Bool.and(G.sameu(m, n, pcmask.k(pcflat(n))), Bool.and(G.sameu(a1, n, G.u1(n)), Bool.and(G.sameu(a2, n, G.u2(n)), G.samef(a3, n, G.fsp(n))))))

def c.c3.m(+n: U32, +g: Nat, r: KC.CPC<CH.CW, CH.CW>) -> U32 & Bool:
  match r:
    case KC.CPC{m, +k, a, va, b, vb}:
      (k, c.c3.k(n, k, KC.CK.c3.wwf(m, G.tw(n, g, G.u1(n)), G.tw(n, g, G.u2(n)), G.tf(n, g, G.fsp(n)))))

# the skeleton of a compacted output is exact (ragged leaves, node counts the sums)
def c.c3sk.k(r: KC.CC3<CH.CW, CH.CW, CH.CF>) -> Bool:
  match r:
    case KC.CC3{o1, o2, o3, m, a1, a2, a3, k}:
      G.skel_ok(Pair.snd(CH.CW, CH.Skel, CH.CW.skel(o1)))

def c.c3sk.m(+g: Nat, +n: U32, r: KC.CPC<CH.CW, CH.CW>) -> Bool:
  match r:
    case KC.CPC{m, k, a, va, b, vb}:
      c.c3sk.k(KC.CK.c3.wwf(m, G.tw(n, g, G.u1(n)), G.tw(n, g, G.u2(n)), G.tf(n, g, G.fsp(n))))

# ---- reductions --------------------------------------------------------------------------------------

def fsnd(r: Array<U32> & U32) -> U32:
  (a, x) = r
  x

def tsnd.k(+n: U32, b: Array<U32>, r: CH.CW & U32) -> U32 & Bool:
  (t, +x) = r
  (x, G.sameu(t, n, b))

def c.fold.a(+n: U32, s: U32 & Bool, p: U32 & Bool, mn: U32 & Bool, mx: U32 & Bool) -> Bool:
  (+vs, bs) = s
  (+vp, bp) = p
  (+vmn, bmn) = mn
  (+vmx, bmx) = mx
  Bool.and(Bool.and(Bool.and(bs, bp), Bool.and(bmn, bmx)), Bool.and(Bool.and(U32.is_eq(vs, fsnd(K.Kernel.fold(~U32, ~U32, ~(a => x => U32.add(a, x)), n, G.u1(n), 0))), U32.is_eq(vp, fsnd(K.Kernel.popcount(n, G.vok(n))))), Bool.and(U32.is_eq(vmn, fsnd(K.Kernel.fold(~U32, ~U32, ~(a => x => U32.min(a, x)), n, G.u1(n), 4294967295))), U32.is_eq(vmx, fsnd(K.Kernel.fold(~U32, ~U32, ~(a => x => U32.max(a, x)), n, G.u1(n), 0))))))

def c.fold(+n: U32, +g: Nat) -> Bool:
  c.fold.a(n, tsnd.k(n, G.u1(n), KC.CK.sum.w(G.tw(n, g, G.u1(n)))), tsnd.k(n, G.vok(n), KC.CK.popcount.w(G.tw(n, g, G.vok(n)))), tsnd.k(n, G.u1(n), KC.CK.min.w(G.tw(n, g, G.u1(n)))), tsnd.k(n, G.u1(n), KC.CK.max.w(G.tw(n, g, G.u1(n)))))

# F32 in row order: the walk and the flatten fallback against the flat Kernel.fsum, bit for bit
def beq(+x: F32, +y: F32) -> Bool:
  U32.is_eq(F32.bits(x), F32.bits(y))

def c.fsum(+n: U32, +g: Nat) -> Bool:
  Bool.and(Bool.and(beq(KC.CK.fsum.f(G.tf(n, g, G.fsp(n))), K.Kernel.fsum(~F32, ~(x => x), n, G.fsp(n))), beq(KC.CK.fsumflat.f(G.tf(n, g, G.fsp(n))), K.Kernel.fsum(~F32, ~(x => x), n, G.fsp(n)))), Bool.and(Bool.and(beq(KC.CK.fsum.f(G.tf(n, g, G.ffin(n))), K.Kernel.fsum(~F32, ~(x => x), n, G.ffin(n))), beq(KC.CK.fsumflat.f(G.tf(n, g, G.ffin(n))), K.Kernel.fsum(~F32, ~(x => x), n, G.ffin(n)))), Bool.and(beq(KC.CK.fsum.w(~(w => U32.to_f32(w)), G.tw(n, g, G.qty(n))), K.Kernel.fsum(~U32, ~(w => U32.to_f32(w)), n, G.qty(n))), beq(KC.CK.fsumflat.w(~(w => U32.to_f32(w)), G.tw(n, g, G.qty(n))), K.Kernel.fsum(~U32, ~(w => U32.to_f32(w)), n, G.qty(n))))))

# min / max seeded with row 0 (Eval.fold1's steps)
def fold1f(~f: F32 -> F32 -> F32, +n: U32, r: Array<F32> & F32) -> F32:
  (a, x0) = r
  Pair.snd(Array<F32>, F32, K.Kernel.fold(~F32, ~F32, ~f, n, a, x0))

def fold1u(~f: U32 -> U32 -> U32, +n: U32, r: Array<U32> & U32) -> U32:
  (a, x0) = r
  Pair.snd(Array<U32>, U32, K.Kernel.fold(~U32, ~U32, ~f, n, a, x0))

def c.minmax(+n: U32, +g: Nat) -> Bool:
  Bool.and(Bool.and(beq(KC.CK.fmin.f(G.tf(n, g, G.fsp(n))), fold1f(~(a => b => K.Kernel.fmin(a, b)), n, Array.get(F32, G.fsp(n), 0))), beq(KC.CK.fmax.f(G.tf(n, g, G.fsp(n))), fold1f(~(a => b => K.Kernel.fmax(a, b)), n, Array.get(F32, G.fsp(n), 0)))), Bool.and(U32.is_eq(KC.CK.imin.w(G.tw(n, g, G.u1(n))), fold1u(~(a => b => KC.CK.i32_min(a, b)), n, Array.get(U32, G.u1(n), 0))), U32.is_eq(KC.CK.imax.w(G.tw(n, g, G.u1(n))), fold1u(~(a => b => KC.CK.i32_max(a, b)), n, Array.get(U32, G.u1(n), 0)))))

# ---- gathers -------------------------------------------------------------------------------------------

# perm[j] = (7919 j + 13) mod n: indices into the source's rows
def perm(+n: U32) -> Array<U32>:
  G.gwp.go(~(p => j => U32.mod(U32.add(U32.mul(j, 7919), 13), p)), U32.to_nat(n), U32.max(n, 1), 0, Array.new(U32, G.dfor(n), 0))

def gfl.w(+n: U32, a: Array<U32>) -> Array<U32>:
  Pair.fst(Array<U32>, Array<U32>, K.Kernel.gather(~U32, n, G.dfor(n), a, perm(n), 0))

def gfl.f(+n: U32, a: Array<F32>) -> Array<F32>:
  Pair.fst(Array<F32>, Array<U32>, K.Kernel.gather(~F32, n, G.dfor(n), a, perm(n), 0.0))

def gfl.s(+n: U32, a: Array<String>) -> Array<String>:
  Pair.fst(Array<String>, Array<U32>, K.Kernel.gather(~String, n, G.dfor(n), a, perm(n), ""))

def gk.w(+n: U32, r: CH.CW & Array<U32>) -> Bool:
  (t, p) = r
  Bool.and(G.sameu(t, n, gfl.w(n, G.u1(n))), G.equ(n, p, perm(n)))

def gk.f(+n: U32, r: CH.CF & Array<U32>) -> Bool:
  (t, p) = r
  Bool.and(G.samef(t, n, gfl.f(n, G.fsp(n))), G.equ(n, p, perm(n)))

def gk.s(+n: U32, r: CH.CS & Array<U32>) -> Bool:
  (t, p) = r
  Bool.and(G.sames(t, n, gfl.s(n, G.strs(n))), G.equ(n, p, perm(n)))

def c.gather(+n: U32, +g: Nat) -> Bool:
  Bool.and(Bool.and(Bool.and(gk.w(n, KC.CK.gather.w(G.tw(n, g, G.u1(n)), perm(n), n, g)), gk.w(n, KC.CK.gatherf.w(G.tw(n, g, G.u1(n)), perm(n), n, g))), Bool.and(gk.f(n, KC.CK.gather.f(G.tf(n, g, G.fsp(n)), perm(n), n, g)), gk.f(n, KC.CK.gatherf.f(G.tf(n, g, G.fsp(n)), perm(n), n, g)))), Bool.and(gk.s(n, KC.CK.gather.s(G.ts(n, g, G.strs(n)), perm(n), n, g)), gk.s(n, KC.CK.gatherf.s(G.ts(n, g, G.strs(n)), perm(n), n, g))))

# ---- one line per (n, g) --------------------------------------------------------------------------

def leaves(t: CH.CW) -> U32:
  Pair.snd(CH.CW, U32, CH.CW.leaves(t))

def line.b(+n: U32, +g: Nat, +k: U32, pc: Bool, c3: Bool) -> String:
  "n=" ++ U32.show(n) ++ " g=" ++ Nat.show(g) ++ " leaves=" ++ U32.show(leaves(G.tw(n, g, G.u1(n)))) ++ " kept=" ++ U32.show(k) ++ G.tag("map", c.map(n, g)) ++ G.tag("mapwf", c.mapwf(n, g)) ++ G.tag("mapfw", c.mapfw(n, g)) ++ G.tag("mapff", c.mapff(n, g)) ++ G.tag("mapp", c.mapp(n, g)) ++ G.tag("mappb", c.mappb(n, g)) ++ G.tag("mappbf", c.mappbf(n, g)) ++ G.tag("zip", c.zip(n, g)) ++ G.tag("zipwff", c.zipwff(n, g)) ++ G.tag("zipffw", c.zipffw(n, g)) ++ G.tag("zipb", c.zipb(n, g)) ++ G.tag("zipv", c.zipv(n, g)) ++ G.tag("zipv1", c.zipv1(n, g)) ++ G.tag("pc", pc) ++ G.tag("c3", c3) ++ G.tag("c3skel", c.c3sk.m(g, n, pcchunk(n, g))) ++ G.tag("fold", c.fold(n, g)) ++ G.tag("fsum", c.fsum(n, g)) ++ G.tag("minmax", c.minmax(n, g)) ++ G.tag("gather", c.gather(n, g)) ++ " done"

def line.a(+n: U32, +g: Nat, pc: U32 & Bool, c3: U32 & Bool) -> String:
  (+k, bpc) = pc
  (+k3, bc3) = c3
  line.b(n, g, k, bpc, Bool.and(U32.is_eq(k, k3), bc3))

def line(+n: U32, +g: Nat) -> String:
  line.a(n, g, c.pc.k(n, pcchunk(n, g)), c.c3.m(n, g, pcchunk(n, g)))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(line(0, 2n))
    IO.print(line(1, 2n))
    IO.print(line(3, 2n))
    IO.print(line(4, 2n))
    IO.print(line(5, 2n))
    IO.print(line(13, 2n))
    IO.print(line(17, 2n))
    IO.print(line(0, 14n))
    IO.print(line(1, 14n))
    IO.print(line(16383, 14n))
    IO.print(line(16384, 14n))
    IO.print(line(16385, 14n))
    IO.print(line(49157, 14n))

#|n=0 g=2 leaves=1 kept=0 done
#|n=1 g=2 leaves=1 kept=0 done
#|n=3 g=2 leaves=1 kept=1 done
#|n=4 g=2 leaves=1 kept=1 done
#|n=5 g=2 leaves=2 kept=1 done
#|n=13 g=2 leaves=4 kept=3 done
#|n=17 g=2 leaves=5 kept=4 done
#|n=0 g=14 leaves=1 kept=0 done
#|n=1 g=14 leaves=1 kept=0 done
#|n=16383 g=14 leaves=1 kept=4216 done
#|n=16384 g=14 leaves=1 kept=4216 done
#|n=16385 g=14 leaves=2 kept=4216 done
#|n=49157 g=14 leaves=4 kept=12646 done
