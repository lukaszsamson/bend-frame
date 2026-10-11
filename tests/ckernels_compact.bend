# T5.2 (DESIGN.md 16.1 compaction, 16.3 F6): per-leaf compaction of src/ckernels.bend at selectivities 0,
# 1, 50 and 100 % (tests/lib/ckgen.bend msel: none, i mod 100 == 0, i odd, all), every arity (CK.ck one
# buffer of each kind incl. Raw strings, CK.c3 / CK.c4 in each sorted kind combination), against the flat
# Kernel.compact_keep of the same column by the same flat mask (the first kept rows), F32 by bits; the
# kept count against Kernel.popcount; each output skeleton's counts exact (ragged leaves: a leaf keeps its
# capacity, its n is the leaf's kept count). Then the RAGGED outputs go through the other wrappers (a zip of
# two compacted columns, the U32 sum, the F32 walk and its flatten fallback, a gather, a second
# compaction) and through CW.rechunk (the rows kept, the leaf count after it). Expected kept counts
# (Python over the generators): sel 0 -> 0; sel 1 -> floor((n - 1) / 100) + 1; sel 50 -> floor(n / 2);
# sel 100 -> n. Leaves after CW.rechunk(g) (every subtree whose kept rows fit 2^g becomes one leaf): n = 17
# at g = 2 is (((4 4) (4 4)) 1): sel 0 / 1 keep 0 / 1 rows -> 1 leaf; sel 50 keeps 2 2 2 2 0 -> the root
# (8 rows) splits, ((2 2) (2 2)) splits into two fitting (2 2) -> ((4 4) 0): 3 leaves; sel 100 keeps the
# shape: 5 leaves. n = 49157 at g = 14 is ((L L) (L 5)): sel 0 / 1 -> 1 leaf; sel 50 keeps 16384 | 8194
# -> 2 leaves; sel 100 -> 4 leaves. n = 16385 (L 1), sel 50 keeps 8192 -> 1 leaf.
import Base
import ./../src/kernels.bend as K
import ./../src/chunks.bend as CH
import ./../src/ckernels.bend as KC
import ./lib/ckgen.bend as G

def cw.w(+n: U32, a: Array<U32>, m: Array<U32>) -> Array<U32>:
  Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, n, G.dfor(n), a, m, 0))

def cw.f(+n: U32, a: Array<F32>, m: Array<U32>) -> Array<F32>:
  Pair.fst(Array<F32>, Array<U32>, K.Kernel.compact_keep(~F32, n, G.dfor(n), a, m, 0.0))

def cw.s(+n: U32, a: Array<String>, m: Array<U32>) -> Array<String>:
  Pair.fst(Array<String>, Array<U32>, K.Kernel.compact_keep(~String, n, G.dfor(n), a, m, ""))

def pop(+n: U32, m: Array<U32>) -> U32:
  Pair.snd(Array<U32>, U32, K.Kernel.popcount(n, m))

def skok(t: CH.CW) -> Bool:
  G.skel_ok(Pair.snd(CH.CW, CH.Skel, CH.CW.skel(t)))

def skokf(t: CH.CF) -> Bool:
  G.skel_ok(Pair.snd(CH.CF, CH.Skel, CH.CF.skel(t)))

def mt(+s: U32, +n: U32, +g: Nat) -> CH.CW:
  G.tw(n, g, G.msel(s, n))

# ---- one buffer of each kind -----------------------------------------------------------------------

def ck.w.k(+s: U32, +n: U32, r: KC.CC1<CH.CW>) -> Bool:
  match r:
    case KC.CC1{o, m, +k}:
      Bool.and(Bool.and(U32.is_eq(k, pop(n, G.msel(s, n))), G.sameu(m, n, G.msel(s, n))), G.sku(o, k, cw.w(n, G.u1(n), G.msel(s, n))))

def ck.f.k(+s: U32, +n: U32, r: KC.CC1<CH.CF>) -> Bool:
  match r:
    case KC.CC1{o, m, +k}:
      Bool.and(U32.is_eq(k, pop(n, G.msel(s, n))), G.skf(o, k, cw.f(n, G.fsp(n), G.msel(s, n))))

def ck.s.k(+s: U32, +n: U32, r: KC.CC1<CH.CS>) -> Bool:
  match r:
    case KC.CC1{o, m, +k}:
      Bool.and(U32.is_eq(k, pop(n, G.msel(s, n))), G.sames(o, k, cw.s(n, G.strs(n), G.msel(s, n))))

def c.ck(+s: U32, +n: U32, +g: Nat) -> Bool:
  Bool.and(ck.w.k(s, n, KC.CK.ck.w(mt(s, n, g), G.tw(n, g, G.u1(n)))), Bool.and(ck.f.k(s, n, KC.CK.ck.f(mt(s, n, g), G.tf(n, g, G.fsp(n)))), ck.s.k(s, n, KC.CK.ck.s(mt(s, n, g), G.ts(n, g, G.strs(n))))))

# ---- three and four buffers (one cursor) --------------------------------------------------------------

def c3.www.k(+s: U32, +n: U32, r: KC.CC3<CH.CW, CH.CW, CH.CW>) -> Bool:
  match r:
    case KC.CC3{o1, o2, o3, m, a1, a2, a3, +k}:
      Bool.and(U32.is_eq(k, pop(n, G.msel(s, n))), Bool.and(Bool.and(G.sku(o1, k, cw.w(n, G.u1(n), G.msel(s, n))), G.sameu(o2, k, cw.w(n, G.u2(n), G.msel(s, n)))), Bool.and(G.sku(o3, k, cw.w(n, G.qty(n), G.msel(s, n))), Bool.and(G.sameu(a1, n, G.u1(n)), G.sameu(a3, n, G.qty(n))))))

def c3.wff.k(+s: U32, +n: U32, r: KC.CC3<CH.CW, CH.CF, CH.CF>) -> Bool:
  match r:
    case KC.CC3{o1, o2, o3, m, a1, a2, a3, +k}:
      Bool.and(U32.is_eq(k, pop(n, G.msel(s, n))), Bool.and(Bool.and(G.sameu(o1, k, cw.w(n, G.u1(n), G.msel(s, n))), G.samef(o2, k, cw.f(n, G.fsp(n), G.msel(s, n)))), Bool.and(G.samef(o3, k, cw.f(n, G.ffin(n), G.msel(s, n))), G.samef(a2, n, G.fsp(n)))))

def c3.fff.k(+s: U32, +n: U32, r: KC.CC3<CH.CF, CH.CF, CH.CF>) -> Bool:
  match r:
    case KC.CC3{o1, o2, o3, m, a1, a2, a3, +k}:
      Bool.and(U32.is_eq(k, pop(n, G.msel(s, n))), Bool.and(Bool.and(G.samef(o1, k, cw.f(n, G.fsp(n), G.msel(s, n))), G.samef(o2, k, cw.f(n, G.ffin(n), G.msel(s, n)))), G.samef(o3, k, cw.f(n, G.fsp(n), G.msel(s, n)))))

def c.c3(+s: U32, +n: U32, +g: Nat) -> Bool:
  Bool.and(c3.www.k(s, n, KC.CK.c3.www(mt(s, n, g), G.tw(n, g, G.u1(n)), G.tw(n, g, G.u2(n)), G.tw(n, g, G.qty(n)))), Bool.and(c3.wff.k(s, n, KC.CK.c3.wff(mt(s, n, g), G.tw(n, g, G.u1(n)), G.tf(n, g, G.fsp(n)), G.tf(n, g, G.ffin(n)))), c3.fff.k(s, n, KC.CK.c3.fff(mt(s, n, g), G.tf(n, g, G.fsp(n)), G.tf(n, g, G.ffin(n)), G.tf(n, g, G.fsp(n))))))

def c4.wwwf.k(+s: U32, +n: U32, r: KC.CC4<CH.CW, CH.CW, CH.CW, CH.CF>) -> Bool:
  match r:
    case KC.CC4{o1, o2, o3, o4, m, a1, a2, a3, a4, +k}:
      Bool.and(U32.is_eq(k, pop(n, G.msel(s, n))), Bool.and(Bool.and(G.sameu(o1, k, cw.w(n, G.u1(n), G.msel(s, n))), G.sameu(o2, k, cw.w(n, G.u2(n), G.msel(s, n)))), Bool.and(Bool.and(G.sameu(o3, k, cw.w(n, G.qty(n), G.msel(s, n))), G.samef(o4, k, cw.f(n, G.fsp(n), G.msel(s, n)))), Bool.and(G.sameu(m, n, G.msel(s, n)), G.samef(a4, n, G.fsp(n))))))

def c4.wwww.k(+s: U32, +n: U32, r: KC.CC4<CH.CW, CH.CW, CH.CW, CH.CW>) -> Bool:
  match r:
    case KC.CC4{o1, o2, o3, o4, m, a1, a2, a3, a4, +k}:
      Bool.and(U32.is_eq(k, pop(n, G.msel(s, n))), Bool.and(G.sameu(o1, k, cw.w(n, G.u1(n), G.msel(s, n))), G.sameu(o4, k, cw.w(n, G.ok(n), G.msel(s, n)))))

def c4.wwff.k(+s: U32, +n: U32, r: KC.CC4<CH.CW, CH.CW, CH.CF, CH.CF>) -> Bool:
  match r:
    case KC.CC4{o1, o2, o3, o4, m, a1, a2, a3, a4, +k}:
      Bool.and(U32.is_eq(k, pop(n, G.msel(s, n))), Bool.and(G.sameu(o2, k, cw.w(n, G.u2(n), G.msel(s, n))), G.samef(o3, k, cw.f(n, G.fsp(n), G.msel(s, n)))))

def c4.wfff.k(+s: U32, +n: U32, r: KC.CC4<CH.CW, CH.CF, CH.CF, CH.CF>) -> Bool:
  match r:
    case KC.CC4{o1, o2, o3, o4, m, a1, a2, a3, a4, +k}:
      Bool.and(U32.is_eq(k, pop(n, G.msel(s, n))), Bool.and(G.sameu(o1, k, cw.w(n, G.u1(n), G.msel(s, n))), G.samef(o4, k, cw.f(n, G.fsp(n), G.msel(s, n)))))

def c4.ffff.k(+s: U32, +n: U32, r: KC.CC4<CH.CF, CH.CF, CH.CF, CH.CF>) -> Bool:
  match r:
    case KC.CC4{o1, o2, o3, o4, m, a1, a2, a3, a4, +k}:
      Bool.and(U32.is_eq(k, pop(n, G.msel(s, n))), Bool.and(G.samef(o1, k, cw.f(n, G.fsp(n), G.msel(s, n))), G.samef(o4, k, cw.f(n, G.ffin(n), G.msel(s, n)))))

def c.c4(+s: U32, +n: U32, +g: Nat) -> Bool:
  Bool.and(Bool.and(c4.wwwf.k(s, n, KC.CK.c4.wwwf(mt(s, n, g), G.tw(n, g, G.u1(n)), G.tw(n, g, G.u2(n)), G.tw(n, g, G.qty(n)), G.tf(n, g, G.fsp(n)))), c4.wwww.k(s, n, KC.CK.c4.wwww(mt(s, n, g), G.tw(n, g, G.u1(n)), G.tw(n, g, G.u2(n)), G.tw(n, g, G.qty(n)), G.tw(n, g, G.ok(n))))), Bool.and(Bool.and(c4.wwff.k(s, n, KC.CK.c4.wwff(mt(s, n, g), G.tw(n, g, G.u1(n)), G.tw(n, g, G.u2(n)), G.tf(n, g, G.fsp(n)), G.tf(n, g, G.ffin(n)))), c4.wfff.k(s, n, KC.CK.c4.wfff(mt(s, n, g), G.tw(n, g, G.u1(n)), G.tf(n, g, G.ffin(n)), G.tf(n, g, G.ffin(n)), G.tf(n, g, G.fsp(n))))), c4.ffff.k(s, n, KC.CK.c4.ffff(mt(s, n, g), G.tf(n, g, G.fsp(n)), G.tf(n, g, G.ffin(n)), G.tf(n, g, G.ffin(n)), G.tf(n, g, G.ffin(n))))))

# ---- the ragged outputs through the other wrappers ----------------------------------------------------

# the compacted u1 / u2 / fsp (ragged, aligned: one mask), the kept count
def rag(+s: U32, +n: U32, +g: Nat) -> KC.CC3<CH.CW, CH.CW, CH.CF>:
  KC.CK.c3.wwf(mt(s, n, g), G.tw(n, g, G.u1(n)), G.tw(n, g, G.u2(n)), G.tf(n, g, G.fsp(n)))

def rag.o1(r: KC.CC3<CH.CW, CH.CW, CH.CF>) -> CH.CW:
  match r:
    case KC.CC3{o1, o2, o3, m, a1, a2, a3, k}:
      o1

def fl.u1(+s: U32, +n: U32) -> Array<U32>:
  cw.w(n, G.u1(n), G.msel(s, n))

def fl.u2(+s: U32, +n: U32) -> Array<U32>:
  cw.w(n, G.u2(n), G.msel(s, n))

def fl.f(+s: U32, +n: U32) -> Array<F32>:
  cw.f(n, G.fsp(n), G.msel(s, n))

def beq(+x: F32, +y: F32) -> Bool:
  U32.is_eq(F32.bits(x), F32.bits(y))

def rz.zip(+s: U32, +n: U32, +k: U32, o1: CH.CW, o2: CH.CW) -> Bool:
  G.sameu(KC.CK.zip.www(~(x => y => U32.sub(x, y)), o1, o2, 0), k, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.sub(x, y)), k, G.dfor(n), fl.u1(s, n), fl.u2(s, n), 0))

def rz.sum.k(+s: U32, +n: U32, +k: U32, r: CH.CW & U32) -> Bool:
  (t, +v) = r
  Bool.and(U32.is_eq(v, Pair.snd(Array<U32>, U32, K.Kernel.fold(~U32, ~U32, ~(a => x => U32.add(a, x)), k, fl.u1(s, n), 0))), G.sameu(t, k, fl.u1(s, n)))

def rz.fsum(+s: U32, +n: U32, +k: U32, o3: CH.CF) -> Bool:
  beq(KC.CK.fsum.f(o3), K.Kernel.fsum(~F32, ~(x => x), k, fl.f(s, n)))

def rz.fsumflat(+s: U32, +n: U32, +k: U32, o3: CH.CF) -> Bool:
  beq(KC.CK.fsumflat.f(o3), K.Kernel.fsum(~F32, ~(x => x), k, fl.f(s, n)))

# a gather from the ragged column: perm[j] = (k - 1 - j) for j < k (the rows reversed)
def rev(+k: U32) -> Array<U32>:
  G.gwp.go(~(p => j => U32.sub(U32.sub(p, 1), j)), U32.to_nat(k), k, 0, Array.new(U32, G.dfor(k), 0))

def rz.gather.k(+s: U32, +n: U32, +k: U32, r: CH.CW & Array<U32>) -> Bool:
  (t, p) = r
  G.sameu(t, k, Pair.fst(Array<U32>, Array<U32>, K.Kernel.gather(~U32, k, G.dfor(k), fl.u1(s, n), rev(k), 0)))

# a second compaction of the ragged column by the ragged mask "u2 odd" (aligned with the ragged output)
def rz.c2.k(+s: U32, +n: U32, +k: U32, r: KC.CC1<CH.CW>) -> Bool:
  match r:
    case KC.CC1{o, m, +k2}:
      Bool.and(U32.is_eq(k2, Pair.snd(Array<U32>, U32, K.Kernel.popcount(k, K.Kernel.map(~U32, ~U32, ~(x => U32.and(x, 1)), k, G.dfor(n), fl.u2(s, n), 0)))), G.sameu(o, k2, Pair.fst(Array<U32>, Array<U32>, K.Kernel.compact_keep(~U32, k, G.dfor(n), fl.u1(s, n), K.Kernel.map(~U32, ~U32, ~(x => U32.and(x, 1)), k, G.dfor(n), fl.u2(s, n), 0), 0))))

def rz.rechunk.j(+k: U32, +s: U32, +n: U32, r: CH.CW & U32) -> String:
  (t, +lv) = r
  G.okb(G.sameu(t, k, fl.u1(s, n))) ++ " leaves=" ++ U32.show(lv)

def rz.rechunk.k(+k: U32, +g: Nat, t: CH.CW, +s: U32, +n: U32) -> String:
  rz.rechunk.j(k, s, n, CH.CW.leaves(t))

def rz.more3.k(+s: U32, +n: U32, +g: Nat, +k: U32, r: KC.CC3<CH.CW, CH.CW, CH.CF>) -> String:
  match r:
    case KC.CC3{o1, o2, o3, m, a1, a2, a3, k3}:
      " rechunk " ++ rz.rechunk.k(k, g, CH.CW.rechunk(g, o1), s, n)

def rz.more2.k(+s: U32, +n: U32, +g: Nat, +k: U32, r: KC.CC3<CH.CW, CH.CW, CH.CF>) -> String:
  match r:
    case KC.CC3{o1, o2, o3, m, a1, a2, a3, k3}:
      G.tag("compact2", rz.c2.k(s, n, k, KC.CK.ck.w(KC.CK.map.ww(~(x => U32.and(x, 1)), o2, 0), o1))) ++ rz.more3.k(s, n, g, k, rag(s, n, g))

def rz.more.k(+s: U32, +n: U32, +g: Nat, +k: U32, r: KC.CC3<CH.CW, CH.CW, CH.CF>) -> String:
  match r:
    case KC.CC3{o1, o2, o3, m, a1, a2, a3, k3}:
      G.tag("fsumflat", rz.fsumflat(s, n, k, o3)) ++ G.tag("gather", rz.gather.k(s, n, k, KC.CK.gather.w(o1, rev(k), k, g))) ++ rz.more2.k(s, n, g, k, rag(s, n, g))

def rz.k(+s: U32, +n: U32, +g: Nat, r: KC.CC3<CH.CW, CH.CW, CH.CF>) -> String:
  match r:
    case KC.CC3{o1, o2, o3, m, a1, a2, a3, +k}:
      "ragged" ++ G.tag("zip", rz.zip(s, n, k, o1, o2)) ++ G.tag("sum", rz.sum.k(s, n, k, KC.CK.sum.w(rag.o1(rag(s, n, g))))) ++ G.tag("fsum", rz.fsum(s, n, k, o3)) ++ rz.more.k(s, n, g, k, rag(s, n, g))

def rz(+s: U32, +n: U32, +g: Nat) -> String:
  rz.k(s, n, g, rag(s, n, g))

def line(+s: U32, +n: U32, +g: Nat) -> String:
  "sel=" ++ U32.show(s) ++ " n=" ++ U32.show(n) ++ " g=" ++ Nat.show(g) ++ " kept=" ++ U32.show(pop(n, G.msel(s, n))) ++ G.tag("ck", c.ck(s, n, g)) ++ G.tag("c3", c.c3(s, n, g)) ++ G.tag("c4", c.c4(s, n, g)) ++ " " ++ rz(s, n, g)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(line(0, 17, 2n))
    IO.print(line(1, 17, 2n))
    IO.print(line(50, 17, 2n))
    IO.print(line(100, 17, 2n))
    IO.print(line(0, 49157, 14n))
    IO.print(line(1, 49157, 14n))
    IO.print(line(50, 49157, 14n))
    IO.print(line(100, 49157, 14n))
    IO.print(line(50, 16385, 14n))

#|sel=0 n=17 g=2 kept=0 ragged rechunk ok leaves=1
#|sel=1 n=17 g=2 kept=1 ragged rechunk ok leaves=1
#|sel=50 n=17 g=2 kept=8 ragged rechunk ok leaves=3
#|sel=100 n=17 g=2 kept=17 ragged rechunk ok leaves=5
#|sel=0 n=49157 g=14 kept=0 ragged rechunk ok leaves=1
#|sel=1 n=49157 g=14 kept=492 ragged rechunk ok leaves=1
#|sel=50 n=49157 g=14 kept=24578 ragged rechunk ok leaves=2
#|sel=100 n=49157 g=14 kept=49157 ragged rechunk ok leaves=4
#|sel=50 n=16385 g=14 kept=8192 ragged rechunk ok leaves=1
