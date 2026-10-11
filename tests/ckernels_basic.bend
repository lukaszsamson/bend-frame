# T5.2 (DESIGN.md 16.1 / 16.3 / 16.4): src/ckernels.bend's wrappers on trees small enough to work out by
# hand (grain 2^2 = 4-row leaves; CW.of(7) is (4 3), CW.of(5) is (4 1), CW.of(3) one leaf). Each line
# prints the result's skeleton and its rows in order (F32 as bits).
#   map x + 10 over 0..6                    -> (4 3) [10..16]
#   zip x * y over 0..6, 100..106          -> (4 3) [0, 101, 204, 309, 416, 525, 636]
#   zip over (4 1) and a leaf of 3: a shape mismatch (WFCFrame excludes it) answers the empty tree: 0 []
#   zipb over the same mismatch: empty output, both operands back unchanged: 0 [] | (4 1) | 3
#   pred_count `x > 2` (AllValid sides as CK.ones1 trees) over 0..6 -> mask (4 3) [0,0,0,1,1,1,1], kept 4
#   zipv x + y, va = [1,0,1,1,0,1,1] vb = AllValid: out [100,0,104,106,0,110,112], vo = va
#   ck by "x mod 3 == 0" over 0..6: leaf 0..3 keeps 0, 3; leaf 4..6 keeps 6 -> (2 1) [0, 3, 6], kept 3
#   c3 by the same mask over (0..6, 100..106, f32 0.5 * i): (2 1) each, [0,3,6] [100,103,106]
#     [0x00000000, 0x3fc00000, 0x40400000]
#   sum / popcount / min / max over 0..6 and the mask: 21 3 0 6
#   gather perm = 6..0 from 100..106 at grain 2: (4 3) [106..100]
#   fsum [1, 2, 3, 0.5, 0.25] at grain 1 (leaves 2 2 1) = 6.75 -> 0x40d80000 (walk and flatten fallback)
#   fsum [inf, 1] -> 0x7f800000; fsum [-0.0, -0.0] -> 0x00000000 (0.0 + -0.0 = 0.0 at the first step)
#   fmin / fmax [-0.0, 0.0, 0.0, -0.0] (15.5.2 tie) -> 0x80000000 / 0x00000000;
#   fmin [NaN, 2, 1] -> 0x3f800000 (NaN skipped); fmax [NaN, NaN] -> NaN
#   imin / imax over the words [5, 2^32 - 1 (-1), 3, 2^31 (-2^31), 7] -> 2147483648 / 7
import Base
import ./../src/kernels.bend as K
import ./../src/chunks.bend as CH
import ./../src/ckernels.bend as KC
import ./lib/ckgen.bend as G
import ./../src/dump.bend as DP

def shu.k(r: Array<U32> & List<&2, U32>) -> String:
  (a, xs) = r
  List.show(~&2, ~U32, ~(x => U32.show(x)), xs)

def bits(+x: F32) -> String:
  Bool.pick(String, K.Kernel.is_nan(x), "nan", "0x" ++ DP.Dump.hex(8n, F32.bits(x)))

def shf.k(r: Array<F32> & List<&2, F32>) -> String:
  (a, xs) = r
  List.show(~&2, ~F32, ~(x => bits(x)), xs)

def cw.b(+s: CH.Skel, r: CH.CW & U32) -> String:
  (t, +n) = r
  G.skel_show(s) ++ " " ++ shu.k(K.Kernel.to_list(~U32, n, CH.CW.flatten(G.dfor(n), t)))

def cw.a(r: CH.CW & CH.Skel) -> String:
  (t, +s) = r
  cw.b(s, CH.CW.rows(t))

def cw(t: CH.CW) -> String:
  cw.a(CH.CW.skel(t))

def cf.b(+s: CH.Skel, r: CH.CF & U32) -> String:
  (t, +n) = r
  G.skel_show(s) ++ " " ++ shf.k(K.Kernel.to_list(~F32, n, CH.CF.flatten(G.dfor(n), t)))

def cf.a(r: CH.CF & CH.Skel) -> String:
  (t, +s) = r
  cf.b(s, CH.CF.rows(t))

def cf(t: CH.CF) -> String:
  cf.a(CH.CF.skel(t))

# 0..n-1 and 100 + i at grain 2
def t(+n: U32) -> CH.CW:
  G.tw(n, 2n, K.Kernel.iota(n, G.dfor(n)))

def t100(+n: U32) -> CH.CW:
  G.tw(n, 2n, K.Kernel.iota_from(n, G.dfor(n), 100))

def lw(xs: List<&2, U32>) -> Array<U32>:
  Pair.snd(U32, Array<U32>, K.Kernel.from_list(~U32, xs, 0))

def lf(xs: List<&2, F32>) -> Array<F32>:
  Pair.snd(U32, Array<F32>, K.Kernel.from_list(~F32, xs, 0.0))

def tf1(+n: U32, xs: List<&2, F32>) -> CH.CF:
  G.tf(n, 1n, lf(xs))

def zipb.k(r: KC.CZB<CH.CW, CH.CW, CH.CW>) -> String:
  match r:
    case KC.CZB{o, a, b}:
      cw(o) ++ " | " ++ cw(a) ++ " | " ++ cw(b)

def pc.k(r: KC.CPC<CH.CW, CH.CW>) -> String:
  match r:
    case KC.CPC{m, +k, a, va, b, vb}:
      cw(m) ++ " kept " ++ U32.show(k)

def pc.s(r: CH.CW & CH.Skel) -> String:
  (x, +s) = r
  pc.k(KC.CK.pc.ww(~U32, ~(p => x => y => Bool.to_u32(U32.is_gt(x, p))), 2, x, KC.CK.ones1(s), t(7), KC.CK.ones1(s)))

def zipv.k(r: KC.CZV<CH.CW, CH.CW, CH.CW>) -> String:
  match r:
    case KC.CZV{o, vo, a, va, b, vb}:
      cw(o) ++ " | " ++ cw(vo)

def zipv.s(r: CH.CW & CH.Skel) -> String:
  (x, +s) = r
  zipv.k(KC.CK.zipv.www(~(x => y => U32.add(x, y)), x, G.tw(7, 2n, lw([1, 0, 1, 1, 0, 1, 1])), t100(7), KC.CK.ones1(s), 0))

# the mask "x mod 3 == 0" over 0..6
def m3() -> CH.CW:
  KC.CK.map.ww(~(x => Bool.to_u32(U32.is_zero(U32.mod(x, 3)))), t(7), 0)

def ck.k(r: KC.CC1<CH.CW>) -> String:
  match r:
    case KC.CC1{o, m, +k}:
      cw(o) ++ " kept " ++ U32.show(k)

def c3.k(r: KC.CC3<CH.CW, CH.CW, CH.CF>) -> String:
  match r:
    case KC.CC3{o1, o2, o3, m, a1, a2, a3, k}:
      cw(o1) ++ " " ++ cw(o2) ++ " " ++ cf(o3)

def halves() -> CH.CF:
  KC.CK.map.wf(~(x => F32.mul(U32.to_f32(x), 0.5)), t(7), 0.0)

def snd(r: CH.CW & U32) -> U32:
  (t, +x) = r
  x

def red() -> String:
  U32.show(snd(KC.CK.sum.w(t(7)))) ++ " " ++ U32.show(snd(KC.CK.popcount.w(m3()))) ++ " " ++ U32.show(snd(KC.CK.min.w(t(7)))) ++ " " ++ U32.show(snd(KC.CK.max.w(t(7))))

def gat.k(r: CH.CW & Array<U32>) -> String:
  (t, p) = r
  cw(t)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("map " ++ cw(KC.CK.map.ww(~(x => U32.add(x, 10)), t(7), 0)))
    IO.print("zip " ++ cw(KC.CK.zip.www(~(x => y => U32.mul(x, y)), t(7), t100(7), 0)))
    IO.print("zip mismatch " ++ cw(KC.CK.zip.www(~(x => y => U32.mul(x, y)), t(5), t(3), 0)))
    IO.print("zipb mismatch " ++ zipb.k(KC.CK.zipb.www(~(x => y => U32.mul(x, y)), t(5), t(3), 0)))
    IO.print("pc " ++ pc.s(CH.CW.skel(t(7))))
    IO.print("zipv " ++ zipv.s(CH.CW.skel(t(7))))
    IO.print("ck " ++ ck.k(KC.CK.ck.w(m3(), t(7))))
    IO.print("c3 " ++ c3.k(KC.CK.c3.wwf(m3(), t(7), t100(7), halves())))
    IO.print("red " ++ red())
    IO.print("gather " ++ gat.k(KC.CK.gather.w(t100(7), lw([6, 5, 4, 3, 2, 1, 0]), 7, 2n)))
    IO.print("gatherf " ++ gat.k(KC.CK.gatherf.w(t100(7), lw([6, 5, 4, 3, 2, 1, 0]), 7, 2n)))
    IO.print("fsum " ++ bits(KC.CK.fsum.f(tf1(5, [1.0, 2.0, 3.0, 0.5, 0.25]))) ++ " " ++ bits(KC.CK.fsumflat.f(tf1(5, [1.0, 2.0, 3.0, 0.5, 0.25]))))
    IO.print("fsum inf " ++ bits(KC.CK.fsum.f(tf1(2, [F32.div(1.0, 0.0), 1.0]))) ++ " -0 " ++ bits(KC.CK.fsum.f(tf1(2, [F32.neg(0.0), F32.neg(0.0)]))))
    IO.print("fmin " ++ bits(KC.CK.fmin.f(tf1(4, [F32.neg(0.0), 0.0, 0.0, F32.neg(0.0)]))) ++ " fmax " ++ bits(KC.CK.fmax.f(tf1(4, [F32.neg(0.0), 0.0, 0.0, F32.neg(0.0)]))))
    IO.print("fmin nan " ++ bits(KC.CK.fmin.f(tf1(3, [F32.div(0.0, 0.0), 2.0, 1.0]))) ++ " fmax nan " ++ bits(KC.CK.fmax.f(tf1(2, [F32.div(0.0, 0.0), F32.div(0.0, 0.0)]))))
    IO.print("imin " ++ U32.show(KC.CK.imin.w(G.tw(5, 1n, lw([5, 4294967295, 3, 2147483648, 7])))) ++ " imax " ++ U32.show(KC.CK.imax.w(G.tw(5, 1n, lw([5, 4294967295, 3, 2147483648, 7])))))

#|map (4 3) [10, 11, 12, 13, 14, 15, 16]
#|zip (4 3) [0, 101, 204, 309, 416, 525, 636]
#|zip mismatch 0 []
#|zipb mismatch 0 [] | (4 1) [0, 1, 2, 3, 4] | 3 [0, 1, 2]
#|pc (4 3) [0, 0, 0, 1, 1, 1, 1] kept 4
#|zipv (4 3) [100, 0, 104, 106, 0, 110, 112] | (4 3) [1, 0, 1, 1, 0, 1, 1]
#|ck (2 1) [0, 3, 6] kept 3
#|c3 (2 1) [0, 3, 6] (2 1) [100, 103, 106] (2 1) [0x00000000, 0x3fc00000, 0x40400000]
#|red 21 3 0 6
#|gather (4 3) [106, 105, 104, 103, 102, 101, 100]
#|gatherf (4 3) [106, 105, 104, 103, 102, 101, 100]
#|fsum 0x40d80000 0x40d80000
#|fsum inf 0x7f800000 -0 0x00000000
#|fmin 0x80000000 fmax 0x00000000
#|fmin nan 0x3f800000 fmax nan nan
#|imin 2147483648 imax 7
