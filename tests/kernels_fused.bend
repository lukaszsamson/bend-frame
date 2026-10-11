# T4.1 (DESIGN.md 16.3 F1-F6): the fused kernels of src/kernels.bend against hand-computed
# expectations (8 rows, nulls, AllValid as the 1-slot ones array, n = 0) and against the unfused
# compositions they replace (the v0.1 passes: map_p, zip, mask_and + zip + mask_data, popcount,
# compact_keep per buffer) on 3000 generated rows, compared slot by slot (F32 by bits). Every
# kernel hands its borrowed inputs back: the hand-backs are printed / compared too. The 8-row
# lines were worked out by hand; the kept counts 1264 / 2571 were recomputed in Python from the
# generators (q1's mask over the two validity patterns; rows i with i mod 7 != 3).
import Base
import ./../src/kernels.bend as K

# ---- helpers ------------------------------------------------------------------------------

def arr(r: U32 & Array<U32>) -> Array<U32>:
  (n, a) = r
  a

def arrf(r: U32 & Array<F32>) -> Array<F32>:
  (n, a) = r
  a

def u(xs: List<&2, U32>) -> Array<U32>:
  arr(K.Kernel.from_list(~U32, xs, 0))

def f(xs: List<&2, F32>) -> Array<F32>:
  arrf(K.Kernel.from_list(~F32, xs, 0.0))

# the 1-slot ones array: an AllValid side
def ones() -> Array<U32>:
  Array.new(U32, 0n, 1)

def shu.k(r: Array<U32> & List<&2, U32>) -> String:
  (a, xs) = r
  List.show(~&2, ~U32, ~(x => U32.show(x)), xs)

# the first n words of a
def shu(+n: U32, a: Array<U32>) -> String:
  shu.k(K.Kernel.to_list(~U32, n, a))

def shf.k(r: Array<F32> & List<&2, F32>) -> String:
  (a, xs) = r
  List.show(~&2, ~F32, ~(x => F32.show(x)), xs)

def shf(+n: U32, a: Array<F32>) -> String:
  shf.k(K.Kernel.to_list(~F32, n, a))

# ---- the 8-row fixture ----------------------------------------------------------------------
#   a  = [5, 60, 51, 50, 100, 7, 0, 99]      va = [1, 1, 0, 1, 1, 1, 0, 1]
#   b  = [1, 2, 3, 4, 5, 6, 7, 8]           vb = [1, 0, 1, 1, 1, 1, 1, 1]
#   ok = [1, 1, 1, 0, 1, 1, 1, 1] (AllValid) id = [10 .. 17]   pr = [0.5, 1.5 .. 7.5]

def fa() -> Array<U32>:
  u([5, 60, 51, 50, 100, 7, 0, 99])

def fva() -> Array<U32>:
  u([1, 1, 0, 1, 1, 1, 0, 1])

def fb() -> Array<U32>:
  u([1, 2, 3, 4, 5, 6, 7, 8])

def fvb() -> Array<U32>:
  u([1, 0, 1, 1, 1, 1, 1, 1])

def fok() -> Array<U32>:
  u([1, 1, 1, 0, 1, 1, 1, 1])

def fid() -> Array<U32>:
  u([10, 11, 12, 13, 14, 15, 16, 17])

def fpr() -> Array<F32>:
  f([0.5, 1.5, 2.5, 3.5, 4.5, 5.5, 6.5, 7.5])

# F1: a > 50 with the literal as a parameter; a comes back
def t.map_pb.k(r: Array<U32> & Array<U32>) -> String:
  (o, a) = r
  "map_pb gt50 " ++ shu(8, o) ++ " a back " ++ shu(8, a)

def t.map_pb() -> String:
  t.map_pb.k(K.Kernel.map_pb(~U32, ~U32, ~U32, ~(p => w => Bool.to_u32(U32.is_gt(w, p))), 8, 3n, fa(), 50, 0))

# F1 over f32: 1.0 - x
def t.map_pb_f.k(r: Array<F32> & Array<F32>) -> String:
  (o, a) = r
  "map_pb 1-x " ++ shf(4, o) ++ " a back " ++ shf(4, a)

def t.map_pb_f() -> String:
  t.map_pb_f.k(K.Kernel.map_pb(~F32, ~F32, ~F32, ~(p => x => F32.sub(p, x)), 4, 2n, f([0.25, 0.5, 0.0, 1.0]), 1.0, 0.0))

# F3: f32(qty) * price, both borrowed
def t.zipb.k(r: K.ZB<U32, F32, F32>) -> String:
  match r:
    case K.ZB{o, a, b}:
      "zipb cast*mul " ++ shf(3, o) ++ " a back " ++ shu(3, a) ++ " b back " ++ shf(3, b)

def t.zipb() -> String:
  t.zipb.k(K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), 3, 2n, u([1, 2, 3]), f([0.5, 0.25, 2.0]), 0.0))

# F2: a + b with validity: w = [1,0,0,1,1,1,0,1], out = w ? a + b : 0
def t.zipv.k(r: K.ZV<U32, U32, U32>) -> String:
  match r:
    case K.ZV{o, vo, a, va, b, vb}:
      "zipv add " ++ shu(8, o) ++ " valid " ++ shu(8, vo) ++ " back " ++ shu(8, a) ++ shu(8, va) ++ shu(8, b) ++ shu(8, vb)

def t.zipv() -> String:
  t.zipv.k(K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.add(x, y)), 8, 3n, fa(), fva(), fb(), fvb(), 0))

# F2 with one AllValid side (the 1-slot ones array, handed back as is)
def t.zipv1.k(r: K.ZV<U32, U32, U32>) -> String:
  match r:
    case K.ZV{o, vo, a, va, b, vb}:
      "zipv mul allvalid-b " ++ shu(8, o) ++ " valid " ++ shu(8, vo) ++ " ones back " ++ shu(1, vb)

def t.zipv1() -> String:
  t.zipv1.k(K.Kernel.zipv(~U32, ~U32, ~U32, ~(x => y => U32.mul(x, y)), 8, 3n, fa(), fva(), fb(), ones(), 0))

# F3 with validity: f32(qty) * price, price nullable
def t.zipv_f.k(r: K.ZV<U32, F32, F32>) -> String:
  match r:
    case K.ZV{o, vo, a, va, b, vb}:
      "zipv cast*mul " ++ shf(4, o) ++ " valid " ++ shu(4, vo)

def t.zipv_f() -> String:
  t.zipv_f.k(K.Kernel.zipv(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), 4, 2n, u([2, 3, 4, 5]), ones(), f([1.5, 2.0, 0.0, 0.5]), u([1, 1, 0, 1]), 0.0))

# F5: q1's `ok & (qty > 50)`: ok AllValid, qty with va; m = [0,1,0,0,1,0,0,1], kept 3
def t.pred.k(r: K.PC<U32, U32>) -> String:
  match r:
    case K.PC{m, k, a, va, b, vb}:
      "pred_count " ++ shu(8, m) ++ " kept " ++ U32.show(k) ++ " ok back " ++ shu(8, a) ++ " qty back " ++ shu(8, b) ++ shu(8, vb)

def t.pred() -> String:
  t.pred.k(K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), 8, 3n, 50, fok(), ones(), fa(), fva()))

# F5 over no rows: kept 0, the mask untouched
def t.pred0.k(r: K.PC<U32, U32>) -> String:
  match r:
    case K.PC{m, k, a, va, b, vb}:
      "pred_count n=0 kept " ++ U32.show(k) ++ " mask slot " ++ shu(1, m)

def t.pred0() -> String:
  t.pred0.k(K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), 0, 0n, 50, Array.new(U32, 0n, 1), ones(), Array.new(U32, 0n, 99), ones()))

# F6: id, b (region codes), price compacted by the q1 mask into depth_for(kept + 1) = 2 (4 slots)
def t.c3.k(r: K.C3<U32, U32, F32>) -> String:
  match r:
    case K.C3{o1, o2, o3, m, a1, a2, a3, +k}:
      "compact3 kept " ++ U32.show(k) ++ " " ++ shu(k, o1) ++ shu(k, o2) ++ shf(k, o3) ++ " mask back " ++ shu(8, m) ++ " inputs back " ++ shu(8, a1) ++ shf(8, a3)

def t.c3() -> String:
  t.c3.k(K.Kernel.compact3(~U32, ~U32, ~F32, 8, 2n, u([0, 1, 0, 0, 1, 0, 0, 1]), fid(), fb(), fpr(), 0, 0, 0.0))

def t.c4.k(r: K.C4<U32, U32, F32, U32>) -> String:
  match r:
    case K.C4{o1, o2, o3, o4, m, a1, a2, a3, a4, +k}:
      "compact4 kept " ++ U32.show(k) ++ " " ++ shu(k, o1) ++ shu(k, o2) ++ shf(k, o3) ++ shu(k, o4) ++ " a4 back " ++ shu(8, a4)

# every row kept, then none kept (the cursor stays 0; out of 1 slot)
def t.c4() -> String:
  t.c4.k(K.Kernel.compact4(~U32, ~U32, ~F32, ~U32, 8, 4n, u([1, 1, 1, 1, 1, 1, 1, 1]), fid(), fb(), fpr(), fva(), 0, 0, 0.0, 0))

def t.c4none() -> String:
  t.c4.k(K.Kernel.compact4(~U32, ~U32, ~F32, ~U32, 8, 0n, u([0, 0, 0, 0, 0, 0, 0, 0]), fid(), fb(), fpr(), fva(), 0, 0, 0.0, 0))

# ---- 3000 generated rows: fused == unfused, slot by slot --------------------------------------

def N() -> U32:
  3000

def DN() -> Nat:
  12n

def g.go(~f: U32 -> U32, n: Nat, +i: U32, out: Array<U32>) -> Array<U32>:
  match n:
    case 0n:
      out
    case 1n+p:
      g.go(~f, p, U32.inc(i), Array.set(U32, out, i, f(i)))

def gf.go(~f: U32 -> F32, n: Nat, +i: U32, out: Array<F32>) -> Array<F32>:
  match n:
    case 0n:
      out
    case 1n+p:
      gf.go(~f, p, U32.inc(i), Array.set(F32, out, i, f(i)))

def ga() -> Array<U32>:
  g.go(~(i => U32.mod(U32.mul(i, 2654435761), 101)), U32.to_nat(N()), 0, Array.new(U32, DN(), 0))

def gb() -> Array<U32>:
  g.go(~(i => U32.mul(i, 2246822519)), U32.to_nat(N()), 0, Array.new(U32, DN(), 0))

def gva() -> Array<U32>:
  g.go(~(i => Bool.to_u32(U32.is_ne(U32.mod(i, 7), 3))), U32.to_nat(N()), 0, Array.new(U32, DN(), 0))

def gvb() -> Array<U32>:
  g.go(~(i => Bool.to_u32(U32.is_ne(U32.mod(i, 5), 1))), U32.to_nat(N()), 0, Array.new(U32, DN(), 0))

def gok() -> Array<U32>:
  g.go(~(i => Bool.to_u32(U32.is_gt(U32.mod(U32.mul(i, 7919), 13), 4))), U32.to_nat(N()), 0, Array.new(U32, DN(), 0))

# prices with fractions, negatives, a NaN, an inf and -0.0 among them
def gp.v(+i: U32) -> F32:
  Bool.pick(F32, U32.is_eq(i, 17), F32.div(0.0, 0.0), Bool.pick(F32, U32.is_eq(i, 29), F32.div(1.0, 0.0), Bool.pick(F32, U32.is_eq(i, 31), F32.neg(0.0), F32.div(U32.to_f32(U32.mod(U32.mul(i, 31), 1000)), Bool.pick(F32, U32.is_eq(U32.mod(i, 3), 0), F32.neg(7.0), 10.0)))))

def gp() -> Array<F32>:
  gf.go(~(i => gp.v(i)), U32.to_nat(N()), 0, Array.new(F32, DN(), 0.0))

def eqf(+x: F32, +y: F32) -> Bool:
  U32.is_eq(F32.bits(x), F32.bits(y))

def eqf_all(+n: U32, a: Array<F32>, b: Array<F32>) -> Bool:
  K.Kernel.all_eq(~F32, ~(x => y => U32.is_eq(F32.bits(x), F32.bits(y))), n, a, b)

def equ_all(+n: U32, a: Array<U32>, b: Array<U32>) -> Bool:
  K.Kernel.all_eq(~U32, ~(x => y => U32.is_eq(x, y)), n, a, b)

# F1: map_pb == map_p == zip against the broadcast literal (Eval's unfused `x > lit`); a back
def d.map_pb.k(r: Array<U32> & Array<U32>) -> Bool:
  (o, a) = r
  Bool.and(equ_all(N(), o, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), N(), DN(), ga(), Array.new(U32, DN(), 50), 0)), equ_all(N(), a, ga()))

def d.map_pb() -> String:
  "diff map_pb " ++ Bool.show(d.map_pb.k(K.Kernel.map_pb(~U32, ~U32, ~U32, ~(p => w => Bool.to_u32(U32.is_gt(w, p))), N(), DN(), ga(), 50, 0)))

# F3: zipb(cast*mul) == zip(mul) over map(cast) (two passes, the same rounding points)
def d.zipb.k(r: K.ZB<U32, F32, F32>) -> Bool:
  match r:
    case K.ZB{o, a, b}:
      Bool.and(eqf_all(N(), o, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), N(), DN(), K.Kernel.map(~U32, ~F32, ~(w => U32.to_f32(w)), N(), DN(), ga(), 0.0), gp(), 0.0)), Bool.and(equ_all(N(), a, ga()), eqf_all(N(), b, gp())))

def d.zipb() -> String:
  "diff zipb " ++ Bool.show(d.zipb.k(K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), N(), DN(), ga(), gp(), 0.0)))

def d.snd(r: Array<F32> & Array<U32>) -> Array<F32>:
  (x, m) = r
  x

def d.sndu(r: Array<U32> & Array<U32>) -> Array<U32>:
  (x, m) = r
  x

# F2 + F3: zipv == mask_data(zip(cast*mul), mask_and(va, vb)) and vout == mask_and(va, vb)
def d.zipv.k(r: K.ZV<U32, F32, F32>) -> Bool:
  match r:
    case K.ZV{o, vo, a, va, b, vb}:
      Bool.and(Bool.and(eqf_all(N(), o, d.snd(K.Kernel.mask_data(~F32, N(), K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), N(), DN(), K.Kernel.map(~U32, ~F32, ~(w => U32.to_f32(w)), N(), DN(), ga(), 0.0), gp(), 0.0), K.Kernel.mask_and(N(), DN(), gva(), gvb()), 0.0))), equ_all(N(), vo, K.Kernel.mask_and(N(), DN(), gva(), gvb()))), Bool.and(Bool.and(equ_all(N(), a, ga()), equ_all(N(), va, gva())), Bool.and(eqf_all(N(), b, gp()), equ_all(N(), vb, gvb()))))

def d.zipv() -> String:
  "diff zipv " ++ Bool.show(d.zipv.k(K.Kernel.zipv(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), N(), DN(), ga(), gva(), gp(), gvb(), 0.0)))

# the unfused q1 predicate: zip(ok and (qty > 50)) with the null rows reset (mask_data over the
# validity AND), then popcount
def d.pred.ref() -> Array<U32>:
  d.sndu(K.Kernel.mask_data(~U32, N(), K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, 50)))), N(), DN(), gok(), gb(), 0), K.Kernel.mask_and(N(), DN(), gva(), gvb()), 0))

def d.pred.c(+k: U32, r: Array<U32> & U32) -> Bool:
  (m, +k2) = r
  U32.is_eq(k, k2)

def d.pred.k(r: K.PC<U32, U32>) -> Bool:
  match r:
    case K.PC{m, +k, a, va, b, vb}:
      Bool.and(Bool.and(equ_all(N(), m, d.pred.ref()), d.pred.c(k, K.Kernel.popcount(N(), d.pred.ref()))), Bool.and(Bool.and(equ_all(N(), a, gok()), equ_all(N(), va, gva())), Bool.and(equ_all(N(), b, gb()), equ_all(N(), vb, gvb()))))

def d.pred() -> String:
  "diff pred_count " ++ Bool.show(d.pred.k(K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), N(), DN(), 50, gok(), gva(), gb(), gvb())))

def fstu(r: Array<U32> & Array<U32>) -> Array<U32>:
  (o, m) = r
  o

def fstf(r: Array<F32> & Array<U32>) -> Array<F32>:
  (o, m) = r
  o

# F6: compact4 == compact_keep per buffer (same mask) and the cursor == popcount(mask), with the
# outputs in depth_for(kept + 1) slots as Column.compact allocates them
def d.c4.k(+kd: Nat, +kept: U32, r: K.C4<U32, F32, U32, U32>) -> Bool:
  match r:
    case K.C4{o1, o2, o3, o4, m, a1, a2, a3, a4, +k}:
      Bool.and(Bool.and(Bool.and(equ_all(kept, o1, fstu(K.Kernel.compact_keep(~U32, N(), kd, ga(), d.pred.ref(), 0))), eqf_all(kept, o2, fstf(K.Kernel.compact_keep(~F32, N(), kd, gp(), d.pred.ref(), 0.0)))), Bool.and(equ_all(kept, o3, fstu(K.Kernel.compact_keep(~U32, N(), kd, gb(), d.pred.ref(), 0))), equ_all(kept, o4, fstu(K.Kernel.compact_keep(~U32, N(), kd, gva(), d.pred.ref(), 0))))), Bool.and(U32.is_eq(k, kept), Bool.and(equ_all(N(), m, d.pred.ref()), eqf_all(N(), a2, gp()))))

def d.c4.a(r: Array<U32> & U32) -> String:
  (m, +kept) = r
  +kd = K.Kernel.depth_for(U32.add(kept, 1))
  "diff compact4 kept " ++ U32.show(kept) ++ " " ++ Bool.show(d.c4.k(kd, kept, K.Kernel.compact4(~U32, ~F32, ~U32, ~U32, N(), kd, d.pred.ref(), ga(), gp(), gb(), gva(), 0, 0.0, 0, 0)))

def d.c4() -> String:
  d.c4.a(K.Kernel.popcount(N(), d.pred.ref()))

def d.c3.k(+kd: Nat, +kept: U32, r: K.C3<F32, U32, U32>) -> Bool:
  match r:
    case K.C3{o1, o2, o3, m, a1, a2, a3, +k}:
      Bool.and(Bool.and(eqf_all(kept, o1, fstf(K.Kernel.compact_keep(~F32, N(), kd, gp(), gva(), 0.0))), Bool.and(equ_all(kept, o2, fstu(K.Kernel.compact_keep(~U32, N(), kd, gb(), gva(), 0))), equ_all(kept, o3, fstu(K.Kernel.compact_keep(~U32, N(), kd, gok(), gva(), 0))))), U32.is_eq(k, kept))

def d.c3.a(r: Array<U32> & U32) -> String:
  (m, +kept) = r
  +kd = K.Kernel.depth_for(U32.add(kept, 1))
  "diff compact3 kept " ++ U32.show(kept) ++ " " ++ Bool.show(d.c3.k(kd, kept, K.Kernel.compact3(~F32, ~U32, ~U32, N(), kd, gva(), gp(), gb(), gok(), 0.0, 0, 0)))

def d.c3() -> String:
  d.c3.a(K.Kernel.popcount(N(), gva()))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(t.map_pb())
    IO.print(t.map_pb_f())
    IO.print(t.zipb())
    IO.print(t.zipv())
    IO.print(t.zipv1())
    IO.print(t.zipv_f())
    IO.print(t.pred())
    IO.print(t.pred0())
    IO.print(t.c3())
    IO.print(t.c4())
    IO.print(t.c4none())
    IO.print(d.map_pb())
    IO.print(d.zipb())
    IO.print(d.zipv())
    IO.print(d.pred())
    IO.print(d.c4())
    IO.print(d.c3())

#|map_pb gt50 [0, 1, 1, 0, 1, 0, 0, 1] a back [5, 60, 51, 50, 100, 7, 0, 99]
#|map_pb 1-x [0.75, 0.5, 1, 0] a back [0.25, 0.5, 0, 1]
#|zipb cast*mul [0.5, 0.5, 6] a back [1, 2, 3] b back [0.5, 0.25, 2]
#|zipv add [6, 0, 0, 54, 105, 13, 0, 107] valid [1, 0, 0, 1, 1, 1, 0, 1] back [5, 60, 51, 50, 100, 7, 0, 99][1, 1, 0, 1, 1, 1, 0, 1][1, 2, 3, 4, 5, 6, 7, 8][1, 0, 1, 1, 1, 1, 1, 1]
#|zipv mul allvalid-b [5, 120, 0, 200, 500, 42, 0, 792] valid [1, 1, 0, 1, 1, 1, 0, 1] ones back [1]
#|zipv cast*mul [3, 6, 0, 2.5] valid [1, 1, 0, 1]
#|pred_count [0, 1, 0, 0, 1, 0, 0, 1] kept 3 ok back [1, 1, 1, 0, 1, 1, 1, 1] qty back [5, 60, 51, 50, 100, 7, 0, 99][1, 1, 0, 1, 1, 1, 0, 1]
#|pred_count n=0 kept 0 mask slot [0]
#|compact3 kept 3 [11, 14, 17][2, 5, 8][1.5, 4.5, 7.5] mask back [0, 1, 0, 0, 1, 0, 0, 1] inputs back [10, 11, 12, 13, 14, 15, 16, 17][0.5, 1.5, 2.5, 3.5, 4.5, 5.5, 6.5, 7.5]
#|compact4 kept 8 [10, 11, 12, 13, 14, 15, 16, 17][1, 2, 3, 4, 5, 6, 7, 8][0.5, 1.5, 2.5, 3.5, 4.5, 5.5, 6.5, 7.5][1, 1, 0, 1, 1, 1, 0, 1] a4 back [1, 1, 0, 1, 1, 1, 0, 1]
#|compact4 kept 0 [][][][] a4 back [1, 1, 0, 1, 1, 1, 0, 1]
#|diff map_pb True
#|diff zipb True
#|diff zipv True
#|diff pred_count True
#|diff compact4 kept 1264 True
#|diff compact3 kept 2571 True
