# T4.1 probe (provisional numbers; plans/M_02.txt W4): the fused kernels of src/kernels.bend
# (Kernel.pred_count, Kernel.compact3, Kernel.zipb, Kernel.map_pb) against the unfused passes
# today's evaluator runs for the q1 predicate + compaction and the q2 arithmetic, at 2^20 rows, flat
# (no chunks), on the real modules (the program imports frame.bend, so every type is shared exactly
# as in the library). Not wired into Eval: T4.2 / T4.3 do that.
#
#   q1today   filter(ok & (qty > 50)) as Eval runs it on AllValid columns: ok and qty copied
#             (ICol = Frame.get_cloned), the literal broadcast (Array.new), zip gt, zip and,
#             popcount, then Column.compact of the 5 columns of the projected frame (ok, qty, id,
#             region codes, price: compact_keep per buffer into depth_for(kept + 1) slots)
#   q1today3  the same with only the 3 selected columns compacted (F8's projection, unfused)
#   q1fused   Kernel.pred_count over the borrowed ok and qty (AllValid: the 1-slot ones array),
#             then Kernel.compact3 of id, region, price with one mask and one cursor
#   q2today   revenue = f32(qty) * price * (1.0 - fill_null(discount, 0.0)) as Eval runs it:
#             qty, price, discount data + mask copied, cast map, zip mul, two broadcasts
#             (1.0, 0.0), Kernel.choose (fill_null), zip sub, zip mul: 11 passes
#   q2fused   Kernel.zipb (F3: the cast inside the product) over the borrowed qty and price,
#             fill_null(discount, 0.0) = AllValid over the same payload (F4: the null slots
#             hold 0.0 already), Kernel.map_pb (F1: 1.0 - x, discount borrowed), Kernel.zip mul
#   q2ntoday  the same without fill_null (null discount -> null revenue, the spike's q2'): copies of
#             qty, price, discount data + mask, cast, zip mul, broadcast 1.0, zip sub, Eval.fix
#             (mask_data), zip mul, Eval.fix: 10 passes
#   q2nfused  Kernel.zipb (F3), Kernel.zipv (F1 + F2: 1.0 a 1-slot array, discount borrowed with its
#             mask), Kernel.zipv of the two temporaries (the AllValid side the 1-slot ones array)
#
#   q1eval / q2eval  the real evaluator (DF.filter + DF.select, DF.with_columns) once per process: a
#             reference for the kernel-level emulations (today's Eval also compacts the frame's other
#             columns and runs its checks), not a cell of the comparison
#
# The timed window runs `reps` repetitions (the frame comes back each time; the output is dropped,
# its row count / first word kept as the data dependency); one untimed run after the clock prints a
# checksum that today's and the fused variant must agree on (q1: kept rows and the wrapping sum of
# the compacted id, region and price bits; q2: the wrapping sum of the revenue's f32 bits).
#   ~/.bend/bin/bend bench/w4/fused.bend -o build/w4/fused && build/w4/fused --threads 1 q1fused 20
#   python3 -I bench/w4/run.py build/w4/fused bench/w4/results/t41_probe.jsonl 7 40   (interleaved cells)
import Base
import ./../../frame.bend as DF
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/kernels.bend as K

# ---- data: 2^20 rows ------------------------------------------------------------------------------

def D() -> Nat:
  20n

def N() -> U32:
  1048576

def Gen.ok(+i: U32) -> U32:
  Bool.to_u32(U32.is_gt(U32.mod(U32.mul(i, 7919), 13), 4))

def Gen.qty(+i: U32) -> U32:
  U32.mod(U32.mul(i, 2654435761), 100)

def Gen.rg(+i: U32) -> U32:
  U32.and(i, 7)

def Gen.price(+i: U32) -> F32:
  F32.div(U32.to_f32(U32.mod(U32.mul(i, 31), 1000)), 10.0)

# discount: null every 10th row (the slot holds the default 0.0, the P0 invariant)
def Gen.disc(+i: U32) -> F32:
  Bool.pick(F32, U32.is_zero(U32.mod(i, 10)), 0.0, F32.div(U32.to_f32(U32.mod(U32.mul(i, 17), 31)), 100.0))

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

# the frame's buffers: ok, qty, id, region codes, discount validity (words), price, discount (f32)
type Flat is Type:
  Flat{ok: Array<U32>, qty: Array<U32>, id: Array<U32>, rg: Array<U32>, vd: Array<U32>, pr: Array<F32>, ds: Array<F32>}

def Flat.gen(+d: Nat) -> Flat:
  Flat{GenU(~(i => Gen.ok(i)), d), GenU(~(i => Gen.qty(i)), d), K.Kernel.iota(U32.shln(1, d), d), GenU(~(i => Gen.rg(i)), d), GenU(~(i => Gen.vdisc(i)), d), GenF(~(i => Gen.price(i)), d), GenF(~(i => Gen.disc(i)), d)}

type St is Type:
  St{f: Flat, acc: U32}

# ---- checksums --------------------------------------------------------------------------------------

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

# ---- today's compaction, repeatable: Kernel.compact_keep's loop (the same step,
# Kernel.compact.put reading a[i]) handing its input back so the frame survives the rep ----------------

type CK<-T: Data> is Type:
  CK{a: Array<T>, o: Array<T>, m: Array<U32>}

def CK.go(~T: Data, n: Nat, +i: U32, +k: U32, ao: Array<T> & Array<T>, mi: Array<U32> & U32) -> CK<T>:
  match n:
    case 0n:
      (a, out) = ao
      (mask, bit) = mi
      CK{a, out, mask}
    case 1n+p:
      (a, out) = ao
      (mask, bit) = mi
      +j = U32.inc(i)
      CK.go(~T, p, j, U32.add(k, bit), K.Kernel.compact.put(~T, out, k, Array.get(T, a, i)), Array.get(U32, mask, j))

def CK.run(~T: Data, +n: U32, +d: Nat, a: Array<T>, m: Array<U32>, +z: T) -> CK<T>:
  CK.go(~T, U32.to_nat(n), 0, 0, (a, Array.new(T, d, z)), Array.get(U32, m, 0))

# ---- q1 today ------------------------------------------------------------------------------------

# Eval: ICol ok, ICol qty (copies), Lit 50 broadcast, Gt (zip), And (zip), Eval.pred, popcount
def Q1T.pred(+n: U32, +d: Nat, ok: Array<U32>, qty: Array<U32>) -> Array<U32> & U32:
  K.Kernel.popcount(n, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => U32.and(x, y)), n, d, ok, K.Kernel.zip(~U32, ~U32, ~U32, ~(x => y => Bool.to_u32(U32.is_gt(x, y))), n, d, qty, Array.new(U32, d, 50), 0), 0))

# the compacted id's first word survives (the data dependency); 5 or 3 columns compacted
def Q1T.c5(+acc: U32, +kept: U32, vd: Array<U32>, ds: Array<F32>, r1: CK<U32>, r2: CK<U32>, r3: CK<U32>, r4: CK<U32>, r5: CK<F32>) -> St:
  match r1 r2 r3 r4 r5:
    case CK{a1, o1, m1} CK{a2, o2, m2} CK{a3, o3, m3} CK{a4, o4, m4} CK{a5, o5, m5}:
      St{Flat{a1, a2, a3, a4, vd, a5, ds}, U32.add(acc, kept)}

def Q1T.c3(+acc: U32, +kept: U32, ok: Array<U32>, qty: Array<U32>, vd: Array<U32>, ds: Array<F32>, r3: CK<U32>, r4: CK<U32>, r5: CK<F32>) -> St:
  match r3 r4 r5:
    case CK{a3, o3, m3} CK{a4, o4, m4} CK{a5, o5, m5}:
      St{Flat{ok, qty, a3, a4, vd, a5, ds}, U32.add(acc, kept)}

# five compactions with the same mask, chained (each hands the mask back)
def Q1T.k5e(+n: U32, +kd: Nat, +acc: U32, +kept: U32, vd: Array<U32>, ds: Array<F32>, r1: CK<U32>, r2: CK<U32>, r3: CK<U32>, r4: CK<U32>, pr: Array<F32>) -> St:
  match r4:
    case CK{a4, o4, m}:
      Q1T.c5(acc, kept, vd, ds, r1, r2, r3, CK{a4, o4, Array.new(U32, 0n, 0)}, CK.run(~F32, n, kd, pr, m, 0.0))

def Q1T.k5d(+n: U32, +kd: Nat, +acc: U32, +kept: U32, vd: Array<U32>, ds: Array<F32>, r1: CK<U32>, r2: CK<U32>, r3: CK<U32>, rg: Array<U32>, pr: Array<F32>) -> St:
  match r3:
    case CK{a3, o3, m}:
      Q1T.k5e(n, kd, acc, kept, vd, ds, r1, r2, CK{a3, o3, Array.new(U32, 0n, 0)}, CK.run(~U32, n, kd, rg, m, 0), pr)

def Q1T.k5c(+n: U32, +kd: Nat, +acc: U32, +kept: U32, vd: Array<U32>, ds: Array<F32>, r1: CK<U32>, r2: CK<U32>, id: Array<U32>, rg: Array<U32>, pr: Array<F32>) -> St:
  match r2:
    case CK{a2, o2, m}:
      Q1T.k5d(n, kd, acc, kept, vd, ds, r1, CK{a2, o2, Array.new(U32, 0n, 0)}, CK.run(~U32, n, kd, id, m, 0), rg, pr)

def Q1T.k5b(+n: U32, +kd: Nat, +acc: U32, +kept: U32, qty: Array<U32>, vd: Array<U32>, ds: Array<F32>, r1: CK<U32>, id: Array<U32>, rg: Array<U32>, pr: Array<F32>) -> St:
  match r1:
    case CK{a1, o1, m}:
      Q1T.k5c(n, kd, acc, kept, vd, ds, CK{a1, o1, Array.new(U32, 0n, 0)}, CK.run(~U32, n, kd, qty, m, 0), id, rg, pr)

def Q1T.k3c(+n: U32, +kd: Nat, +acc: U32, +kept: U32, ok: Array<U32>, qty: Array<U32>, vd: Array<U32>, ds: Array<F32>, r3: CK<U32>, r4: CK<U32>, pr: Array<F32>) -> St:
  match r4:
    case CK{a4, o4, m}:
      Q1T.c3(acc, kept, ok, qty, vd, ds, r3, CK{a4, o4, Array.new(U32, 0n, 0)}, CK.run(~F32, n, kd, pr, m, 0.0))

def Q1T.k3b(+n: U32, +kd: Nat, +acc: U32, +kept: U32, ok: Array<U32>, qty: Array<U32>, vd: Array<U32>, ds: Array<F32>, r3: CK<U32>, rg: Array<U32>, pr: Array<F32>) -> St:
  match r3:
    case CK{a3, o3, m}:
      Q1T.k3c(n, kd, acc, kept, ok, qty, vd, ds, CK{a3, o3, Array.new(U32, 0n, 0)}, CK.run(~U32, n, kd, rg, m, 0), pr)

def Q1T.after2(all: Bool, +n: U32, +kd: Nat, +acc: U32, +kept: U32, ok: Array<U32>, qty: Array<U32>, id: Array<U32>, rg: Array<U32>, vd: Array<U32>, pr: Array<F32>, ds: Array<F32>, m: Array<U32>) -> St:
  match all:
    case True{}:
      Q1T.k5b(n, kd, acc, kept, qty, vd, ds, CK.run(~U32, n, kd, ok, m, 0), id, rg, pr)
    case False{}:
      Q1T.k3b(n, kd, acc, kept, ok, qty, vd, ds, CK.run(~U32, n, kd, id, m, 0), rg, pr)

def Q1T.after(all: Bool, +n: U32, +acc: U32, ok: Array<U32>, qty: Array<U32>, id: Array<U32>, rg: Array<U32>, vd: Array<U32>, pr: Array<F32>, ds: Array<F32>, r: Array<U32> & U32) -> St:
  (m, +kept) = r
  Q1T.after2(all, n, K.Kernel.depth_for(U32.add(kept, 1)), acc, kept, ok, qty, id, rg, vd, pr, ds, m)

def Q1T.t2(all: Bool, +n: U32, +d: Nat, +acc: U32, ok1: Array<U32>, ok2: Array<U32>, id: Array<U32>, rg: Array<U32>, vd: Array<U32>, pr: Array<F32>, ds: Array<F32>, rq: Array<U32> & Array<U32>) -> St:
  (q1, q2) = rq
  Q1T.after(all, n, acc, ok1, q1, id, rg, vd, pr, ds, Q1T.pred(n, d, ok2, q2))

def Q1T.t1(all: Bool, +n: U32, +d: Nat, +acc: U32, qty: Array<U32>, id: Array<U32>, rg: Array<U32>, vd: Array<U32>, pr: Array<F32>, ds: Array<F32>, rok: Array<U32> & Array<U32>) -> St:
  (ok1, ok2) = rok
  Q1T.t2(all, n, d, acc, ok1, ok2, id, rg, vd, pr, ds, Array.clone(U32, qty))

def Q1T.rep(reps: Nat, +all: Bool, +n: U32, +d: Nat, st: St) -> St:
  match reps st:
    case 0n St{f, acc}:
      St{f, acc}
    case 1n+p St{Flat{ok, qty, id, rg, vd, pr, ds}, acc}:
      Q1T.rep(p, all, n, d, Q1T.t1(all, n, d, acc, qty, id, rg, vd, pr, ds, Array.clone(U32, ok)))

# ---- q1 fused ------------------------------------------------------------------------------------

def Q1F.c(+acc: U32, ok: Array<U32>, qty: Array<U32>, vd: Array<U32>, ds: Array<F32>, r: K.C3<U32, U32, F32>) -> St:
  match r:
    case K.C3{o1, o2, o3, m, a1, a2, a3, +k}:
      St{Flat{ok, qty, a1, a2, vd, a3, ds}, U32.add(acc, k)}

def Q1F.p(+n: U32, +acc: U32, id: Array<U32>, rg: Array<U32>, vd: Array<U32>, pr: Array<F32>, ds: Array<F32>, r: K.PC<U32, U32>) -> St:
  match r:
    case K.PC{m, +kept, ok, v1, qty, v2}:
      Q1F.c(acc, ok, qty, vd, ds, K.Kernel.compact3(~U32, ~U32, ~F32, n, K.Kernel.depth_for(U32.add(kept, 1)), m, id, rg, pr, 0, 0, 0.0))

def Q1F.rep(reps: Nat, +n: U32, +d: Nat, st: St) -> St:
  match reps st:
    case 0n St{f, acc}:
      St{f, acc}
    case 1n+p St{Flat{ok, qty, id, rg, vd, pr, ds}, acc}:
      Q1F.rep(p, n, d, Q1F.p(n, acc, id, rg, vd, pr, ds, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, 50, ok, Array.new(U32, 0n, 1), qty, Array.new(U32, 0n, 1))))

# ---- q1 verification (untimed): kept, then the wrapping sum of id + region + price bits ----------------

def chk3(+kept: U32, o1: Array<U32>, o2: Array<U32>, o3: Array<F32>) -> U32 & U32:
  (kept, U32.add(U32.add(Sum(kept, o1), Sum(kept, o2)), SumB(kept, o3)))

def Q1T.v3(+kept: U32, r1: CK<U32>, r2: CK<U32>, r3: CK<F32>) -> U32 & U32:
  match r1 r2 r3:
    case CK{a1, o1, m1} CK{a2, o2, m2} CK{a3, o3, m3}:
      chk3(kept, o1, o2, o3)

def Q1T.v2c(+n: U32, +kd: Nat, +kept: U32, pr: Array<F32>, r1: CK<U32>, r2: CK<U32>) -> U32 & U32:
  match r2:
    case CK{a2, o2, m}:
      Q1T.v3(kept, r1, CK{a2, o2, Array.new(U32, 0n, 0)}, CK.run(~F32, n, kd, pr, m, 0.0))

def Q1T.v2b(+n: U32, +kd: Nat, +kept: U32, rg: Array<U32>, pr: Array<F32>, r1: CK<U32>) -> U32 & U32:
  match r1:
    case CK{a1, o1, m}:
      Q1T.v2c(n, kd, kept, pr, CK{a1, o1, Array.new(U32, 0n, 0)}, CK.run(~U32, n, kd, rg, m, 0))

def Q1T.v2(+n: U32, id: Array<U32>, rg: Array<U32>, pr: Array<F32>, r: Array<U32> & U32) -> U32 & U32:
  (m, +kept) = r
  +kd = K.Kernel.depth_for(U32.add(kept, 1))
  Q1T.v2b(n, kd, kept, rg, pr, CK.run(~U32, n, kd, id, m, 0))

def Q1T.verify(+n: U32, +d: Nat, f: Flat) -> U32 & U32:
  match f:
    case Flat{ok, qty, id, rg, vd, pr, ds}:
      Q1T.v2(n, id, rg, pr, Q1T.pred(n, d, ok, qty))

def Q1F.v2(r: K.C3<U32, U32, F32>) -> U32 & U32:
  match r:
    case K.C3{o1, o2, o3, m, a1, a2, a3, +k}:
      chk3(k, o1, o2, o3)

def Q1F.v1(+n: U32, id: Array<U32>, rg: Array<U32>, pr: Array<F32>, r: K.PC<U32, U32>) -> U32 & U32:
  match r:
    case K.PC{m, +kept, ok, v1, qty, v2}:
      Q1F.v2(K.Kernel.compact3(~U32, ~U32, ~F32, n, K.Kernel.depth_for(U32.add(kept, 1)), m, id, rg, pr, 0, 0, 0.0))

def Q1F.verify(+n: U32, +d: Nat, f: Flat) -> U32 & U32:
  match f:
    case Flat{ok, qty, id, rg, vd, pr, ds}:
      Q1F.v1(n, id, rg, pr, K.Kernel.pred_count(~U32, ~U32, ~U32, ~(p => x => y => U32.and(x, Bool.to_u32(U32.is_gt(y, p)))), n, d, 50, ok, Array.new(U32, 0n, 1), qty, Array.new(U32, 0n, 1)))

# ---- q2 today ------------------------------------------------------------------------------------

# Eval on the expression tree: Cast(qty) map, Mul zip, Lit 1.0 broadcast, fill_null(discount, 0.0) =
# Lit 0.0 broadcast + Kernel.choose (discount's mask), Sub zip, Mul zip (every fix a no-op: AllValid)
def Q2T.fill(r: Array<U32> & Array<F32>) -> Array<F32>:
  (m, x) = r
  x

def Q2T.expr(+n: U32, +d: Nat, q: Array<U32>, p: Array<F32>, vd: Array<U32>, ds: Array<F32>) -> Array<F32>:
  K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, K.Kernel.map(~U32, ~F32, ~(w => U32.to_f32(w)), n, d, q, 0.0), p, 0.0), K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.sub(x, y)), n, d, Array.new(F32, d, 1.0), Q2T.fill(K.Kernel.choose(~F32, n, vd, ds, Array.new(F32, d, 0.0))), 0.0), 0.0)

def Q2T.t5(+acc: U32, f: Flat, r: Array<F32> & F32) -> St:
  (a, +x) = r
  St{f, U32.add(acc, F32.bits(x))}

def Q2T.t4(+n: U32, +d: Nat, +acc: U32, ok: Array<U32>, id: Array<U32>, rg: Array<U32>, q1: Array<U32>, p1: Array<F32>, d1: Array<F32>, q2: Array<U32>, p2: Array<F32>, d2: Array<F32>, rv: Array<U32> & Array<U32>) -> St:
  (v1, v2) = rv
  Q2T.t5(acc, Flat{ok, q1, id, rg, v1, p1, d1}, Array.get(F32, Q2T.expr(n, d, q2, p2, v2, d2), 1))

def Q2T.t3(+n: U32, +d: Nat, +acc: U32, ok: Array<U32>, id: Array<U32>, rg: Array<U32>, vd: Array<U32>, q1: Array<U32>, p1: Array<F32>, q2: Array<U32>, p2: Array<F32>, rd: Array<F32> & Array<F32>) -> St:
  (d1, d2) = rd
  Q2T.t4(n, d, acc, ok, id, rg, q1, p1, d1, q2, p2, d2, Array.clone(U32, vd))

def Q2T.t2(+n: U32, +d: Nat, +acc: U32, ok: Array<U32>, id: Array<U32>, rg: Array<U32>, vd: Array<U32>, ds: Array<F32>, q1: Array<U32>, q2: Array<U32>, rp: Array<F32> & Array<F32>) -> St:
  (p1, p2) = rp
  Q2T.t3(n, d, acc, ok, id, rg, vd, q1, p1, q2, p2, Array.clone(F32, ds))

def Q2T.t1(+n: U32, +d: Nat, +acc: U32, ok: Array<U32>, id: Array<U32>, rg: Array<U32>, vd: Array<U32>, pr: Array<F32>, ds: Array<F32>, rq: Array<U32> & Array<U32>) -> St:
  (q1, q2) = rq
  Q2T.t2(n, d, acc, ok, id, rg, vd, ds, q1, q2, Array.clone(F32, pr))

def Q2T.rep(reps: Nat, +n: U32, +d: Nat, st: St) -> St:
  match reps st:
    case 0n St{f, acc}:
      St{f, acc}
    case 1n+p St{Flat{ok, qty, id, rg, vd, pr, ds}, acc}:
      Q2T.rep(p, n, d, Q2T.t1(n, d, acc, ok, id, rg, vd, pr, ds, Array.clone(U32, qty)))

def Q2T.verify(+n: U32, +d: Nat, f: Flat) -> U32 & U32:
  match f:
    case Flat{ok, qty, id, rg, vd, pr, ds}:
      (n, SumB(n, Q2T.expr(n, d, qty, pr, vd, ds)))

# ---- q2 fused ------------------------------------------------------------------------------------

def Q2F.t2(+n: U32, +d: Nat, +acc: U32, ok: Array<U32>, id: Array<U32>, rg: Array<U32>, vd: Array<U32>, qty: Array<U32>, pr: Array<F32>, t: Array<F32>, r: Array<F32> & Array<F32>) -> St:
  (s, ds) = r
  Q2T.t5(acc, Flat{ok, qty, id, rg, vd, pr, ds}, Array.get(F32, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, t, s, 0.0), 1))

def Q2F.t1(+n: U32, +d: Nat, +acc: U32, ok: Array<U32>, id: Array<U32>, rg: Array<U32>, vd: Array<U32>, ds: Array<F32>, r: K.ZB<U32, F32, F32>) -> St:
  match r:
    case K.ZB{t, qty, pr}:
      Q2F.t2(n, d, acc, ok, id, rg, vd, qty, pr, t, K.Kernel.map_pb(~F32, ~F32, ~F32, ~(p => x => F32.sub(p, x)), n, d, ds, 1.0, 0.0))

def Q2F.rep(reps: Nat, +n: U32, +d: Nat, st: St) -> St:
  match reps st:
    case 0n St{f, acc}:
      St{f, acc}
    case 1n+p St{Flat{ok, qty, id, rg, vd, pr, ds}, acc}:
      Q2F.rep(p, n, d, Q2F.t1(n, d, acc, ok, id, rg, vd, ds, K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), n, d, qty, pr, 0.0)))

def Q2F.v2(+n: U32, +d: Nat, t: Array<F32>, r: Array<F32> & Array<F32>) -> U32 & U32:
  (s, ds) = r
  (n, SumB(n, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, t, s, 0.0)))

def Q2F.v1(+n: U32, +d: Nat, ds: Array<F32>, r: K.ZB<U32, F32, F32>) -> U32 & U32:
  match r:
    case K.ZB{t, qty, pr}:
      Q2F.v2(n, d, t, K.Kernel.map_pb(~F32, ~F32, ~F32, ~(p => x => F32.sub(p, x)), n, d, ds, 1.0, 0.0))

def Q2F.verify(+n: U32, +d: Nat, f: Flat) -> U32 & U32:
  match f:
    case Flat{ok, qty, id, rg, vd, pr, ds}:
      Q2F.v1(n, d, ds, K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), n, d, qty, pr, 0.0))

# ---- q2 with a nullable discount and no fill_null (the spike's q2'): F2 ---------------------------------
# rev = f32(qty) * price * (1.0 - discount), null where discount is null (the slot reset to 0.0)

# today: qty, price, discount data + mask copied, cast map, zip mul, broadcast 1.0, zip sub, Eval.fix
# (mask_data over discount's mask), zip mul (vand AllValid & Mask = the same mask), Eval.fix again
def Q2N.e2(+n: U32, +d: Nat, t: Array<F32>, r: Array<F32> & Array<U32>) -> Array<F32> & Array<U32>:
  (s, m) = r
  K.Kernel.mask_data(~F32, n, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, t, s, 0.0), m, 0.0)

def Q2N.expr(+n: U32, +d: Nat, q: Array<U32>, p: Array<F32>, vd: Array<U32>, ds: Array<F32>) -> Array<F32> & Array<U32>:
  Q2N.e2(n, d, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, K.Kernel.map(~U32, ~F32, ~(w => U32.to_f32(w)), n, d, q, 0.0), p, 0.0), K.Kernel.mask_data(~F32, n, K.Kernel.zip(~F32, ~F32, ~F32, ~(x => y => F32.sub(x, y)), n, d, Array.new(F32, d, 1.0), ds, 0.0), vd, 0.0))

def Q2N.t5(+acc: U32, f: Flat, r: Array<F32> & Array<U32>) -> St:
  (x, m) = r
  Q2T.t5(acc, f, Array.get(F32, x, 1))

def Q2N.t4(+n: U32, +d: Nat, +acc: U32, ok: Array<U32>, id: Array<U32>, rg: Array<U32>, q1: Array<U32>, p1: Array<F32>, d1: Array<F32>, q2: Array<U32>, p2: Array<F32>, d2: Array<F32>, rv: Array<U32> & Array<U32>) -> St:
  (v1, v2) = rv
  Q2N.t5(acc, Flat{ok, q1, id, rg, v1, p1, d1}, Q2N.expr(n, d, q2, p2, v2, d2))

def Q2N.t3(+n: U32, +d: Nat, +acc: U32, ok: Array<U32>, id: Array<U32>, rg: Array<U32>, vd: Array<U32>, q1: Array<U32>, p1: Array<F32>, q2: Array<U32>, p2: Array<F32>, rd: Array<F32> & Array<F32>) -> St:
  (d1, d2) = rd
  Q2N.t4(n, d, acc, ok, id, rg, q1, p1, d1, q2, p2, d2, Array.clone(U32, vd))

def Q2N.t2(+n: U32, +d: Nat, +acc: U32, ok: Array<U32>, id: Array<U32>, rg: Array<U32>, vd: Array<U32>, ds: Array<F32>, q1: Array<U32>, q2: Array<U32>, rp: Array<F32> & Array<F32>) -> St:
  (p1, p2) = rp
  Q2N.t3(n, d, acc, ok, id, rg, vd, q1, p1, q2, p2, Array.clone(F32, ds))

def Q2N.t1(+n: U32, +d: Nat, +acc: U32, ok: Array<U32>, id: Array<U32>, rg: Array<U32>, vd: Array<U32>, pr: Array<F32>, ds: Array<F32>, rq: Array<U32> & Array<U32>) -> St:
  (q1, q2) = rq
  Q2N.t2(n, d, acc, ok, id, rg, vd, ds, q1, q2, Array.clone(F32, pr))

def Q2N.rep(reps: Nat, +n: U32, +d: Nat, st: St) -> St:
  match reps st:
    case 0n St{f, acc}:
      St{f, acc}
    case 1n+p St{Flat{ok, qty, id, rg, vd, pr, ds}, acc}:
      Q2N.rep(p, n, d, Q2N.t1(n, d, acc, ok, id, rg, vd, pr, ds, Array.clone(U32, qty)))

# (valid count, wrapping sum of the f32 bits)
def Q2N.chk(+n: U32, r: Array<F32> & Array<U32>) -> U32 & U32:
  (x, m) = r
  (Sum(n, m), SumB(n, x))

def Q2N.verify(+n: U32, +d: Nat, f: Flat) -> U32 & U32:
  match f:
    case Flat{ok, qty, id, rg, vd, pr, ds}:
      Q2N.chk(n, Q2N.expr(n, d, qty, pr, vd, ds))

# fused: zipb (F3) over the borrowed qty and price, zipv (F1 + F2: the literal 1.0 as a 1-slot array, the
# AllValid side the 1-slot ones array) over the borrowed discount, zipv of the two temporaries
def Q2NF.zv(r: K.ZV<F32, F32, F32>) -> Array<F32> & Array<U32>:
  match r:
    case K.ZV{o, vo, a, va, b, vb}:
      (o, vo)

def Q2NF.mul(+n: U32, +d: Nat, t: Array<F32>, r: K.ZV<F32, F32, F32>) -> (Array<F32> & Array<U32>) & Array<U32> & Array<F32>:
  match r:
    case K.ZV{u, vu, one, ones, ds, vd}:
      (Q2NF.zv(K.Kernel.zipv(~F32, ~F32, ~F32, ~(x => y => F32.mul(x, y)), n, d, t, Array.new(U32, 0n, 1), u, vu, 0.0)), vd, ds)

def Q2NF.t2(+acc: U32, ok: Array<U32>, id: Array<U32>, rg: Array<U32>, qty: Array<U32>, pr: Array<F32>, r: (Array<F32> & Array<U32>) & Array<U32> & Array<F32>) -> St:
  (rv, vd, ds) = r
  Q2N.t5(acc, Flat{ok, qty, id, rg, vd, pr, ds}, rv)

def Q2NF.t1(+n: U32, +d: Nat, +acc: U32, ok: Array<U32>, id: Array<U32>, rg: Array<U32>, vd: Array<U32>, ds: Array<F32>, r: K.ZB<U32, F32, F32>) -> St:
  match r:
    case K.ZB{t, qty, pr}:
      Q2NF.t2(acc, ok, id, rg, qty, pr, Q2NF.mul(n, d, t, K.Kernel.zipv(~F32, ~F32, ~F32, ~(x => y => F32.sub(x, y)), n, d, Array.new(F32, 0n, 1.0), Array.new(U32, 0n, 1), ds, vd, 0.0)))

def Q2NF.rep(reps: Nat, +n: U32, +d: Nat, st: St) -> St:
  match reps st:
    case 0n St{f, acc}:
      St{f, acc}
    case 1n+p St{Flat{ok, qty, id, rg, vd, pr, ds}, acc}:
      Q2NF.rep(p, n, d, Q2NF.t1(n, d, acc, ok, id, rg, vd, ds, K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), n, d, qty, pr, 0.0)))

def Q2NF.v2(+n: U32, r: (Array<F32> & Array<U32>) & Array<U32> & Array<F32>) -> U32 & U32:
  (rv, vd, ds) = r
  Q2N.chk(n, rv)

def Q2NF.v1(+n: U32, +d: Nat, vd: Array<U32>, ds: Array<F32>, r: K.ZB<U32, F32, F32>) -> U32 & U32:
  match r:
    case K.ZB{t, qty, pr}:
      Q2NF.v2(n, Q2NF.mul(n, d, t, K.Kernel.zipv(~F32, ~F32, ~F32, ~(x => y => F32.sub(x, y)), n, d, Array.new(F32, 0n, 1.0), Array.new(U32, 0n, 1), ds, vd, 0.0)))

def Q2NF.verify(+n: U32, +d: Nat, f: Flat) -> U32 & U32:
  match f:
    case Flat{ok, qty, id, rg, vd, pr, ds}:
      Q2NF.v1(n, d, vd, ds, K.Kernel.zipb(~U32, ~F32, ~F32, ~(x => y => F32.mul(U32.to_f32(x), y)), n, d, qty, pr, 0.0))

# ---- driver ------------------------------------------------------------------------------------------

def run(+mode: String, reps: Nat, f: Flat) -> St:
  match mode:
    case "q1today":
      Q1T.rep(reps, True{}, N(), D(), St{f, 0})
    case "q1today3":
      Q1T.rep(reps, False{}, N(), D(), St{f, 0})
    case "q1fused":
      Q1F.rep(reps, N(), D(), St{f, 0})
    case "q2today":
      Q2T.rep(reps, N(), D(), St{f, 0})
    case "q2ntoday":
      Q2N.rep(reps, N(), D(), St{f, 0})
    case "q2nfused":
      Q2NF.rep(reps, N(), D(), St{f, 0})
    case _:
      Q2F.rep(reps, N(), D(), St{f, 0})

def verify(+mode: String, f: Flat) -> U32 & U32:
  match mode:
    case "q1today":
      Q1T.verify(N(), D(), f)
    case "q1today3":
      Q1T.verify(N(), D(), f)
    case "q1fused":
      Q1F.verify(N(), D(), f)
    case "q2today":
      Q2T.verify(N(), D(), f)
    case "q2ntoday":
      Q2N.verify(N(), D(), f)
    case "q2nfused":
      Q2NF.verify(N(), D(), f)
    case _:
      Q2F.verify(N(), D(), f)

def show(+mode: String, +reps: U32, +ms: U32, +acc: U32, r: U32 & U32) -> String:
  (k, s) = r
  "{\"mode\":\"" ++ mode ++ "\",\"rows\":1048576,\"reps\":" ++ U32.show(reps) ++ ",\"ms_total\":" ++ U32.show(ms) ++ ",\"acc\":" ++ U32.show(acc) ++ ",\"check_k\":" ++ U32.show(k) ++ ",\"check_s\":" ++ U32.show(s) ++ "}"

# ---- the real evaluator (one run per process: Eval consumes the frame) -------------------------------
# q1eval: DF.filter(ok & (qty > 50)) then DF.select(id, region, price) over the frame (region as u32
# codes); q2eval: DF.with_columns(revenue) over qty, price and the nullable discount. Prints the result's
# height; the time is ONE run at the 1 ms clock: a reference for the kernel-level q1today / q2today
# emulations above, not a cell of the comparison

def Real.frame(f: Flat) -> C.Frame:
  match f:
    case Flat{ok, qty, id, rg, vd, pr, ds}:
      C.Frame{N(), [C.Named{"ok", C.CBool{N(), D(), C.AllValid{}, ok}}, C.Named{"qty", C.CU32{N(), D(), C.AllValid{}, qty}}, C.Named{"id", C.CU32{N(), D(), C.AllValid{}, id}}, C.Named{"region", C.CU32{N(), D(), C.AllValid{}, rg}}, C.Named{"price", C.CF32{N(), D(), C.AllValid{}, pr}}, C.Named{"discount", C.CF32{N(), D(), C.Mask{vd}, ds}}]}

def Real.h2(r: C.Frame & U32) -> U32:
  (g, +h) = r
  h

def Real.h(r: E.ResT(C.Frame)) -> U32:
  match r:
    case Done{g}:
      Real.h2(DF.height(g))
    case Fail{e}:
      4294967295

def Real.q1b(r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Done{g}:
      DF.select(g, [DF.col("id"), DF.col("region"), DF.col("price")])
    case Fail{e}:
      Fail{e}

def Real.run(+mode: String, f: C.Frame) -> U32:
  match mode:
    case "q1eval":
      Real.h(Real.q1b(DF.filter(f, DF.and(DF.col("ok"), DF.gt(DF.col("qty"), DF.lit_u32(50))))))
    case _:
      Real.h(DF.with_columns(f, [DF.alias(DF.mul(DF.mul(DF.cast_f32(DF.col("qty")), DF.col("price")), DF.sub(DF.lit_f32(1.0), DF.fill_null(DF.col("discount"), DF.lit_f32(0.0)))), "revenue")]))

def Real.timed(+mode: String, f: C.Frame) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    h : U32 <- IO.pure(U32, Real.run(mode, f))
    t1 : Nat <- IO.now()
    IO.print(show(mode, 1, U32.from_nat(Nat.sub(t1, t0)), 0, (h, 0)))

def fin(+mode: String, +reps: U32, +t0: Nat, +t1: Nat, st: St) -> String:
  match st:
    case St{f, acc}:
      show(mode, reps, U32.from_nat(Nat.sub(t1, t0)), acc, verify(mode, f))

def timed(+mode: String, +reps: U32, f: Flat) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    st : St <- IO.pure(St, run(mode, U32.to_nat(reps), f))
    t1 : Nat <- IO.now()
    IO.print(fin(mode, reps, t0, t1, st))

def nat_of.k(m: Maybe<&2, Nat>, +dflt: Nat) -> Nat:
  match m:
    case Some{v}:
      v
    case None{}:
      dflt

def go2(real: Bool, +mode: String, +reps: U32) -> IO(Unit):
  match real:
    case True{}:
      Real.timed(mode, Real.frame(Flat.gen(D())))
    case False{}:
      timed(mode, reps, Flat.gen(D()))

def go(args: List<String>) -> IO(Unit):
  match args:
    case exe <> +mode <> reps <> Nil{}:
      go2(Bool.or(String.eq(mode, "q1eval"), String.eq(mode, "q2eval")), mode, U32.from_nat(nat_of.k(Nat.read(reps), 10n)))
    case _:
      IO.print("usage: fused <q1today|q1today3|q1fused|q2today|q2fused|q2ntoday|q2nfused|q1eval|q2eval> <reps>")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
