# T5.1 (DESIGN.md 16.1 D1): the builder and flatten at the production grain 2^14 around the leaf
# boundary: n = 0, 1, 2^14 - 1, 2^14 (one leaf: the buffer moved), 2^14 + 1 (a full leaf and a 1-row
# leaf), 3 * 2^14 + 5, 2^20 (64 full leaves, a perfect tree of depth 6). For each size and each payload
# kind (U32 words, F32 with NaN / -0.0 / inf / subnormal bits, Raw strings up to 3 * 2^14 + 5 rows) the
# line prints the skeleton summary (leaves, tree height, first and last leaf rows, `ok` = every node's
# counts are exact) and `rt` = flatten(of(src)) equals src in every row (F32 by bits). Expected values:
# leaves = ceil(n / 2^14) (1 for n <= 2^14), last leaf = n - 2^14 * (leaves - 1); heights of the
# binary-counter fold: 2 leaves -> 1; 3 * 2^14 + 5 is leaves 16384 x 3 then 5, and leaf 3 merges
# tz(4) = 2 times -> ((L L) (L 5)), height 2; 64 leaves -> a perfect tree of height 6.
import Base
import ./../src/kernels.bend as K
import ./../src/chunks.bend as CH

# u[i] = i * 2654435761 + 12345 (wrapping)
def gu.go(f: Nat, +i: U32, out: Array<U32>) -> Array<U32>:
  match f:
    case 0n:
      out
    case 1n+p:
      gu.go(p, U32.inc(i), Array.set(U32, out, i, U32.add(U32.mul(i, 2654435761), 12345)))

def gu(+n: U32, +d: Nat) -> Array<U32>:
  gu.go(U32.to_nat(n), 0, Array.new(U32, d, 0))

# f[i]: NaN every 97th row, -0.0 every 89th, +inf every 83rd, a subnormal every 79th, else i / 7
def gf.v(+i: U32) -> F32:
  Bool.pick(F32, U32.is_zero(U32.mod(i, 97)), F32.div(0.0, 0.0), Bool.pick(F32, U32.is_zero(U32.mod(i, 89)), F32.neg(0.0), Bool.pick(F32, U32.is_zero(U32.mod(i, 83)), F32.div(1.0, 0.0), Bool.pick(F32, U32.is_zero(U32.mod(i, 79)), F32.div(1.0e-38, 1000.0), F32.div(U32.to_f32(i), 7.0)))))

def gf.go(f: Nat, +i: U32, out: Array<F32>) -> Array<F32>:
  match f:
    case 0n:
      out
    case 1n+p:
      gf.go(p, U32.inc(i), Array.set(F32, out, i, gf.v(i)))

def gf(+n: U32, +d: Nat) -> Array<F32>:
  gf.go(U32.to_nat(n), 0, Array.new(F32, d, 0.0))

def gs.go(f: Nat, +i: U32, out: Array<String>) -> Array<String>:
  match f:
    case 0n:
      out
    case 1n+p:
      gs.go(p, U32.inc(i), Array.set(String, out, i, "r" ++ U32.show(U32.mod(U32.mul(i, 31), 1000))))

def gs(+n: U32, +d: Nat) -> Array<String>:
  gs.go(U32.to_nat(n), 0, Array.new(String, d, ""))

def dep(+n: U32) -> Nat:
  K.Kernel.depth_for(U32.max(n, 1))

# ---- skeleton summary --------------------------------------------------------------------------

type Sum is Data:
  Sum{leaves: U32, height: U32, first: U32, last: U32, ok: Bool}

def sum.node(+rows: U32, +lrows: U32, +lr: U32, +rr: U32, a: Sum, b: Sum) -> Sum:
  match a b:
    case Sum{la, ha, fa, ta, oa} Sum{lb, hb, fb, tb, ob}:
      Sum{U32.add(la, lb), U32.inc(U32.max(ha, hb)), fa, tb, Bool.and(Bool.and(oa, ob), Bool.and(U32.is_eq(lrows, lr), U32.is_eq(rows, U32.add(lrows, rr))))}

def sum(s: CH.Skel) -> Sum:
  match s:
    case CH.KLeaf{+n}:
      Sum{1, 0, n, n, True{}}
    case CH.KNode{+rows, +lrows, +l, +r}:
      sum.node(rows, lrows, CH.Skel.rows(l), CH.Skel.rows(r), sum(l), sum(r))

def ok_show(b: Bool) -> String:
  match b:
    case True{}:
      "ok"
    case False{}:
      "BAD"

def sum.show(s: Sum) -> String:
  match s:
    case Sum{l, h, f, t, ok}:
      "leaves " ++ U32.show(l) ++ " height " ++ U32.show(h) ++ " first " ++ U32.show(f) ++ " last " ++ U32.show(t) ++ " " ++ ok_show(ok)

# ---- one line per size and kind ----------------------------------------------------------------

def same(b: Bool) -> String:
  match b:
    case True{}:
      "rt same"
    case False{}:
      "rt DIFF"

def w.k(+n: U32, s: CH.Skel, r: CH.CW & U32) -> String:
  (t, +rows) = r
  sum.show(sum(s)) ++ " rows " ++ U32.show(rows) ++ " " ++ same(K.Kernel.all_eq(~U32, ~(x => y => U32.is_eq(x, y)), n, CH.CW.flatten(dep(rows), t), gu(n, dep(n))))

def w.a(+n: U32, r: CH.CW & CH.Skel) -> String:
  (t, s) = r
  w.k(n, s, CH.CW.rows(t))

def w(+n: U32) -> String:
  "u32 n=" ++ U32.show(n) ++ " " ++ w.a(n, CH.CW.skel(CH.CW.of(n, dep(n), CH.Ch.grain(), gu(n, dep(n)))))

def f.k(+n: U32, s: CH.Skel, r: CH.CF & U32) -> String:
  (t, +rows) = r
  sum.show(sum(s)) ++ " " ++ same(K.Kernel.all_eq(~F32, ~(x => y => U32.is_eq(F32.bits(x), F32.bits(y))), n, CH.CF.flatten(dep(rows), t), gf(n, dep(n))))

def f.a(+n: U32, r: CH.CF & CH.Skel) -> String:
  (t, s) = r
  f.k(n, s, CH.CF.rows(t))

def f(+n: U32) -> String:
  "f32 n=" ++ U32.show(n) ++ " " ++ f.a(n, CH.CF.skel(CH.CF.of(n, dep(n), CH.Ch.grain(), gf(n, dep(n)))))

def s.k(+n: U32, sk: CH.Skel, r: CH.CS & U32) -> String:
  (t, +rows) = r
  sum.show(sum(sk)) ++ " " ++ same(K.Kernel.all_eq(~String, ~(x => y => String.eq(x, y)), n, CH.CS.flatten(dep(rows), t), gs(n, dep(n))))

def s.a(+n: U32, r: CH.CS & CH.Skel) -> String:
  (t, sk) = r
  s.k(n, sk, CH.CS.rows(t))

def s(+n: U32) -> String:
  "str n=" ++ U32.show(n) ++ " " ++ s.a(n, CH.CS.skel(CH.CS.of(n, dep(n), CH.Ch.grain(), gs(n, dep(n)))))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(w(0))
    IO.print(w(1))
    IO.print(w(16383))
    IO.print(w(16384))
    IO.print(w(16385))
    IO.print(w(49157))
    IO.print(w(1048576))
    IO.print(f(0))
    IO.print(f(1))
    IO.print(f(16383))
    IO.print(f(16384))
    IO.print(f(16385))
    IO.print(f(49157))
    IO.print(f(1048576))
    IO.print(s(0))
    IO.print(s(1))
    IO.print(s(16385))
    IO.print(s(49157))
#|u32 n=0 leaves 1 height 0 first 0 last 0 ok rows 0 rt same
#|u32 n=1 leaves 1 height 0 first 1 last 1 ok rows 1 rt same
#|u32 n=16383 leaves 1 height 0 first 16383 last 16383 ok rows 16383 rt same
#|u32 n=16384 leaves 1 height 0 first 16384 last 16384 ok rows 16384 rt same
#|u32 n=16385 leaves 2 height 1 first 16384 last 1 ok rows 16385 rt same
#|u32 n=49157 leaves 4 height 2 first 16384 last 5 ok rows 49157 rt same
#|u32 n=1048576 leaves 64 height 6 first 16384 last 16384 ok rows 1048576 rt same
#|f32 n=0 leaves 1 height 0 first 0 last 0 ok rt same
#|f32 n=1 leaves 1 height 0 first 1 last 1 ok rt same
#|f32 n=16383 leaves 1 height 0 first 16383 last 16383 ok rt same
#|f32 n=16384 leaves 1 height 0 first 16384 last 16384 ok rt same
#|f32 n=16385 leaves 2 height 1 first 16384 last 1 ok rt same
#|f32 n=49157 leaves 4 height 2 first 16384 last 5 ok rt same
#|f32 n=1048576 leaves 64 height 6 first 16384 last 16384 ok rt same
#|str n=0 leaves 1 height 0 first 0 last 0 ok rt same
#|str n=1 leaves 1 height 0 first 1 last 1 ok rt same
#|str n=16385 leaves 2 height 1 first 16384 last 1 ok rt same
#|str n=49157 leaves 4 height 2 first 16384 last 5 ok rt same
