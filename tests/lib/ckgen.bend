# tests/lib/ckgen.bend -- T5.2 test helpers (tests/ckernels*.bend): deterministic column generators, chunk
# trees built from them, flatten-and-compare helpers. Test-only; tests/lib is not run by scripts/test.sh.
import Base
import ./../../src/kernels.bend as K
import ./../../src/chunks.bend as CH
import ./../../src/ckernels.bend as KC

def dfor(+n: U32) -> Nat:
  K.Kernel.depth_for(U32.max(n, 1))

# ---- generators: out[i] = g(i) for i < n in 2^dfor(n) slots ---------------------------------------

def gw.go(~g: U32 -> U32, f: Nat, +i: U32, out: Array<U32>) -> Array<U32>:
  match f:
    case 0n:
      out
    case 1n+p:
      gw.go(~g, p, U32.inc(i), Array.set(U32, out, i, g(i)))

def gw(~g: U32 -> U32, +n: U32) -> Array<U32>:
  gw.go(~g, U32.to_nat(n), 0, Array.new(U32, dfor(n), 0))

def gfl.go(~g: U32 -> F32, f: Nat, +i: U32, out: Array<F32>) -> Array<F32>:
  match f:
    case 0n:
      out
    case 1n+p:
      gfl.go(~g, p, U32.inc(i), Array.set(F32, out, i, g(i)))

def gfl(~g: U32 -> F32, +n: U32) -> Array<F32>:
  gfl.go(~g, U32.to_nat(n), 0, Array.new(F32, dfor(n), 0.0))

def gst.go(~g: U32 -> String, f: Nat, +i: U32, out: Array<String>) -> Array<String>:
  match f:
    case 0n:
      out
    case 1n+p:
      gst.go(~g, p, U32.inc(i), Array.set(String, out, i, g(i)))

def gst(~g: U32 -> String, +n: U32) -> Array<String>:
  gst.go(~g, U32.to_nat(n), 0, Array.new(String, dfor(n), ""))

# the test columns
def hash(+i: U32, +s: U32) -> U32:
  U32.add(U32.mul(i, 2654435761), s)

def u1(+n: U32) -> Array<U32>:
  gw(~(i => hash(i, 1)), n)

def u2(+n: U32) -> Array<U32>:
  gw(~(i => hash(i, 2)), n)

# q1's columns: ok (bool i mod 3 != 0), qty ((37 i) mod 101), their validity (i mod 7 != 3, i mod 11 != 5)
def ok(+n: U32) -> Array<U32>:
  gw(~(i => Bool.to_u32(U32.is_ne(U32.mod(i, 3), 0))), n)

def qty(+n: U32) -> Array<U32>:
  gw(~(i => U32.mod(U32.mul(i, 37), 101)), n)

def vok(+n: U32) -> Array<U32>:
  gw(~(i => Bool.to_u32(U32.is_ne(U32.mod(i, 7), 3))), n)

def vqty(+n: U32) -> Array<U32>:
  gw(~(i => Bool.to_u32(U32.is_ne(U32.mod(i, 11), 5))), n)

# masks of selectivity 0 / 1 / 50 / 100 %: none, i mod 100 == 0, i odd, all
def msel.v(+s: U32, +i: U32) -> U32:
  Bool.pick(U32, U32.is_eq(s, 0), 0, Bool.pick(U32, U32.is_eq(s, 1), Bool.to_u32(U32.is_zero(U32.mod(i, 100))), Bool.pick(U32, U32.is_eq(s, 50), U32.and(i, 1), 1)))

def gwp.go(~g: U32 -> U32 -> U32, f: Nat, +p: U32, +i: U32, out: Array<U32>) -> Array<U32>:
  match f:
    case 0n:
      out
    case 1n+q:
      gwp.go(~g, q, p, U32.inc(i), Array.set(U32, out, i, g(p, i)))

def msel(+s: U32, +n: U32) -> Array<U32>:
  gwp.go(~(p => i => msel.v(p, i)), U32.to_nat(n), s, 0, Array.new(U32, dfor(n), 0))

# f32: i / 7 with NaN every 97th row, -0.0 every 89th, +inf every 83rd, a subnormal every 79th
def fsp.v(+i: U32) -> F32:
  Bool.pick(F32, U32.is_zero(U32.mod(i, 97)), F32.div(0.0, 0.0), Bool.pick(F32, U32.is_zero(U32.mod(i, 89)), F32.neg(0.0), Bool.pick(F32, U32.is_zero(U32.mod(i, 83)), F32.div(1.0, 0.0), Bool.pick(F32, U32.is_zero(U32.mod(i, 79)), F32.div(1.0e-38, 1000.0), F32.div(U32.to_f32(i), 7.0)))))

def fsp(+n: U32) -> Array<F32>:
  gfl(~(i => fsp.v(i)), n)

# f32 finite, with cancellation: (-1)^i * 1e7 + i / 3
def ffin.v(+i: U32) -> F32:
  F32.add(Bool.pick(F32, U32.is_zero(U32.and(i, 1)), 10000000.0, F32.neg(10000000.0)), F32.div(U32.to_f32(i), 3.0))

def ffin(+n: U32) -> Array<F32>:
  gfl(~(i => ffin.v(i)), n)

def strs(+n: U32) -> Array<String>:
  gst(~(i => "s" ++ U32.show(U32.mod(i, 1000))), n)

# ---- trees ------------------------------------------------------------------------------------------

def tw(+n: U32, +g: Nat, a: Array<U32>) -> CH.CW:
  CH.CW.of(n, dfor(n), g, a)

def tf(+n: U32, +g: Nat, a: Array<F32>) -> CH.CF:
  CH.CF.of(n, dfor(n), g, a)

def ts(+n: U32, +g: Nat, a: Array<String>) -> CH.CS:
  CH.CS.of(n, dfor(n), g, a)

# ---- comparisons ------------------------------------------------------------------------------------

def equ(+n: U32, a: Array<U32>, b: Array<U32>) -> Bool:
  K.Kernel.all_eq(~U32, ~(x => y => U32.is_eq(x, y)), n, a, b)

def eqf(+n: U32, a: Array<F32>, b: Array<F32>) -> Bool:
  K.Kernel.all_eq(~F32, ~(x => y => U32.is_eq(F32.bits(x), F32.bits(y))), n, a, b)

def eqs(+n: U32, a: Array<String>, b: Array<String>) -> Bool:
  K.Kernel.all_eq(~String, ~(x => y => String.eq(x, y)), n, a, b)

# rows and the flattened buffer
def fw.k(r: CH.CW & U32) -> U32 & Array<U32>:
  (t, +n) = r
  (n, CH.CW.flatten(dfor(n), t))

def fw(t: CH.CW) -> U32 & Array<U32>:
  fw.k(CH.CW.rows(t))

def ff.k(r: CH.CF & U32) -> U32 & Array<F32>:
  (t, +n) = r
  (n, CH.CF.flatten(dfor(n), t))

def ff(t: CH.CF) -> U32 & Array<F32>:
  ff.k(CH.CF.rows(t))

def fs.k(r: CH.CS & U32) -> U32 & Array<String>:
  (t, +n) = r
  (n, CH.CS.flatten(dfor(n), t))

def fs(t: CH.CS) -> U32 & Array<String>:
  fs.k(CH.CS.rows(t))

# does the tree hold exactly the n rows of b?
def sameu.k(+n: U32, b: Array<U32>, r: U32 & Array<U32>) -> Bool:
  (+m, a) = r
  Bool.and(U32.is_eq(m, n), equ(n, a, b))

def sameu(t: CH.CW, +n: U32, b: Array<U32>) -> Bool:
  sameu.k(n, b, fw(t))

def samef.k(+n: U32, b: Array<F32>, r: U32 & Array<F32>) -> Bool:
  (+m, a) = r
  Bool.and(U32.is_eq(m, n), eqf(n, a, b))

def samef(t: CH.CF, +n: U32, b: Array<F32>) -> Bool:
  samef.k(n, b, ff(t))

def sames.k(+n: U32, b: Array<String>, r: U32 & Array<String>) -> Bool:
  (+m, a) = r
  Bool.and(U32.is_eq(m, n), eqs(n, a, b))

def sames(t: CH.CS, +n: U32, b: Array<String>) -> Bool:
  sames.k(n, b, fs(t))

# every node's counts are exact (lrows = rows(l), rows = lrows + rows(r))
def skel_ok(s: CH.Skel) -> Bool:
  match s:
    case CH.KLeaf{n}:
      True{}
    case CH.KNode{+rows, +lrows, +l, +r}:
      Bool.and(Bool.and(U32.is_eq(lrows, CH.Skel.rows(l)), U32.is_eq(rows, U32.add(lrows, CH.Skel.rows(r)))), Bool.and(skel_ok(l), skel_ok(r)))

def skel_show(s: CH.Skel) -> String:
  match s:
    case CH.KLeaf{n}:
      U32.show(n)
    case CH.KNode{rows, lrows, l, r}:
      "(" ++ skel_show(l) ++ " " ++ skel_show(r) ++ ")"

def okb(b: Bool) -> String:
  match b:
    case True{}:
      "ok"
    case False{}:
      "BAD"

def tag(+name: String, b: Bool) -> String:
  match b:
    case True{}:
      ""
    case False{}:
      " BAD:" ++ name

# the skeleton's counts exact AND the tree holds exactly the n rows of b
def sku.k(+n: U32, b: Array<U32>, r: CH.CW & CH.Skel) -> Bool:
  (t, s) = r
  Bool.and(skel_ok(s), sameu(t, n, b))

def sku(t: CH.CW, +n: U32, b: Array<U32>) -> Bool:
  sku.k(n, b, CH.CW.skel(t))

def skf.k(+n: U32, b: Array<F32>, r: CH.CF & CH.Skel) -> Bool:
  (t, s) = r
  Bool.and(skel_ok(s), samef(t, n, b))

def skf(t: CH.CF, +n: U32, b: Array<F32>) -> Bool:
  skf.k(n, b, CH.CF.skel(t))
