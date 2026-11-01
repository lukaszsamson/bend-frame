# tests/regress/lib/v03.bend -- helpers of the v0.3 W1 fast-path tests (tests/regress/V03_*). Not a test
# itself: its main prints nothing (the runner reports it as "PASS (no expect)").
import Base
import ./../../../frame.bend as DF
import ./../../../src/err.bend as E
import ./../../../src/column.bend as C
import ./../../../src/plan.bend as P
import ./../../../src/kernels.bend as K

def cx.k(+g: Nat, q: P.Plan -> P.Plan, r: P.Env & P.Plan) -> IO(E.ResT(C.Frame)):
  (env, p) = r
  DF.collect_with(DF.engine_chunked_at(g), q(p), env)

# the plan q over the frame f (as the source "t"), run by the chunked engine at grain 2^g
def cx(+g: Nat, q: P.Plan -> P.Plan, f: C.Frame) -> IO(E.ResT(C.Frame)):
  cx.k(g, q, DF.source("t", f))

def lz.k(q: P.Plan -> P.Plan, r: P.Env & P.Plan) -> IO(E.ResT(C.Frame)):
  (env, p) = r
  DF.collect(q(p), env)

# the same plan run by the reference engine (DF.collect)
def lz(q: P.Plan -> P.Plan, f: C.Frame) -> IO(E.ResT(C.Frame)):
  lz.k(q, DF.source("t", f))

# ---- big frames from formulas, and a checksum of a result (V03_fastpaths_big) ------------------------

# a u32 column of n rows: row i holds f(i) when z(i) = 1, null when z(i) = 0 (f must answer 0 there: the
# null slot holds the dtype default, DESIGN.md 9 P0)
def ucol(~f: U32 -> U32, ~z: U32 -> U32, +n: U32) -> C.Column:
  +d = K.Kernel.depth_for(n)
  C.CU32{n, d, C.Mask{K.Kernel.map(~U32, ~U32, ~z, n, d, K.Kernel.iota(n, d), 0)}, K.Kernel.map(~U32, ~U32, ~f, n, d, K.Kernel.iota(n, d), 0)}

# h folded over rows i < n of one column, row by row: h = (h * 1000003) xor (valid ? word : 0xDEADBEEF)
def ck.go(n: Nat, +i: U32, +h: U32, rm: Array<U32> & U32, ra: Array<U32> & U32) -> U32:
  match n:
    case 0n:
      h
    case 1n+p:
      (m, +mv) = rm
      (a, +av) = ra
      +j = U32.inc(i)
      ck.go(p, j, U32.xor(U32.mul(h, 1000003), Bool.pick(U32, U32.is_zero(mv), 3735928559, av)), Array.get(U32, m, j), Array.get(U32, a, j))

def ck.w(+h: U32, +len: U32, v: C.Valid, a: Array<U32>) -> U32:
  ck.go(U32.to_nat(len), 0, h, Array.get(U32, C.Valid.materialize(v, 0n), 0), Array.get(U32, a, 0))

# word columns only (bool / u32 / i32); any other kind folds a marker
def ck.col(+h: U32, c: C.Column) -> U32:
  match c:
    case C.CBool{+len, d, v, a}:
      ck.w(h, len, v, a)
    case C.CU32{+len, d, v, a}:
      ck.w(h, len, v, a)
    case C.CI32{+len, d, v, a}:
      ck.w(h, len, v, a)
    case C.CF32{len, d, v, a}:
      U32.xor(h, 1)
    case C.CStr{len, d, v, a}:
      U32.xor(h, 2)

def ck.cols(cs: List<&1, C.Named>, +h: U32) -> U32:
  match cs:
    case Nil{}:
      h
    case C.Named{n, c} <> rest:
      ck.cols(rest, ck.col(h, c))

# "h=<height> ck=<checksum>", or the error
def ck(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error " ++ E.Err.show(e)
    case Done{C.Frame{+h, cs}}:
      "h=" ++ U32.show(h) ++ " ck=" ++ U32.show(ck.cols(cs, 2166136261))

def main() -> IO(Unit):
  IO.pure(Unit, Unit{})
