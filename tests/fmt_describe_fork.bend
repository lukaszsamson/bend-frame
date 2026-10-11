# Fmt.describe with its columns in a balanced fork (v0.2 T5.4, DESIGN.md 16.4 D4): from 2^16 rows each
# column's statistics are computed by a lane of a fork over the column list (a column is taken out of the
# list, described with all its passes sequential, and handed back); under 2^16 rows, or with one column,
# the sequential walk runs. Nothing observable changes, so:
#   * for 1, 2, 3, 4 and 7 columns over 70000 rows (u32, i32, f32 with nulls and NaN / -0.0 / inf, a u32
#     with nulls, str, bool) every column of the result equals (dump text: F32 bits, nulls) the same column
#     described ALONE (one column = the sequential walk)
#   * the exact statistics of the u32 column, derived by hand from the generator
#   * the frame handed back by Fmt.describe is untouched: described again it gives the same result; its
#     height and column names are unchanged
#   * the boundary: 65535 rows (sequential) and 65536 rows (forked) both match the lone descriptions
# Generator (n rows, d = depth_for(n)):
#   u  u32  i                                         0 .. n-1
#   iv i32  i * 2654435761 (mod 2^32), as i32 words
#   f  f32  null when i mod 4 = 3 (slot 0.0); else (i * 37 mod 1009) / 8, except i = 12345: +inf,
#           i mod 997 = 5: NaN, i mod 991 = 3 (valid): -0.0
#   g  f32  (i * 13 mod 997) / 3
#   h  u32  null when i mod 5 = 0 (slot 0); else i mod 1000
#   s  str  show(i mod 13), null when i mod 7 = 0 (slot "")
#   bb bool i mod 3 = 0
# Hand-derived for u over n = 65536 (the first forked size): count 65536, null_count 0, mean
# (0 + .. + 65535) / 65536 = 32767.5 (the sum 2^15 * 65535 is an f32), min 0, max 65535, and the
# nearest-rank quantiles of Fmt.d.idx, m = n - 1 = 65535: 25% at row (m + 2) / 4 = 16384, 50% at
# (m + 1) / 2 = 32768, 75% at (3m + 2) / 4 = 49151 (the sorted values are 0 .. 65535, so the value is
# the row). std = sqrt(n (n + 1) / 12) = 18918.758 (the sum of squared deviations is n (n^2 - 1) / 12,
# over n - 1): 0x4693cd84 is 18918.758 as an f32.
import Base
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/kernels.bend as K
import ./../src/column.bend as C
import ./../src/strs.bend as ST
import ./../src/fmt.bend as F

def nan() -> F32:
  F32.div(0.0, 0.0)

def inf() -> F32:
  F32.div(1.0, 0.0)

def f_null(+i: U32) -> Bool:
  U32.is_eq(U32.mod(i, 4), 3)

def vf(+i: U32) -> U32:
  Bool.pick(U32, f_null(i), 0, 1)

def fv(+i: U32) -> F32:
  +v = F32.div(U32.to_f32(U32.mod(U32.mul(i, 37), 1009)), 8.0)
  Bool.pick(F32, f_null(i), 0.0, Bool.pick(F32, U32.is_eq(i, 12345), inf(), Bool.pick(F32, U32.is_eq(U32.mod(i, 997), 5), nan(), Bool.pick(F32, U32.is_eq(U32.mod(i, 991), 3), F32.neg(0.0), v))))

def gv(+i: U32) -> F32:
  F32.div(U32.to_f32(U32.mod(U32.mul(i, 13), 997)), 3.0)

def word(+i: U32) -> U32:
  U32.mul(i, 2654435761)

def h_null(+i: U32) -> Bool:
  U32.is_eq(U32.mod(i, 5), 0)

def vh(+i: U32) -> U32:
  Bool.pick(U32, h_null(i), 0, 1)

def hv(+i: U32) -> U32:
  Bool.pick(U32, h_null(i), 0, U32.mod(i, 1000))

def s_null(+i: U32) -> Bool:
  U32.is_eq(U32.mod(i, 7), 0)

def vs(+i: U32) -> U32:
  Bool.pick(U32, s_null(i), 0, 1)

def sv(+i: U32) -> String:
  Bool.pick(String, s_null(i), "", U32.show(U32.mod(i, 13)))

def bv(+i: U32) -> U32:
  Bool.pick(U32, U32.is_eq(U32.mod(i, 3), 0), 1, 0)

def ucol(+n: U32, +d: Nat) -> C.Column:
  C.CU32{n, d, C.AllValid{}, K.Kernel.map(~U32, ~U32, ~(i => i), n, d, K.Kernel.iota(n, d), 0)}

def icol(+n: U32, +d: Nat) -> C.Column:
  C.CI32{n, d, C.AllValid{}, K.Kernel.map(~U32, ~U32, ~(i => word(i)), n, d, K.Kernel.iota(n, d), 0)}

def fcol(+n: U32, +d: Nat) -> C.Column:
  C.CF32{n, d, C.Mask{K.Kernel.map(~U32, ~U32, ~(i => vf(i)), n, d, K.Kernel.iota(n, d), 0)}, K.Kernel.map(~U32, ~F32, ~(i => fv(i)), n, d, K.Kernel.iota(n, d), 0.0)}

def gcol(+n: U32, +d: Nat) -> C.Column:
  C.CF32{n, d, C.AllValid{}, K.Kernel.map(~U32, ~F32, ~(i => gv(i)), n, d, K.Kernel.iota(n, d), 0.0)}

def hcol(+n: U32, +d: Nat) -> C.Column:
  C.CU32{n, d, C.Mask{K.Kernel.map(~U32, ~U32, ~(i => vh(i)), n, d, K.Kernel.iota(n, d), 0)}, K.Kernel.map(~U32, ~U32, ~(i => hv(i)), n, d, K.Kernel.iota(n, d), 0)}

def scol(+n: U32, +d: Nat) -> C.Column:
  C.CStr{n, d, C.Mask{K.Kernel.map(~U32, ~U32, ~(i => vs(i)), n, d, K.Kernel.iota(n, d), 0)}, ST.SRaw{K.Kernel.map(~U32, ~String, ~(i => sv(i)), n, d, K.Kernel.iota(n, d), "")}}

def bcol(+n: U32, +d: Nat) -> C.Column:
  C.CBool{n, d, C.AllValid{}, K.Kernel.map(~U32, ~U32, ~(i => bv(i)), n, d, K.Kernel.iota(n, d), 0)}

def frame(+n: U32) -> C.Frame:
  C.Frame{n, [C.Named{"u", ucol(n, K.Kernel.depth_for(n))}, C.Named{"iv", icol(n, K.Kernel.depth_for(n))}, C.Named{"f", fcol(n, K.Kernel.depth_for(n))}, C.Named{"g", gcol(n, K.Kernel.depth_for(n))}, C.Named{"h", hcol(n, K.Kernel.depth_for(n))}, C.Named{"s", scol(n, K.Kernel.depth_for(n))}, C.Named{"bb", bcol(n, K.Kernel.depth_for(n))}]}

def sub(+n: U32, +names: List<&2, String>) -> E.ResT(C.Frame):
  C.Frame.select_names(frame(n), names)

def desc(r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  DF.describe(r)

# the column `name` of a describe result as a one-column frame's dump
def pick.k(+name: String, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      DF.dump(C.Frame.select_names(f, [name]))

def pick(+name: String, f: C.Frame) -> String:
  pick.k(name, Done{f})

def one.b(+name: String, r: C.Frame & C.Frame, lone: E.ResT(C.Frame)) -> C.Frame & String:
  (keep, copy) = r
  (keep, Bool.pick(String, String.eq(pick(name, copy), pick.k(name, lone)), "ok", "DIFF " ++ name))

# per column: the forked description's column equals the lone description's column
def one(+n: U32, full: C.Frame, +name: String) -> C.Frame & String:
  one.b(name, C.Frame.clone(full), desc(sub(n, [name])))

def step.k(acc: List<&2, String>, r: C.Frame & String) -> C.Frame & List<&2, String>:
  (full, s) = r
  (full, s <> acc)

def step(+n: U32, +name: String, st: C.Frame & List<&2, String>) -> C.Frame & List<&2, String>:
  (full, acc) = st
  step.k(acc, one(n, full, name))

def go(+n: U32, names: List<&2, String>, st: C.Frame & List<&2, String>) -> C.Frame & List<&2, String>:
  match names:
    case Nil{}:
      st
    case nm <> t:
      go(n, t, step(n, nm, st))

def verdict.k(r: C.Frame & List<&2, String>) -> String:
  (f, acc) = r
  String.join(List.reverse(&2, String, acc), " ")

def verdict.f(+n: U32, +names: List<&2, String>, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{full}:
      verdict.k(go(n, names, (full, Nil{})))

def check(+n: U32, +names: List<&2, String>) -> String:
  verdict.f(n, names, desc(sub(n, names)))

# Fmt.describe's frame comes back untouched: described again it gives the same result, and it keeps its
# height and column names
def again.d(+same: Bool, r: C.Frame & C.FInfo) -> String:
  (f, i) = r
  match i:
    case C.FInfo{h, ns}:
      Bool.pick(String, same, "same", "DIFFERENT") ++ " h=" ++ U32.show(h) ++ " " ++ String.join(ns, ",")

def again.c(first: E.ResT(C.Frame), r: C.Frame & E.ResT(C.Frame)) -> String:
  (kept2, second) = r
  again.d(String.eq(DF.dump(first), DF.dump(second)), C.Frame.info(kept2))

def again.k(r: C.Frame & E.ResT(C.Frame)) -> String:
  (kept, first) = r
  again.c(first, F.Fmt.describe(kept))

def again() -> String:
  again.k(F.Fmt.describe(frame(70000)))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(check(70000, ["f"]))
    IO.print(check(70000, ["u", "f"]))
    IO.print(check(70000, ["g", "iv", "h"]))
    IO.print(check(70000, ["u", "f", "g", "iv"]))
    IO.print(check(70000, ["u", "iv", "f", "g", "h", "s", "bb"]))
    # the order of the columns does not matter
    IO.print(check(70000, ["bb", "s", "h", "g", "f", "iv", "u"]))
    # the boundary
    IO.print(check(65535, ["u", "f", "s", "bb"]))
    IO.print(check(65536, ["u", "f", "s", "bb"]))
    # the exact statistics of u
    IO.print(DF.dump(desc(sub(65536, ["u"]))))
    # the input frame is untouched
    IO.print(again())
#|ok
#|ok ok
#|ok ok ok
#|ok ok ok ok
#|ok ok ok ok ok ok ok
#|ok ok ok ok ok ok ok
#|ok ok ok ok
#|ok ok ok ok
#|frame
#|height	9
#|width	2
#|col	str	"statistic"
#|col	f32	"u"
#|row	"count"	0x47800000
#|row	"null_count"	0x00000000
#|row	"mean"	0x46ffff00
#|row	"std"	0x4693cd84
#|row	"min"	0x00000000
#|row	"25%"	0x46800000
#|row	"50%"	0x47000000
#|row	"75%"	0x473fff00
#|row	"max"	0x477fff00
#|
#|same h=70000 u,iv,f,g,h,s,bb
