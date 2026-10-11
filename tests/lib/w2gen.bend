# Shared by tests/hcode_*.bend and tests/ranks_*.bend (v0.2 W2.1 / W2.2): the key shapes, small
# helpers. tests/lib is not run by scripts/test.sh (no `#|` lines, never matched).
#
# shapes (row i of n):
#   ShD distinct      "k" ++ a scrambled u32 (all distinct for any n tested)
#   ShP prefix        a 31-char shared prefix ++ a scrambled u32 (LCP >= 31: 4 radix rounds)
#   ShQ long prefix   102 bytes of U+00E9 (2-byte UTF-8, so words straddle characters) ++ number
#   ShS skew          half the rows in 8 hot keys, half distinct
#   ShE equal         one value
#   ShL low           at most 1000 distinct
#   ShU uni           NUL, the 1-4 byte UTF-8 boundaries, U+10FFFF, prefixes of each other
#   ShZ empty mix     "" in every third row, short keys otherwise
#   ShN nul           ("" | "a" | "b") ++ i mod 40 NULs: NUL-extensions of each other across the
#                     8-byte round boundaries
#   ShM aligned       'a' x (i mod 35) ++ ("" | "b" | U+00E9): equal prefixes ending at every
#                     offset of the 8-byte rounds
#   ShW wide          code points above U+10FFFF (up to U+FFFFFFFF) mixed with ordinary ones:
#                     the fallback of the rank stage
import Base
import ./../../src/kernels.bend as K

type Shape is Data:
  ShD{}
  ShP{}
  ShQ{}
  ShS{}
  ShE{}
  ShL{}
  ShU{}
  ShZ{}
  ShN{}
  ShW{}
  ShM{}

def Gen.h(+i: U32) -> U32:
  U32.mul(U32.add(i, 1), 2654435761)

def Gen.skew(hot: Bool, +h: U32) -> String:
  match hot:
    case True{}:
      "hot" ++ U32.show(U32.and(U32.shrn(h, 8n), 7))
    case False{}:
      "k" ++ U32.show(h)

def Gen.ch(+c: U32) -> String:
  SCon{Chr{c}, SNil{}}

def Gen.uni.b(+j: U32) -> String:
  Bool.pick(String, U32.is_eq(j, 0), "", Bool.pick(String, U32.is_eq(j, 1), Gen.ch(0), Bool.pick(String, U32.is_eq(j, 2), "a", Bool.pick(String, U32.is_eq(j, 3), SCon{Chr{97}, SCon{Chr{0}, SNil{}}}, Bool.pick(String, U32.is_eq(j, 4), Gen.ch(127), Bool.pick(String, U32.is_eq(j, 5), Gen.ch(128), Bool.pick(String, U32.is_eq(j, 6), Gen.ch(2047), Bool.pick(String, U32.is_eq(j, 7), Gen.ch(2048), Bool.pick(String, U32.is_eq(j, 8), Gen.ch(65535), Bool.pick(String, U32.is_eq(j, 9), Gen.ch(65536), Bool.pick(String, U32.is_eq(j, 10), Gen.ch(1114111), "\u{65e5}\u{672c}")))))))))))

def Gen.uni(+i: U32) -> String:
  Gen.uni.b(U32.mod(i, 12)) ++ Gen.uni.b(U32.mod(U32.div(i, 12), 12)) ++ Bool.pick(String, U32.is_eq(U32.mod(i, 5), 0), "", U32.show(U32.mod(i, 37)))

def Gen.rep(n: Nat, +c: U32, tail: String) -> String:
  match n:
    case 0n:
      tail
    case 1n+p:
      SCon{Chr{c}, Gen.rep(p, c, tail)}

def Gen.nul.p(+p: U32, +t: String) -> String:
  Bool.pick(String, U32.is_eq(p, 0), t, Bool.pick(String, U32.is_eq(p, 1), SCon{Chr{97}, t}, SCon{Chr{98}, t}))

def Gen.nul(+i: U32) -> String:
  Gen.nul.p(U32.mod(U32.div(i, 40), 3), Gen.rep(U32.to_nat(U32.mod(i, 40)), 0, ""))

def Gen.wide.c(+j: U32) -> U32:
  Bool.pick(U32, U32.is_eq(j, 0), 0, Bool.pick(U32, U32.is_eq(j, 1), 127, Bool.pick(U32, U32.is_eq(j, 2), 128, Bool.pick(U32, U32.is_eq(j, 3), 1114111, Bool.pick(U32, U32.is_eq(j, 4), 1114112, Bool.pick(U32, U32.is_eq(j, 5), 2147483647, Bool.pick(U32, U32.is_eq(j, 6), 2147483648, Bool.pick(U32, U32.is_eq(j, 7), 4294967295, 65))))))))

def Gen.wide.s(+a: U32, +s: String) -> String:
  Bool.pick(String, U32.is_eq(a, 0), s, SCon{Chr{65}, s})

def Gen.wide.t(+a: U32, +c1: U32, +j: U32) -> String:
  Gen.wide.s(a, SCon{Chr{c1}, Bool.pick(String, U32.is_eq(j, 9), SNil{}, Gen.ch(Gen.wide.c(j)))})

# 9 x 10 two- and one-character strings, doubled by a leading "A", behind 0-5 copies of U+110000, a NUL ending the first half of the rows (a string and its NUL extension)
def Gen.wide.z(+z: U32, +s: String) -> String:
  Bool.pick(String, U32.is_eq(z, 0), s ++ Gen.ch(0), s)

def Gen.wide(+i: U32) -> String:
  Gen.wide.z(U32.mod(U32.div(i, 1080), 2), Gen.rep(U32.to_nat(U32.mod(U32.div(i, 180), 6)), 1114112, Gen.wide.t(U32.mod(U32.div(i, 90), 2), Gen.wide.c(U32.mod(i, 9)), U32.mod(U32.div(i, 9), 10))))

def Gen.m.t(+j: U32) -> String:
  Bool.pick(String, U32.is_eq(j, 0), "", Bool.pick(String, U32.is_eq(j, 1), "b", Gen.ch(233)))

def Gen.key(sh: Shape, +i: U32) -> String:
  match sh:
    case ShD{}:
      "k" ++ U32.show(Gen.h(i))
    case ShP{}:
      "customer_segment_internal_code_" ++ U32.show(Gen.h(i))
    case ShQ{}:
      Gen.rep(51n, 233, U32.show(Gen.h(i)))
    case ShS{}:
      Gen.skew(U32.is_eq(U32.and(Gen.h(i), 1), 0), Gen.h(i))
    case ShE{}:
      "all_rows_hold_this_one_value"
    case ShL{}:
      "v" ++ U32.show(U32.mod(Gen.h(i), 1000))
    case ShU{}:
      Gen.uni(i)
    case ShZ{}:
      Bool.pick(String, U32.is_eq(U32.mod(i, 3), 0), "", "z" ++ U32.show(U32.mod(Gen.h(i), 7)))
    case ShN{}:
      Gen.nul(i)
    case ShW{}:
      Gen.wide(i)
    case ShM{}:
      Gen.rep(U32.to_nat(U32.mod(i, 35)), 97, Gen.m.t(U32.mod(U32.div(i, 35), 3)))

def Gen.go(n: Nat, +i: U32, +sh: Shape, a: Array<String>) -> Array<String>:
  match n:
    case 0n:
      a
    case 1n+p:
      Gen.go(p, U32.inc(i), sh, Array.set(String, a, i, Gen.key(sh, i)))

def Gen.depth(+n: U32) -> Nat:
  K.Kernel.depth_for(U32.max(n, 1))

# the n rows of a shape in 2^depth_for(n) slots (a fresh copy every call)
def Gen.mk(+n: U32, +sh: Shape) -> Array<String>:
  Gen.go(U32.to_nat(n), 0, sh, Array.new(String, Gen.depth(n), ""))

# ---- reports -------------------------------------------------------------------------------------

def Rep.line.k(name: String, bad: String, ok: Bool) -> String:
  match ok:
    case True{}:
      name ++ ": ok"
    case False{}:
      name ++ ": BAD" ++ bad

def Rep.line(name: String, +bad: String) -> String:
  Rep.line.k(name, bad, String.is_empty(bad))

def Eq.u32(+n: U32, a: Array<U32>, b: Array<U32>) -> Bool:
  K.Kernel.all_eq(~U32, ~(x => y => U32.is_eq(x, y)), n, a, b)
