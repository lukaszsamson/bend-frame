# bench/w6/cmp.bend -- comparing two DF.dump texts without deep recursion (a String compare is a
# non-tail walk: String.eq on a 60 KB dump overflows the native stack), and a short outcome line.
#
# Test-only. Idioms: DESIGN 9.
import Base

# (FNV-1a over the code points, the length): equal pairs mean equal texts here (a 64-bit check)
type HN is Data:
  HN{h: U32, g: U32, n: U32}

def Cmp.fold(s: String, +h: U32, +g: U32, +n: U32) -> HN:
  match s:
    case SNil{}:
      HN{h, g, n}
    case SCon{Chr{+c}, t}:
      Cmp.fold(t, U32.mul(U32.xor(h, c), 16777619), U32.add(U32.mul(g, 31), U32.inc(c)), U32.inc(n))

def Cmp.hn(s: String) -> HN:
  Cmp.fold(s, 2166136261, 7, 0)

def Cmp.same.k(a: HN, b: HN) -> Bool:
  match a b:
    case HN{+h1, +g1, +n1} HN{+h2, +g2, +n2}:
      Bool.and(U32.is_eq(h1, h2), Bool.and(U32.is_eq(g1, g2), U32.is_eq(n1, n2)))

# a and b are the same text
def Cmp.same(+a: String, +b: String) -> Bool:
  Cmp.same.k(Cmp.hn(a), Cmp.hn(b))

# ---- the first difference ------------------------------------------------------------------------------
# the walk stops at the first differing character: the suffixes from it, its index, still equal

type PW is Data:
  PW{ra: String, rb: String, i: U32, same: Bool}

def Cmp.pos.step.k(eq: Bool, +x: U32, +y: U32, s: String, t: String, +i: U32) -> PW:
  match eq:
    case True{}:
      PW{SNil{}, SNil{}, U32.inc(i), True{}}
    case False{}:
      PW{SCon{Chr{x}, s}, SCon{Chr{y}, t}, i, False{}}

def Cmp.pos.step(+x: U32, +y: U32, s: String, t: String, +i: U32) -> PW:
  Cmp.pos.step.k(U32.is_eq(x, y), x, y, s, t, i)

def Cmp.pos(a: String, b: String, st: PW) -> PW:
  match a b st:
    case _ _ PW{ra, rb, i, False{}}:
      PW{ra, rb, i, False{}}
    case SNil{} SNil{} PW{ra, rb, i, True{}}:
      PW{SNil{}, SNil{}, i, True{}}
    case SNil{} t PW{ra, rb, +i, True{}}:
      PW{SNil{}, t, i, False{}}
    case s SNil{} PW{ra, rb, +i, True{}}:
      PW{s, SNil{}, i, False{}}
    case SCon{Chr{x}, +s} SCon{Chr{y}, +t} PW{ra, rb, +i, True{}}:
      Cmp.pos(s, t, Cmp.pos.step(x, y, s, t, i))

# the first n characters
def Cmp.take(f: Nat, s: String) -> String:
  match f s:
    case 0n _:
      SNil{}
    case _ SNil{}:
      SNil{}
    case 1n+p SCon{c, t}:
      SCon{c, Cmp.take(p, t)}

def Cmp.diff.m(pw: PW) -> String:
  match pw:
    case PW{ra, rb, +i, same}:
      "differs at char " ++ U32.show(i) ++ ": want <" ++ Cmp.take(60n, ra) ++ "> got <" ++ Cmp.take(60n, rb) ++ ">"

# "" when the texts are the same, else where they first differ
def Cmp.diff(+a: String, +b: String) -> String:
  Bool.pick(String, Cmp.same(a, b), "", Cmp.diff.m(Cmp.pos(a, b, PW{SNil{}, SNil{}, 0, True{}})))

# ---- a one-line outcome of a dump -----------------------------------------------------------------
# the text of the first k lines, TAB shown as a space, lines joined by " | "

type HD is Data:
  HD{k: U32, acc: String, go: Bool}

def Cmp.hd.nl(last: Bool, +k: U32, acc: String) -> HD:
  match last:
    case True{}:
      HD{0, acc, False{}}
    case False{}:
      HD{U32.sub(k, 1), SCon{Chr{32}, SCon{Chr{124}, acc}}, True{}}

def Cmp.hd.a(nl: Bool, +c: U32, +k: U32, acc: String) -> HD:
  match nl:
    case True{}:
      Cmp.hd.nl(U32.is_le(k, 1), k, acc)
    case False{}:
      HD{k, SCon{Chr{Bool.pick(U32, U32.is_eq(c, 9), 32, c)}, acc}, True{}}

def Cmp.hd.step(+c: U32, +k: U32, acc: String) -> HD:
  Cmp.hd.a(U32.is_eq(c, 10), c, k, acc)

def Cmp.hd.go(s: String, st: HD) -> String:
  match s st:
    case SNil{} HD{k, acc, go}:
      String.reverse(acc)
    case _ HD{k, acc, False{}}:
      String.reverse(acc)
    case SCon{Chr{+c}, t} HD{+k, acc, True{}}:
      Cmp.hd.go(t, Cmp.hd.step(c, k, acc))

def Cmp.head(s: String, +k: U32) -> String:
  Cmp.hd.go(s, HD{k, SNil{}, True{}})

# "frame ..." for a frame (its height and width lines), the error line for an error
def Cmp.outcome.k(err: Bool, s: String) -> String:
  match err:
    case True{}:
      Cmp.head(s, 1)
    case False{}:
      Cmp.head(s, 3)

def Cmp.outcome(+s: String) -> String:
  Cmp.outcome.k(String.starts_with(s, "error"), s)
