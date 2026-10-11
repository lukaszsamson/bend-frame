# W2.4: the packed coder Hc.code.pk and its lookup Hc.find.pk (src/hcode.bend), the join's string
# table, against Hc.code (W2.1, itself checked against the v0.1 coder by tests/hcode_diff.bend).
# Per build shape and size n, under three ~mix templates (identity, a constant: every probe
# collides, four values):
#  - codes in ALL 2^d slots (0 beyond n) and next equal to Hc.code(.., first = 0);
#  - the packed entries: pl[e] = the code-point count of entry e's string (its first row, from
#    Hc.code's fr) and pk[po[e] .. po[e] + pl[e]) = its code points, po[0] = 0, po[e + 1] =
#    po[e] + pl[e], cur = the total (long-prefix rows force pk to double several times);
#  - the lookup of a query set (the first n2 rows of a query shape): out[i] = the id of the entry
#    equal to q[i], 2^32 - 1 when there is none, 0 beyond n2. Reference: Hc.code over b ++ q,
#    whose first next ids are b's entries in the same order, so q[i] is present iff its code there
#    is below next (and then it is the id).
# Expected values: every line "ok" (the references are Hc.code and a code-point walk).
import Base
import ./lib/w2gen.bend as G
import ./../src/kernels.bend as K
import ./../src/hcode.bend as H

# ---- the packed entries ----------------------------------------------------------------------------

# s against pk[o ..] (r = (pk, pk[o]), read ahead)
def Pk.walk(s: String, +o: U32, ok: Bool, r: Array<U32> & U32) -> Array<U32> & Bool:
  match s:
    case SNil{}:
      (pk, x) = r
      (pk, ok)
    case SCon{Chr{+c}, t}:
      (pk, +x) = r
      +o2 = U32.inc(o)
      Pk.walk(t, o2, Bool.and(ok, U32.is_eq(c, x)), Array.get(U32, pk, o2))

def Pk.len(s: String, +n: U32) -> U32:
  match s:
    case SNil{}:
      n
    case SCon{c, t}:
      Pk.len(t, U32.inc(n))

type PE is Type:
  PE{a: Array<String>, fr: Array<U32>, po: Array<U32>, pl: Array<U32>, pk: Array<U32>, sum: U32, ok: Bool}

def Pe.d(a: Array<String>, fr: Array<U32>, po: Array<U32>, pl: Array<U32>, +ok: Bool, +sum: U32, +l: U32, +n: U32, w: Array<U32> & Bool) -> PE:
  (pk, +wok) = w
  PE{a, fr, po, pl, pk, U32.add(sum, l), Bool.and(ok, Bool.and(wok, U32.is_eq(l, n)))}

def Pe.c(fr: Array<U32>, pk: Array<U32>, +ok: Bool, +sum: U32, ra: Array<String> & String, ro: Array<U32> & U32, rl: Array<U32> & U32) -> PE:
  (a, +s) = ra
  (po, +o) = ro
  (pl, +l) = rl
  Pe.d(a, fr, po, pl, Bool.and(ok, U32.is_eq(o, sum)), sum, l, Pk.len(s, 0), Pk.walk(s, o, True{}, Array.get(U32, pk, o)))

def Pe.b(+e: U32, a: Array<String>, po: Array<U32>, pl: Array<U32>, pk: Array<U32>, +ok: Bool, +sum: U32, rf: Array<U32> & U32) -> PE:
  (fr, +f) = rf
  Pe.c(fr, pk, ok, sum, Array.get(String, a, f), Array.get(U32, po, e), Array.get(U32, pl, e))

def Pe.one(+e: U32, st: PE) -> PE:
  match st:
    case PE{a, fr, po, pl, pk, +sum, +ok}:
      Pe.b(e, a, po, pl, pk, ok, sum, Array.get(U32, fr, e))

def Pe.go(n: Nat, +e: U32, st: PE) -> PE:
  match n:
    case 0n:
      st
    case 1n+p:
      Pe.go(p, U32.inc(e), Pe.one(e, st))

# ---- the lookup's reference ---------------------------------------------------------------------

# out[i] = c[off + i] when below bn, else 2^32 - 1, for i < n
def Ex.go(n: Nat, +i: U32, +off: U32, +bn: U32, out: Array<U32>, r: Array<U32> & U32) -> Array<U32>:
  match n:
    case 0n:
      (c, x) = r
      out
    case 1n+p:
      (c, +x) = r
      +j = U32.inc(i)
      Ex.go(p, j, off, bn, Array.set(U32, out, i, Bool.pick(U32, U32.is_lt(x, bn), x, 4294967295)), Array.get(U32, c, U32.add(off, j)))

def Ex.k(+n: U32, +n2: U32, +d2: Nat, +bn: U32, hc: H.HC) -> Array<U32>:
  match hc:
    case H.HC{next, a, hs, rp, ids, codes, fr, bl}:
      Ex.go(U32.to_nat(n2), 0, n, bn, Array.new(U32, d2, 0), Array.get(U32, codes, n))

# the expected lookup answers of q = the first n2 rows of sh2 against b = the first n rows of sh
def Ex(+n: U32, +sh: G.Shape, +n2: U32, +sh2: G.Shape, +bn: U32) -> Array<U32>:
  +d2 = G.Gen.depth(n2)
  +d3 = G.Gen.depth(U32.add(n, n2))
  Ex.k(n, n2, d2, bn, H.Hc.code(~(s => H.Hc.hash(s)), U32.add(n, n2), d3, 0, K.Kernel.append(~String, n, n2, d3, G.Gen.mk(n, sh), G.Gen.mk(n2, sh2), "")))

# ---- one case -----------------------------------------------------------------------------------

def One.f(+ok: Bool, +n2: U32, ex: Array<U32>, hq: H.HQ) -> Bool:
  match hq:
    case H.HQ{q, hs, ix, po, pl, pk, out}:
      Bool.and(ok, G.Eq.u32(U32.shln(1, G.Gen.depth(n2)), out, ex))

def One.e(~mix: U32 -> U32, +ok: Bool, +n: U32, +sh: G.Shape, +n2: U32, +sh2: G.Shape, +next: U32, +cur: U32, hs: Array<U32>, ix: Array<U32>, pe: PE) -> Bool:
  match pe:
    case PE{a, fr, po, pl, pk, +sum, +pok}:
      One.f(Bool.and(Bool.and(ok, pok), U32.is_eq(sum, cur)), n2, Ex(n, sh, n2, sh2, next), H.Hc.find.pk(~mix, n, n2, G.Gen.depth(n2), hs, ix, po, pl, pk, G.Gen.mk(n2, sh2)))

def One.a(~mix: U32 -> U32, +n: U32, +d: Nat, +sh: G.Shape, +n2: U32, +sh2: G.Shape, hj: H.HJ, hc: H.HC) -> Bool:
  match hj hc:
    case H.HJ{+next, b, hs, ix, codes, po, pl, pk, +cur, pd} H.HC{+rnext, a, rhs, rrp, rids, rcodes, fr, bl}:
      One.e(~mix, Bool.and(U32.is_eq(next, rnext), G.Eq.u32(U32.shln(1, d), codes, rcodes)), n, sh, n2, sh2, next, cur, hs, ix, Pe.go(U32.to_nat(next), 0, PE{a, fr, po, pl, pk, 0, True{}}))

# build the first n rows of sh, look the first n2 rows of sh2 up
def One(~mix: U32 -> U32, +n: U32, +sh: G.Shape, +n2: U32, +sh2: G.Shape) -> Bool:
  +d = G.Gen.depth(n)
  One.a(~mix, n, d, sh, n2, sh2, H.Hc.code.pk(~mix, n, d, G.Gen.mk(n, sh)), H.Hc.code(~(s => H.Hc.hash(s)), n, d, 0, G.Gen.mk(n, sh)))

# the constant template (every probe collides)
def Mix.c(+h: U32) -> U32:
  7

def Run.fail(+ok: Bool, +n: U32, +n2: U32, rest: String) -> String:
  match ok:
    case True{}:
      rest
    case False{}:
      " n=" ++ U32.show(n) ++ ",q=" ++ U32.show(n2) ++ rest

# every size n, the query: the same shape at n2 = n + n / 2 + 3 rows (the first n present, then
# rows the build side may lack) and the other shape at n rows
def Run.sizes(~mix: U32 -> U32, sizes: List<&2, U32>, +sh: G.Shape, +other: G.Shape) -> String:
  match sizes:
    case Nil{}:
      ""
    case +n <> t:
      +n2 = U32.add(U32.add(n, U32.div(n, 2)), 3)
      Run.fail(One(~mix, n, sh, n2, sh), n, n2, Run.fail(One(~mix, n, sh, n, other), n, n, Run.sizes(~mix, t, sh, other)))

def sizes.std() -> List<&2, U32>:
  [0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 33, 100, 257]

def sizes.col() -> List<&2, U32>:
  [0, 1, 2, 3, 7, 8, 9, 33, 129]

def Run.shape(+name: String, +sh: G.Shape, +other: G.Shape) -> IO(Unit):
  do IO<Unit>:
    IO.print(G.Rep.line("fnv " ++ name, Run.sizes(~(h => h), sizes.std(), sh, other)))
    IO.print(G.Rep.line("const " ++ name, Run.sizes(~(h => Mix.c(h)), sizes.col(), sh, other)))
    IO.print(G.Rep.line("few " ++ name, Run.sizes(~(h => U32.and(h, 3)), sizes.std(), sh, other)))

def main() -> IO(Unit):
  do IO<Unit>:
    Run.shape("distinct", G.ShD{}, G.ShP{})
    Run.shape("prefix", G.ShP{}, G.ShD{})
    Run.shape("longprefix", G.ShQ{}, G.ShP{})
    Run.shape("skew", G.ShS{}, G.ShL{})
    Run.shape("equal", G.ShE{}, G.ShZ{})
    Run.shape("low", G.ShL{}, G.ShS{})
    Run.shape("uni", G.ShU{}, G.ShN{})
    Run.shape("empty", G.ShZ{}, G.ShE{})
    Run.shape("nul", G.ShN{}, G.ShU{})
    Run.shape("aligned", G.ShM{}, G.ShN{})
    IO.print(G.Rep.line("fnv big distinct", Run.sizes(~(h => h), [1023, 1024, 1025, 4097], G.ShD{}, G.ShS{})))
    IO.print(G.Rep.line("fnv big longprefix", Run.sizes(~(h => h), [1023, 1025], G.ShQ{}, G.ShD{})))
#|fnv distinct: ok
#|const distinct: ok
#|few distinct: ok
#|fnv prefix: ok
#|const prefix: ok
#|few prefix: ok
#|fnv longprefix: ok
#|const longprefix: ok
#|few longprefix: ok
#|fnv skew: ok
#|const skew: ok
#|few skew: ok
#|fnv equal: ok
#|const equal: ok
#|few equal: ok
#|fnv low: ok
#|const low: ok
#|few low: ok
#|fnv uni: ok
#|const uni: ok
#|few uni: ok
#|fnv empty: ok
#|const empty: ok
#|few empty: ok
#|fnv nul: ok
#|const nul: ok
#|few nul: ok
#|fnv aligned: ok
#|const aligned: ok
#|few aligned: ok
#|fnv big distinct: ok
#|fnv big longprefix: ok
