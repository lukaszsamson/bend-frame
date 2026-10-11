# W2.2: the rank stage (src/ranks.bend) against v0.1, on every key shape.
#  - Rk.words(n, d, flip, a) vs Sort.str_words(n, d, flip, a) for flip 0 and 2^32 - 1: the same
#    words in ALL 2^d slots (0 beyond n), and the rows come back untouched;
#  - Rk.dict(dict) vs ST.Dict.ranks(dict) on a Dictionary built from the same rows (code 0 = "",
#    entries in first-appearance order): the same rank in all 2^dd slots and the same dictionary.
# The code-point order, a prefix first, is Base's String order; the reference IS v0.1.
# Shapes with code points above U+10FFFF (the packing fallback) cannot be built here: the
# interpreter refuses such a Chr; bench/w2/w2diff.bend runs them natively.
import Base
import ./lib/w2gen.bend as G
import ./../src/kernels.bend as K
import ./../src/strs.bend as ST
import ./../src/sort.bend as SO
import ./../src/ranks.bend as R

# rows back untouched AND words equal
def Rd.both(+n: U32, +d: Nat, r: Array<String> & Array<U32>, a: Array<String>, w0: Array<U32>) -> Bool:
  (a1, w1) = r
  Bool.and(K.Kernel.all_eq(~String, ~(x => y => String.eq(x, y)), n, a, a1), G.Eq.u32(U32.shln(1, d), w0, w1))

def Rd.one(+n: U32, +flip: U32, +sh: G.Shape) -> Bool:
  +d = G.Gen.depth(n)
  Rd.both(n, d, R.Rk.words(n, d, flip, G.Gen.mk(n, sh)), G.Gen.mk(n, sh), SO.Sort.str_words(n, d, flip, G.Gen.mk(n, sh)))

# ---- Dictionary ----------------------------------------------------------------------------------

def Dg.go(n: Nat, +i: U32, d: ST.Dict, r: Array<String> & String) -> ST.Dict:
  match n:
    case 0n:
      (a, s) = r
      d
    case 1n+p:
      (a, s) = r
      +j = U32.inc(i)
      Dg.go(p, j, ST.Dict.fst(ST.Dict.code(d, s)), Array.get(String, a, j))

def Dg.mk(+n: U32, +sh: G.Shape) -> ST.Dict:
  Dg.go(U32.to_nat(n), 0, ST.Dict.empty(), Array.get(String, G.Gen.mk(n, sh), 0))

def Dg.cmp.k(+dd: Nat, same: Bool, r1: Array<U32>, r2: Array<U32>) -> Bool:
  Bool.and(same, G.Eq.u32(U32.shln(1, dd), r1, r2))

def Dg.cmp.s(r1: Array<U32>, r2: Array<U32>, +dd: Nat, r: ST.Dict & ST.Dict & Bool) -> Bool:
  (x, y, same) = r
  Dg.cmp.k(dd, same, r1, r2)

def Dg.cmp.d(d1: ST.Dict, r1: Array<U32>, d2: ST.Dict, r2: Array<U32>) -> Bool:
  match d1:
    case ST.Dict{k, +dd, strs, b, slots, tag}:
      Dg.cmp.s(r1, r2, dd, ST.Dict.same(ST.Dict{k, dd, strs, b, slots, tag}, d2))

def Dg.cmp(x: ST.Dict & Array<U32>, y: ST.Dict & Array<U32>) -> Bool:
  (d1, r1) = x
  (d2, r2) = y
  Dg.cmp.d(d1, r1, d2, r2)

def Dg.one(+n: U32, +sh: G.Shape) -> Bool:
  Dg.cmp(ST.Dict.ranks(Dg.mk(n, sh)), R.Rk.dict(Dg.mk(n, sh)))

# ---- the sizes -------------------------------------------------------------------------------------

def Rd.fail(+ok: Bool, +n: U32, +tag: String, rest: String) -> String:
  match ok:
    case True{}:
      rest
    case False{}:
      " n=" ++ U32.show(n) ++ tag ++ rest

def Rd.sizes(sizes: List<&2, U32>, +sh: G.Shape) -> String:
  match sizes:
    case Nil{}:
      ""
    case +n <> t:
      Rd.fail(Rd.one(n, 0, sh), n, " flip0", Rd.fail(Rd.one(n, 4294967295, sh), n, " flip1", Rd.fail(Dg.one(n, sh), n, " dict", Rd.sizes(t, sh))))

def sizes.std() -> List<&2, U32>:
  [0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 32, 33, 100, 255, 256, 257, 700]

def sizes.big() -> List<&2, U32>:
  [1023, 1024, 1025, 4095, 4096, 4097]

def Rd.shape(+name: String, +sh: G.Shape) -> IO(Unit):
  IO.print(G.Rep.line(name, Rd.sizes(sizes.std(), sh)))

def main() -> IO(Unit):
  do IO<Unit>:
    Rd.shape("distinct", G.ShD{})
    Rd.shape("prefix", G.ShP{})
    Rd.shape("longprefix", G.ShQ{})
    Rd.shape("skew", G.ShS{})
    Rd.shape("equal", G.ShE{})
    Rd.shape("low", G.ShL{})
    Rd.shape("uni", G.ShU{})
    Rd.shape("empty", G.ShZ{})
    Rd.shape("nul", G.ShN{})
    Rd.shape("aligned", G.ShM{})
    IO.print(G.Rep.line("big distinct", Rd.sizes(sizes.big(), G.ShD{})))
    IO.print(G.Rep.line("big prefix", Rd.sizes(sizes.big(), G.ShP{})))
    IO.print(G.Rep.line("big skew", Rd.sizes(sizes.big(), G.ShS{})))
    IO.print(G.Rep.line("big uni", Rd.sizes(sizes.big(), G.ShU{})))
#|distinct: ok
#|prefix: ok
#|longprefix: ok
#|skew: ok
#|equal: ok
#|low: ok
#|uni: ok
#|empty: ok
#|nul: ok
#|aligned: ok
#|big distinct: ok
#|big prefix: ok
#|big skew: ok
#|big uni: ok
