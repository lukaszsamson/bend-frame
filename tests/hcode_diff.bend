# W2.1: Hc.code (src/hcode.bend) against the v0.1 coder Sort.str_codes, on every key shape.
# Per shape and size n, for first = 0 and first = 1 (unique / ranks, group_by), the new coder must
# answer: the same `next`; the same codes in ALL 2^d slots (0 beyond n); fr = the first row of
# every entry (computed from the reference codes: row i is new iff its code is the next free one);
# bl = the UTF-8 byte length of every entry (Hc.blen of the entry's string). The same under a
# template hash that collides everywhere (a constant) and one with four hash values.
# Expected values: every line "ok" (the reference IS v0.1, so the expected output is its own).
import Base
import ./lib/w2gen.bend as G
import ./../src/kernels.bend as K
import ./../src/sort.bend as SO
import ./../src/hcode.bend as H

type OR is Type:
  OR{a: Array<String>, codes: Array<U32>, next: U32}

def Or.fin(a: Array<String>, c: Array<U32>, cs: SO.CS) -> OR:
  match cs:
    case SO.CS{m, +next}:
      OR{a, c, next}

def Or.of(r: Array<String> & Array<U32> & SO.CS) -> OR:
  (a, c, cs) = r
  Or.fin(a, c, cs)

def Fr.put(+nw: Bool, +e: U32, +i: U32, fr: Array<U32>) -> Array<U32>:
  match nw:
    case True{}:
      Array.set(U32, fr, e, i)
    case False{}:
      fr

# the first row of every id, from first-appearance codes: row i is new iff code == the next free id
def Fr.go(n: Nat, +i: U32, +first: U32, +next: U32, fr: Array<U32>, r: Array<U32> & U32) -> Array<U32> & Array<U32>:
  match n:
    case 0n:
      (c, x) = r
      (c, fr)
    case 1n+p:
      (c, +x) = r
      +nw = U32.is_eq(x, next)
      Fr.go(p, U32.inc(i), first, U32.add(next, Bool.to_u32(nw)), Fr.put(nw, U32.sub(next, first), i, fr), Array.get(U32, c, U32.inc(i)))

def Cmp.j(+ok: Bool, +d: Nat, +k: U32, bl1: Array<U32>, r: Array<String> & Array<U32>) -> Bool:
  (ents, perm) = r
  Bool.and(ok, G.Eq.u32(U32.shln(1, d), K.Kernel.map(~String, ~U32, ~(s => H.Hc.blen(s, 0)), k, d, ents, 0), bl1))

def Cmp.i(+ok: Bool, +d: Nat, +k: U32, a1: Array<String>, bl1: Array<U32>, frr: Array<U32>, cf: Array<U32> & Array<U32>) -> Bool:
  (f1, f2) = cf
  Cmp.j(Bool.and(ok, G.Eq.u32(U32.shln(1, d), frr, f1)), d, k, bl1, K.Kernel.gather(~String, k, d, a1, f2, ""))

def Cmp.h(+ok: Bool, +d: Nat, +k: U32, a1: Array<String>, fr1: Array<U32>, bl1: Array<U32>, r: Array<U32> & Array<U32>) -> Bool:
  (c, frr) = r
  Cmp.i(ok, d, k, a1, bl1, frr, Array.clone(U32, fr1))

def Cmp.g(+ok: Bool, +n: U32, +d: Nat, +first: U32, +k: U32, a1: Array<String>, c0b: Array<U32>, fr1: Array<U32>, bl1: Array<U32>) -> Bool:
  Cmp.h(ok, d, k, a1, fr1, bl1, Fr.go(U32.to_nat(n), 0, first, first, Array.new(U32, d, 0), Array.get(U32, c0b, 0)))

def Cmp.f(+ok: Bool, +n: U32, +d: Nat, +first: U32, +k: U32, a1: Array<String>, cc0: Array<U32> & Array<U32>, c1: Array<U32>, fr1: Array<U32>, bl1: Array<U32>) -> Bool:
  (c0, c0b) = cc0
  Cmp.g(Bool.and(ok, G.Eq.u32(U32.shln(1, d), c0, c1)), n, d, first, k, a1, c0b, fr1, bl1)

def Cmp.k(+n: U32, +d: Nat, +first: U32, o: OR, h: H.HC) -> Bool:
  match o h:
    case OR{a0, c0, +nx0} H.HC{+nx1, a1, hs, rp, ids, c1, fr1, bl1}:
      Cmp.f(U32.is_eq(nx0, nx1), n, d, first, U32.sub(nx1, first), a1, Array.clone(U32, c0), c1, fr1, bl1)

def Hd.one(~hash: String -> H.HB, +n: U32, +first: U32, +sh: G.Shape) -> Bool:
  +d = G.Gen.depth(n)
  Cmp.k(n, d, first, Or.of(SO.Sort.str_codes(n, d, first, G.Gen.mk(n, sh))), H.Hc.code(~hash, n, d, first, G.Gen.mk(n, sh)))

def Hd.fail(+ok: Bool, +n: U32, +first: U32, rest: String) -> String:
  match ok:
    case True{}:
      rest
    case False{}:
      " n=" ++ U32.show(n) ++ ",first=" ++ U32.show(first) ++ rest

def Hd.sizes(~hash: String -> H.HB, sizes: List<&2, U32>, +sh: G.Shape) -> String:
  match sizes:
    case Nil{}:
      ""
    case +n <> t:
      Hd.fail(Hd.one(~hash, n, 0, sh), n, 0, Hd.fail(Hd.one(~hash, n, 1, sh), n, 1, Hd.sizes(~hash, t, sh)))

def sizes.std() -> List<&2, U32>:
  [0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 32, 33, 100, 255, 256, 257, 700]

def sizes.big() -> List<&2, U32>:
  [1023, 1024, 1025, 4095, 4096, 4097]

def sizes.col() -> List<&2, U32>:
  [0, 1, 2, 3, 7, 8, 9, 33, 129]

# the template hashes: FNV-1a + bytes (the default), a constant (every probe collides), four values
def Hd.t.const(s: String) -> H.HB:
  H.Hc.hash.const(7, s)

def Hd.t.few.k(hb: H.HB) -> H.HB:
  match hb:
    case H.HB{h, b}:
      H.HB{U32.and(h, 3), b}

def Hd.t.few(s: String) -> H.HB:
  Hd.t.few.k(H.Hc.hash(s))

def Hd.shape(+name: String, +sh: G.Shape) -> IO(Unit):
  do IO<Unit>:
    IO.print(G.Rep.line("fnv " ++ name, Hd.sizes(~(s => H.Hc.hash(s)), sizes.std(), sh)))
    IO.print(G.Rep.line("const " ++ name, Hd.sizes(~(s => Hd.t.const(s)), sizes.col(), sh)))
    IO.print(G.Rep.line("few " ++ name, Hd.sizes(~(s => Hd.t.few(s)), sizes.std(), sh)))

def main() -> IO(Unit):
  do IO<Unit>:
    Hd.shape("distinct", G.ShD{})
    Hd.shape("prefix", G.ShP{})
    Hd.shape("longprefix", G.ShQ{})
    Hd.shape("skew", G.ShS{})
    Hd.shape("equal", G.ShE{})
    Hd.shape("low", G.ShL{})
    Hd.shape("uni", G.ShU{})
    Hd.shape("empty", G.ShZ{})
    Hd.shape("nul", G.ShN{})
    Hd.shape("aligned", G.ShM{})
    IO.print(G.Rep.line("fnv big distinct", Hd.sizes(~(s => H.Hc.hash(s)), sizes.big(), G.ShD{})))
    IO.print(G.Rep.line("fnv big skew", Hd.sizes(~(s => H.Hc.hash(s)), sizes.big(), G.ShS{})))
    IO.print(G.Rep.line("fnv big prefix", Hd.sizes(~(s => H.Hc.hash(s)), sizes.big(), G.ShP{})))
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
#|fnv big skew: ok
#|fnv big prefix: ok
