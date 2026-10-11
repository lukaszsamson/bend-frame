# W6.2: UTF-8 decoding in the lane is byte for byte the runtime's `File.read` (the decoder v0.1 reads
# every field with): an invalid byte becomes U+FFFD and is read again, truncated sequences at the end
# of a field become U+FFFD, overlongs, surrogates, > U+10FFFF and every narrowed second-byte range
# (E0 A0.., ED ..9F, F0 90.., F4 ..8F) decode the same way.
#
# One single-column file (no header), one field per line, written byte by byte from
#   - every byte except LF, CR, `"` and `,` (the CSV syntax) as a line of its own,
#   - every (lead C0..FF, any second byte) pair,
#   - every 3- and 4-byte combination of the boundary leads x boundary continuations (and 'A'),
#   - 600 valid scalars from the whole range (1 to 4 byte encodings),
# is decoded by `File.read` (the reference text) and by the lane, both as raw rows (TyR) and as
# per-region Dictionary entries (TyS, gathered back to rows), read in pieces of 997 and 1 MiB
# bytes. The row strings joined by LF must equal the reference text (a hash and a length).
import Base
import ./../src/kernels.bend as K
import ./../src/csvprod.bend as P
import ./../src/csvlane.bend as L
import ./../bench/w6/hx.bend as X
import ./../bench/w6/cmp.bend as M

# ---- the lines ------------------------------------------------------------------------------------------

# a line (bytes) pushed, reversed, onto an accumulator of bytes (newest first), then its LF
def Ug.emit(line: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match line:
    case Nil{}:
      10 <> acc
    case +b <> t:
      Ug.emit(t, b <> acc)

def Ug.lines(ls: List<&2, List<&2, U32>>, acc: List<&2, U32>) -> List<&2, U32>:
  match ls:
    case Nil{}:
      acc
    case l <> t:
      Ug.lines(t, Ug.emit(l, acc))

# the bytes lo .. lo + n - 1 as one-byte lines (without the CSV syntax bytes)
def Ug.syn(+b: U32) -> Bool:
  Bool.or(Bool.or(U32.is_eq(b, 10), U32.is_eq(b, 13)), Bool.or(U32.is_eq(b, 34), U32.is_eq(b, 44)))

def Ug.single.k(skip: Bool, +b: U32, rest: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match skip:
    case True{}:
      rest
    case False{}:
      (b <> Nil{}) <> rest

def Ug.singles(f: Nat, +b: U32) -> List<&2, List<&2, U32>>:
  match f:
    case 0n:
      Nil{}
    case 1n+p:
      Ug.single.k(Ug.syn(b), b, Ug.singles(p, U32.inc(b)))

# [x, y] for every y in 0 .. 255 (without the syntax bytes)
def Ug.pair.k(skip: Bool, +x: U32, +y: U32, rest: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match skip:
    case True{}:
      rest
    case False{}:
      (x <> y <> Nil{}) <> rest

def Ug.pairs.y(f: Nat, +x: U32, +y: U32) -> List<&2, List<&2, U32>>:
  match f:
    case 0n:
      Nil{}
    case 1n+p:
      Ug.pair.k(Ug.syn(y), x, y, Ug.pairs.y(p, x, U32.inc(y)))

def Ug.app(xs: List<&2, List<&2, U32>>, ys: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      ys
    case h <> t:
      h <> Ug.app(t, ys)

# every lead from x with every second byte
def Ug.pairs(f: Nat, +x: U32) -> List<&2, List<&2, U32>>:
  match f:
    case 0n:
      Nil{}
    case 1n+p:
      Ug.app(Ug.pairs.y(256n, x, 0), Ug.pairs(p, U32.inc(x)))

def Ug.snoc(xs: List<&2, U32>, +y: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      y <> Nil{}
    case h <> t:
      h <> Ug.snoc(t, y)

# each prefix extended by each byte of ys
def Ug.cross.p(+p: List<&2, U32>, ys: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match ys:
    case Nil{}:
      Nil{}
    case +y <> t:
      Ug.snoc(p, y) <> Ug.cross.p(p, t)

def Ug.cross(ps: List<&2, List<&2, U32>>, +ys: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> t:
      Ug.app(Ug.cross.p(p, ys), Ug.cross(t, ys))

def Ug.ones(xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      (x <> Nil{}) <> Ug.ones(t)

def Ug.three() -> List<&2, List<&2, U32>>:
  Ug.cross(Ug.cross(Ug.ones([224, 225, 226, 237, 238, 239, 240, 241, 243, 244, 245]), [128, 143, 144, 159, 160, 191, 192, 65]), [128, 143, 191, 194, 65])

def Ug.four() -> List<&2, List<&2, U32>>:
  Ug.cross(Ug.cross(Ug.cross(Ug.ones([240, 241, 244, 245]), [128, 143, 144, 159, 191, 65]), [128, 191, 65]), [128, 191, 65])

# valid scalars: the UTF-8 encoding of cp (a line byte list)
def Ug.enc(+cp: U32) -> List<&2, U32>:
  Bool.pick(List<&2, U32>, U32.is_lt(cp, 128), cp <> Nil{},
  Bool.pick(List<&2, U32>, U32.is_lt(cp, 2048), U32.add(192, U32.div(cp, 64)) <> U32.add(128, U32.mod(cp, 64)) <> Nil{},
  Bool.pick(List<&2, U32>, U32.is_lt(cp, 65536), U32.add(224, U32.div(cp, 4096)) <> U32.add(128, U32.mod(U32.div(cp, 64), 64)) <> U32.add(128, U32.mod(cp, 64)) <> Nil{},
  U32.add(240, U32.div(cp, 262144)) <> U32.add(128, U32.mod(U32.div(cp, 4096), 64)) <> U32.add(128, U32.mod(U32.div(cp, 64), 64)) <> U32.add(128, U32.mod(cp, 64)) <> Nil{})))

def Ug.mix(+x: U32) -> U32:
  +a = U32.mul(U32.xor(x, U32.shrn(x, 16n)), 2146121005)
  +b = U32.mul(U32.xor(a, U32.shrn(a, 15n)), 2221713035)
  U32.xor(b, U32.shrn(b, 16n))

# a code point from i: mixed over the whole range, never a surrogate, never CSV syntax; the first
# ones are the boundary scalars
def Ug.cp.s(+c: U32) -> U32:
  Bool.pick(U32, Bool.and(U32.is_ge(c, 55296), U32.is_le(c, 57343)), U32.sub(c, 2048), Bool.pick(U32, Ug.syn(c), U32.add(c, 1), c))

def Ug.cp.t(+i: U32) -> U32:
  Bool.pick(U32, U32.is_eq(i, 0), 36, Bool.pick(U32, U32.is_eq(i, 1), 127, Bool.pick(U32, U32.is_eq(i, 2), 128, Bool.pick(U32, U32.is_eq(i, 3), 2047, Bool.pick(U32, U32.is_eq(i, 4), 2048, Bool.pick(U32, U32.is_eq(i, 5), 55295, Bool.pick(U32, U32.is_eq(i, 6), 57344, Bool.pick(U32, U32.is_eq(i, 7), 65533, Bool.pick(U32, U32.is_eq(i, 8), 65535, Bool.pick(U32, U32.is_eq(i, 9), 65536, Bool.pick(U32, U32.is_eq(i, 10), 1114111, 983040)))))))))))

def Ug.cp.b(+i: U32) -> U32:
  Bool.pick(U32, U32.is_lt(i, 12), Ug.cp.t(i), U32.mod(Ug.mix(i), 1114112))

def Ug.cp(+i: U32) -> U32:
  Ug.cp.s(Ug.cp.b(i))

def Ug.scalars(f: Nat, +i: U32) -> List<&2, List<&2, U32>>:
  match f:
    case 0n:
      Nil{}
    case 1n+p:
      Ug.enc(Ug.cp(i)) <> Ug.scalars(p, U32.inc(i))

def Ug.all() -> List<&2, List<&2, U32>>:
  Ug.app(Ug.singles(256n, 0), Ug.app(Ug.pairs(64n, 192), Ug.app(Ug.three(), Ug.app(Ug.four(), Ug.scalars(600n, 0)))))

# ---- folding rows -----------------------------------------------------------------------------------------

def Ut.nl(st: M.HN) -> M.HN:
  match st:
    case M.HN{+h, +g, +n}:
      M.Cmp.fold("\n", h, g, n)

def Ut.row(s: String, st: M.HN) -> M.HN:
  match st:
    case M.HN{+h, +g, +n}:
      Ut.nl(M.Cmp.fold(s, h, g, n))

# raw rows a[0..n)
def Ut.raw(f: Nat, +r: U32, rd: Array<String> & String, st: M.HN) -> M.HN:
  match f:
    case 0n:
      (a, s) = rd
      st
    case 1n+p:
      (a, s) = rd
      Ut.raw(p, U32.inc(r), Array.get(String, a, U32.inc(r)), Ut.row(s, st))

def Ut.raws(+n: U32, a: Array<String>, st: M.HN) -> M.HN:
  Ut.raw(U32.to_nat(n), 0, Array.get(String, a, 0), st)

def Ut.gathered(+n: U32, r: Array<String> & Array<U32>, st: M.HN) -> M.HN:
  (rows, perm) = r
  Ut.raws(n, rows, st)

# the part of a lane: its rows folded
def Ut.part(+n: U32, co: L.CO, st: M.HN) -> M.HN:
  match co:
    case L.OR{a, v, nulls}:
      Ut.raws(n, a, st)
    case L.OS{c, v, nulls, k, ents}:
      Ut.gathered(n, K.Kernel.gather(~String, n, K.Kernel.depth_for(U32.max(n, 1)), ents, c, ""), st)
    case other:
      st

def Ut.lo(lo: L.LO, st: M.HN) -> M.HN:
  match lo:
    case L.LO{+n, rej, rag, rgn, lines, co <> Nil{}}:
      Ut.part(n, co, st)
    case _:
      M.HN{0, 0, 0}

def Ut.los(los: List<&1, L.LO>, st: M.HN) -> M.HN:
  match los:
    case Nil{}:
      st
    case lo <> t:
      Ut.los(t, Ut.lo(lo, st))

def Ut.lanes(regs: List<&1, P.Rg>, +ts: List<&2, L.Ty>) -> List<&1, L.LO>:
  match regs:
    case Nil{}:
      Nil{}
    case rg <> t:
      L.Ln.lane(ts, 1, 44, rg) <> Ut.lanes(t, ts)

def Ut.out(o: P.PrOut, +ts: List<&2, L.Ty>) -> M.HN:
  match o:
    case P.PrOk{nr, odd, regs}:
      Ut.los(Ut.lanes(regs, ts), M.HN{2166136261, 7, 0})
    case P.PrErr{code, msg}:
      M.HN{0, 0, 0}

def Ut.same(a: M.HN, b: M.HN) -> Bool:
  M.Cmp.same.k(a, b)

def Ut.verdict(+ok: Bool) -> String:
  Bool.pick(String, ok, "same as File.read", "DIFFERENT")

def Ut.run(+path: String, +piece: U32, +want: M.HN, +raw: Bool) -> IO(String):
  do IO<String>:
    o : P.PrOut <- P.Pr.regions(path, 0, 1, piece)
    return Bool.pick(String, raw, "raw rows", "dictionary") ++ " at " ++ U32.show(piece) ++ ": " ++ Ut.verdict(Ut.same(want, Ut.out(o, Bool.pick(List<&2, L.Ty>, raw, [L.TyR{}], [L.TyS{}]))))

def Ut.go(+path: String, +want: M.HN) -> IO(Unit):
  do IO<Unit>:
    a : String <- Ut.run(path, 997, want, True{})
    IO.print(a)
    b : String <- Ut.run(path, 997, want, False{})
    IO.print(b)
    c : String <- Ut.run(path, 1048576, want, True{})
    IO.print(c)
    d : String <- Ut.run(path, 1048576, want, False{})
    IO.print(d)

def Ut.text(+path: String, +nbytes: U32) -> IO(Unit):
  do IO<Unit>:
    txt : String <- X.Hx.text(path)
    +hn : M.HN = M.Cmp.hn(txt)
    Ut.go(path, hn)

def Ut.lens(bs: List<&2, U32>) -> U32:
  X.Hx.len(bs, 0)

def main() -> IO(Unit):
  do IO<Unit>:
    +bs : List<&2, U32> = X.Hx.rev(Ug.lines(Ug.all(), Nil{}))
    IO.print("bytes " ++ U32.show(Ut.lens(bs)))
    X.Hx.write_bytes("/tmp/bend_frame_csvlane_utf8.csv", bs)
    Ut.text("/tmp/bend_frame_csvlane_utf8.csv", 0)
#|bytes 54688
#|raw rows at 997: same as File.read
#|dictionary at 997: same as File.read
#|raw rows at 1048576: same as File.read
#|dictionary at 1048576: same as File.read
