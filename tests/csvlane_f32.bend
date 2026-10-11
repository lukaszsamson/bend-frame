# W6.2: f32 parsing in the lane is BIT-identical to v0.1's `F32.read` (strtof) of the trimmed text.
#
# 20,000 generated rows (a mixing function of the row index: ten families) go through the
# producer and the lane (`TyF`, pieces of 8 KiB and 1 MiB) and every row's validity and F32 bits
# are compared with `F32.read(String.trim(text))` of the same text:
#   0 the Clinger fast path (mantissa <= 2^24, <= 10 fraction digits, sign, leading zeros)
#   1 integers          2 the same with blanks around   3 mantissas at 2^24 - 6 .. 2^24 + 5
#   4 mantissas beyond 2^24 with 1-3 fraction digits (the fast path must NOT take them)
#   5 32-bit mantissas  6 11-13 fraction digits (24-bit mantissas)   7 tiny values (many leading zeros)
#   8 exponent forms    9 nan, inf, -inf, empty, blanks, ".5", "5.", "-0"
# The counts are printed; a mismatch prints the first row and its text.
import Base
import ./../src/csvprod.bend as P
import ./../src/csvlane.bend as L
import ./../bench/w6/hx.bend as X

# ---- the generator -----------------------------------------------------------------------------

def Gn.mix(+x: U32) -> U32:
  +a = U32.mul(U32.xor(x, U32.shrn(x, 16n)), 2146121005)
  +b = U32.mul(U32.xor(a, U32.shrn(a, 15n)), 2221713035)
  U32.xor(b, U32.shrn(b, 16n))

def Gn.dot(dot: Bool, s: String) -> String:
  match dot:
    case True{}:
      SCon{Chr{46}, s}
    case False{}:
      s

# the digit k (from the right) of m, then a point after fd digits
def Gn.push(+k: U32, +fd: U32, +d: U32, acc: String) -> String:
  Gn.dot(Bool.and(U32.is_gt(fd, 0), U32.is_eq(k, U32.sub(fd, 1))), SCon{Chr{U32.add(48, d)}, acc})

def Gn.dec.go(f: Nat, +m: U32, +k: U32, +fd: U32, acc: String) -> String:
  match f:
    case 0n:
      acc
    case 1n+p:
      Gn.dec.go(p, U32.div(m, 10), U32.inc(k), fd, Gn.push(k, fd, U32.mod(m, 10), acc))

# m as decimal digits with fd of them after a point (at least one before it)
def Gn.dec(+m: U32, +fd: U32) -> String:
  Gn.dec.go(U32.to_nat(U32.max(U32.from_nat(String.length(U32.show(m))), U32.inc(fd))), m, 0, fd, "")

def Gn.sign.k(+s: U32) -> String:
  Bool.pick(String, U32.is_eq(s, 0), "", Bool.pick(String, U32.is_eq(s, 1), "-", "+"))

def Gn.sign(+r: U32) -> String:
  Gn.sign.k(U32.mod(r, 3))

def Gn.special.k(+s: U32) -> String:
  Bool.pick(String, U32.is_eq(s, 0), "nan", Bool.pick(String, U32.is_eq(s, 1), "inf", Bool.pick(String, U32.is_eq(s, 2), "-inf", Bool.pick(String, U32.is_eq(s, 3), "", Bool.pick(String, U32.is_eq(s, 4), "   ", Bool.pick(String, U32.is_eq(s, 5), ".5", Bool.pick(String, U32.is_eq(s, 6), "5.", "-0")))))))

def Gn.special(+r: U32) -> String:
  Gn.special.k(U32.mod(r, 8))

def Gn.body(+f: U32, +r: U32, +r2: U32) -> String:
  Bool.pick(String, U32.is_eq(f, 0), Gn.dec(U32.mod(r, 16777217), U32.mod(r2, 11)),
  Bool.pick(String, U32.is_eq(f, 1), Gn.dec(U32.mod(r, 1000000), 0),
  Bool.pick(String, U32.is_eq(f, 2), Gn.dec(U32.mod(r, 16777217), U32.mod(r2, 11)),
  Bool.pick(String, U32.is_eq(f, 3), Gn.dec(U32.add(16777210, U32.mod(r, 12)), U32.mod(r2, 4)),
  Bool.pick(String, U32.is_eq(f, 4), Gn.dec(U32.add(16777217, U32.mod(r, 40000000)), U32.inc(U32.mod(r2, 3))),
  Bool.pick(String, U32.is_eq(f, 5), Gn.dec(r, U32.mod(r2, 10)),
  Bool.pick(String, U32.is_eq(f, 6), Gn.dec(U32.mod(r, 16777217), U32.add(11, U32.mod(r2, 3))),
  Bool.pick(String, U32.is_eq(f, 7), Gn.dec(U32.mod(r, 100), U32.mod(r2, 11)),
  Gn.dec(U32.mod(r, 100000), U32.mod(r2, 5)) ++ "e" ++ Gn.sign(r) ++ U32.show(U32.mod(r2, 30))))))))))

# the blanks of family 2 go before the sign
def Gn.fam(+f: U32, +r: U32, +r2: U32) -> String:
  Bool.pick(String, U32.is_eq(f, 2), "  " ++ Gn.sign(r2) ++ Gn.body(f, r, r2) ++ " \t", Gn.sign(r2) ++ Gn.body(f, r, r2))

# the text of row i
def Gn.text.k(+f: U32, +r: U32) -> String:
  Bool.pick(String, U32.is_eq(f, 9), Gn.special(r), Gn.fam(f, r, Gn.mix(r)))

def Gn.text(+i: U32) -> String:
  Gn.text.k(U32.mod(i, 10), Gn.mix(U32.add(U32.mul(i, 2654435761), 12345)))

# n rows from row i0
def Gn.lines(f: Nat, +i: U32) -> String:
  match f:
    case 0n:
      ""
    case 1n+p:
      Gn.text(i) ++ "\n" ++ Gn.lines(p, U32.inc(i))

# ---- what v0.1 would read ---------------------------------------------------------------------

# ok: 1 valid, 0 null, 2 does not parse; bits of the value
type W2 is Data:
  W2{ok: U32, bits: U32}

def Gn.want.m(+empty: Bool, m: Maybe<&2, F32>) -> W2:
  match m:
    case Some{x}:
      W2{1, F32.bits(x)}
    case None{}:
      W2{Bool.pick(U32, empty, 0, 2), 0}

def Gn.want.s(+s: String) -> W2:
  Gn.want.m(String.is_empty(s), F32.read(s))

def Gn.want(+i: U32) -> W2:
  Gn.want.s(String.trim(Gn.text(i)))

# ---- checking a lane's rows ---------------------------------------------------------------------------

# rows checked, rows that differ, the first one (+ 1)
type FS is Type:
  FS{a: Array<F32>, v: Array<U32>, i: U32, bad: U32, first: U32}

def Fc.first(+take: Bool, +first: U32, +i: U32) -> U32:
  Bool.pick(U32, take, U32.inc(i), first)

def Fc.step.k(w: W2, +i: U32, +bad: U32, +first: U32, a: Array<F32>, v: Array<U32>, +x: F32, +y: U32) -> FS:
  match w:
    case W2{+ok, +bits}:
      +same = Bool.and(U32.is_eq(y, ok), Bool.or(U32.is_ne(ok, 1), U32.is_eq(F32.bits(x), bits)))
      FS{a, v, U32.inc(i), U32.add(bad, Bool.to_u32(Bool.not(same))), Fc.first(Bool.and(Bool.not(same), U32.is_eq(first, 0)), first, i)}

def Fc.step.v(a: Array<F32>, +x: F32, +i: U32, +bad: U32, +first: U32, rv: Array<U32> & U32) -> FS:
  (v, +y) = rv
  Fc.step.k(Gn.want(i), i, bad, first, a, v, x, y)

def Fc.step.a(+i: U32, +bad: U32, +first: U32, v: Array<U32>, +r: U32, ra: Array<F32> & F32) -> FS:
  (a, +x) = ra
  Fc.step.v(a, x, i, bad, first, Array.get(U32, v, r))

def Fc.go(f: Nat, +r: U32, st: FS) -> FS:
  match f st:
    case 0n other:
      other
    case 1n+p FS{a, v, +i, +bad, +first}:
      Fc.go(p, U32.inc(r), Fc.step.a(i, bad, first, v, r, Array.get(F32, a, r)))

# the counts after every lane (file order)
type CT is Data:
  CT{i: U32, bad: U32, first: U32}

def Fc.fin(st: FS, +bd: U32) -> CT:
  match st:
    case FS{a, v, +i, +bad, +first}:
      CT{i, U32.add(bad, bd), first}

# the part of a lane: its rows, from global row i
def Fc.part(+n: U32, co: L.CO, +i: U32, +bad: U32, +first: U32) -> CT:
  match co:
    case L.OF{a, v, nulls, bd, bl, bt}:
      Fc.fin(Fc.go(U32.to_nat(n), 0, FS{a, v, i, bad, first}), bd)
    case other:
      CT{i, 4294967295, first}

def Fc.lo(lo: L.LO, st: CT) -> CT:
  match lo st:
    case L.LO{+n, rej, rag, rgn, lines, co <> Nil{}} CT{+i, +bad, +first}:
      Fc.part(n, co, i, bad, first)
    case _ other:
      CT{0, 4294967295, 0}

def Fc.los(los: List<&1, L.LO>, st: CT) -> CT:
  match los:
    case Nil{}:
      st
    case lo <> t:
      Fc.los(t, Fc.lo(lo, st))

def Fc.lanes(regs: List<&1, P.Rg>, +ts: List<&2, L.Ty>) -> List<&1, L.LO>:
  match regs:
    case Nil{}:
      Nil{}
    case rg <> t:
      L.Ln.lane(ts, 1, 44, rg) <> Fc.lanes(t, ts)

def Fc.show(ct: CT) -> String:
  match ct:
    case CT{+i, bad, +first}:
      "rows " ++ U32.show(i) ++ ", differing " ++ U32.show(bad) ++ Bool.pick(String, U32.is_eq(first, 0), "", ", first row " ++ U32.show(U32.sub(first, 1)) ++ " <" ++ Gn.text(U32.sub(first, 1)) ++ ">")

def Fc.out(o: P.PrOut) -> String:
  match o:
    case P.PrOk{nr, odd, regs}:
      Fc.show(Fc.los(Fc.lanes(regs, [L.TyF{}]), CT{0, 0, 0}))
    case P.PrErr{code, msg}:
      "io error " ++ msg

def Fc.run(+path: String, +piece: U32) -> IO(Unit):
  do IO<Unit>:
    o : P.PrOut <- P.Pr.regions(path, 2, 2, piece)
    IO.print("piece " ++ U32.show(piece) ++ ": " ++ Fc.out(o))

# ---- the file ---------------------------------------------------------------------------------------------

# blocks of 500 rows appended to one file (r: the result of the previous write, with the handle)
def Wr.blocks(f: Nat, +b: U32, r: File & Result<&1, &1, U32 & String, Unit>) -> IO(File):
  match f:
    case 0n:
      (h, res) = r
      IO.pure(File, h)
    case 1n+p:
      (h, res) = r
      do IO<File>:
        r2 : File & Result<&1, &1, U32 & String, Unit> <- File.write(h, Gn.lines(500n, U32.mul(b, 500)))
        Wr.blocks(p, U32.inc(b), r2)

def Wr.header(r: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  do IO<Unit>:
    h2 : File <- Wr.blocks(40n, 0, r)
    File.close(h2)

def Wr.opened(o: Result<&1, &1, U32 & String, File>) -> IO(Unit):
  match o:
    case Done{h}:
      do IO<Unit>:
        r : File & Result<&1, &1, U32 & String, Unit> <- File.write(h, "x\n")
        Wr.header(r)
    case Fail{(code, msg)}:
      IO.print("cannot write: " ++ msg)

def main() -> IO(Unit):
  do IO<Unit>:
    o : Result<&1, &1, U32 & String, File> <- File.open("/tmp/bend_frame_csvlane_f32.csv", "w")
    Wr.opened(o)
    Fc.run("/tmp/bend_frame_csvlane_f32.csv", 8192)
    Fc.run("/tmp/bend_frame_csvlane_f32.csv", 1048576)
    Fc.run("/tmp/bend_frame_csvlane_f32.csv", 100003)
#|piece 8192: rows 20000, differing 0
#|piece 1048576: rows 20000, differing 0
#|piece 100003: rows 20000, differing 0
