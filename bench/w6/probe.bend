# bench/w6/probe.bend -- W6.1 / W6.2 bench probe: the production producer (src/csvprod.bend) and lane
# (src/csvlane.bend) on a CSV with the sales schema, phases timed, ONE balanced fork over the
# regions (a test fork: the integration step W6.3 forks the same way), in a program that imports
# frame.bend (the real "hot" String / List build: DESIGN 17.1.3).
#
#   ~/.bend/bin/bend bench/w6/probe.bend -o build/w6/probe
#   build/w6/probe [--threads N] <file> [piece bytes] [mode] [schema] [raw]
#
#   mode pack   the producer only (File.read_at pieces -> packed regions): read_ms, bytes, regions
#   mode lanes  producer, then the fork over the regions (one Ln.lane per region); read_ms, fork_ms;
#               untimed afterwards: the rows and one checksum per column (values, validity, F32 bits,
#               string contents: order-sensitive over the rows)
#   mode ref    v0.1's Csv.read_with with the same schema (read_ms, the same checksums): the oracle
#               (the checksums of `lanes` and `ref` must be equal)
#
# schema: dtype letters, U u32, I i32, F f32, B bool, S str (default USSUFFB: the sales file);
# raw: "raw" reads Str columns as raw rows (TyR) instead of per-region Dictionaries (TyS).
# One JSON line on stdout. The header line is skipped (the header step is W6.3's: here its length is
# found by scanning the first bytes).
import Base
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/kernels.bend as K
import ./../../src/column.bend as C
import ./../../src/strs.bend as ST
import ./../../src/csv.bend as V
import ./../../src/csvprod.bend as P
import ./../../src/csvlane.bend as L
import ./../../frame.bend as DF
import ./hx.bend as X
import ./rd.bend as R

# ---- the fork: one balanced binary tree over the regions, a flat lane per leaf --------------------------

type LT is Type:
  LE{}
  LL{o: L.LO}
  LN{l: LT, r: LT}

def Fk.tree(+ts: List<&2, L.Ty>, +w: U32, +sep: U32, t: P.Rt) -> LT:
  match t:
    case P.RE{}:
      LE{}
    case P.RL{rg}:
      LL{L.Ln.lane(ts, w, sep, rg)}
    case P.RN{l, r}:
      a b = Fk.tree(ts, w, sep, l) Fk.tree(ts, w, sep, r)
      LN{a, b}

# the lanes in order
def Fk.list(t: LT, acc: List<&1, L.LO>) -> List<&1, L.LO>:
  match t:
    case LE{}:
      acc
    case LL{o}:
      o <> acc
    case LN{l, r}:
      Fk.list(l, Fk.list(r, acc))

# the rows of the lanes (forces them), the lanes handed back
def Fk.rows.go(xs: List<&1, L.LO>, +n: U32, acc: List<&1, L.LO>) -> U32 & List<&1, L.LO>:
  match xs:
    case Nil{}:
      (n, List.reverse(&1, L.LO, acc))
    case L.LO{+m, rej, rag, rgn, lines, cols} <> t:
      Fk.rows.go(t, U32.add(n, m), L.LO{m, rej, rag, rgn, lines, cols} <> acc)

# ---- checksums (untimed) -------------------------------------------------------------------------------

def Ck.mix(+h: U32, +x: U32) -> U32:
  U32.mul(U32.xor(h, x), 16777619)

def Ck.sel(c: Bool, +a: U32, +b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

# a word column (u32 / i32 / bool / row hashes) and its 0/1 validity, n rows
def Ck.ww.go(n: Nat, +i: U32, +h: U32, ra: Array<U32> & U32, rv: Array<U32> & U32) -> U32:
  match n:
    case 0n:
      (a, x) = ra
      (v, y) = rv
      h
    case 1n+p:
      (a, +x) = ra
      (v, +y) = rv
      +j = U32.inc(i)
      Ck.ww.go(p, j, Ck.mix(h, Ck.sel(U32.is_eq(y, 1), x, 2654435769)), Array.get(U32, a, j), Array.get(U32, v, j))

def Ck.ff.go(n: Nat, +i: U32, +h: U32, ra: Array<F32> & F32, rv: Array<U32> & U32) -> U32:
  match n:
    case 0n:
      (a, x) = ra
      (v, y) = rv
      h
    case 1n+p:
      (a, x) = ra
      (v, +y) = rv
      +j = U32.inc(i)
      Ck.ff.go(p, j, Ck.mix(h, Ck.sel(U32.is_eq(y, 1), F32.bits(x), 2654435769)), Array.get(F32, a, j), Array.get(U32, v, j))

def Ck.w(+n: U32, a: Array<U32>, v: Array<U32>, +h: U32) -> U32:
  Ck.ww.go(U32.to_nat(n), 0, h, Array.get(U32, a, 0), Array.get(U32, v, 0))

def Ck.f(+n: U32, a: Array<F32>, v: Array<U32>, +h: U32) -> U32:
  Ck.ff.go(U32.to_nat(n), 0, h, Array.get(F32, a, 0), Array.get(U32, v, 0))

# raw rows: the hash of each row's string
def Ck.rr.go(n: Nat, +i: U32, +h: U32, ra: Array<String> & String, rv: Array<U32> & U32) -> U32:
  match n:
    case 0n:
      (a, s) = ra
      (v, y) = rv
      h
    case 1n+p:
      (a, s) = ra
      (v, +y) = rv
      +j = U32.inc(i)
      Ck.rr.go(p, j, Ck.mix(h, Ck.sel(U32.is_eq(y, 1), ST.Str.hash(s), 2654435769)), Array.get(String, a, j), Array.get(U32, v, j))

def Ck.r(+n: U32, a: Array<String>, v: Array<U32>, +h: U32) -> U32:
  Ck.rr.go(U32.to_nat(n), 0, h, Array.get(String, a, 0), Array.get(U32, v, 0))

# a Dictionary part: the hash of each entry once, then rows by code (gather)
def Ck.eh.go(n: Nat, +i: U32, out: Array<U32>, r: Array<String> & String) -> Array<U32>:
  match n:
    case 0n:
      (a, s) = r
      out
    case 1n+p:
      (a, s) = r
      Ck.eh.go(p, U32.inc(i), Array.set(U32, out, i, ST.Str.hash(s)), Array.get(String, a, U32.inc(i)))

def Ck.s.k(+n: U32, v: Array<U32>, +h: U32, r: Array<U32> & Array<U32>) -> U32:
  (rows, perm) = r
  Ck.w(n, rows, v, h)

def Ck.s(+n: U32, c: Array<U32>, v: Array<U32>, +k: U32, ents: Array<String>, +h: U32) -> U32:
  Ck.s.k(n, v, h, K.Kernel.gather(~U32, n, K.Kernel.depth_for(U32.max(n, 1)), Ck.eh.go(U32.to_nat(k), 0, Array.new(U32, K.Kernel.depth_for(U32.max(k, 1)), 0), Array.get(String, ents, 0)), c, 0))

def Ck.one(co: L.CO, +n: U32, +h: U32) -> U32:
  match co:
    case L.OW{a, v, nulls, bad, bl, bt}:
      Ck.w(n, a, v, h)
    case L.OF{a, v, nulls, bad, bl, bt}:
      Ck.f(n, a, v, h)
    case L.OS{c, v, nulls, k, ents}:
      Ck.s(n, c, v, k, ents, h)
    case L.OR{a, v, nulls}:
      Ck.r(n, a, v, h)

# every column of a lane: the running hashes in column order
def Ck.cols(cs: List<&1, L.CO>, hs: List<&2, U32>, +n: U32) -> List<&2, U32>:
  match cs hs:
    case co <> ct h <> ht:
      Ck.one(co, n, h) <> Ck.cols(ct, ht, n)
    case _ _:
      Nil{}

def Ck.lanes(xs: List<&1, L.LO>, hs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      hs
    case L.LO{+n, rej, rag, rgn, lines, cols} <> t:
      Ck.lanes(t, Ck.cols(cols, hs, n))

def Ck.init.go(f: Nat) -> List<&2, U32>:
  match f:
    case 0n:
      Nil{}
    case 1n+p:
      2166136261 <> Ck.init.go(p)

def Ck.init(+k: U32) -> List<&2, U32>:
  Ck.init.go(U32.to_nat(k))

def Ck.show(hs: List<&2, U32>) -> String:
  match hs:
    case Nil{}:
      ""
    case +h <> Nil{}:
      U32.show(h)
    case +h <> t:
      U32.show(h) ++ "," ++ Ck.show(t)

# ---- v0.1's frame: the same checksums ------------------------------------------------------------------

def Ref.col(c: C.Column, +h: U32) -> U32:
  match c:
    case C.CU32{+n, +d, v, x}:
      Ck.w(n, x, C.Valid.materialize(v, d), h)
    case C.CBool{+n, +d, v, x}:
      Ck.w(n, x, C.Valid.materialize(v, d), h)
    case C.CI32{+n, +d, v, x}:
      Ck.w(n, x, C.Valid.materialize(v, d), h)
    case C.CF32{+n, +d, v, x}:
      Ck.f(n, x, C.Valid.materialize(v, d), h)
    case C.CStr{+n, +d, v, x}:
      Ck.r(n, ST.Strs.decode(n, d, x), C.Valid.materialize(v, d), h)

def Ref.cols(cs: List<&1, C.Named>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      Nil{}
    case C.Named{nm, c} <> t:
      Ref.col(c, 2166136261) <> Ref.cols(t)

def Ref.out(+t0: Nat, +t1: Nat, r: E.ResT(C.Frame)) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("{\"probe\":\"w6\",\"mode\":\"ref\",\"error\":\"" ++ E.Err.show(e) ++ "\"}")
    case Done{C.Frame{+h, cols}}:
      IO.print("{\"probe\":\"w6\",\"mode\":\"ref\",\"n\":" ++ U32.show(h) ++ ",\"read_ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"chk\":\"" ++ Ck.show(Ref.cols(cols)) ++ "\"}")

def Ref.run(+path: String, tys: String) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    r : E.ResT(C.Frame) <- V.Csv.read_with(path, V.Csv.default(), R.Hr.dts(tys))
    t1 : Nat <- IO.now()
    Ref.out(t0, t1, r)

# ---- the header's length ---------------------------------------------------------------------------------

# the index + 1 of the first LF in the bytes (0: none)
def Hd.lf(bs: List<&2, U32>, +i: U32) -> U32:
  match bs:
    case Nil{}:
      0
    case +b <> t:
      Bool.pick(U32, U32.is_eq(b, 10), U32.inc(i), Hd.lf(t, U32.inc(i)))

def Hd.res(f: File, res: Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(U32):
  match res:
    case Fail{(code, msg)}:
      do IO<U32>:
        File.close(f)
        return 0
    case Done{bs}:
      do IO<U32>:
        File.close(f)
        return Hd.lf(bs, 0)

def Hd.got(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(U32):
  (f, res) = r
  Hd.res(f, res)

def Hd.opened(o: Result<&1, &1, U32 & String, File>) -> IO(U32):
  match o:
    case Done{f}:
      do IO<U32>:
        r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_at(f, 0, 4096)
        Hd.got(r)
    case Fail{(code, msg)}:
      IO.pure(U32, 0)

def Hd.len(path: String) -> IO(U32):
  do IO<U32>:
    o : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    Hd.opened(o)

# ---- the probe -----------------------------------------------------------------------------------------------

def Pb.bytes(xs: List<&1, P.Rg>, +b: U32, +t: U32) -> U32 & U32:
  match xs:
    case Nil{}:
      (b, t)
    case P.Rg{a, +n, off, line0, +nt, lfs, fin} <> rest:
      Pb.bytes(rest, U32.add(b, n), U32.add(t, nt))

def Pb.packed(+piece: U32, +nr: U32, +t0: Nat, +t1: Nat, r: U32 & U32) -> IO(Unit):
  (+b, +t) = r
  IO.print("{\"probe\":\"w6\",\"mode\":\"pack\",\"piece\":" ++ U32.show(piece) ++ ",\"regions\":" ++ U32.show(nr) ++ ",\"bytes\":" ++ U32.show(b) ++ ",\"terms\":" ++ U32.show(t) ++ ",\"read_ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ "}")

def Pb.done(+mode: String, +piece: U32, +nr: U32, +t0: Nat, +t1: Nat, +t2: Nat, r: U32 & List<&1, L.LO>, +k: U32) -> IO(Unit):
  (+n, los) = r
  IO.print("{\"probe\":\"w6\",\"mode\":\"" ++ mode ++ "\",\"piece\":" ++ U32.show(piece) ++ ",\"regions\":" ++ U32.show(nr) ++ ",\"n\":" ++ U32.show(n) ++ ",\"read_ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"fork_ms\":" ++ Nat.show(Nat.sub(t2, t1)) ++ ",\"ms\":" ++ Nat.show(Nat.sub(t2, t0)) ++ ",\"chk\":\"" ++ Ck.show(Ck.lanes(los, Ck.init(k))) ++ "\"}")

# the fork over the regions, timed; the lanes' rows force them
def Pb.fork(+mode: String, +piece: U32, +nr: U32, +t0: Nat, +t1: Nat, ts: List<&2, L.Ty>, +w: U32, regs: List<&1, P.Rg>) -> IO(Unit):
  do IO<Unit>:
    rs : U32 & List<&1, L.LO> = Fk.rows.go(Fk.list(Fk.tree(ts, w, 44, P.Rt.of(regs)), Nil{}), 0, Nil{})
    t2 : Nat <- IO.now()
    Pb.done(mode, piece, nr, t0, t1, t2, rs, w)

def Pb.read.k(pack: Bool, +mode: String, +piece: U32, +nr: U32, +t0: Nat, +t1: Nat, ts: List<&2, L.Ty>, +w: U32, regs: List<&1, P.Rg>) -> IO(Unit):
  match pack:
    case True{}:
      Pb.packed(piece, nr, t0, t1, Pb.bytes(regs, 0, 0))
    case False{}:
      Pb.fork(mode, piece, nr, t0, t1, ts, w, regs)

def Pb.read(+mode: String, +piece: U32, +w: U32, +t0: Nat, ts: List<&2, L.Ty>, o: P.PrOut) -> IO(Unit):
  match o:
    case P.PrErr{code, msg}:
      IO.print("{\"error\":\"" ++ msg ++ "\"}")
    case P.PrOk{nr, odd, regs}:
      do IO<Unit>:
        t1 : Nat <- IO.now()
        Pb.read.k(String.eq(mode, "pack"), mode, piece, nr, t0, t1, ts, w, regs)

def Pb.run.k(+path: String, +piece: U32, +mode: String, +tys: String, +raw: Bool, +off0: U32) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    o : P.PrOut <- P.Pr.regions(path, off0, 2, piece)
    Pb.read(mode, piece, U32.from_nat(String.length(tys)), t0, R.Hr.tys(tys, raw), o)

def Pb.run(+path: String, +piece: U32, +mode: String, +tys: String, +raw: Bool) -> IO(Unit):
  do IO<Unit>:
    +off0 : U32 <- Hd.len(path)
    Pb.run.k(path, piece, mode, tys, raw, off0)

# ---- args ------------------------------------------------------------------------------------------------------

def Ar.nth(+i: Nat, xs: List<&2, String>, +d: String) -> String:
  match i xs:
    case _ Nil{}:
      d
    case 0n h <> t:
      h
    case 1n+j h <> t:
      Ar.nth(j, t, d)

def Ar.promote(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> Ar.promote(t)

def Ar.num(m: Maybe<&2, U32>, +d: U32) -> U32:
  match m:
    case Some{x}:
      x
    case None{}:
      d

def go.m(+path: String, +piece: U32, +mode: String, +tys: String, +raw: Bool) -> IO(Unit):
  Bool.pick(IO(Unit), String.eq(mode, "ref"), Ref.run(path, tys), Pb.run(path, piece, mode, tys, raw))

def go(+xs: List<&2, String>) -> IO(Unit):
  go.m(Ar.nth(0n, xs, "bench/data/sales_1000.csv"), Ar.num(U32.read(Ar.nth(1n, xs, "262144")), 262144), Ar.nth(2n, xs, "lanes"), Ar.nth(3n, xs, "USSUFFB"), String.eq(Ar.nth(4n, xs, ""), "raw"))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(List.tail(&2, String, Ar.promote(args)))
