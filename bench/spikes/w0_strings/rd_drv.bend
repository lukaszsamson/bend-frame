# W0 spike T5 driver body (disposable): times the piece reader of rd.bend on a CSV with the
# sales schema (u32, str, str, u32, f32, f32, bool; header line), prints one JSON line.
# Imported by rd_solo.bend (without frame.bend) and rd_frame.bend (the same code inside a program
# that imports frame.bend and runs today's reader too: the real integrated build, T4).
#   mode spike: read (producer) -> fork (lanes) -> merge/concat, each phase timed (ms)
#   mode pack:  the producer only (File.read_at pieces, pack + lexical scan): its serial cost
import Base
import ./../../../src/kernels.bend as K
import ./../../../src/strs.bend as ST
import ./rd.bend as R

def Drv.sales() -> List<&2, R.Ty>:
  R.TyU{} <> R.TyS{} <> R.TyS{} <> R.TyU{} <> R.TyF{} <> R.TyF{} <> R.TyB{} <> Nil{}

def Drv.len(xs: List<&2, R.Ty>, +n: U32) -> U32:
  match xs:
    case Nil{}:
      n
    case h <> t:
      Drv.len(t, U32.inc(n))

# column types by letter: U u32, S str, F f32, B bool, anything else: the column is skipped
def Drv.ty(+c: U32) -> R.Ty:
  Bool.pick(R.Ty, U32.is_eq(c, 85), R.TyU{}, Bool.pick(R.Ty, U32.is_eq(c, 83), R.TyS{}, Bool.pick(R.Ty, U32.is_eq(c, 70), R.TyF{}, Bool.pick(R.Ty, U32.is_eq(c, 66), R.TyB{}, R.TyN{}))))

def Drv.tys(s: String) -> List<&2, R.Ty>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      Drv.ty(c) <> Drv.tys(t)

# ---- checksums (untimed) -----------------------------------------------------------------------

def Ck.mix(+h: U32, +x: U32) -> U32:
  U32.mul(U32.xor(h, x), 16777619)

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
      Ck.ww.go(p, j, Ck.mix(h, R.W(U32.is_eq(y, 1), x, 2654435769)), Array.get(U32, a, j), Array.get(U32, v, j))

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
      Ck.ff.go(p, j, Ck.mix(h, R.W(U32.is_eq(y, 1), F32.bits(x), 2654435769)), Array.get(F32, a, j), Array.get(U32, v, j))

# a word column (u32 / bool / dictionary codes) and its 0/1 validity, n rows
def Ck.w(+n: U32, a: Array<U32>, v: Array<U32>) -> U32:
  Ck.ww.go(U32.to_nat(n), 0, 2166136261, Array.get(U32, a, 0), Array.get(U32, v, 0))

def Ck.f(+n: U32, a: Array<F32>, v: Array<U32>) -> U32:
  Ck.ff.go(U32.to_nat(n), 0, 2166136261, Array.get(F32, a, 0), Array.get(U32, v, 0))

def Ck.d.k(r: ST.Dict & U32) -> U32:
  (d, k) = r
  k

# a column checksum, its nulls, its index from the end (i) and first bad row + 1 (0: none)
type CR3 is Data:
  CR3{h: U32, nl: U32, bc: U32, br: U32}

def Ck.col(+n: U32, +i: U32, c: R.FC) -> CR3:
  match c:
    case R.FW{a, v, +nulls, +bad}:
      CR3{Ck.w(n, a, v), nulls, i, bad}
    case R.FF{a, v, +nulls, +bad}:
      CR3{Ck.f(n, a, v), nulls, i, bad}
    case R.FSt{c, v, +nulls, dict}:
      CR3{Ck.mix(Ck.w(n, c, v), Ck.d.k(ST.Dict.size(dict))), nulls, i, 0}

# columns come last first from Cat.cols: fold them (order-sensitive) into one checksum
# rest: the earlier columns (a bad cell there wins: the first column in column order)
def Ck.cols.k(r: CR3, rest: CR3) -> CR3:
  match r rest:
    case CR3{+h, +nl, +bc, +br} CR3{+hs, +nls, +bcs, +brs}:
      +early = U32.is_ne(brs, 0)
      CR3{Ck.mix(hs, h), U32.add(nls, nl), R.W(early, bcs, bc), R.W(early, brs, br)}

def Ck.cols(cs: List<&1, R.FC>, +n: U32, +i: U32) -> CR3:
  match cs:
    case Nil{}:
      CR3{2166136261, 0, 0, 0}
    case c <> t:
      Ck.cols.k(Ck.col(n, i, c), Ck.cols(t, n, U32.inc(i)))

def Ck.line.g(r: Array<U32> & U32) -> U32:
  (a, x) = r
  x

# the physical line of global row `row` (lanes in order)
def Ck.line(xs: List<&1, R.LO>, +row: U32) -> U32:
  match xs:
    case Nil{}:
      0
    case R.LO{+n, rej, rag, rgn, lines, cols} <> t:
      R.W(U32.is_lt(row, n), Ck.line.g(Array.get(U32, lines, row)), Ck.line(t, U32.sub(row, n)))

# ---- mode spike -----------------------------------------------------------------------------------

def Drv.err(+rej: U32, +rag: U32, +rgn: U32, +w: U32, +bc: U32, +br: U32, +line: U32) -> String:
  Bool.pick(String, U32.is_ne(rej, 0), "malformed", Bool.pick(String, U32.is_ne(rag, 0), "ragged " ++ U32.show(rag) ++ " " ++ U32.show(rgn), Bool.pick(String, U32.is_ne(br, 0), "bad " ++ U32.show(U32.sub(U32.sub(w, 1), bc)) ++ " " ++ U32.show(line), "ok")))

def Drv.json(+mode: String, +piece: U32, +nr: U32, +n: U32, +w: U32, +t0: Nat, +t1: Nat, +t2: Nat, +t3: Nat, s: R.SUM, los: List<&1, R.LO>, r: CR3) -> IO(Unit):
  match s:
    case R.SUM{n2, +rej, +rag, +rgn}:
      match r:
        case CR3{+h, +nulls, +bc, +br}:
          IO.print("{\"spike\":\"rd\",\"mode\":\"" ++ mode ++ "\",\"piece\":" ++ U32.show(piece) ++ ",\"regions\":" ++ U32.show(nr) ++ ",\"n\":" ++ U32.show(n) ++ ",\"read_ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"fork_ms\":" ++ Nat.show(Nat.sub(t2, t1)) ++ ",\"merge_ms\":" ++ Nat.show(Nat.sub(t3, t2)) ++ ",\"ms\":" ++ Nat.show(Nat.sub(t3, t0)) ++ ",\"rej\":" ++ U32.show(rej) ++ ",\"rag\":" ++ U32.show(rag) ++ ",\"rgn\":" ++ U32.show(rgn) ++ ",\"nulls\":" ++ U32.show(nulls) ++ ",\"err\":\"" ++ Drv.err(rej, rag, rgn, w, bc, br, Ck.line(los, U32.sub(br, 1))) ++ "\",\"chk\":" ++ U32.show(h) ++ "}")

def Drv.merged(+w: U32, +mode: String, +piece: U32, +nr: U32, +t0: Nat, +t1: Nat, +t2: Nat, s: R.SUM, r: List<&1, R.LO> & List<&1, R.FC>) -> IO(Unit):
  match s:
    case R.SUM{+n, +rej, +rag, +rgn}:
      (los, fcs) = r
      do IO<Unit>:
        t3 : Nat <- IO.now()
        Drv.json(mode, piece, nr, n, w, t0, t1, t2, t3, R.SUM{n, rej, rag, rgn}, los, Ck.cols(fcs, n, 0))

def Drv.forked(+ts: List<&2, R.Ty>, +mode: String, +piece: U32, +nr: U32, +t0: Nat, +t1: Nat, r: List<&1, R.LO> & R.SUM) -> IO(Unit):
  (los, s) = r
  match s:
    case R.SUM{+n, +rej, +rag, +rgn}:
      do IO<Unit>:
        t2 : Nat <- IO.now()
        Drv.merged(Drv.len(ts, 0), mode, piece, nr, t0, t1, t2, R.SUM{n, rej, rag, rgn}, R.Cat.cols(ts, 0, K.Kernel.depth_for(U32.max(n, 1)), (los, Nil{})))

def Drv.lanes(+ts: List<&2, R.Ty>, +mode: String, +piece: U32, +nr: U32, +t0: Nat, +t1: Nat, t: R.Rt) -> IO(Unit):
  Drv.forked(ts, mode, piece, nr, t0, t1, R.Lo.sum(R.Lt.list(R.Ln.tree(ts, Drv.len(ts, 0), 44, t), Nil{}), (Nil{}, R.SUM{0, 0, 0, 0})))

# region bytes and terminators (mode pack's validation)
def Drv.bytes(xs: List<&1, R.Rg>, +b: U32, +t: U32) -> U32 & U32:
  match xs:
    case Nil{}:
      (b, t)
    case R.Rg{a, +n, line0, +nt, fin, hd} <> rest:
      Drv.bytes(rest, U32.add(b, n), U32.add(t, nt))

def Drv.packed(+piece: U32, +nr: U32, +err: U32, +t0: Nat, +t1: Nat, r: U32 & U32) -> IO(Unit):
  (+b, +t) = r
  IO.print("{\"spike\":\"rd\",\"mode\":\"pack\",\"piece\":" ++ U32.show(piece) ++ ",\"regions\":" ++ U32.show(nr) ++ ",\"bytes\":" ++ U32.show(b) ++ ",\"terms\":" ++ U32.show(t) ++ ",\"err\":" ++ U32.show(err) ++ ",\"ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"chk\":" ++ U32.show(U32.add(b, t)) ++ "}")

def Drv.read.k(pack: Bool, +ts: List<&2, R.Ty>, +mode: String, +piece: U32, +nr: U32, +err: U32, +t0: Nat, +t1: Nat, regs: List<&1, R.Rg>) -> IO(Unit):
  match pack:
    case True{}:
      Drv.packed(piece, nr, err, t0, t1, Drv.bytes(regs, 0, 0))
    case False{}:
      Drv.lanes(ts, mode, piece, nr, t0, t1, R.Rt.top(32n, R.Rt.leaves(regs, Nil{})))

def Drv.read(+ts: List<&2, R.Ty>, +mode: String, +piece: U32, +pack: Bool, +t0: Nat, rs: R.RS) -> IO(Unit):
  match rs:
    case R.REnd{+nr, regs, +err}:
      do IO<Unit>:
        t1 : Nat <- IO.now()
        Drv.read.k(pack, ts, mode, piece, nr, err, t0, t1, regs)
    case R.RRun{f, off, size, p, line0, hd, nr, pk, regs}:
      IO.print("{\"error\":\"read did not finish\"}")

def Drv.run.k(+path: String, +piece: U32, +mode: String, +ts: List<&2, R.Ty>) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    rs : R.RS <- R.Rd.regions(path, piece, 1)
    Drv.read(ts, mode, piece, String.eq(mode, "pack"), t0, rs)

def Drv.run(+path: String, +piece: U32, +mode: String, tys: String) -> IO(Unit):
  Drv.run.k(path, piece, mode, Drv.tys(tys))

# ---- args ----------------------------------------------------------------------------------------

def Drv.nth(+i: Nat, xs: List<&2, String>, +d: String) -> String:
  match i xs:
    case _ Nil{}:
      d
    case 0n h <> t:
      h
    case 1n+j h <> t:
      Drv.nth(j, t, d)

def Drv.promote(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> Drv.promote(t)

def Drv.num(m: Maybe<&2, U32>, +d: U32) -> U32:
  match m:
    case Some{x}:
      x
    case None{}:
      d
