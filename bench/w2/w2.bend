# W2.1 / W2.2 native probes (v0.2): the flat coder Hc.code and the rank stage vs v0.1 (the v0.1
# functions come from tests/lib/v01str.bend since W2.3 deleted them from src/).
#   ~/.bend/bin/bend bench/w2/w2.bend -o build/w2/w2
#   build/w2/w2 [--threads N] <shape> <n> <mode>
# shape: distinct prefix longprefix skew equal low uni empty nul aligned wide   (tests/lib/w2gen.bend)
# mode (coder):  old     Sort.str_codes_par (v0.1: Base Map, 8 forked blocks from 2^16 rows)
#                oldseq  Sort.str_codes (v0.1: one Map)
#                new     Hc.code with the default template (FNV-1a + UTF-8 byte lengths, one walk)
#                newh    Hc.code with ST.Str.hash only (no byte lengths): the cost of counting bytes
#                pk      Hc.code.pk (W2.4: one walk hashes and packs the code points, hits compare flat)
# mode (words):  rold    Sort.str_words (v0.1: Map coder + Map.to_list ranks; frees its input rows)
#                rnew    Rk.words (Hc.code, then the rank stage, the rows handed back)
#                rstage  Hc.code then Rk.ranks then the gather, each stage timed (code_ms rank_ms
#                        gather_ms) and the rank stage's rows back
#                rparts  the stage opened up: code_ms off_ms pack_ms rounds_ms (incl. the rank
#                        scatter) gather_ms
#                dold / dnew  Dict.ranks (v0.1) vs Rk.dict on the dictionary of the rows' distinct
#                        entries (k = distinct strings + 1)
# mode frame:    never used for measuring: it only makes frame.bend's reader reachable so the program
#                has the same hot types as a program importing the library (DESIGN 17.1.3)
# The keys are generated and walked once before the clock; rows stay alive past the clock
# (`keep`): freeing 1M strings inside a timed region would be timed too. stdout: one JSON line;
# chk = FNV fold of the codes (code modes) or the words (word modes): equal chk = equal output.
import Base
import ./../../frame.bend as DF
import ./../../src/kernels.bend as K
import ./../../src/strs.bend as ST
import ./../../tests/lib/v01str.bend as V1
import ./../../src/hcode.bend as H
import ./../../src/ranks.bend as R
import ./../../tests/lib/w2gen.bend as G

def shape_of(+s: String) -> G.Shape:
  Bool.pick(G.Shape, String.eq(s, "prefix"), G.ShP{},
  Bool.pick(G.Shape, String.eq(s, "longprefix"), G.ShQ{},
  Bool.pick(G.Shape, String.eq(s, "skew"), G.ShS{},
  Bool.pick(G.Shape, String.eq(s, "equal"), G.ShE{},
  Bool.pick(G.Shape, String.eq(s, "low"), G.ShL{},
  Bool.pick(G.Shape, String.eq(s, "uni"), G.ShU{},
  Bool.pick(G.Shape, String.eq(s, "empty"), G.ShZ{},
  Bool.pick(G.Shape, String.eq(s, "nul"), G.ShN{},
  Bool.pick(G.Shape, String.eq(s, "aligned"), G.ShM{},
  Bool.pick(G.Shape, String.eq(s, "wide"), G.ShW{}, G.ShD{}))))))))))

def Str.len(s: String, +acc: U32) -> U32:
  match s:
    case SNil{}:
      acc
    case SCon{c, t}:
      Str.len(t, U32.inc(acc))

def chk(+n: U32, a: Array<U32>) -> Array<U32> & U32:
  K.Kernel.fold(~U32, ~U32, ~(acc => c => U32.mul(U32.xor(acc, c), 16777619)), n, a, 2166136261)

def pr(+mode: String, +shape: String, +n: U32, +k: U32, +chars: U32, +ms: Nat, +x: U32, +extra: String) -> IO(Unit):
  IO.print("{\"w2\":\"" ++ mode ++ "\",\"shape\":\"" ++ shape ++ "\",\"n\":" ++ U32.show(n) ++ ",\"k\":" ++ U32.show(k) ++ ",\"chars\":" ++ U32.show(chars) ++ ",\"ms\":" ++ Nat.show(ms) ++ ",\"chk\":" ++ U32.show(x) ++ extra ++ "}")

# the length of row 0, read after the last clock: the rows stay alive until then
def keep.k(r: Array<String> & String) -> U32:
  (a, s) = r
  Str.len(s, 0)

def keep(a: Array<String>) -> String:
  ",\"keep\":" ++ U32.show(keep.k(Array.get(String, a, 0)))

# ---- coder modes -----------------------------------------------------------------------------------

def fin.ck(+mode: String, +shape: String, +n: U32, +chars: U32, +t0: Nat, +t1: Nat, +k: U32, a: Array<String>, r: Array<U32> & U32) -> IO(Unit):
  (codes, +x) = r
  pr(mode, shape, n, k, chars, Nat.sub(t1, t0), x, keep(a))

def fin.cs(+mode: String, +shape: String, +n: U32, +chars: U32, +t0: Nat, +t1: Nat, codes: Array<U32>, +k: U32, a: Array<String>) -> IO(Unit):
  fin.ck(mode, shape, n, chars, t0, t1, k, a, chk(n, codes))

def run.old.k(+mode: String, +shape: String, +n: U32, +chars: U32, +t0: Nat, r: Array<String> & Array<U32> & V1.CS) -> IO(Unit):
  (strs, codes, cs) = r
  match cs:
    case V1.CS{m, +k}:
      do IO<Unit>:
        t1 : Nat <- IO.now()
        fin.cs(mode, shape, n, chars, t0, t1, codes, k, strs)

def run.new.k(+mode: String, +shape: String, +n: U32, +chars: U32, +t0: Nat, st: H.HC) -> IO(Unit):
  match st:
    case H.HC{+next, a, hs, rp, ids, out, fr, bl}:
      do IO<Unit>:
        t1 : Nat <- IO.now()
        fin.cs(mode, shape, n, chars, t0, t1, out, next, a)

def run.pk.k(+mode: String, +shape: String, +n: U32, +chars: U32, +t0: Nat, st: H.HJ) -> IO(Unit):
  match st:
    case H.HJ{+next, a, hs, ix, out, po, pl, pk, cur, pd}:
      do IO<Unit>:
        t1 : Nat <- IO.now()
        fin.cs(mode, shape, n, chars, t0, t1, out, next, a)

# ---- word modes ------------------------------------------------------------------------------------

def run.rold.k(+shape: String, +n: U32, +chars: U32, +t0: Nat, w: Array<U32>) -> IO(Unit):
  do IO<Unit>:
    t1 : Nat <- IO.now()
    fin.cs("rold", shape, n, chars, t0, t1, w, 0, Array.new(String, 0n, ""))

def run.rnew.k(+shape: String, +n: U32, +chars: U32, +t0: Nat, r: Array<String> & Array<U32>) -> IO(Unit):
  (a, w) = r
  do IO<Unit>:
    t1 : Nat <- IO.now()
    fin.cs("rnew", shape, n, chars, t0, t1, w, 0, a)

# rstage: code, rank stage, gather
def rs.out(+shape: String, +n: U32, +chars: U32, +k: U32, +t0: Nat, +t1: Nat, +t2: Nat, +t3: Nat, a: Array<String>, r: Array<U32> & U32) -> IO(Unit):
  (w, +x) = r
  pr("rstage", shape, n, k, chars, Nat.sub(t3, t0), x, keep(a) ++ ",\"code_ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"rank_ms\":" ++ Nat.show(Nat.sub(t2, t1)) ++ ",\"gather_ms\":" ++ Nat.show(Nat.sub(t3, t2)))

def rs.fin(+shape: String, +n: U32, +chars: U32, +k: U32, +t0: Nat, +t1: Nat, +t2: Nat, a: Array<String>, r: Array<U32> & Array<U32>) -> IO(Unit):
  (w, codes) = r
  do IO<Unit>:
    t3 : Nat <- IO.now()
    rs.out(shape, n, chars, k, t0, t1, t2, t3, a, chk(n, w))

def rs.rk(+shape: String, +n: U32, +d: Nat, +chars: U32, +k: U32, +t0: Nat, +t1: Nat, codes: Array<U32>, rk: R.RK) -> IO(Unit):
  match rk:
    case R.RK{a, fr, rank}:
      do IO<Unit>:
        t2 : Nat <- IO.now()
        rs.fin(shape, n, chars, k, t0, t1, t2, a, K.Kernel.gather(~U32, n, d, rank, codes, 0))

def rs.k(+shape: String, +n: U32, +d: Nat, +chars: U32, +t0: Nat, st: H.HC) -> IO(Unit):
  match st:
    case H.HC{+k, a, hs, rp, ids, out, fr, bl}:
      do IO<Unit>:
        t1 : Nat <- IO.now()
        rs.rk(shape, n, d, chars, k, t0, t1, out, R.Rk.ranks(k, K.Kernel.depth_for(U32.max(k, 1)), 0, a, fr, bl))

# rparts: the rank stage opened up: code, offsets, pack, rounds + rank scatter, gather
def rp.out(+shape: String, +n: U32, +chars: U32, +k: U32, +t0: Nat, +t1: Nat, +t2: Nat, +t3: Nat, +t4: Nat, +t5: Nat, a: Array<String>, r: Array<U32> & U32) -> IO(Unit):
  (w, +x) = r
  pr("rparts", shape, n, k, chars, Nat.sub(t5, t0), x, keep(a) ++ ",\"code_ms\":" ++ Nat.show(Nat.sub(t1, t0)) ++ ",\"off_ms\":" ++ Nat.show(Nat.sub(t2, t1)) ++ ",\"pack_ms\":" ++ Nat.show(Nat.sub(t3, t2)) ++ ",\"rounds_ms\":" ++ Nat.show(Nat.sub(t4, t3)) ++ ",\"gather_ms\":" ++ Nat.show(Nat.sub(t5, t4)))

def rp.fin(+shape: String, +n: U32, +chars: U32, +k: U32, +t0: Nat, +t1: Nat, +t2: Nat, +t3: Nat, +t4: Nat, a: Array<String>, r: Array<U32> & Array<U32>) -> IO(Unit):
  (w, codes) = r
  do IO<Unit>:
    t5 : Nat <- IO.now()
    rp.out(shape, n, chars, k, t0, t1, t2, t3, t4, t5, a, chk(n, w))

def rp.d(+shape: String, +n: U32, +d: Nat, +chars: U32, +k: U32, +t0: Nat, +t1: Nat, +t2: Nat, +t3: Nat, codes: Array<U32>, rk: R.RK) -> IO(Unit):
  match rk:
    case R.RK{a, fr, rank}:
      do IO<Unit>:
        t4 : Nat <- IO.now()
        rp.fin(shape, n, chars, k, t0, t1, t2, t3, t4, a, K.Kernel.gather(~U32, n, d, rank, codes, 0))

def rp.c(+shape: String, +n: U32, +d: Nat, +chars: U32, +k: U32, +t0: Nat, +t1: Nat, +t2: Nat, +mx: U32, codes: Array<U32>, bl: Array<U32>, rf: R.RF) -> IO(Unit):
  match rf:
    case R.RF{a, fr, wo, pk, cm}:
      do IO<Unit>:
        t3 : Nat <- IO.now()
        rp.d(shape, n, d, chars, k, t0, t1, t2, t3, codes, R.Rk.run(k, K.Kernel.depth_for(U32.max(k, 1)), 0, 8, mx, a, fr, wo, bl, pk))

def rp.b(+shape: String, +n: U32, +d: Nat, +chars: U32, +k: U32, +t0: Nat, +t1: Nat, codes: Array<U32>, a: Array<String>, fr: Array<U32>, rw: R.RW) -> IO(Unit):
  match rw:
    case R.RW{+tot, +mx, bl, wo}:
      do IO<Unit>:
        t2 : Nat <- IO.now()
        rp.c(shape, n, d, chars, k, t0, t1, t2, mx, codes, bl, R.Rf.go(U32.to_nat(k), 0, R.RF{a, fr, wo, Array.new(U32, K.Kernel.depth_for(U32.inc(tot)), 0), 0}))

def rp.k(+shape: String, +n: U32, +d: Nat, +chars: U32, +t0: Nat, st: H.HC) -> IO(Unit):
  match st:
    case H.HC{+k, a, hs, rp, ids, out, fr, bl}:
      do IO<Unit>:
        t1 : Nat <- IO.now()
        rp.b(shape, n, d, chars, k, t0, t1, out, a, fr, R.Rw.go(U32.to_nat(k), 0, 0, 0, 3, 2n, Array.new(U32, K.Kernel.depth_for(U32.inc(k)), 0), Array.get(U32, bl, 0)))

# ---- the Dictionary ranks (v0.1 Map vs the flat stage), the dictionary of the distinct entries -----

def dg.go(n: Nat, +i: U32, d: ST.Dict, r: Array<String> & String) -> ST.Dict & Array<String>:
  match n:
    case 0n:
      (a, s) = r
      (d, a)
    case 1n+p:
      (a, s) = r
      +j = U32.inc(i)
      dg.go(p, j, ST.Dict.fst(ST.Dict.code(d, s)), Array.get(String, a, j))

def dict.out(+mode: String, +shape: String, +n: U32, +chars: U32, +k: U32, +t0: Nat, +t1: Nat, a: Array<String>, r: Array<U32> & U32) -> IO(Unit):
  (rk, +x) = r
  pr(mode, shape, n, k, chars, Nat.sub(t1, t0), x, keep(a))

def dict.fin(+mode: String, +shape: String, +n: U32, +chars: U32, +k: U32, +t0: Nat, a: Array<String>, r: ST.Dict & Array<U32>) -> IO(Unit):
  (d, rk) = r
  do IO<Unit>:
    t1 : Nat <- IO.now()
    dict.out(mode, shape, n, chars, k, t0, t1, a, chk(k, rk))

def dict.rank(+new: Bool, +mode: String, +shape: String, +n: U32, +chars: U32, +k: U32, +t0: Nat, a: Array<String>, d: ST.Dict) -> IO(Unit):
  match new:
    case True{}:
      dict.fin(mode, shape, n, chars, k, t0, a, R.Rk.dict(d))
    case False{}:
      dict.fin(mode, shape, n, chars, k, t0, a, V1.Dict.ranks(d))

def dict.run(+new: Bool, +mode: String, +shape: String, +n: U32, +chars: U32, a: Array<String>, d: ST.Dict) -> IO(Unit):
  match d:
    case ST.Dict{+k, dd, strs, b, slots, tag}:
      do IO<Unit>:
        t0 : Nat <- IO.now()
        dict.rank(new, mode, shape, n, chars, k, t0, a, ST.Dict{k, dd, strs, b, slots, tag})

def dict.start.d(+new: Bool, +mode: String, +shape: String, +n: U32, +chars: U32, r: ST.Dict & Array<String>) -> IO(Unit):
  (dc, a) = r
  dict.run(new, mode, shape, n, chars, a, dc)

def dict.start.c(+new: Bool, +mode: String, +shape: String, +n: U32, r: Array<String> & U32) -> IO(Unit):
  (a, +chars) = r
  dict.start.d(new, mode, shape, n, chars, dg.go(U32.to_nat(n), 0, ST.Dict.empty(), Array.get(String, a, 0)))

def dict.start(+new: Bool, +mode: String, +shape: String, +n: U32) -> IO(Unit):
  dict.start.c(new, mode, shape, n, K.Kernel.fold(~String, ~U32, ~(acc => s => U32.add(acc, Str.len(s, 0))), n, G.Gen.mk(n, shape_of(shape)), 0))

# ---- dispatch --------------------------------------------------------------------------------------

type Mode is Data:
  MOld{}
  MOldSeq{}
  MNew{}
  MNewH{}
  MROld{}
  MRNew{}
  MRStage{}
  MRParts{}
  MDOld{}
  MDNew{}
  MPk{}
  MFrame{}

def mode_of(+s: String) -> Mode:
  Bool.pick(Mode, String.eq(s, "old"), MOld{},
  Bool.pick(Mode, String.eq(s, "oldseq"), MOldSeq{},
  Bool.pick(Mode, String.eq(s, "new"), MNew{},
  Bool.pick(Mode, String.eq(s, "newh"), MNewH{},
  Bool.pick(Mode, String.eq(s, "rold"), MROld{},
  Bool.pick(Mode, String.eq(s, "rnew"), MRNew{},
  Bool.pick(Mode, String.eq(s, "rstage"), MRStage{},
  Bool.pick(Mode, String.eq(s, "rparts"), MRParts{},
  Bool.pick(Mode, String.eq(s, "dold"), MDOld{},
  Bool.pick(Mode, String.eq(s, "dnew"), MDNew{},
  Bool.pick(Mode, String.eq(s, "pk"), MPk{},
  MFrame{})))))))))))

def run.mode(m: Mode, +mode: String, +shape: String, +n: U32, +d: Nat, +chars: U32, +t0: Nat, a: Array<String>) -> IO(Unit):
  match m:
    case MOld{}:
      run.old.k(mode, shape, n, chars, t0, V1.Sort.str_codes_par(n, d, 0, a))
    case MOldSeq{}:
      run.old.k(mode, shape, n, chars, t0, V1.Sort.str_codes(n, d, 0, a))
    case MNew{}:
      run.new.k(mode, shape, n, chars, t0, H.Hc.code.fnv(n, d, 0, a))
    case MNewH{}:
      run.new.k(mode, shape, n, chars, t0, H.Hc.code(~(s => H.Hc.hash.h(s)), n, d, 0, a))
    case MPk{}:
      run.pk.k(mode, shape, n, chars, t0, H.Hc.code.pk(~(h => h), n, d, a))
    case MROld{}:
      run.rold.k(shape, n, chars, t0, V1.Sort.str_words(n, d, 0, a))
    case MRNew{}:
      run.rnew.k(shape, n, chars, t0, R.Rk.words(n, d, 0, a))
    case MRStage{}:
      rs.k(shape, n, d, chars, t0, H.Hc.code.fnv(n, d, 0, a))
    case MRParts{}:
      rp.k(shape, n, d, chars, t0, H.Hc.code.fnv(n, d, 0, a))
    case _:
      IO.print("unknown mode " ++ mode)

def run.go(m: Mode, +mode: String, +shape: String, +n: U32, +d: Nat, r: Array<String> & U32) -> IO(Unit):
  (a, +chars) = r
  do IO<Unit>:
    t0 : Nat <- IO.now()
    run.mode(m, mode, shape, n, d, chars, t0, a)

def run(m: Mode, +mode: String, +shape: String, +n: U32) -> IO(Unit):
  +d = G.Gen.depth(n)
  run.go(m, mode, shape, n, d, K.Kernel.fold(~String, ~U32, ~(acc => s => U32.add(acc, Str.len(s, 0))), n, G.Gen.mk(n, shape_of(shape)), 0))

def go.mode(m: Mode, +mode: String, +shape: String, +n: U32) -> IO(Unit):
  match m:
    case MFrame{}:
      do IO<Unit>:
        r : DF.ResT(DF.Frame()) <- DF.read_csv("/dev/null")
        IO.print("frame")
    case MDOld{}:
      dict.start(False{}, mode, shape, n)
    case MDNew{}:
      dict.start(True{}, mode, shape, n)
    case other:
      run(other, mode, shape, n)

def nth(+i: Nat, xs: List<&2, String>, +d: String) -> String:
  match i xs:
    case _ Nil{}:
      d
    case 0n h <> t:
      h
    case 1n+j h <> t:
      nth(j, t, d)

def promote(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> promote(t)

def num(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{x}:
      x
    case None{}:
      1000

def go(+xs: List<&2, String>) -> IO(Unit):
  go.mode(mode_of(nth(2n, xs, "new")), nth(2n, xs, "new"), nth(0n, xs, "distinct"), num(U32.read(nth(1n, xs, "1000"))))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(List.tail(&2, String, promote(args)))
