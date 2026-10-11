# W0 measurement driver for the v0.2 performance milestone (plans/M_02.txt W0, G6). Native only:
#   ~/.bend/bin/bend bench/m2/driver.bend -o build/m2/<candidate|baseline>/driver
#   ./driver [--threads N] <mode> <op> <file> <aux|-> [batch [param [out.csv]]]
#
# The SAME file is built at the pinned baseline (3612482, bench/m2/baseline.sh copies it in) and at
# the candidate checkout, so the two binaries differ only in src/ and frame.bend. It imports the
# public facade (frame.bend as DF) for every operation (read_csv, clone, collect, sources, lazy
# plan verbs, describe, write_csv) and the src/ modules only where the facade has no door: the
# plan constructors (GroupBy with maintain_order False, like bench/queries.bend), the walk that
# forces every cell (bench/main.bend `force`) and the content hash (`Hc.*`). If the column
# representation changes, only `force` and `Hc.*` (the "shim" at the top) need adapting; the hash
# is a function of the LOGICAL content, so the frozen expected values stay valid.
#
# modes (one process = one mode = one op):
#   phases  parse (read, then a full walk of every buffer), prep (the input-preservation clone:
#           the run is over a clone and the originals stay referenced until after the clock, as
#           bench/main.bend), compute (the plan's Lazy.collect, or the eager describe for q6; the
#           result stays alive), check (content hash of the first result, consuming it: the
#           output/validation phase; any pending parallel work is billed here, so compute+check is
#           the honest figure and e2e the fair one)
#   e2e     ONE timed region: read + compute + check (hash) with consume semantics: no walk, no
#           preservation clone, the inputs are freed inside the region
#   e2ecsv  one timed region: read + compute + write_csv(out.csv, floats at 4 decimals); the content
#           hash is taken after the clock (the runner also hashes the file)
#   selfcheck  (not a measurement) the content hash of <file> read with Raw / Dictionary / default strings
#           and of a clone must agree: {"raw","dict","auto","clone","eq"}
#   stages  untimed setup, then each eager stage of q1..q6 timed on its own over fresh clones
#           (filter alone, select alone, sort alone, group_by alone, ...); see `stg.*`
# ops: q1..q6 (file = sales csv, aux = products csv), parse, nunique (select n_unique(x)), group,
#   unique, join (hc files: k, v, x / dim k, w), filter (qty > param over the sales file)
# batch: inputs per timed window (default 1; IO.now has 1 ms resolution, so 1k-row controls use
#   batch > 1, each input parsed on its own); every ms field is the WINDOW, the runner divides.
#
# stdout: one JSON line of integers (ms) and hashes, or a line starting with "error:".
#
# CSV reader: every input is read through bench/m2/engine.bend (EN.Eng.read_csv): BF_ENGINE=v02 selects the
# v0.2 reader (W6.3, DESIGN.md 16.5 D7), anything else v0.1. The baseline build gets bench/m2/engine_v01.bend
# as its engine.bend (bench/m2/baseline.sh): v0.1 whatever BF_ENGINE says. selfcheck reads with v0.1 only.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/kernels.bend as K
import ./../../src/column.bend as C
import ./../../src/strs.bend as ST
import ./../../src/join.bend as J
import ./../../src/plan.bend as P
import ./../../src/expr.bend as X
import ./engine.bend as EN

# ===== shim: forcing (bench/main.bend `force`, every cell read once) ==========================

def Fw.k(t: D.DType, +n: U32, d: Nat, v: C.Valid, r: Array<U32> & U32) -> C.Column & U32:
  (x, h) = r
  (C.Column.mk_w(t, n, d, v, x), h)

def Ff.k(+n: U32, d: Nat, v: C.Valid, r: Array<F32> & F32) -> C.Column & U32:
  (x, h) = r
  (C.CF32{n, d, v, x}, F32.to_u32(h))

def Fs.k(+n: U32, d: Nat, v: C.Valid, r: ST.Strs & U32) -> C.Column & U32:
  (x, h) = r
  (C.CStr{n, d, v, x}, h)

def Fs.r(r: Array<String> & U32) -> ST.Strs & U32:
  (a, h) = r
  (ST.SRaw{a}, h)

def Fs.d(dict: ST.Dict, r: Array<U32> & U32) -> ST.Strs & U32:
  (c, h) = r
  (ST.SDict{c, dict}, h)

def Fs.walk(+n: U32, x: ST.Strs) -> ST.Strs & U32:
  match x:
    case ST.SRaw{a}:
      Fs.r(K.Kernel.fold(~String, ~U32, ~(a => y => U32.add(a, J.Str.hash(y, 0))), n, a, 0))
    case ST.SDict{c, dict}:
      Fs.d(dict, K.Kernel.fold(~U32, ~U32, ~(a => y => U32.add(a, y)), n, c, 0))

def Fw.col(c: C.Column) -> C.Column & U32:
  match c:
    case C.CBool{+n, d, v, x}:
      Fw.k(D.TBool{}, n, d, v, K.Kernel.fold(~U32, ~U32, ~(a => y => U32.add(a, y)), n, x, 0))
    case C.CU32{+n, d, v, x}:
      Fw.k(D.TU32{}, n, d, v, K.Kernel.fold(~U32, ~U32, ~(a => y => U32.add(a, y)), n, x, 0))
    case C.CI32{+n, d, v, x}:
      Fw.k(D.TI32{}, n, d, v, K.Kernel.fold(~U32, ~U32, ~(a => y => U32.add(a, y)), n, x, 0))
    case C.CF32{+n, d, v, x}:
      Ff.k(n, d, v, K.Kernel.fold(~F32, ~F32, ~(a => y => F32.add(a, y)), n, x, 0.0))
    case C.CStr{+n, d, v, x}:
      Fs.k(n, d, v, Fs.walk(n, x))

def Fw.add(n: String, acc: List<&1, C.Named>, +h: U32, r: C.Column & U32) -> List<&1, C.Named> & U32:
  (c, x) = r
  (C.Named{n, c} <> acc, U32.add(h, x))

def Fw.step(n: String, c: C.Column, st: List<&1, C.Named> & U32) -> List<&1, C.Named> & U32:
  (acc, +h) = st
  Fw.add(n, acc, h, Fw.col(c))

def Fw.go(cols: List<&1, C.Named>, st: List<&1, C.Named> & U32) -> List<&1, C.Named> & U32:
  match cols:
    case Nil{}:
      st
    case C.Named{n, c} <> rest:
      Fw.go(rest, Fw.step(n, c, st))

def Fw.fin(+h: U32, r: List<&1, C.Named> & U32) -> C.Frame & U32:
  (acc, x) = r
  (C.Frame{h, List.reverse(&1, C.Named, acc)}, x)

# every cell of the frame read once; the frame comes back with a checksum of the walk
def Fw.force(f: C.Frame) -> C.Frame & U32:
  match f:
    case C.Frame{+h, cols}:
      Fw.fin(h, Fw.go(cols, (Nil{}, 0)))

# ===== shim: content hash (Hc) ================================================================
# An order-sensitive FNV-1a over the LOGICAL content of a frame, independent of the physical
# representation: per column the name, a dtype tag, the length, the validity (an all-ones mask
# hashes like AllValid), the payload with every null slot reset to a constant (so garbage under
# nulls does not count), F32 as bits with every NaN canonical (the documented NaN-payload
# relaxation), strings by their text (a Dictionary column hashes the same as the Raw one).
# CONSUMES the frame (the check is the last use). Defined once here; later engines must produce
# the same value for the same logical frame (frozen expected values are compared with it).

def Hc.mix(+h: U32, +y: U32) -> U32:
  U32.mul(U32.xor(h, y), 16777619)

def Hc.fbits(+x: F32) -> U32:
  Bool.pick(U32, K.Kernel.is_nan(x), 2143289344, F32.bits(x))

def Hc.sh(s: String) -> U32:
  J.Str.hash(s, 0)

def Hc.fu32(+n: U32, a: Array<U32>) -> Array<U32> & U32:
  K.Kernel.fold(~U32, ~U32, ~(h => y => U32.mul(U32.xor(h, y), 16777619)), n, a, 2166136261)

def Hc.ff32(+n: U32, a: Array<F32>) -> Array<F32> & U32:
  K.Kernel.fold(~F32, ~U32, ~(h => x => U32.mul(U32.xor(h, Hc.fbits(x)), 16777619)), n, a, 2166136261)

def Hc.fstr(+n: U32, a: Array<String>) -> Array<String> & U32:
  K.Kernel.fold(~String, ~U32, ~(h => s => U32.mul(U32.xor(h, Hc.sh(s)), 16777619)), n, a, 2166136261)

# validity: (normalised validity, its hash); an all-ones mask is AllValid
def Hc.vn.r(r: Array<U32> & U32) -> C.Valid & U32:
  (m, hv) = r
  (C.Mask{m}, hv)

def Hc.vn.q(+full: Bool, +n: U32, m: Array<U32>) -> C.Valid & U32:
  match full:
    case True{}:
      (C.AllValid{}, 0)
    case False{}:
      Hc.vn.r(Hc.fu32(n, m))

def Hc.vn.p(+n: U32, r: Array<U32> & U32) -> C.Valid & U32:
  (m, +cnt) = r
  Hc.vn.q(U32.is_eq(cnt, n), n, m)

def Hc.vn(+n: U32, v: C.Valid) -> C.Valid & U32:
  match v:
    case C.AllValid{}:
      (C.AllValid{}, 0)
    case C.Mask{m}:
      Hc.vn.p(n, K.Kernel.popcount(n, m))

# header hash of a column: tag, length, validity
def Hc.head(+tag: U32, +n: U32, +hv: U32) -> U32:
  Hc.mix(Hc.mix(Hc.mix(2166136261, tag), n), hv)

def Hc.d(+h0: U32, r: Array<U32> & U32) -> U32:
  (a, +hp) = r
  Hc.mix(h0, hp)

def Hc.df(+h0: U32, r: Array<F32> & U32) -> U32:
  (a, +hp) = r
  Hc.mix(h0, hp)

def Hc.ds(+h0: U32, r: Array<String> & U32) -> U32:
  (a, +hp) = r
  Hc.mix(h0, hp)

# --- U32 / Bool / I32 words
def Hc.u32.m(+n: U32, +h0: U32, r: Array<U32> & Array<U32>) -> U32:
  (a, m) = r
  Hc.d(h0, Hc.fu32(n, a))

def Hc.u32.v(+n: U32, +h0: U32, v: C.Valid, a: Array<U32>) -> U32:
  match v:
    case C.AllValid{}:
      Hc.d(h0, Hc.fu32(n, a))
    case C.Mask{m}:
      Hc.u32.m(n, h0, K.Kernel.mask_data(~U32, n, a, m, 0))

def Hc.u32.a(+tag: U32, +n: U32, a: Array<U32>, vv: C.Valid & U32) -> U32:
  (v, +hv) = vv
  Hc.u32.v(n, Hc.head(tag, n, hv), v, a)

# --- F32
def Hc.f32.m(+n: U32, +h0: U32, r: Array<F32> & Array<U32>) -> U32:
  (a, m) = r
  Hc.df(h0, Hc.ff32(n, a))

def Hc.f32.v(+n: U32, +h0: U32, v: C.Valid, a: Array<F32>) -> U32:
  match v:
    case C.AllValid{}:
      Hc.df(h0, Hc.ff32(n, a))
    case C.Mask{m}:
      Hc.f32.m(n, h0, K.Kernel.mask_data(~F32, n, a, m, 0.0))

def Hc.f32.a(+n: U32, a: Array<F32>, vv: C.Valid & U32) -> U32:
  (v, +hv) = vv
  Hc.f32.v(n, Hc.head(4, n, hv), v, a)

# --- Raw strings
def Hc.raw.m(+n: U32, +h0: U32, r: Array<String> & Array<U32>) -> U32:
  (a, m) = r
  Hc.ds(h0, Hc.fstr(n, a))

def Hc.raw.v(+n: U32, +h0: U32, v: C.Valid, a: Array<String>) -> U32:
  match v:
    case C.AllValid{}:
      Hc.ds(h0, Hc.fstr(n, a))
    case C.Mask{m}:
      Hc.raw.m(n, h0, K.Kernel.mask_data(~String, n, a, m, ""))

# --- Dictionary strings: the hash of every entry once, gathered per row
def Hc.dict.tab(+k: U32, +dd: Nat, strs: Array<String>) -> Array<U32>:
  K.Kernel.map(~String, ~U32, ~(s => Hc.sh(s)), k, dd, strs, 0)

def Hc.gat(r: Array<U32> & Array<U32>) -> Array<U32>:
  (a, b) = r
  a

def Hc.dict.row(+n: U32, +d: Nat, tab: Array<U32>, codes: Array<U32>) -> Array<U32>:
  Hc.gat(K.Kernel.gather(~U32, n, d, tab, codes, 0))

# valid rows: gather, then null rows reset to 0 again
def Hc.dict.m2(+n: U32, +h0: U32, r: Array<U32> & Array<U32>) -> U32:
  (a, m) = r
  Hc.d(h0, Hc.fu32(n, a))

def Hc.dict.m1(+n: U32, +d: Nat, +h0: U32, tab: Array<U32>, r: Array<U32> & Array<U32>) -> U32:
  (codes, m) = r
  Hc.dict.m2(n, h0, K.Kernel.mask_data(~U32, n, Hc.dict.row(n, d, tab, codes), m, 0))

def Hc.dict.v(+n: U32, +d: Nat, +h0: U32, v: C.Valid, tab: Array<U32>, codes: Array<U32>) -> U32:
  match v:
    case C.AllValid{}:
      Hc.d(h0, Hc.fu32(n, Hc.dict.row(n, d, tab, codes)))
    case C.Mask{m}:
      Hc.dict.m1(n, d, h0, tab, K.Kernel.mask_data(~U32, n, codes, m, 0))

def Hc.dict.go(+n: U32, +d: Nat, +h0: U32, v: C.Valid, codes: Array<U32>, dict: ST.Dict) -> U32:
  match dict:
    case ST.Dict{+k, +dd, strs, b, slots, tag}:
      Hc.dict.v(n, d, h0, v, Hc.dict.tab(k, dd, strs), codes)

def Hc.str.v(+n: U32, +d: Nat, +h0: U32, v: C.Valid, x: ST.Strs) -> U32:
  match x:
    case ST.SRaw{a}:
      Hc.raw.v(n, h0, v, a)
    case ST.SDict{codes, dict}:
      Hc.dict.go(n, d, h0, v, codes, dict)

def Hc.str.a(+n: U32, +d: Nat, x: ST.Strs, vv: C.Valid & U32) -> U32:
  (v, +hv) = vv
  Hc.str.v(n, d, Hc.head(5, n, hv), v, x)

def Hc.col(c: C.Column) -> U32:
  match c:
    case C.CBool{+n, d, v, x}:
      Hc.u32.a(1, n, x, Hc.vn(n, v))
    case C.CU32{+n, d, v, x}:
      Hc.u32.a(2, n, x, Hc.vn(n, v))
    case C.CI32{+n, d, v, x}:
      Hc.u32.a(3, n, x, Hc.vn(n, v))
    case C.CF32{+n, d, v, x}:
      Hc.f32.a(n, x, Hc.vn(n, v))
    case C.CStr{+n, d, v, x}:
      Hc.str.a(n, d, x, Hc.vn(n, v))

def Hc.step(+acc: U32, n: String, c: C.Column) -> U32:
  Hc.mix(Hc.mix(acc, Hc.sh(n)), Hc.col(c))

def Hc.cols(cols: List<&1, C.Named>, +acc: U32) -> U32:
  match cols:
    case Nil{}:
      acc
    case C.Named{n, c} <> t:
      Hc.cols(t, Hc.step(acc, n, c))

def Hc.frame(f: C.Frame) -> U32:
  match f:
    case C.Frame{+h, cols}:
      Hc.cols(cols, Hc.mix(2166136261, h))

# ===== the check: (content hash, dump hash for small results, rows) ===========================

type Chk is Data:
  Chk{h: U32, d: U32, hd: U32, rows: U32, err: String}

# a result of at most this many rows is also hashed through DF.dump_frame (the typed oracle text,
# no src/ internals): an independent second witness for the small results
def Chk.small() -> U32:
  2000

def Chk.pair(+h: U32, r: C.Frame & C.Frame) -> Chk:
  (a, b) = r
  Chk{Hc.frame(a), J.Str.hash(DF.dump_frame(b), 0), 1, h, ""}

def Chk.fk(+small: Bool, +h: U32, f: C.Frame) -> Chk:
  match small:
    case True{}:
      Chk.pair(h, DF.clone(f))
    case False{}:
      Chk{Hc.frame(f), 0, 0, h, ""}

def Chk.fr(r: C.Frame & U32) -> Chk:
  (f, +h) = r
  Chk.fk(U32.is_le(h, Chk.small()), h, f)

def Chk.res(r: E.ResT(C.Frame)) -> Chk:
  match r:
    case Fail{e}:
      Chk{0, 0, 0, 0, E.Err.show(e)}
    case Done{f}:
      Chk.fr(C.Frame.height(f))

# the first result of a job list (the rest are the kept inputs and further batch results)
def Chk.first(rs: List<&1, E.ResT(C.Frame)>) -> Chk:
  match rs:
    case Nil{}:
      Chk{0, 0, 0, 0, "no result"}
    case r <> t:
      Chk.res(r)

# ===== inputs ==================================================================================

type In is Type:
  In{s: C.Frame, p: C.Frame, ks: C.Frame, kp: C.Frame}

def rd.j2(s: C.Frame, rp: E.ResT(C.Frame)) -> E.ResT(In):
  match rp:
    case Fail{e}:
      Fail{e}
    case Done{p}:
      Done{In{s, p, C.Frame.empty(), C.Frame.empty()}}

def rd.j(rs: E.ResT(C.Frame), rp: E.ResT(C.Frame)) -> E.ResT(In):
  match rs:
    case Fail{e}:
      Fail{e}
    case Done{s}:
      rd.j2(s, rp)

def rd.aux.k(+none: Bool, +ppath: String) -> IO(E.ResT(C.Frame)):
  match none:
    case True{}:
      IO.pure(E.ResT(C.Frame), Done{C.Frame.empty()})
    case False{}:
      EN.Eng.read_csv(ppath)

# aux "-": no second file (an empty frame)
def rd.aux(+ppath: String) -> IO(E.ResT(C.Frame)):
  rd.aux.k(String.eq(ppath, "-"), ppath)

def rd.one(+path: String, +ppath: String) -> IO(E.ResT(In)):
  do IO<E.ResT(In)>:
    rs : E.ResT(C.Frame) <- EN.Eng.read_csv(path)
    rp : E.ResT(C.Frame) <- rd.aux(ppath)
    return rd.j(rs, rp)

def rd.push.a(i: In, acc: E.ResT(List<&1, In>)) -> E.ResT(List<&1, In>):
  match acc:
    case Fail{e}:
      Fail{e}
    case Done{rest}:
      Done{i <> rest}

def rd.push(r: E.ResT(In), acc: E.ResT(List<&1, In>)) -> E.ResT(List<&1, In>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{i}:
      rd.push.a(i, acc)

# m inputs, each read on its own
def rd.many(+m: Nat, +path: String, +ppath: String, acc: E.ResT(List<&1, In>)) -> IO(E.ResT(List<&1, In>)):
  match m:
    case 0n:
      IO.pure(E.ResT(List<&1, In>), acc)
    case 1n+k:
      do IO<E.ResT(List<&1, In>)>:
        r : E.ResT(In) <- rd.one(path, ppath)
        rd.many(k, path, ppath, rd.push(r, acc))

# --- the walk (untimed in e2e: the parse phase of `phases` = read + this walk)

def wk.one.a(ks: C.Frame, kp: C.Frame, rs: C.Frame & U32, rp: C.Frame & U32) -> In & U32:
  (s, +x) = rs
  (p, +y) = rp
  (In{s, p, ks, kp}, U32.add(x, y))

def wk.one(i: In) -> In & U32:
  match i:
    case In{s, p, ks, kp}:
      wk.one.a(ks, kp, Fw.force(s), Fw.force(p))

def wk.all.c(r1: In & U32, r2: List<&1, In> & U32) -> List<&1, In> & U32:
  (i, +x) = r1
  (t, +y) = r2
  (i <> t, U32.add(x, y))

def wk.all(ins: List<&1, In>) -> List<&1, In> & U32:
  match ins:
    case Nil{}:
      (Nil{}, 0)
    case i <> t:
      wk.all.c(wk.one(i), wk.all(t))

# --- the input-preservation clone: the run goes over a clone, the originals stay in ks/kp

def pr.one.a(r1: C.Frame & C.Frame, r2: C.Frame & C.Frame) -> In:
  (s2, ks) = r1
  (p2, kp) = r2
  In{s2, p2, ks, kp}

def pr.one(i: In) -> In:
  match i:
    case In{s, p, ks, kp}:
      pr.one.a(DF.clone(s), DF.clone(p))

def pr.all.b(i: In, t: List<&1, In>) -> List<&1, In>:
  i <> t

def pr.all(ins: List<&1, In>) -> List<&1, In>:
  match ins:
    case Nil{}:
      Nil{}
    case i <> t:
      pr.all.b(pr.one(i), pr.all(t))


# ===== the plans (bench/queries.bend; GroupBy keeps maintain_order False like the baseline runs) ===

def Pl.revenue() -> X.Expr:
  DF.mul(DF.mul(DF.cast_f32(DF.col("qty")), DF.col("price")), DF.sub(DF.lit_f32(1.0), DF.fill_null(DF.col("discount"), DF.lit_f32(0.0))))

def Pl.q1(+s: P.Plan) -> P.Plan:
  DF.lazy_select(DF.lazy_filter(s, DF.and(DF.col("ok"), DF.gt(DF.col("qty"), DF.lit_u32(50)))), [DF.col("id"), DF.col("region"), DF.col("price")])

def Pl.q2(+s: P.Plan) -> P.Plan:
  DF.lazy_with_columns(s, [DF.alias(Pl.revenue(), "revenue")])

def Pl.q3(+s: P.Plan) -> P.Plan:
  DF.lazy_sort(P.GroupBy{[DF.col("region")], [DF.alias(DF.sum(DF.col("revenue")), "revenue_sum"), DF.alias(DF.mean(DF.col("price")), "price_mean"), DF.alias(DF.len(), "count"), DF.alias(DF.max(DF.col("qty")), "qty_max")], False{}, Pl.q2(s)}, [DF.asc("region")])

def Pl.q4(+s: P.Plan) -> P.Plan:
  DF.lazy_head(DF.lazy_sort(s, [DF.asc("region"), DF.desc("price"), DF.asc("id")]), 10)

def Pl.q5(+s: P.Plan, +p: P.Plan) -> P.Plan:
  DF.lazy_sort(P.GroupBy{[DF.col("category")], [DF.alias(DF.sum(DF.col("qty")), "qty_sum")], False{}, DF.lazy_inner_join(s, p, ["product"], ["product"])}, [DF.asc("category")])

def Pl.nunique(+s: P.Plan) -> P.Plan:
  DF.lazy_select(s, [DF.alias(DF.n_unique(DF.col("x")), "n")])

def Pl.group(+s: P.Plan) -> P.Plan:
  P.GroupBy{[DF.col("k")], [DF.alias(DF.sum(DF.col("v")), "vs"), DF.alias(DF.len(), "n")], False{}, s}

def Pl.unique(+s: P.Plan) -> P.Plan:
  DF.lazy_unique(DF.lazy_select(s, [DF.col("k")]), ["k"])

def Pl.join(+s: P.Plan, +p: P.Plan) -> P.Plan:
  DF.lazy_inner_join(s, p, ["k"], ["k"])

# filter: a numeric predicate with a chosen selectivity (qty is uniform on 1..100)
def Pl.filter(+par: U32, +s: P.Plan) -> P.Plan:
  DF.lazy_filter(s, DF.gt(DF.col("qty"), DF.lit_u32(par)))

def Pl.of(+op: String, +par: U32, +s: P.Plan, +p: P.Plan) -> P.Plan:
  Bool.pick(P.Plan, String.eq(op, "q1"), Pl.q1(s),
  Bool.pick(P.Plan, String.eq(op, "q2"), Pl.q2(s),
  Bool.pick(P.Plan, String.eq(op, "q3"), Pl.q3(s),
  Bool.pick(P.Plan, String.eq(op, "q4"), Pl.q4(s),
  Bool.pick(P.Plan, String.eq(op, "q5"), Pl.q5(s, p),
  Bool.pick(P.Plan, String.eq(op, "nunique"), Pl.nunique(s),
  Bool.pick(P.Plan, String.eq(op, "group"), Pl.group(s),
  Bool.pick(P.Plan, String.eq(op, "unique"), Pl.unique(s),
  Bool.pick(P.Plan, String.eq(op, "join"), Pl.join(s, p), Pl.filter(par, s))))))))))

# sales.select(id, qty, price, discount).describe(): eager, as bench/queries.bend Q.q6
def Pl.q6(f: C.Frame) -> E.ResT(C.Frame):
  DF.describe(C.Frame.select_names(f, ["id", "qty", "price", "discount"]))

# ===== the job: one compute over one input =====================================================

def job.b(+op: String, +par: U32, s: P.Plan, r: P.Env & P.Plan) -> IO(E.ResT(C.Frame)):
  (env, +p) = r
  DF.collect(Pl.of(op, par, s, p), env)

def job.a(+op: String, +par: U32, r: P.Env & P.Plan, p: C.Frame) -> IO(E.ResT(C.Frame)):
  (env, +s) = r
  job.b(op, par, s, DF.add_source(env, "products", p))

# op parse: no query, the parsed sales frame is the result (the check hashes it)
def job.k3(+kind: U32, +op: String, +par: U32, s: C.Frame, p: C.Frame) -> IO(E.ResT(C.Frame)):
  match kind:
    case 0:
      job.a(op, par, DF.source("sales", s), p)
    case 1:
      IO.pure(E.ResT(C.Frame), Pl.q6(s))
    case _:
      IO.pure(E.ResT(C.Frame), Done{s})

def job.kind(+op: String) -> U32:
  Bool.pick(U32, String.eq(op, "q6"), 1, Bool.pick(U32, String.eq(op, "parse"), 2, 0))

def job.w(r: E.ResT(C.Frame), ks: C.Frame, kp: C.Frame) -> List<&1, E.ResT(C.Frame)>:
  r <> Done{ks} <> Done{kp} <> Nil{}

# the result, then the kept inputs (alive past the clock)
def job.i(r: E.ResT(C.Frame), ks: C.Frame, kp: C.Frame) -> IO(List<&1, E.ResT(C.Frame)>):
  IO.pure(List<&1, E.ResT(C.Frame)>, job.w(r, ks, kp))

def job(+op: String, +par: U32, i: In) -> IO(List<&1, E.ResT(C.Frame)>):
  match i:
    case In{s, p, ks, kp}:
      do IO<List<&1, E.ResT(C.Frame)>>:
        r : E.ResT(C.Frame) <- job.k3(job.kind(op), op, par, s, p)
        job.i(r, ks, kp)

def cat(xs: List<&1, E.ResT(C.Frame)>, ys: List<&1, E.ResT(C.Frame)>) -> List<&1, E.ResT(C.Frame)>:
  match xs:
    case Nil{}:
      ys
    case x <> t:
      x <> cat(t, ys)

def run.all(ins: List<&1, In>, +op: String, +par: U32, acc: List<&1, E.ResT(C.Frame)>) -> IO(List<&1, E.ResT(C.Frame)>):
  match ins:
    case Nil{}:
      IO.pure(List<&1, E.ResT(C.Frame)>, acc)
    case i <> t:
      do IO<List<&1, E.ResT(C.Frame)>>:
        r : List<&1, E.ResT(C.Frame)> <- job(op, par, i)
        run.all(t, op, par, cat(r, acc))

# write the first result as CSV (floats at 4 decimals); the frame comes back in the list
def wr.first(+outp: String, rs: List<&1, E.ResT(C.Frame)>) -> IO(List<&1, E.ResT(C.Frame)>):
  match rs:
    case Nil{}:
      IO.pure(List<&1, E.ResT(C.Frame)>, Nil{})
    case r <> t:
      do IO<List<&1, E.ResT(C.Frame)>>:
        r2 : E.ResT(C.Frame) <- DF.write_csv_opts(r, outp, DF.write_opts(',', True{}, Some{4}))
        return r2 <> t

# ===== output ====================================================================================

def Js.kv(+k: String, +v: Nat) -> String:
  ",\"" ++ k ++ "\":" ++ Nat.show(v)

def Js.head(+op: String, +mode: String, +m: Nat) -> String:
  "{\"op\":\"" ++ op ++ "\",\"mode\":\"" ++ mode ++ "\"" ++ Js.kv("batch", m)

def Js.fin.k(+err: String, +line: String) -> String:
  Bool.pick(String, String.is_empty(err), line, "error: " ++ err)

def Js.fin.c(+h: U32, +d: U32, +hd: U32, +rows: U32, +err: String, +pre: String) -> String:
  Js.fin.k(err, pre ++ ",\"chk\":" ++ U32.show(h) ++ ",\"dump\":" ++ U32.show(d) ++ ",\"has_dump\":" ++ U32.show(hd) ++ ",\"rows\":" ++ U32.show(rows) ++ "}")

def Js.fin(c: Chk, +pre: String) -> String:
  match c:
    case Chk{h, d, hd, rows, err}:
      Js.fin.c(h, d, hd, rows, err, pre)

# ===== modes =====================================================================================

def Run.ph.b(+op: String, +par: U32, +m: Nat, +t0: Nat, +t1: Nat, w: List<&1, In> & U32) -> IO(Unit):
  (ins, +wc) = w
  do IO<Unit>:
    +t2 : Nat <- IO.now()
    ins2 : List<&1, In> <- IO.pure(List<&1, In>, pr.all(ins))
    +t3 : Nat <- IO.now()
    rs : List<&1, E.ResT(C.Frame)> <- run.all(ins2, op, par, Nil{})
    +t4 : Nat <- IO.now()
    c : Chk <- IO.pure(Chk, Chk.first(rs))
    +t5 : Nat <- IO.now()
    IO.print(Js.fin(c, Js.head(op, "phases", m) ++ Js.kv("read_ms", Nat.sub(t1, t0)) ++ Js.kv("walk_ms", Nat.sub(t2, t1)) ++ Js.kv("parse_ms", Nat.sub(t2, t0)) ++ Js.kv("prep_ms", Nat.sub(t3, t2)) ++ Js.kv("compute_ms", Nat.sub(t4, t3)) ++ Js.kv("check_ms", Nat.sub(t5, t4)) ++ ",\"walk\":" ++ U32.show(wc)))

def Run.ph.a(+op: String, +par: U32, +m: Nat, +t0: Nat, +t1: Nat, r: E.ResT(List<&1, In>)) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("error: " ++ E.Err.show(e))
    case Done{ins}:
      Run.ph.b(op, par, m, t0, t1, wk.all(ins))

def Run.phases(+op: String, +par: U32, +m: Nat, +path: String, +ppath: String) -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    r : E.ResT(List<&1, In>) <- rd.many(m, path, ppath, Done{Nil{}})
    +t1 : Nat <- IO.now()
    Run.ph.a(op, par, m, t0, t1, r)

# e2e (hash output): read + compute + content hash in one region, consuming
def Run.e2e.h(+op: String, +par: U32, +m: Nat, +t0: Nat, ins: List<&1, In>) -> IO(Unit):
  do IO<Unit>:
    rs : List<&1, E.ResT(C.Frame)> <- run.all(ins, op, par, Nil{})
    c : Chk <- IO.pure(Chk, Chk.first(rs))
    +t1 : Nat <- IO.now()
    IO.print(Js.fin(c, Js.head(op, "e2e", m) ++ Js.kv("e2e_ms", Nat.sub(t1, t0))))

# e2ecsv: read + compute + write_csv in one region; the hash is taken after the clock
def Run.e2e.c(+op: String, +par: U32, +m: Nat, +outp: String, +t0: Nat, ins: List<&1, In>) -> IO(Unit):
  do IO<Unit>:
    rs : List<&1, E.ResT(C.Frame)> <- run.all(ins, op, par, Nil{})
    rs2 : List<&1, E.ResT(C.Frame)> <- wr.first(outp, rs)
    +t1 : Nat <- IO.now()
    c : Chk <- IO.pure(Chk, Chk.first(rs2))
    IO.print(Js.fin(c, Js.head(op, "e2ecsv", m) ++ Js.kv("e2e_ms", Nat.sub(t1, t0))))

def Run.e2e.k(+csv: Bool, +op: String, +par: U32, +m: Nat, +outp: String, +t0: Nat, ins: List<&1, In>) -> IO(Unit):
  match csv:
    case True{}:
      Run.e2e.c(op, par, m, outp, t0, ins)
    case False{}:
      Run.e2e.h(op, par, m, t0, ins)

def Run.e2e.a(+csv: Bool, +op: String, +par: U32, +m: Nat, +outp: String, +t0: Nat, r: E.ResT(List<&1, In>)) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("error: " ++ E.Err.show(e))
    case Done{ins}:
      Run.e2e.k(csv, op, par, m, outp, t0, ins)

def Run.e2e(+csv: Bool, +op: String, +par: U32, +m: Nat, +path: String, +ppath: String, +outp: String) -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    r : E.ResT(List<&1, In>) <- rd.many(m, path, ppath, Done{Nil{}})
    Run.e2e.a(csv, op, par, m, outp, t0, r)

# ===== stages: each eager stage of q1..q6 timed on its own (mode `stages`) =======================
# One parse (read + walk), then 11 stages in sequence, each over fresh clones of the inputs (or the
# previous stage's output, which the next stage consumes): filter_q1, select_q1, withcols_q2,
# groupby_q3, sort_q3, sort_q4, head_q4, join_q5, groupby_q5, sort_q5, describe_q6. The eager verbs
# (DF.filter, DF.select, ...) run the stage alone, WITHOUT the optimizer's pushdown/fusion, so the
# stage times are a diagnostic of where the time goes, not a decomposition of the lazy q-times.
# Clones, the per-stage hash and the bookkeeping sit outside each stage's clock. ms is the stage
# itself (IO.now has 1 ms resolution); rows and chk are of the stage's result.

def Stg.name(+k: U32) -> String:
  match k:
    case 0:
      "filter_q1"
    case 1:
      "select_q1"
    case 2:
      "withcols_q2"
    case 3:
      "groupby_q3"
    case 4:
      "sort_q3"
    case 5:
      "sort_q4"
    case 6:
      "head_q4"
    case 7:
      "join_q5"
    case 8:
      "groupby_q5"
    case 9:
      "sort_q5"
    case _:
      "describe_q6"

# stages 1, 3, 4, 6, 8, 9 take the previous stage's output; the others a clone of the sales frame
def Stg.uses_last(+k: U32) -> Bool:
  match k:
    case 1:
      True{}
    case 3:
      True{}
    case 4:
      True{}
    case 6:
      True{}
    case 8:
      True{}
    case 9:
      True{}
    case _:
      False{}

def Stg.op(+k: U32, a: C.Frame, b: C.Frame) -> E.ResT(C.Frame):
  match k:
    case 0:
      DF.filter(a, DF.and(DF.col("ok"), DF.gt(DF.col("qty"), DF.lit_u32(50))))
    case 1:
      DF.select(a, [DF.col("id"), DF.col("region"), DF.col("price")])
    case 2:
      DF.with_columns(a, [DF.alias(Pl.revenue(), "revenue")])
    case 3:
      DF.group_by(a, [DF.col("region")], [DF.alias(DF.sum(DF.col("revenue")), "revenue_sum"), DF.alias(DF.mean(DF.col("price")), "price_mean"), DF.alias(DF.len(), "count"), DF.alias(DF.max(DF.col("qty")), "qty_max")])
    case 4:
      DF.sort(a, [DF.asc("region")])
    case 5:
      DF.sort(a, [DF.asc("region"), DF.desc("price"), DF.asc("id")])
    case 6:
      DF.head(a, 10)
    case 7:
      DF.inner_join(a, b, ["product"], ["product"])
    case 8:
      DF.group_by(a, [DF.col("category")], [DF.alias(DF.sum(DF.col("qty")), "qty_sum")])
    case 9:
      DF.sort(a, [DF.asc("category")])
    case _:
      Pl.q6(a)

# a failed stage becomes an empty frame (rows 0 / a different chk: the runner flags it)
def Stg.un(x: E.ResT(C.Frame)) -> C.Frame:
  match x:
    case Fail{e}:
      C.Frame.empty()
    case Done{f}:
      f

# (the frame, its record): rows and a content hash taken on a clone (outside the clock)
def Stg.rec.b(+name: String, +ms: Nat, +h: U32, +rows: U32, f: C.Frame) -> C.Frame & String:
  (f, ",\"" ++ name ++ "_ms\":" ++ Nat.show(ms) ++ ",\"" ++ name ++ "_rows\":" ++ U32.show(rows) ++ ",\"" ++ name ++ "_chk\":" ++ U32.show(h))

def Stg.rec.a(+name: String, +ms: Nat, f: C.Frame, r: C.Frame & U32) -> C.Frame & String:
  (c, +rows) = r
  Stg.rec.b(name, ms, Hc.frame(c), rows, f)

def Stg.rec.k(+name: String, +ms: Nat, r: C.Frame & C.Frame) -> C.Frame & String:
  (f, c) = r
  Stg.rec.a(name, ms, f, C.Frame.height(c))

def Stg.rec(+name: String, +ms: Nat, f: C.Frame) -> C.Frame & String:
  Stg.rec.k(name, ms, DF.clone(f))

# the loop state: the JSON so far, the sales and products frames, the last stage's output
type W is Type:
  W{j: String, s: C.Frame, p: C.Frame, f: C.Frame}

def Stg.next(+j: String, s: C.Frame, p: C.Frame, r: C.Frame & String) -> W:
  (f, +line) = r
  W{j ++ line, s, p, f}

def Stg.go(+k: U32, +j: String, s: C.Frame, pp: C.Frame & C.Frame, a: C.Frame) -> IO(W):
  (b, p2) = pp
  do IO<W>:
    +t0 : Nat <- IO.now()
    x : E.ResT(C.Frame) <- IO.pure(E.ResT(C.Frame), Stg.op(k, a, b))
    +t1 : Nat <- IO.now()
    return Stg.next(j, s, p2, Stg.rec(Stg.name(k), Nat.sub(t1, t0), Stg.un(x)))

def Stg.go.s(+k: U32, +j: String, pp: C.Frame & C.Frame, rs: C.Frame & C.Frame) -> IO(W):
  (a, s2) = rs
  Stg.go(k, j, s2, pp, a)

def Stg.pick(+k: U32, +j: String, s: C.Frame, p: C.Frame, last: C.Frame, +ul: Bool) -> IO(W):
  match ul:
    case True{}:
      Stg.go(k, j, s, DF.clone(p), last)
    case False{}:
      Stg.go.s(k, j, DF.clone(p), DF.clone(s))

def Stg.stage(+k: U32, w: W) -> IO(W):
  match w:
    case W{j, s, p, f}:
      Stg.pick(k, j, s, p, f, Stg.uses_last(k))

def Stg.fin(w: W) -> IO(Unit):
  match w:
    case W{j, s, p, f}:
      IO.print(j ++ "}")

def Stg.loop(left: Nat, +k: U32, w: W) -> IO(Unit):
  match left:
    case 0n:
      Stg.fin(w)
    case 1n+r:
      do IO<Unit>:
        w2 : W <- Stg.stage(k, w)
        Stg.loop(r, U32.add(k, 1), w2)

def Stg.start.k(+t0: Nat, +t1: Nat, +t2: Nat, +wc: U32, ins: List<&1, In>) -> IO(Unit):
  match ins:
    case Nil{}:
      IO.print("error: no input")
    case In{s, p, ks, kp} <> t:
      Stg.loop(11n, 0, W{"{\"op\":\"stages\",\"mode\":\"stages\",\"batch\":1" ++ Js.kv("read_ms", Nat.sub(t1, t0)) ++ Js.kv("walk_ms", Nat.sub(t2, t1)) ++ Js.kv("parse_ms", Nat.sub(t2, t0)) ++ ",\"walk\":" ++ U32.show(wc), s, p, C.Frame.empty()})

def Stg.start.w(+t0: Nat, +t1: Nat, w: List<&1, In> & U32) -> IO(Unit):
  (ins, +wc) = w
  do IO<Unit>:
    +t2 : Nat <- IO.now()
    Stg.start.k(t0, t1, t2, wc, ins)

def Stg.start.r(+t0: Nat, +t1: Nat, r: E.ResT(List<&1, In>)) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("error: " ++ E.Err.show(e))
    case Done{ins}:
      Stg.start.w(t0, t1, wk.all(ins))

def Stg.start(+path: String, +ppath: String) -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    r : E.ResT(List<&1, In>) <- rd.many(1n, path, ppath, Done{Nil{}})
    +t1 : Nat <- IO.now()
    Stg.start.r(t0, t1, r)


# ===== selfcheck: the content hash is independent of the string storage ========================
# `selfcheck <op ignored> <file.csv>`: the file read with Raw and with Dictionary strings and with the
# reader's default must hash alike, and so must a clone (a clone whose hash differs reports 1);
# prints {"mode":"selfcheck","raw":..,"dict":..,"auto":..,"clone":..,"eq":1|0}.

def Self.h(r: E.ResT(C.Frame)) -> U32:
  match r:
    case Fail{e}:
      0
    case Done{f}:
      Hc.frame(f)

def Self.cmp(+x: U32, +y: U32) -> U32:
  Bool.pick(U32, U32.is_eq(x, y), x, 1)

def Self.cl(r: C.Frame & C.Frame) -> U32:
  (a, b) = r
  Self.cmp(Hc.frame(a), Hc.frame(b))

def Self.clone(r: E.ResT(C.Frame)) -> U32:
  match r:
    case Fail{e}:
      0
    case Done{f}:
      Self.cl(DF.clone(f))

def Self.eq(+a: U32, +b: U32, +c: U32, +d: U32) -> U32:
  Bool.pick(U32, Bool.and(Bool.and(U32.is_eq(a, b), U32.is_eq(a, c)), U32.is_eq(a, d)), 1, 0)

def Self.fin(+a: U32, +b: U32, +c: U32, +d: U32) -> IO(Unit):
  IO.print("{\"mode\":\"selfcheck\",\"raw\":" ++ U32.show(a) ++ ",\"dict\":" ++ U32.show(b) ++ ",\"auto\":" ++ U32.show(c) ++ ",\"clone\":" ++ U32.show(d) ++ ",\"eq\":" ++ U32.show(Self.eq(a, b, c, d)) ++ "}")

def Self.go(+path: String) -> IO(Unit):
  do IO<Unit>:
    ra : E.ResT(C.Frame) <- DF.read_csv_enc(path, DF.csv_opts(',', True{}, 100), Nil{}, DF.str_raw())
    rb : E.ResT(C.Frame) <- DF.read_csv_enc(path, DF.csv_opts(',', True{}, 100), Nil{}, DF.str_dict())
    rc : E.ResT(C.Frame) <- DF.read_csv(path)
    rd : E.ResT(C.Frame) <- DF.read_csv(path)
    Self.fin(Self.h(ra), Self.h(rb), Self.h(rc), Self.clone(rd))


# ===== args ======================================================================================

def nth(+i: Nat, xs: List<&2, String>, +d: String) -> String:
  match i xs:
    case _ Nil{}:
      d
    case 0n h <> t:
      h
    case 1n+j h <> t:
      nth(j, t, d)

def nat.of(m: Maybe<&2, Nat>, +d: Nat) -> Nat:
  match m:
    case None{}:
      d
    case Some{v}:
      v

def promote(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> promote(t)

def Run.d3(+is_csv: Bool, +mode: String, +op: String, +par: U32, +m: Nat, +path: String, +ppath: String, +outp: String) -> IO(Unit):
  match is_csv:
    case True{}:
      Run.e2e(True{}, op, par, m, path, ppath, outp)
    case False{}:
      IO.print("error: unknown mode " ++ mode)

def Run.d4(+is_stg: Bool, +is_csv: Bool, +mode: String, +op: String, +par: U32, +m: Nat, +path: String, +ppath: String, +outp: String) -> IO(Unit):
  match is_stg:
    case True{}:
      Stg.start(path, ppath)
    case False{}:
      Run.d3(is_csv, mode, op, par, m, path, ppath, outp)

def Run.d5(+is_self: Bool, +is_stg: Bool, +is_csv: Bool, +mode: String, +op: String, +par: U32, +m: Nat, +path: String, +ppath: String, +outp: String) -> IO(Unit):
  match is_self:
    case True{}:
      Self.go(path)
    case False{}:
      Run.d4(is_stg, is_csv, mode, op, par, m, path, ppath, outp)

def Run.d2(+is_e2e: Bool, +mode: String, +op: String, +par: U32, +m: Nat, +path: String, +ppath: String, +outp: String) -> IO(Unit):
  match is_e2e:
    case True{}:
      Run.e2e(False{}, op, par, m, path, ppath, outp)
    case False{}:
      Run.d5(String.eq(mode, "selfcheck"), String.eq(mode, "stages"), String.eq(mode, "e2ecsv"), mode, op, par, m, path, ppath, outp)

def Run.d1(+is_ph: Bool, +mode: String, +op: String, +par: U32, +m: Nat, +path: String, +ppath: String, +outp: String) -> IO(Unit):
  match is_ph:
    case True{}:
      Run.phases(op, par, m, path, ppath)
    case False{}:
      Run.d2(String.eq(mode, "e2e"), mode, op, par, m, path, ppath, outp)

def go(+xs: List<&2, String>) -> IO(Unit):
  Run.d1(String.eq(nth(0n, xs, "phases"), "phases"), nth(0n, xs, "phases"), nth(1n, xs, "q1"), U32.from_nat(nat.of(Nat.read(nth(5n, xs, "0")), 0n)), nat.of(Nat.read(nth(4n, xs, "1")), 1n), nth(2n, xs, "bench/data/sales_1000.csv"), nth(3n, xs, "bench/data/products.csv"), nth(6n, xs, "build/m2/out.csv"))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(List.tail(&2, String, promote(args)))
