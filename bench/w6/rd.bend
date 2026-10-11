# bench/w6/rd.bend -- the TEST-SIDE reader of W6.1 / W6.2: a complete CSV read built from the
# production pieces only, in the shape W6.3 will integrate them:
#
#   header step (here: from the reference parser's records, test-only)
#     -> Pr.regions (src/csvprod.bend) -> Ln.lane per region (src/csvlane.bend), in file order
#     -> combine: malformed, ragged, per column the first bad cell, concatenation, one Dictionary
#        merge per Str column in region order (v0.1's first-appearance codes)
#
# Hr.read(path, hdr, sep, schema, piece, raw) answers what Csv.read_full answers (the frame or
# the first error in the v0.1 order), so tests compare DF.dump of both. NOT production code: it
# is sequential, takes no row cap, no inference, no EncAuto, and its header step uses csvparse.
#
# Idioms: DESIGN 9 (helpers above callers, pairs taken apart in the next helper's parameter).
import Base
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/kernels.bend as K
import ./../../src/column.bend as C
import ./../../src/strs.bend as ST
import ./../../src/csvparse.bend as H
import ./../../src/csv.bend as V
import ./../../src/csvprod.bend as P
import ./../../src/csvlane.bend as L
import ./hx.bend as X

# ---- schema letters -------------------------------------------------------------------------------

# U u32, I i32, F f32, B bool, S str (R: a raw string column, TyR)
def Hr.ty(+c: U32, +raw: Bool) -> L.Ty:
  Bool.pick(L.Ty, U32.is_eq(c, 85), L.TyU{}, Bool.pick(L.Ty, U32.is_eq(c, 73), L.TyI{}, Bool.pick(L.Ty, U32.is_eq(c, 70), L.TyF{}, Bool.pick(L.Ty, U32.is_eq(c, 66), L.TyB{}, Bool.pick(L.Ty, raw, L.TyR{}, L.TyS{})))))

def Hr.tys(s: String, +raw: Bool) -> List<&2, L.Ty>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      Hr.ty(c, raw) <> Hr.tys(t, raw)

def Hr.dt(+c: U32) -> D.DType:
  Bool.pick(D.DType, U32.is_eq(c, 85), D.TU32{}, Bool.pick(D.DType, U32.is_eq(c, 73), D.TI32{}, Bool.pick(D.DType, U32.is_eq(c, 70), D.TF32{}, Bool.pick(D.DType, U32.is_eq(c, 66), D.TBool{}, D.TStr{}))))

def Hr.dts(s: String) -> List<&2, D.DType>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      Hr.dt(c) <> Hr.dts(t)

# ---- the header step (test-only: from the reference parser's records) ---------------------------

# names, width, the offset and physical line the data starts at, the reference accepted the file
type Hd is Data:
  Hd{names: List<&2, String>, w: U32, off0: U32, line0: U32, ok: Bool}

def Hr.blank(r: H.CsvRec) -> Bool:
  match r:
    case H.CsvRec{l, H.CsvCell{t, q} <> Nil{}}:
      Bool.and(String.is_empty(t), Bool.not(q))
    case _:
      False{}

def Hr.width(r: H.CsvRec) -> U32:
  match r:
    case H.CsvRec{l, cs}:
      U32.from_nat(List.length(&2, H.CsvCell, cs))

def Hr.line(r: H.CsvRec) -> U32:
  match r:
    case H.CsvRec{l, cs}:
      l

def Hr.names(r: H.CsvRec) -> List<&2, String>:
  match r:
    case H.CsvRec{l, cs}:
      V.Csv.names(cs)

# the offset of the record starting on `line` (the LF positions lf)
def Hr.off.k(r: List<&2, U32>) -> U32:
  match r:
    case Nil{}:
      0
    case +o <> t:
      o

def Hr.off(+lf: List<&2, U32>, +line: U32) -> U32:
  Hr.off.k(X.Hx.offs(lf, line <> Nil{}))

# the records from the first non-blank one
def Hr.lead.k(blank: Bool, r: H.CsvRec, t: List<&2, H.CsvRec>, rest: List<&2, H.CsvRec>) -> List<&2, H.CsvRec>:
  match blank:
    case True{}:
      rest
    case False{}:
      r <> t

def Hr.lead(rs: List<&2, H.CsvRec>) -> List<&2, H.CsvRec>:
  match rs:
    case Nil{}:
      Nil{}
    case +r <> +t:
      Hr.lead.k(Hr.blank(r), r, t, Hr.lead(t))

# has_header: the first non-blank record holds the names, the data starts at the next record
def Hr.hdr.n(+r: H.CsvRec, next: List<&2, H.CsvRec>, +lf: List<&2, U32>, +size: U32) -> Hd:
  match next:
    case Nil{}:
      Hd{Hr.names(r), Hr.width(r), size, 1, True{}}
    case +n <> u:
      Hd{Hr.names(r), Hr.width(r), Hr.off(lf, Hr.line(n)), Hr.line(n), True{}}

def Hr.hdr(rs: List<&2, H.CsvRec>, lf: List<&2, U32>, +size: U32) -> Hd:
  match rs:
    case Nil{}:
      Hd{Nil{}, 0, size, 1, True{}}
    case r <> t:
      Hr.hdr.n(r, t, lf, size)

# no header: names column_i, the width of the first non-blank record, the data is the file
def Hr.nohdr(rs: List<&2, H.CsvRec>) -> Hd:
  match rs:
    case Nil{}:
      Hd{Nil{}, 0, 0, 1, True{}}
    case +r <> t:
      Hd{V.Csv.gen_names(U32.to_nat(Hr.width(r)), 0n), Hr.width(r), 0, 1, True{}}

def Hr.header.k(hdr: Bool, rs: List<&2, H.CsvRec>, lf: List<&2, U32>, +size: U32) -> Hd:
  match hdr:
    case True{}:
      Hr.hdr(Hr.lead(rs), lf, size)
    case False{}:
      Hr.nohdr(Hr.lead(rs))

# a rejected file: the answer is the malformed error whatever the header says
def Hr.header(hdr: Bool, ans: H.Ans, lf: List<&2, U32>, +size: U32, +k: U32) -> Hd:
  match ans:
    case H.Rejected{}:
      Hd{Nil{}, k, 0, 1, False{}}
    case H.Parsed{rs}:
      Hr.header.k(hdr, rs, lf, size)

# ---- the lanes, in file order -----------------------------------------------------------------------

def Hr.lanes(regs: List<&1, P.Rg>, +ts: List<&2, L.Ty>, +w: U32, +sep: U32) -> List<&1, L.LO>:
  match regs:
    case Nil{}:
      Nil{}
    case rg <> t:
      L.Ln.lane(ts, w, sep, rg) <> Hr.lanes(t, ts, w, sep)

# ---- the summary: rows, rejected, the first ragged record in lane order ------------------------------

def Hr.sel(c: Bool, +a: U32, +b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

type SM is Data:
  SM{n: U32, rej: U32, rag: U32, rgn: U32}

def Hr.sum.add(+n: U32, +rej: U32, +rag: U32, +rgn: U32, s: SM) -> SM:
  match s:
    case SM{+n0, +rj, +rg, +rn}:
      +first = Bool.and(U32.is_ne(rag, 0), U32.is_eq(rg, 0))
      SM{U32.add(n0, n), U32.or(rj, rej), Hr.sel(first, rag, rg), Hr.sel(first, rgn, rn)}

def Hr.sum.one(x: L.LO, st: List<&1, L.LO> & SM) -> List<&1, L.LO> & SM:
  match x:
    case L.LO{+n, +rej, +rag, +rgn, lines, cols}:
      (acc, s) = st
      (L.LO{n, rej, rag, rgn, lines, cols} <> acc, Hr.sum.add(n, rej, rag, rgn, s))

# lanes in order -> (lanes in order, summary)
def Hr.sum(xs: List<&1, L.LO>, st: List<&1, L.LO> & SM) -> List<&1, L.LO> & SM:
  match xs:
    case Nil{}:
      (acc, s) = st
      (List.reverse(&1, L.LO, acc), s)
    case h <> t:
      Hr.sum(t, Hr.sum.one(h, st))

# ---- column c of every lane: parts (rows, the column's part); the lanes keep their other columns ----

def Hr.dummy() -> L.CO:
  L.OW{Array.new(U32, 0n, 0), Array.new(U32, 0n, 0), 0, 0, 0, ""}

def Hr.take.c.k(here: Bool, h: L.CO, r: List<&1, L.CO> & L.CO) -> List<&1, L.CO> & L.CO:
  match here:
    case True{}:
      (t, x) = r
      (Hr.dummy() <> t, h)
    case False{}:
      (t, x) = r
      (h <> t, x)

def Hr.take.c(cols: List<&1, L.CO>, +c: U32) -> List<&1, L.CO> & L.CO:
  match cols:
    case Nil{}:
      (Nil{}, Hr.dummy())
    case h <> t:
      Hr.take.c.k(U32.is_eq(c, 0), h, Hr.take.c(t, U32.sub(c, 1)))

type CP is Type:
  CP{n: U32, co: L.CO}

def Hr.take.k2(+n: U32, +rej: U32, +rag: U32, +rgn: U32, lines: Array<U32>, rest: List<&1, L.LO> & List<&1, CP>, r: List<&1, L.CO> & L.CO) -> List<&1, L.LO> & List<&1, CP>:
  (los, cps) = rest
  (cols, co) = r
  (L.LO{n, rej, rag, rgn, lines, cols} <> los, CP{n, co} <> cps)

def Hr.take.k(+c: U32, x: L.LO, rest: List<&1, L.LO> & List<&1, CP>) -> List<&1, L.LO> & List<&1, CP>:
  match x:
    case L.LO{+n, rej, rag, rgn, lines, cols}:
      Hr.take.k2(n, rej, rag, rgn, lines, rest, Hr.take.c(cols, c))

def Hr.take(+c: U32, xs: List<&1, L.LO>) -> List<&1, L.LO> & List<&1, CP>:
  match xs:
    case Nil{}:
      (Nil{}, Nil{})
    case h <> t:
      Hr.take.k(c, h, Hr.take(c, t))

# ---- concatenating the parts of one column ----------------------------------------------------------------

# the first bad cell (its line and text) is the first part's; word / f32 parts are copied at their
# offsets
type AW is Type:
  AW{off: U32, a: Array<U32>, v: Array<U32>, nulls: U32, bad: U32, bl: U32, bt: String}

type AF is Type:
  AF{off: U32, a: Array<F32>, v: Array<U32>, nulls: U32, bad: U32, bl: U32, bt: String}

# Str: the dictionary so far, the remapped codes; Raw: the strings
type AS is Type:
  AS{off: U32, c: Array<U32>, v: Array<U32>, nulls: U32, dict: ST.Dict}

type AR is Type:
  AR{off: U32, a: Array<String>, v: Array<U32>, nulls: U32}

def Hr.aw.part(+m: U32, co: L.CO, st: AW) -> AW:
  match co st:
    case L.OW{a, v, +nb, +bd, +bl, bt} AW{+off, oa, ov, +nulls, +bad, +obl, obt}:
      +first = Bool.and(U32.is_eq(bad, 0), U32.is_ne(bd, 0))
      AW{U32.add(off, m), K.Kernel.copy_into(~U32, m, off, oa, a), K.Kernel.copy_into(~U32, m, off, ov, v), U32.add(nulls, nb), Hr.sel(first, bd, bad), Hr.sel(first, bl, obl), Bool.pick(String, first, bt, obt)}
    case _ other:
      other

def Hr.af.part(+m: U32, co: L.CO, st: AF) -> AF:
  match co st:
    case L.OF{a, v, +nb, +bd, +bl, bt} AF{+off, oa, ov, +nulls, +bad, +obl, obt}:
      +first = Bool.and(U32.is_eq(bad, 0), U32.is_ne(bd, 0))
      AF{U32.add(off, m), K.Kernel.copy_into(~F32, m, off, oa, a), K.Kernel.copy_into(~U32, m, off, ov, v), U32.add(nulls, nb), Hr.sel(first, bd, bad), Hr.sel(first, bl, obl), Bool.pick(String, first, bt, obt)}
    case _ other:
      other

def Hr.ar.part(+m: U32, co: L.CO, st: AR) -> AR:
  match co st:
    case L.OR{a, v, +nb} AR{+off, oa, ov, +nulls}:
      AR{U32.add(off, m), K.Kernel.copy_into(~String, m, off, oa, a), K.Kernel.copy_into(~U32, m, off, ov, v), U32.add(nulls, nb)}
    case _ other:
      other

# remap[id] = the global code of local entry id (inserted when new: global first-appearance order)
def Hr.rm.one.k(+id: U32, m: Array<U32>, r: ST.Dict & U32) -> ST.Dict & Array<U32>:
  (dict, +code) = r
  (dict, Array.set(U32, m, id, code))

def Hr.rm.one(+id: U32, s: String, st: ST.Dict & Array<U32>) -> ST.Dict & Array<U32>:
  (dict, m) = st
  Hr.rm.one.k(id, m, ST.Dict.code(dict, s))

def Hr.rm.go(f: Nat, +id: U32, st: ST.Dict & Array<U32>, r: Array<String> & String) -> ST.Dict & Array<U32>:
  match f:
    case 0n:
      (ents, s) = r
      st
    case 1n+p:
      (ents, s) = r
      Hr.rm.go(p, U32.inc(id), Hr.rm.one(id, s, st), Array.get(String, ents, U32.inc(id)))

def Hr.rm.fst(r: Array<U32> & Array<U32>) -> Array<U32>:
  (a, b) = r
  a

def Hr.as.fin(+m: U32, +off: U32, +nulls: U32, oc: Array<U32>, ov: Array<U32>, c: Array<U32>, v: Array<U32>, r: ST.Dict & Array<U32>) -> AS:
  (dict, map) = r
  AS{U32.add(off, m), K.Kernel.copy_into(~U32, m, off, oc, Hr.rm.fst(K.Kernel.gather(~U32, m, K.Kernel.depth_for(U32.max(m, 1)), map, c, 0))), K.Kernel.copy_into(~U32, m, off, ov, v), nulls, dict}

def Hr.as.part(+m: U32, co: L.CO, st: AS) -> AS:
  match co st:
    case L.OS{c, v, +nb, +k, ents} AS{+off, oc, ov, +nulls, dict}:
      Hr.as.fin(m, off, U32.add(nulls, nb), oc, ov, c, v, Hr.rm.go(U32.to_nat(k), 0, (dict, Array.new(U32, K.Kernel.depth_for(U32.max(k, 1)), 0)), Array.get(String, ents, 0)))
    case _ other:
      other

def Hr.cat.w(ps: List<&1, CP>, st: AW) -> AW:
  match ps:
    case Nil{}:
      st
    case CP{+m, co} <> t:
      Hr.cat.w(t, Hr.aw.part(m, co, st))

def Hr.cat.f(ps: List<&1, CP>, st: AF) -> AF:
  match ps:
    case Nil{}:
      st
    case CP{+m, co} <> t:
      Hr.cat.f(t, Hr.af.part(m, co, st))

def Hr.cat.s(ps: List<&1, CP>, st: AS) -> AS:
  match ps:
    case Nil{}:
      st
    case CP{+m, co} <> t:
      Hr.cat.s(t, Hr.as.part(m, co, st))

def Hr.cat.r(ps: List<&1, CP>, st: AR) -> AR:
  match ps:
    case Nil{}:
      st
    case CP{+m, co} <> t:
      Hr.cat.r(t, Hr.ar.part(m, co, st))

# ---- a finished column -----------------------------------------------------------------------------------

def Hr.valid(+nulls: U32, v: Array<U32>) -> C.Valid:
  Bool.pick(C.Valid, U32.is_zero(nulls), C.AllValid{}, C.Mask{v})

def Hr.w.fin.k(isbad: Bool, +name: String, +t: D.DType, +n: U32, +d: Nat, +nulls: U32, a: Array<U32>, v: Array<U32>, +bl: U32, +bt: String) -> E.ResT(C.Named):
  match isbad:
    case True{}:
      V.Csv.col.err(name, t, bt, bl)
    case False{}:
      Done{C.Named{name, C.Column.mk_w(t, n, d, Hr.valid(nulls, v), a)}}

def Hr.w.fin(+name: String, +t: D.DType, +n: U32, +d: Nat, st: AW) -> E.ResT(C.Named):
  match st:
    case AW{off, a, v, +nulls, +bad, +bl, bt}:
      Hr.w.fin.k(U32.is_ne(bad, 0), name, t, n, d, nulls, a, v, bl, bt)

def Hr.f.fin.k(isbad: Bool, +name: String, +t: D.DType, +n: U32, +d: Nat, +nulls: U32, a: Array<F32>, v: Array<U32>, +bl: U32, +bt: String) -> E.ResT(C.Named):
  match isbad:
    case True{}:
      V.Csv.col.err(name, t, bt, bl)
    case False{}:
      Done{C.Named{name, C.CF32{n, d, Hr.valid(nulls, v), a}}}

def Hr.f.fin(+name: String, +t: D.DType, +n: U32, +d: Nat, st: AF) -> E.ResT(C.Named):
  match st:
    case AF{off, a, v, +nulls, +bad, +bl, bt}:
      Hr.f.fin.k(U32.is_ne(bad, 0), name, t, n, d, nulls, a, v, bl, bt)

def Hr.s.fin(+name: String, +n: U32, +d: Nat, st: AS) -> E.ResT(C.Named):
  match st:
    case AS{off, c, v, +nulls, dict}:
      Done{C.Named{name, C.CStr{n, d, Hr.valid(nulls, v), ST.SDict{c, dict}}}}

def Hr.r.fin(+name: String, +n: U32, +d: Nat, st: AR) -> E.ResT(C.Named):
  match st:
    case AR{off, a, v, +nulls}:
      Done{C.Named{name, C.CStr{n, d, Hr.valid(nulls, v), ST.SRaw{a}}}}

# one column from its parts
def Hr.col.k(t: L.Ty, +name: String, +dt: D.DType, +n: U32, +d: Nat, ps: List<&1, CP>) -> E.ResT(C.Named):
  match t:
    case L.TyF{}:
      Hr.f.fin(name, dt, n, d, Hr.cat.f(ps, AF{0, Array.new(F32, d, 0.0), Array.new(U32, d, 0), 0, 0, 0, ""}))
    case L.TyS{}:
      Hr.s.fin(name, n, d, Hr.cat.s(ps, AS{0, Array.new(U32, d, 0), Array.new(U32, d, 0), 0, ST.Dict.empty()}))
    case L.TyR{}:
      Hr.r.fin(name, n, d, Hr.cat.r(ps, AR{0, Array.new(String, d, ""), Array.new(U32, d, 0), 0}))
    case _:
      Hr.w.fin(name, dt, n, d, Hr.cat.w(ps, AW{0, Array.new(U32, d, 0), Array.new(U32, d, 0), 0, 0, 0, ""}))

# every column of the frame: its parts from the lanes in order (the lanes keep the other columns);
# the finished columns come out last first
def Hr.cols.k(t: L.Ty, +name: String, +dt: D.DType, +n: U32, +d: Nat, acc: List<&1, E.ResT(C.Named)>, r: List<&1, L.LO> & List<&1, CP>) -> List<&1, L.LO> & List<&1, E.ResT(C.Named)>:
  (los, ps) = r
  (los, Hr.col.k(t, name, dt, n, d, ps) <> acc)

def Hr.cols.step(t: L.Ty, +name: String, +dt: D.DType, +c: U32, +n: U32, +d: Nat, st: List<&1, L.LO> & List<&1, E.ResT(C.Named)>) -> List<&1, L.LO> & List<&1, E.ResT(C.Named)>:
  (los, acc) = st
  Hr.cols.k(t, name, dt, n, d, acc, Hr.take(c, los))

def Hr.cols(ts: List<&2, L.Ty>, dts: List<&2, D.DType>, names: List<&2, String>, +c: U32, +n: U32, +d: Nat, st: List<&1, L.LO> & List<&1, E.ResT(C.Named)>) -> List<&1, L.LO> & List<&1, E.ResT(C.Named)>:
  match ts dts names:
    case t <> tt dt <> dtt nm <> nmt:
      Hr.cols(tt, dtt, nmt, U32.inc(c), n, d, Hr.cols.step(t, nm, dt, c, n, d, st))
    case _ _ _:
      st

# the first column (in order) holding an error wins
def Hr.fold(rs: List<&1, E.ResT(C.Named)>, acc: E.ResT(List<&1, C.Named>)) -> E.ResT(List<&1, C.Named>):
  match rs:
    case Nil{}:
      acc
    case r <> t:
      Hr.fold(t, V.Csv.cols.k(r, acc))

def Hr.build.k(r: List<&1, L.LO> & List<&1, E.ResT(C.Named)>) -> E.ResT(C.Frame):
  (los, cols) = r
  V.Csv.fin(Hr.fold(cols, Done{Nil{}}))

def Hr.build(ts: List<&2, L.Ty>, dts: List<&2, D.DType>, names: List<&2, String>, +n: U32, los: List<&1, L.LO>) -> E.ResT(C.Frame):
  Hr.build.k(Hr.cols(ts, dts, names, 0, n, K.Kernel.depth_for(U32.max(n, 1)), (los, Nil{})))

# malformed quoting first, then the first ragged record, then the columns
def Hr.comb.r(rag: Bool, +w: U32, +rg: U32, +line: U32, +n: U32, ts: List<&2, L.Ty>, dts: List<&2, D.DType>, names: List<&2, String>, los: List<&1, L.LO>) -> E.ResT(C.Frame):
  match rag:
    case True{}:
      Fail{E.ParseError{line, "expected " ++ U32.show(w) ++ " fields, got " ++ U32.show(rg)}}
    case False{}:
      Hr.build(ts, dts, names, n, los)

def Hr.comb.m(rej: Bool, +w: U32, +rag: U32, +rg: U32, +n: U32, ts: List<&2, L.Ty>, dts: List<&2, D.DType>, names: List<&2, String>, los: List<&1, L.LO>) -> E.ResT(C.Frame):
  match rej:
    case True{}:
      Fail{V.Csv.malformed()}
    case False{}:
      Hr.comb.r(U32.is_ne(rag, 0), w, rg, rag, n, ts, dts, names, los)

def Hr.comb.k(sm: SM, +w: U32, ts: List<&2, L.Ty>, dts: List<&2, D.DType>, names: List<&2, String>, los: List<&1, L.LO>) -> E.ResT(C.Frame):
  match sm:
    case SM{+n, +rej, +rag, +rgn}:
      Hr.comb.m(U32.is_ne(rej, 0), w, rag, rgn, n, ts, dts, names, los)

def Hr.comb.s(r: List<&1, L.LO> & SM, +w: U32, ts: List<&2, L.Ty>, dts: List<&2, D.DType>, names: List<&2, String>) -> E.ResT(C.Frame):
  (los, sm) = r
  Hr.comb.k(sm, w, ts, dts, names, los)

def Hr.comb.odd(odd: Bool, +w: U32, +sep: U32, +ts: List<&2, L.Ty>, dts: List<&2, D.DType>, names: List<&2, String>, regs: List<&1, P.Rg>) -> E.ResT(C.Frame):
  match odd:
    case True{}:
      Fail{V.Csv.malformed()}
    case False{}:
      Hr.comb.s(Hr.sum(Hr.lanes(regs, ts, w, sep), (Nil{}, SM{0, 0, 0, 0})), w, ts, dts, names)

def Hr.comb(o: P.PrOut, +w: U32, +sep: U32, +ts: List<&2, L.Ty>, dts: List<&2, D.DType>, names: List<&2, String>) -> E.ResT(C.Frame):
  match o:
    case P.PrErr{code, msg}:
      Fail{E.IoError{code, msg}}
    case P.PrOk{nr, odd, regs}:
      Hr.comb.odd(U32.is_ne(odd, 0), w, sep, ts, dts, names, regs)

# ---- the read ------------------------------------------------------------------------------------------

# no record at all (empty file, blank lines only): the (0, 0) frame, or the dtype-count error
def Hr.none(+k: U32) -> E.ResT(C.Frame):
  Bool.pick(E.ResT(C.Frame), U32.is_eq(k, 0), Done{C.Frame.empty()}, Fail{E.InvalidOperation{"csv schema: " ++ U32.show(k) ++ " dtypes for 0 columns"}})

def Hr.go.c(cnt: Bool, path: String, +w: U32, +k: U32, +off0: U32, +line0: U32, +sep: U32, +piece: U32, ts: List<&2, L.Ty>, dts: List<&2, D.DType>, names: List<&2, String>) -> IO(E.ResT(C.Frame)):
  match cnt:
    case True{}:
      IO.pure(E.ResT(C.Frame), Fail{E.InvalidOperation{"csv schema: " ++ U32.show(k) ++ " dtypes for " ++ U32.show(w) ++ " columns"}})
    case False{}:
      do IO<E.ResT(C.Frame)>:
        o : P.PrOut <- P.Pr.regions(path, off0, line0, piece)
        return Hr.comb(o, w, sep, ts, dts, names)

def Hr.go.n(none: Bool, cnt: Bool, path: String, +w: U32, +k: U32, +off0: U32, +line0: U32, +sep: U32, +piece: U32, ts: List<&2, L.Ty>, dts: List<&2, D.DType>, names: List<&2, String>) -> IO(E.ResT(C.Frame)):
  match none:
    case True{}:
      IO.pure(E.ResT(C.Frame), Hr.none(k))
    case False{}:
      Hr.go.c(cnt, path, w, k, off0, line0, sep, piece, ts, dts, names)

def Hr.go.k(ok: Bool, none: Bool, cnt: Bool, path: String, +w: U32, +k: U32, +off0: U32, +line0: U32, +sep: U32, +piece: U32, ts: List<&2, L.Ty>, dts: List<&2, D.DType>, names: List<&2, String>) -> IO(E.ResT(C.Frame)):
  match ok:
    case False{}:
      IO.pure(E.ResT(C.Frame), Fail{V.Csv.malformed()})
    case True{}:
      Hr.go.n(none, cnt, path, w, k, off0, line0, sep, piece, ts, dts, names)

def Hr.go(path: String, hd: Hd, +k: U32, +sep: U32, +piece: U32, ts: List<&2, L.Ty>, dts: List<&2, D.DType>) -> IO(E.ResT(C.Frame)):
  match hd:
    case Hd{names, +w, off0, line0, ok}:
      Hr.go.k(ok, U32.is_eq(w, 0), U32.is_ne(w, k), path, w, k, off0, line0, sep, piece, ts, dts, names)

def Hr.header2(hdr: Bool, ans: H.Ans, sc: X.Sc, +k: U32) -> Hd:
  match sc:
    case X.Sc{+n, lf, qn, last}:
      Hr.header(hdr, ans, X.Hx.rev(lf), n, k)

# Hr.read: the file read through the producer and the lanes. schema: the dtype letters; raw: Str
# columns as raw rows (TyR) instead of per-region Dictionaries (TyS)
def Hr.read(+path: String, +hdr: Bool, +sep: U32, +schema: String, +piece: U32, +raw: Bool) -> IO(E.ResT(C.Frame)):
  do IO<E.ResT(C.Frame)>:
    +bs : List<&2, U32> <- X.Hx.bytes(path)
    txt : String <- X.Hx.text(path)
    Hr.go(path, Hr.header2(hdr, H.parse_sep(sep, txt), X.Hx.scan(bs, 0, Nil{}, 0, 0), U32.from_nat(String.length(schema))), U32.from_nat(String.length(schema)), sep, piece, Hr.tys(schema, raw), Hr.dts(schema))

# ---- the physical lines of the kept rows (tests/csvlane_lines.bend) ------------------------------------
# rows, a hash of their lines, whether anything made the rows meaningless (a rejected or ragged lane,
# a header-step error)
type LN is Data:
  LN{n: U32, h: U32, flag: U32}

def Hr.ln.mix(+h: U32, +x: U32) -> U32:
  U32.mul(U32.xor(h, x), 16777619)

def Hr.ln.go(f: Nat, +i: U32, +h: U32, rd: Array<U32> & U32) -> U32:
  match f:
    case 0n:
      (a, x) = rd
      h
    case 1n+p:
      (a, +x) = rd
      Hr.ln.go(p, U32.inc(i), Hr.ln.mix(h, x), Array.get(U32, a, U32.inc(i)))

def Hr.ln.one(+n: U32, lines: Array<U32>, +h: U32) -> U32:
  Hr.ln.go(U32.to_nat(n), 0, h, Array.get(U32, lines, 0))

def Hr.ln.lo(lo: L.LO, st: LN) -> LN:
  match lo st:
    case L.LO{+n, +rej, +rag, rgn, lines, cols} LN{+n0, +h, +flag}:
      LN{U32.add(n0, n), Hr.ln.one(n, lines, h), U32.or(flag, U32.or(rej, Hr.sel(U32.is_ne(rag, 0), 1, 0)))}

def Hr.ln.los(los: List<&1, L.LO>, st: LN) -> LN:
  match los:
    case Nil{}:
      st
    case lo <> t:
      Hr.ln.los(t, Hr.ln.lo(lo, st))

# the lines the reference parser gives the kept records: the records from the data start (after the
# header when there is one), blank ones dropped when w > 1; flag when a kept record is ragged
def Hr.ln.ref.m(keep: Bool, ragd: Bool, +l: U32, +n: U32, +h: U32, +flag: U32) -> LN:
  match keep:
    case True{}:
      LN{U32.inc(n), Hr.ln.mix(h, l), U32.or(flag, Bool.to_u32(ragd))}
    case False{}:
      LN{n, h, U32.or(flag, Bool.to_u32(ragd))}

def Hr.ln.ref.k(keep: Bool, ragd: Bool, +l: U32, st: LN) -> LN:
  match st:
    case LN{+n, +h, +flag}:
      Hr.ln.ref.m(keep, ragd, l, n, h, flag)

def Hr.ln.ref.s(+blank: Bool, +g: U32, +l: U32, +w: U32, st: LN) -> LN:
  Hr.ln.ref.k(Bool.not(Bool.and(blank, U32.is_gt(w, 1))), Bool.and(Bool.not(Bool.and(blank, U32.is_gt(w, 1))), U32.is_ne(g, w)), l, st)

def Hr.ln.ref(rs: List<&2, H.CsvRec>, +w: U32, st: LN) -> LN:
  match rs:
    case Nil{}:
      st
    case +r <> t:
      Hr.ln.ref(t, w, Hr.ln.ref.s(Hr.blank(r), Hr.width(r), Hr.line(r), w, st))

def Hr.ln.tail(rs: List<&2, H.CsvRec>) -> List<&2, H.CsvRec>:
  match rs:
    case Nil{}:
      Nil{}
    case h <> t:
      t

# the records of the data: after the header (hdr) or all (the reference's order is oldest first)
def Hr.ln.data(+hdr: Bool, rs: List<&2, H.CsvRec>) -> List<&2, H.CsvRec>:
  match hdr:
    case True{}:
      Hr.ln.tail(Hr.lead(rs))
    case False{}:
      rs

def Hr.ln.cmp(c: LN, r: LN) -> String:
  match c r:
    case LN{+n1, +h1, +f1} LN{+n2, +h2, +f2}:
      Bool.pick(String, U32.is_ne(U32.or(f1, f2), 0), "n/a", Bool.pick(String, Bool.and(U32.is_eq(n1, n2), U32.is_eq(h1, h2)), "ok " ++ U32.show(n1), "DIFF candidate rows " ++ U32.show(n1) ++ " hash " ++ U32.show(h1) ++ ", reference rows " ++ U32.show(n2) ++ " hash " ++ U32.show(h2)))

def Hr.ln.cand(o: P.PrOut, +w: U32, +sep: U32, ts: List<&2, L.Ty>) -> LN:
  match o:
    case P.PrOk{nr, odd, regs}:
      Hr.ln.los(Hr.lanes(regs, ts, w, sep), LN{0, 2166136261, odd})
    case P.PrErr{code, msg}:
      LN{0, 0, 9}

# the reference's lines of the kept rows (n/a when the file is rejected or has a ragged record)
def Hr.ln.refans(+hdr: Bool, ans: H.Ans, +w: U32) -> LN:
  match ans:
    case H.Rejected{}:
      LN{0, 0, 9}
    case H.Parsed{rs}:
      Hr.ln.ref(Hr.ln.data(hdr, rs), w, LN{0, 2166136261, 0})

def Hr.ln.run(path: String, +w: U32, +sep: U32, +piece: U32, +off0: U32, +line0: U32, ts: List<&2, L.Ty>, rf: LN) -> IO(String):
  do IO<String>:
    o : P.PrOut <- P.Pr.regions(path, off0, line0, piece)
    return Hr.ln.cmp(Hr.ln.cand(o, w, sep, ts), rf)

def Hr.ln.hd.k(go: Bool, path: String, +w: U32, +sep: U32, +piece: U32, +off0: U32, +line0: U32, ts: List<&2, L.Ty>, rf: LN) -> IO(String):
  match go:
    case True{}:
      Hr.ln.run(path, w, sep, piece, off0, line0, ts, rf)
    case False{}:
      IO.pure(String, "n/a")

def Hr.ln.hd(path: String, hd: Hd, +k: U32, +sep: U32, +piece: U32, ts: List<&2, L.Ty>, rf: LN) -> IO(String):
  match hd:
    case Hd{names, +w, off0, line0, ok}:
      Hr.ln.hd.k(Bool.and(ok, U32.is_eq(w, k)), path, w, sep, piece, off0, line0, ts, rf)

def Hr.ln.start.k(path: String, +hdr: Bool, +sep: U32, +piece: U32, +k: U32, ts: List<&2, L.Ty>, +ans: H.Ans, hd: Hd) -> IO(String):
  match hd:
    case Hd{names, +w, +off0, +line0, ok}:
      Hr.ln.hd(path, Hd{names, w, off0, line0, ok}, k, sep, piece, ts, Hr.ln.refans(hdr, ans, w))

def Hr.ln.start(path: String, +hdr: Bool, +sep: U32, +schema: String, +piece: U32, +ans: H.Ans, sc: X.Sc) -> IO(String):
  Hr.ln.start.k(path, hdr, sep, piece, U32.from_nat(String.length(schema)), Hr.tys(schema, True{}), ans, Hr.header2(hdr, ans, sc, U32.from_nat(String.length(schema))))

# Hr.linesig: "ok <rows>" when the lanes' lines of the kept rows are exactly the reference parser's
# record lines (after the header, blanks dropped for w > 1), n/a when the file has no such rows
def Hr.linesig(+path: String, +hdr: Bool, +sep: U32, +schema: String, +piece: U32) -> IO(String):
  do IO<String>:
    +bs : List<&2, U32> <- X.Hx.bytes(path)
    txt : String <- X.Hx.text(path)
    +ans : H.Ans = H.parse_sep(sep, txt)
    Hr.ln.start(path, hdr, sep, schema, piece, ans, X.Hx.scan(bs, 0, Nil{}, 0, 0))
