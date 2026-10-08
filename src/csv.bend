# src/csv.bend -- CSV reading (type inference, explicit schemas), rendering, files.
# DESIGN.md 4.11. Reading goes through the hub parser (hash
# 0x64aa7934c3659ee6a818595494b38921, fetched at check time), writing is ours.
# Everything is linear: rows are transposed into column field lists in one pass,
# strings are only ever appended on their right-nested side (String.concat/join).
# Idioms: helpers above callers; a match on a parameter; loop state in parameters.
import Base
import bend-csv-parser@0.1.0.1/core.bend as H
import ./dtype.bend as D
import ./err.bend as E
import ./column.bend as C
import ./fmt.bend as F

type CsvOpts is Data:
  CsvOpts{sep: Char, has_header: Bool, infer_rows: U32}

# an inferred column: Csv.infer answers these (the schema layer maps them to Field)
type CsvField is Data:
  CsvField{name: String, dtype: D.DType}

# a field that does not parse under its column's dtype
type Bad is Data:
  Bad{line: U32, text: String}

# comma, header row, look at the first 100 rows to infer
def Csv.default() -> CsvOpts:
  CsvOpts{',', True{}, 100}

# ---- field classification (a field is trimmed before it is read) --------------------

def Csv.is_bool(+s: String) -> Bool:
  Bool.or(Bool.or(String.eq(s, "true"), String.eq(s, "false")), Bool.or(String.eq(s, "True"), String.eq(s, "False")))

def Csv.some_u32(m: Maybe<&2, U32>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      True{}

def Csv.some_i32(m: Maybe<&2, D.I32>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      True{}

def Csv.some_f32(m: Maybe<&2, F32>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      True{}

# s: trimmed and not empty
def Csv.ok.t(t: D.DType, s: String) -> Bool:
  match t:
    case D.TU32{}:
      Csv.some_u32(U32.read(s))
    case D.TI32{}:
      Csv.some_i32(D.I32.read(s))
    case D.TF32{}:
      Csv.some_f32(F32.read(s))
    case D.TBool{}:
      Csv.is_bool(s)
    case D.TStr{}:
      True{}

# an empty field is a null: it fits every dtype
def Csv.ok(t: D.DType, +f: String) -> Bool:
  Bool.or(String.is_empty(f), Csv.ok.t(t, String.trim(f)))

def Csv.chk(acc: Bool, t: D.DType, f: String) -> Bool:
  match acc:
    case False{}:
      False{}
    case True{}:
      Csv.ok(t, f)

# every one of the first k fields fits t (acc: all so far)
def Csv.all_ok(k: Nat, xs: List<&2, String>, +t: D.DType, acc: Bool) -> Bool:
  match k:
    case 0n:
      acc
    case 1n+p:
      match xs:
        case Nil{}:
          acc
        case h <> tl:
          Csv.all_ok(p, tl, t, Csv.chk(acc, t, h))

# some field of the first k is not empty
def Csv.has_value(k: Nat, xs: List<&2, String>, acc: Bool) -> Bool:
  match k:
    case 0n:
      acc
    case 1n+p:
      match xs:
        case Nil{}:
          acc
        case h <> tl:
          Csv.has_value(p, tl, Bool.or(acc, Bool.not(String.is_empty(h))))

def Csv.pick(any: Bool, u: Bool, i: Bool, f: Bool, b: Bool) -> D.DType:
  Bool.pick(D.DType, any, Bool.pick(D.DType, u, D.TU32{}, Bool.pick(D.DType, i, D.TI32{}, Bool.pick(D.DType, f, D.TF32{}, Bool.pick(D.DType, b, D.TBool{}, D.TStr{})))), D.TStr{})

# the first k fields decide: all empty -> str; u32, i32, f32, bool, else str
def Csv.infer.col(+xs: List<&2, String>, +k: Nat) -> D.DType:
  Csv.pick(Csv.has_value(k, xs, False{}), Csv.all_ok(k, xs, D.TU32{}, True{}), Csv.all_ok(k, xs, D.TI32{}, True{}), Csv.all_ok(k, xs, D.TF32{}, True{}), Csv.all_ok(k, xs, D.TBool{}, True{}))

# ---- field -> scalar -----------------------------------------------------------------------

def Csv.su32(m: Maybe<&2, U32>) -> D.Scalar:
  match m:
    case None{}:
      D.SNull{}
    case Some{v}:
      D.SU32{v}

def Csv.si32(m: Maybe<&2, D.I32>) -> D.Scalar:
  match m:
    case None{}:
      D.SNull{}
    case Some{v}:
      D.SI32{v}

def Csv.sf32(m: Maybe<&2, F32>) -> D.Scalar:
  match m:
    case None{}:
      D.SNull{}
    case Some{v}:
      D.SF32{v}

def Csv.sbool(+s: String) -> D.Scalar:
  Bool.pick(D.Scalar, Bool.or(String.eq(s, "true"), String.eq(s, "True")), D.SBool{True{}}, D.SBool{False{}})

# s: trimmed and not empty (a failed read answers null; the check passes come first)
def Csv.scalar.t(t: D.DType, s: String) -> D.Scalar:
  match t:
    case D.TU32{}:
      Csv.su32(U32.read(s))
    case D.TI32{}:
      Csv.si32(D.I32.read(s))
    case D.TF32{}:
      Csv.sf32(F32.read(s))
    case D.TBool{}:
      Csv.sbool(s)
    case D.TStr{}:
      D.SStr{s}

def Csv.scalar.n(empty: Bool, t: D.DType, f: String) -> D.Scalar:
  match empty:
    case True{}:
      D.SNull{}
    case False{}:
      match t:
        case D.TStr{}:
          D.SStr{f}
        case other:
          Csv.scalar.t(other, String.trim(f))

def Csv.scalar(+t: D.DType, +f: String) -> D.Scalar:
  Csv.scalar.n(String.is_empty(f), t, f)

def Csv.conv(xs: List<&2, String>, +t: D.DType) -> List<&2, D.Scalar>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> tl:
      Csv.scalar(t, h) <> Csv.conv(tl, t)

# ---- strict check: the first field that does not parse under t --------------------------------

def Csv.bad.k(ok: Bool, +line: U32, +f: String) -> Maybe<&2, Bad>:
  match ok:
    case True{}:
      None{}
    case False{}:
      Some{Bad{line, f}}

def Csv.bad.pick(found: Maybe<&2, Bad>, t: D.DType, line: U32, +f: String) -> Maybe<&2, Bad>:
  match found:
    case Some{b}:
      Some{b}
    case None{}:
      Csv.bad.k(Csv.ok(t, f), line, f)

def Csv.bad(xs: List<&2, String>, +t: D.DType, +line: U32, found: Maybe<&2, Bad>) -> Maybe<&2, Bad>:
  match xs:
    case Nil{}:
      found
    case h <> tl:
      Csv.bad(tl, t, U32.add(line, 1), Csv.bad.pick(found, t, line, h))

# ---- columns ------------------------------------------------------------------------------------

def Csv.col.ok(name: String, r: E.ResT(C.Column)) -> E.ResT(C.Named):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{c}:
      Done{C.Named{name, c}}

def Csv.col.build(name: String, +xs: List<&2, String>, +t: D.DType) -> E.ResT(C.Named):
  Csv.col.ok(name, C.Column.from_scalars(Csv.conv(xs, t), t))

def Csv.col.chk(m: Maybe<&2, Bad>, name: String, xs: List<&2, String>, +t: D.DType) -> E.ResT(C.Named):
  match m:
    case Some{Bad{line, text}}:
      Fail{E.ParseError{line, "column " ++ name ++ ": cannot parse \"" ++ text ++ "\" as " ++ D.DType.show(t)}}
    case None{}:
      Csv.col.build(name, xs, t)

# check: also run the strict pass (explicit schema, or inference saw only a prefix)
def Csv.col.t(+name: String, +xs: List<&2, String>, +t: D.DType, check: Bool, +line0: U32) -> E.ResT(C.Named):
  match check:
    case True{}:
      Csv.col.chk(Csv.bad(xs, t, line0, None{}), name, xs, t)
    case False{}:
      Csv.col.build(name, xs, t)

# a column whose dtype is inferred from its first k fields
def Csv.col.inf(name: String, +xs: List<&2, String>, +k: Nat, check: Bool, line0: U32) -> E.ResT(C.Named):
  Csv.col.t(name, xs, Csv.infer.col(xs, k), check, line0)

def Csv.cols.k(a: E.ResT(C.Named), b: E.ResT(List<&1, C.Named>)) -> E.ResT(List<&1, C.Named>):
  match a b:
    case Done{x} Done{y}:
      Done{x <> y}
    case Fail{e} _:
      Fail{e}
    case _ Fail{e}:
      Fail{e}

# names x column fields x dtypes (an empty dtype list means: infer every column).
# The first column and the others are built in parallel (a parallel let: ~1.8x on the 7-column sales file).
def Csv.cols(names: List<&2, String>, cs: List<&2, List<&2, String>>, ts: List<&2, D.DType>, +k: Nat, +check: Bool, +line0: U32) -> E.ResT(List<&1, C.Named>):
  match names cs ts:
    case n <> nt c <> ct Nil{}:
      a b = Csv.col.inf(n, c, k, check, line0) Csv.cols(nt, ct, Nil{}, k, check, line0)
      Csv.cols.k(a, b)
    case n <> nt c <> ct d <> dt:
      a b = Csv.col.t(n, c, d, True{}, line0) Csv.cols(nt, ct, dt, k, check, line0)
      Csv.cols.k(a, b)
    case _ _ _:
      Done{Nil{}}

def Csv.fin(r: E.ResT(List<&1, C.Named>)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{cols}:
      C.Frame.from_columns(cols)

# ---- rows -> columns ---------------------------------------------------------------------------------

def Csv.nils(n: Nat) -> List<&2, List<&2, String>>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Nil{} <> Csv.nils(p)

# push the fields of one row onto the head of each column accumulator
def Csv.tr.row(fs: List<&2, String>, accs: List<&2, List<&2, String>>) -> List<&2, List<&2, String>>:
  match fs accs:
    case f <> ft a <> at:
      (f <> a) <> Csv.tr.row(ft, at)
    case _ _:
      Nil{}

# rows come LAST first, so the accumulated columns end up in file order
def Csv.tr(rows: List<&2, List<&2, String>>, accs: List<&2, List<&2, String>>) -> List<&2, List<&2, String>>:
  match rows:
    case Nil{}:
      accs
    case r <> rt:
      Csv.tr(rt, Csv.tr.row(r, accs))

def Csv.gen_names(n: Nat, +i: Nat) -> List<&2, String>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      ("column_" ++ Nat.show(i)) <> Csv.gen_names(p, Nat.add(i, 1n))

def Csv.take_rows(k: Nat, rows: List<&2, List<&2, String>>) -> List<&2, List<&2, String>>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      match rows:
        case Nil{}:
          Nil{}
        case r <> rt:
          r <> Csv.take_rows(p, rt)

# first row whose field count is not n
def Csv.ragged.pick(found: Maybe<&2, E.Err>, +got: Nat, +want: Nat, line: U32) -> Maybe<&2, E.Err>:
  match found:
    case Some{e}:
      Some{e}
    case None{}:
      Bool.pick(Maybe<&2, E.Err>, Nat.is_eq(got, want), None{}, Some{E.ParseError{line, "expected " ++ Nat.show(want) ++ " fields, got " ++ Nat.show(got)}})

def Csv.ragged(rows: List<&2, List<&2, String>>, +n: Nat, +line: U32, found: Maybe<&2, E.Err>) -> Maybe<&2, E.Err>:
  match rows:
    case Nil{}:
      found
    case r <> rt:
      Csv.ragged(rt, n, U32.add(line, 1), Csv.ragged.pick(found, List.length(&2, String, r), n, line))

def Csv.first_err(a: Maybe<&2, E.Err>, b: Maybe<&2, E.Err>) -> Maybe<&2, E.Err>:
  match a:
    case Some{e}:
      Some{e}
    case None{}:
      b

# explicit dtypes must cover every column
def Csv.ts.err.k(+got: Nat, +n: Nat, ts: List<&2, D.DType>) -> Maybe<&2, E.Err>:
  match ts:
    case Nil{}:
      None{}
    case h <> tl:
      Bool.pick(Maybe<&2, E.Err>, Nat.is_eq(got, n), None{}, Some{E.InvalidOperation{"csv schema: " ++ Nat.show(got) ++ " dtypes for " ++ Nat.show(n) ++ " columns"}})

def Csv.ts.err(+ts: List<&2, D.DType>, +n: Nat) -> Maybe<&2, E.Err>:
  Csv.ts.err.k(List.length(&2, D.DType, ts), n, ts)

# ---- the frame ---------------------------------------------------------------------------------------------

# a row limit of 0 means every row
def Csv.limit(+inf: U32) -> U32:
  Bool.pick(U32, U32.is_eq(inf, 0), 4294967295, inf)

def Csv.rows.h(names: List<&2, String>, cs: List<&2, List<&2, String>>, ts: List<&2, D.DType>, +k: Nat, +check: Bool, +line0: U32) -> E.ResT(C.Frame):
  Csv.fin(Csv.cols(names, cs, ts, k, check, line0))

# names, data rows: ragged / dtype-count errors first, then transpose and build
def Csv.rows.g(bad: Maybe<&2, E.Err>, +names: List<&2, String>, +data: List<&2, List<&2, String>>, +inf: U32, ts: List<&2, D.DType>, +line0: U32) -> E.ResT(C.Frame):
  match bad:
    case Some{e}:
      Fail{e}
    case None{}:
      Csv.rows.h(names, Csv.tr(List.reverse(&2, List<&2, String>, data), Csv.nils(List.length(&2, String, names))), ts, U32.to_nat(Csv.limit(inf)), Bool.not(Bool.or(U32.is_eq(inf, 0), U32.is_ge(inf, U32.from_nat(List.length(&2, List<&2, String>, data))))), line0)

def Csv.blank.t(e: Bool, t: List<&2, String>) -> Bool:
  match t:
    case Nil{}:
      e
    case h <> tl:
      False{}

# a record of one empty field is a blank line
def Csv.is_blank(r: List<&2, String>) -> Bool:
  match r:
    case Nil{}:
      False{}
    case h <> t:
      Csv.blank.t(String.is_empty(h), t)

def Csv.drop.k(b: Bool, r: List<&2, String>, rest: List<&2, List<&2, String>>) -> List<&2, List<&2, String>>:
  match b:
    case True{}:
      rest
    case False{}:
      r <> rest

def Csv.drop_blank(rows: List<&2, List<&2, String>>) -> List<&2, List<&2, String>>:
  match rows:
    case Nil{}:
      Nil{}
    case +r <> rt:
      Csv.drop.k(Csv.is_blank(r), r, Csv.drop_blank(rt))

# with more than one column blank lines are skipped (error line numbers do not count them)
def Csv.skip_blank(multi: Bool, rows: List<&2, List<&2, String>>) -> List<&2, List<&2, String>>:
  match multi:
    case True{}:
      Csv.drop_blank(rows)
    case False{}:
      rows

def Csv.rows.d(+names: List<&2, String>, data0: List<&2, List<&2, String>>, hdr: Bool, inf: U32, +ts: List<&2, D.DType>) -> E.ResT(C.Frame):
  +line0 = Bool.pick(U32, hdr, 2, 1)
  +data = Csv.skip_blank(Nat.is_gt(List.length(&2, String, names), 1n), data0)
  Csv.rows.g(Csv.first_err(Csv.ragged(data, List.length(&2, String, names), line0, None{}), Csv.ts.err(ts, List.length(&2, String, names))), names, data, inf, ts, line0)

def Csv.rows.hd(hdr: Bool, +first: List<&2, String>, rest: List<&2, List<&2, String>>, inf: U32, ts: List<&2, D.DType>) -> E.ResT(C.Frame):
  match hdr:
    case True{}:
      Csv.rows.d(first, rest, True{}, inf, ts)
    case False{}:
      Csv.rows.d(Csv.gen_names(List.length(&2, String, first), 0n), first <> rest, False{}, inf, ts)

def Csv.rows(rows: List<&2, List<&2, String>>, hdr: Bool, inf: U32, ts: List<&2, D.DType>) -> E.ResT(C.Frame):
  match rows:
    case Nil{}:
      Done{C.Frame.empty()}
    case first <> rest:
      Csv.rows.hd(hdr, first, rest, inf, ts)

def Csv.parse.a(ans: H.Ans, hdr: Bool, inf: U32, ts: List<&2, D.DType>) -> E.ResT(C.Frame):
  match ans:
    case H.Rejected{}:
      Fail{E.ParseError{0, "malformed csv"}}
    case H.Parsed{rows}:
      Csv.rows(rows, hdr, inf, ts)

# Strict schema: dtypes by column position, a value that does not parse is a
# ParseError (no lenient nulls); the dtype count must equal the column count.
def Csv.parse_with(text: String, opts: CsvOpts, ts: List<&2, D.DType>) -> E.ResT(C.Frame):
  match opts:
    case CsvOpts{sep, hdr, inf}:
      Csv.parse.a(H.parse_sep(Char.to_u32(sep), text), hdr, inf, ts)

# Inferred schema (first infer_rows rows; 0 = all): bool, u32, i32, f32, str.
def Csv.parse(text: String, opts: CsvOpts) -> E.ResT(C.Frame):
  Csv.parse_with(text, opts, Nil{})

# ---- Csv.infer: names + dtypes only ---------------------------------------------------------------------------

def Csv.infer.fields(names: List<&2, String>, cs: List<&2, List<&2, String>>, +k: Nat) -> List<&2, CsvField>:
  match names cs:
    case n <> nt c <> ct:
      CsvField{n, Csv.infer.col(c, k)} <> Csv.infer.fields(nt, ct, k)
    case _ _:
      Nil{}

def Csv.infer.d(+names: List<&2, String>, data: List<&2, List<&2, String>>, +k: U32) -> List<&2, CsvField>:
  Csv.infer.fields(names, Csv.tr(List.reverse(&2, List<&2, String>, Csv.take_rows(U32.to_nat(k), data)), Csv.nils(List.length(&2, String, names))), U32.to_nat(k))

def Csv.infer.hd(hdr: Bool, +first: List<&2, String>, rest: List<&2, List<&2, String>>, +k: U32) -> List<&2, CsvField>:
  match hdr:
    case True{}:
      Csv.infer.d(first, rest, k)
    case False{}:
      Csv.infer.d(Csv.gen_names(List.length(&2, String, first), 0n), first <> rest, k)

def Csv.infer.rows(rows: List<&2, List<&2, String>>, hdr: Bool, k: U32) -> List<&2, CsvField>:
  match rows:
    case Nil{}:
      Nil{}
    case first <> rest:
      Csv.infer.hd(hdr, first, rest, k)

def Csv.infer.a(ans: H.Ans, hdr: Bool, inf: U32) -> E.Res(List<&2, CsvField>):
  match ans:
    case H.Rejected{}:
      Fail{E.ParseError{0, "malformed csv"}}
    case H.Parsed{rows}:
      Done{Csv.infer.rows(rows, hdr, Csv.limit(inf))}

# The schema Csv.parse would infer, without building columns.
def Csv.infer(text: String, opts: CsvOpts) -> E.Res(List<&2, CsvField>):
  match opts:
    case CsvOpts{sep, hdr, inf}:
      Csv.infer.a(H.parse_sep(Char.to_u32(sep), text), hdr, inf)

# ---- rendering ---------------------------------------------------------------------------------------------------

def Csv.special(+u: U32, +sep: U32) -> Bool:
  Bool.or(Bool.or(U32.is_eq(u, sep), U32.is_eq(u, 34)), Bool.or(U32.is_eq(u, 10), U32.is_eq(u, 13)))

# a field holding sep, a quote, CR or LF is quoted
def Csv.needs_q(s: String, +sep: U32, acc: Bool) -> Bool:
  match s:
    case SNil{}:
      acc
    case SCon{c, tl}:
      Csv.needs_q(tl, sep, Bool.or(acc, Csv.special(Char.to_u32(c), sep)))

def Csv.dq.k(q: Bool, +c: Char, rest: String) -> String:
  match q:
    case True{}:
      SCon{c, SCon{c, rest}}
    case False{}:
      SCon{c, rest}

# double every quote
def Csv.dq(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, tl}:
      Csv.dq.k(U32.is_eq(Char.to_u32(c), 34), c, Csv.dq(tl))

def Csv.quote.k(nq: Bool, s: String) -> String:
  match nq:
    case True{}:
      "\"" ++ Csv.dq(s) ++ "\""
    case False{}:
      s

def Csv.quote(+s: String, +sep: U32) -> String:
  Csv.quote.k(Csv.needs_q(s, sep, False{}), s)

def Csv.f32(x: F32, prec: Maybe<&2, U32>) -> String:
  match prec:
    case None{}:
      F32.show(x)
    case Some{p}:
      F.Fmt.fixed(x, p)

# null: empty; bool: true/false; floats: shortest digits, or `prec` decimals
def Csv.cell(sc: D.Scalar, prec: Maybe<&2, U32>, sep: U32) -> String:
  match sc:
    case D.SNull{}:
      ""
    case D.SF32{x}:
      Csv.f32(x, prec)
    case D.SStr{s}:
      Csv.quote(s, sep)
    case other:
      D.Scalar.show(other)

def Csv.cells(xs: List<&2, D.Scalar>, +prec: Maybe<&2, U32>, +sep: U32) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> tl:
      Csv.cell(h, prec, sep) <> Csv.cells(tl, prec, sep)

# x ++ y for each pair (right-nested appends: linear)
def Csv.zip(a: List<&2, String>, b: List<&2, String>) -> List<&2, String>:
  match a b:
    case x <> xt y <> yt:
      (x ++ y) <> Csv.zip(xt, yt)
    case _ _:
      Nil{}

# pre ++ x ++ y for each pair
def Csv.zip_pre(a: List<&2, String>, b: List<&2, String>, +pre: String) -> List<&2, String>:
  match a b:
    case x <> xt y <> yt:
      (pre ++ x ++ y) <> Csv.zip_pre(xt, yt, pre)
    case _ _:
      Nil{}

def Csv.col_cells.b(+name: String, prec: Maybe<&2, U32>, +sep: U32, r: C.Column & List<&2, D.Scalar>) -> C.Named & List<&2, String>:
  (c, xs) = r
  (C.Named{name, c}, Csv.cells(xs, prec, sep))

def Csv.col_cells(nc: C.Named, +h: U32, prec: Maybe<&2, U32>, sep: U32) -> C.Named & List<&2, String>:
  match nc:
    case C.Named{name, col}:
      Csv.col_cells.b(name, prec, sep, C.Column.scalars(col, 0, h))

# the lines of columns 1.. : every cell is preceded by the separator, the line ends in "\n"
def Csv.rest.k(sp: String, r1: C.Named & List<&2, String>, r2: List<&1, C.Named> & List<&2, String>) -> List<&1, C.Named> & List<&2, String>:
  (nc, cells) = r1
  (cols, lines) = r2
  (nc <> cols, Csv.zip_pre(cells, lines, sp))

def Csv.rest(cols: List<&1, C.Named>, +h: U32, +prec: Maybe<&2, U32>, +sep: U32, +sp: String) -> List<&1, C.Named> & List<&2, String>:
  match cols:
    case Nil{}:
      (Nil{}, List.replicate(String, U32.to_nat(h), "\n"))
    case nc <> t:
      Csv.rest.k(sp, Csv.col_cells(nc, h, prec, sep), Csv.rest(t, h, prec, sep, sp))

def Csv.lines.k(r1: C.Named & List<&2, String>, r2: List<&1, C.Named> & List<&2, String>) -> List<&1, C.Named> & List<&2, String>:
  (nc, cells) = r1
  (cols, lines) = r2
  (nc <> cols, Csv.zip(cells, lines))

def Csv.lines(cols: List<&1, C.Named>, +h: U32, +prec: Maybe<&2, U32>, +sep: U32, +sp: String) -> List<&1, C.Named> & List<&2, String>:
  match cols:
    case Nil{}:
      (Nil{}, Nil{})
    case nc <> t:
      Csv.lines.k(Csv.col_cells(nc, h, prec, sep), Csv.rest(t, h, prec, sep, sp))

def Csv.header.rest(names: List<&2, String>, +sep: U32, +sp: String) -> String:
  match names:
    case Nil{}:
      ""
    case h <> t:
      sp ++ Csv.quote(h, sep) ++ Csv.header.rest(t, sep, sp)

def Csv.header(names: List<&2, String>, +sep: U32, +sp: String) -> String:
  match names:
    case Nil{}:
      ""
    case h <> t:
      Csv.quote(h, sep) ++ Csv.header.rest(t, sep, sp)

def Csv.render.t(+h: U32, hd: String, r: List<&1, C.Named> & List<&2, String>) -> C.Frame & String:
  (cols, lines) = r
  (C.Frame{h, cols}, hd ++ "\n" ++ String.concat(lines))

def Csv.render.m(f: C.Frame, names: List<&2, String>, prec: Maybe<&2, U32>, +sep: U32, +sp: String) -> C.Frame & String:
  match f:
    case C.Frame{+h, cols}:
      Csv.render.t(h, Csv.header(names, sep, sp), Csv.lines(cols, h, prec, sep, sp))

def Csv.render.k(r: C.Frame & List<&2, String>, prec: Maybe<&2, U32>, sep: U32, sp: String) -> C.Frame & String:
  (f, names) = r
  Csv.render.m(f, names, prec, sep, sp)

# Header row, then one line per row ("\n" line ends); nulls are empty fields. Floats
# print with F32.show when prec is None, else with exactly `prec` decimals.
def Csv.render_with(f: C.Frame, prec: Maybe<&2, U32>, +sep: Char) -> C.Frame & String:
  Csv.render.k(C.Frame.names(f), prec, Char.to_u32(sep), SCon{sep, SNil{}})

def Csv.render(f: C.Frame, prec: Maybe<&2, U32>) -> C.Frame & String:
  Csv.render_with(f, prec, ',')

# ---- files ---------------------------------------------------------------------------------------------------------------------

# the file is read whole (size, then read), closed, then parsed; every IO failure is an IoError value
def Csv.read.fin(opts: CsvOpts, ts: List<&2, D.DType>, f: File, res: Result<&1, &1, U32 & String, String>) -> IO(E.ResT(C.Frame)):
  match res:
    case Done{text}:
      do IO<E.ResT(C.Frame)>:
        File.close(f)
        return Csv.parse_with(text, opts, ts)
    case Fail{(code, msg)}:
      do IO<E.ResT(C.Frame)>:
        File.close(f)
        return Fail{E.IoError{code, msg}}

def Csv.read.got(opts: CsvOpts, ts: List<&2, D.DType>, r: File & Result<&1, &1, U32 & String, String>) -> IO(E.ResT(C.Frame)):
  (f, res) = r
  Csv.read.fin(opts, ts, f, res)

def Csv.read.sized(opts: CsvOpts, ts: List<&2, D.DType>, f: File, res: Result<&1, &1, U32 & String, U32>) -> IO(E.ResT(C.Frame)):
  match res:
    case Done{n}:
      do IO<E.ResT(C.Frame)>:
        r : File & Result<&1, &1, U32 & String, String> <- File.read(f, n)
        Csv.read.got(opts, ts, r)
    case Fail{(code, msg)}:
      do IO<E.ResT(C.Frame)>:
        File.close(f)
        return Fail{E.IoError{code, msg}}

def Csv.read.size(opts: CsvOpts, ts: List<&2, D.DType>, r: File & Result<&1, &1, U32 & String, U32>) -> IO(E.ResT(C.Frame)):
  (f, res) = r
  Csv.read.sized(opts, ts, f, res)

def Csv.read.opened(opts: CsvOpts, ts: List<&2, D.DType>, o: Result<&1, &1, U32 & String, File>) -> IO(E.ResT(C.Frame)):
  match o:
    case Done{f}:
      do IO<E.ResT(C.Frame)>:
        r : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
        Csv.read.size(opts, ts, r)
    case Fail{(code, msg)}:
      IO.pure(E.ResT(C.Frame), Fail{E.IoError{code, msg}})

# Strict explicit dtypes (by column position), see Csv.parse_with.
def Csv.read_with(path: String, opts: CsvOpts, ts: List<&2, D.DType>) -> IO(E.ResT(C.Frame)):
  do IO<E.ResT(C.Frame)>:
    o : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    Csv.read.opened(opts, ts, o)

def Csv.read(path: String, opts: CsvOpts) -> IO(E.ResT(C.Frame)):
  Csv.read_with(path, opts, Nil{})

def Csv.write.done(f: C.Frame, file: File, w: Result<&1, &1, U32 & String, Unit>) -> IO(C.Frame & Result<&1, &1, U32 & String, Unit>):
  do IO<C.Frame & Result<&1, &1, U32 & String, Unit>>:
    File.close(file)
    return (f, w)

def Csv.write.wrote(f: C.Frame, r: File & Result<&1, &1, U32 & String, Unit>) -> IO(C.Frame & Result<&1, &1, U32 & String, Unit>):
  (file, w) = r
  Csv.write.done(f, file, w)

def Csv.write.opened(f: C.Frame, text: String, o: Result<&1, &1, U32 & String, File>) -> IO(C.Frame & Result<&1, &1, U32 & String, Unit>):
  match o:
    case Done{file}:
      do IO<C.Frame & Result<&1, &1, U32 & String, Unit>>:
        r : File & Result<&1, &1, U32 & String, Unit> <- File.write(file, text)
        Csv.write.wrote(f, r)
    case Fail{(code, msg)}:
      IO.pure(C.Frame & Result<&1, &1, U32 & String, Unit>, (f, Fail{(code, msg)}))

def Csv.write.go(r: C.Frame & String, path: String) -> IO(C.Frame & Result<&1, &1, U32 & String, Unit>):
  (f, text) = r
  do IO<C.Frame & Result<&1, &1, U32 & String, Unit>>:
    o : Result<&1, &1, U32 & String, File> <- File.open(path, "w")
    Csv.write.opened(f, text, o)

# renders with F32.show (Csv.render(f, None{})) and writes the file; the frame comes back
def Csv.write(f: C.Frame, path: String) -> IO(C.Frame & Result<&1, &1, U32 & String, Unit>):
  Csv.write.go(Csv.render(f, None{}), path)
