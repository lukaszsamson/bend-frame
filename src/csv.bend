# src/csv.bend -- CSV reading (type inference, explicit schemas), rendering, files.
# DESIGN.md 4.11 and 15.6. Reading goes through src/csvparse.bend (a fork of the hub
# parser that keeps quotedness and physical line numbers), writing is ours.
# Everything is linear: records are transposed into column cell lists in one pass,
# strings are only ever appended on their right-nested side (String.concat/join).
# Idioms: helpers above callers; a match on a parameter; loop state in parameters.
import Base
import ./csvparse.bend as H
import ./dtype.bend as D
import ./err.bend as E
import ./kernels.bend as K
import ./column.bend as C
import ./fmt.bend as F

type CsvOpts is Data:
  CsvOpts{sep: Char, has_header: Bool, infer_rows: U32}

# write options: separator, header line or not, F32 with this many decimals (None: shortest digits)
type CsvWriteOpts is Data:
  CsvWriteOpts{sep: Char, include_header: Bool, float_precision: Maybe<&2, U32>}

# an inferred column: Csv.infer answers these (the schema layer maps them to Field)
type CsvField is Data:
  CsvField{name: String, dtype: D.DType}

# a cell that does not parse under its column's dtype: its position in the column
# (the record's physical line is looked up only when the error is built)
type Bad is Data:
  Bad{idx: U32, text: String}

# the header names and the data records that passed the shape checks
type Prep is Data:
  Prep{names: List<&2, String>, data: List<&2, H.CsvRec>}

# comma, header row, look at the first 100 rows to infer
def Csv.default() -> CsvOpts:
  CsvOpts{',', True{}, 100}

def Csv.infer_rows(opts: CsvOpts) -> U32:
  match opts:
    case CsvOpts{sep, hdr, inf}:
      inf

# comma, header line, shortest float digits
def Csv.write_default() -> CsvWriteOpts:
  CsvWriteOpts{',', True{}, None{}}

# ---- cell classification (a numeric cell is trimmed before it is read; DESIGN.md 15.6.1) --------

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

# s: trimmed; an empty one is a null: it fits every dtype
def Csv.ok.e(t: D.DType, +s: String) -> Bool:
  Bool.or(String.is_empty(s), Csv.ok.t(t, s))

# a str cell always fits; any other cell fits when its trimmed text is empty (null) or reads
def Csv.ok.c(t: D.DType, c: H.CsvCell) -> Bool:
  match c:
    case H.CsvCell{f, q}:
      Csv.ok.e(t, String.trim(f))

def Csv.ok(t: D.DType, c: H.CsvCell) -> Bool:
  match t:
    case D.TStr{}:
      True{}
    case other:
      Csv.ok.c(other, c)

def Csv.chk(acc: Bool, t: D.DType, c: H.CsvCell) -> Bool:
  match acc:
    case False{}:
      False{}
    case True{}:
      Csv.ok(t, c)

# every one of the first k cells fits t (acc: all so far)
def Csv.all_ok(k: Nat, xs: List<&2, H.CsvCell>, +t: D.DType, acc: Bool) -> Bool:
  match k:
    case 0n:
      acc
    case 1n+p:
      match xs:
        case Nil{}:
          acc
        case h <> tl:
          Csv.all_ok(p, tl, t, Csv.chk(acc, t, h))

# a cell with text left after trimming (quotes or not)
def Csv.has.c(c: H.CsvCell) -> Bool:
  match c:
    case H.CsvCell{f, q}:
      Bool.not(String.is_empty(String.trim(f)))

# some cell of the first k has text
def Csv.has_value(k: Nat, xs: List<&2, H.CsvCell>, acc: Bool) -> Bool:
  match k:
    case 0n:
      acc
    case 1n+p:
      match xs:
        case Nil{}:
          acc
        case h <> tl:
          Csv.has_value(p, tl, Bool.or(acc, Csv.has.c(h)))

def Csv.pick(any: Bool, u: Bool, i: Bool, f: Bool, b: Bool) -> D.DType:
  Bool.pick(D.DType, any, Bool.pick(D.DType, u, D.TU32{}, Bool.pick(D.DType, i, D.TI32{}, Bool.pick(D.DType, f, D.TF32{}, Bool.pick(D.DType, b, D.TBool{}, D.TStr{})))), D.TStr{})

# the first k cells decide: no text at all -> str; u32, i32, f32, bool, else str
def Csv.infer.col(+xs: List<&2, H.CsvCell>, +k: Nat) -> D.DType:
  Csv.pick(Csv.has_value(k, xs, False{}), Csv.all_ok(k, xs, D.TU32{}, True{}), Csv.all_ok(k, xs, D.TI32{}, True{}), Csv.all_ok(k, xs, D.TF32{}, True{}), Csv.all_ok(k, xs, D.TBool{}, True{}))

# ---- cell -> scalar -----------------------------------------------------------------------

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

def Csv.scalar.n(empty: Bool, t: D.DType, s: String) -> D.Scalar:
  match empty:
    case True{}:
      D.SNull{}
    case False{}:
      Csv.scalar.t(t, s)

# a numeric / bool cell: s is trimmed, empty is null
def Csv.scalar.num(t: D.DType, +s: String) -> D.Scalar:
  Csv.scalar.n(String.is_empty(s), t, s)

def Csv.scalar.sq(null: Bool, f: String) -> D.Scalar:
  match null:
    case True{}:
      D.SNull{}
    case False{}:
      D.SStr{f}

# a str cell: quoted is the text verbatim ("" is the empty string), unquoted empty is null
def Csv.scalar.str(+q: Bool, +f: String) -> D.Scalar:
  Csv.scalar.sq(Bool.and(Bool.not(q), String.is_empty(f)), f)

def Csv.scalar.c(+t: D.DType, q: Bool, f: String) -> D.Scalar:
  match t:
    case D.TStr{}:
      Csv.scalar.str(q, f)
    case other:
      Csv.scalar.num(other, String.trim(f))

def Csv.scalar(+t: D.DType, c: H.CsvCell) -> D.Scalar:
  match c:
    case H.CsvCell{f, q}:
      Csv.scalar.c(t, q, f)

def Csv.conv(xs: List<&2, H.CsvCell>, +t: D.DType) -> List<&2, D.Scalar>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> tl:
      Csv.scalar(t, h) <> Csv.conv(tl, t)

# ---- strict check: the first cell that does not parse under t --------------------------------

def Csv.bad.k(ok: Bool, +idx: U32, +f: String) -> Maybe<&2, Bad>:
  match ok:
    case True{}:
      None{}
    case False{}:
      Some{Bad{idx, f}}

def Csv.bad.c(t: D.DType, idx: U32, c: H.CsvCell) -> Maybe<&2, Bad>:
  match c:
    case H.CsvCell{+f, q}:
      Csv.bad.k(Csv.ok(t, H.CsvCell{f, q}), idx, f)

def Csv.bad.pick(found: Maybe<&2, Bad>, t: D.DType, idx: U32, c: H.CsvCell) -> Maybe<&2, Bad>:
  match found:
    case Some{b}:
      Some{b}
    case None{}:
      Csv.bad.c(t, idx, c)

def Csv.bad(xs: List<&2, H.CsvCell>, +t: D.DType, +idx: U32, found: Maybe<&2, Bad>) -> Maybe<&2, Bad>:
  match xs:
    case Nil{}:
      found
    case h <> tl:
      Csv.bad(tl, t, U32.add(idx, 1), Csv.bad.pick(found, t, idx, h))

# the physical line of the idx-th data record (0 when absent: not reachable)
def Csv.line_at(lines: List<&2, U32>, +idx: U32) -> U32:
  Maybe.default(&2, U32, List.get(&2, U32, lines, U32.to_nat(idx)), 0)

# ---- columns ------------------------------------------------------------------------------------

def Csv.col.ok(name: String, r: E.ResT(C.Column)) -> E.ResT(C.Named):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{c}:
      Done{C.Named{name, c}}

def Csv.col.build(name: String, +xs: List<&2, H.CsvCell>, +t: D.DType) -> E.ResT(C.Named):
  Csv.col.ok(name, C.Column.from_scalars(Csv.conv(xs, t), t))

def Csv.col.err(+name: String, +t: D.DType, +text: String, +line: U32) -> E.ResT(C.Named):
  Fail{E.ParseError{line, "column " ++ name ++ ": cannot parse \"" ++ text ++ "\" as " ++ D.DType.show(t)}}

def Csv.col.chk(m: Maybe<&2, Bad>, name: String, xs: List<&2, H.CsvCell>, +t: D.DType, lines: List<&2, U32>) -> E.ResT(C.Named):
  match m:
    case Some{Bad{idx, text}}:
      Csv.col.err(name, t, text, Csv.line_at(lines, idx))
    case None{}:
      Csv.col.build(name, xs, t)

# check: also run the strict pass (explicit schema, or inference saw only a prefix)
def Csv.col.t(+name: String, +xs: List<&2, H.CsvCell>, +t: D.DType, check: Bool, lines: List<&2, U32>) -> E.ResT(C.Named):
  match check:
    case True{}:
      Csv.col.chk(Csv.bad(xs, t, 0, None{}), name, xs, t, lines)
    case False{}:
      Csv.col.build(name, xs, t)

# a column whose dtype is inferred from its first k cells
def Csv.col.inf(name: String, +xs: List<&2, H.CsvCell>, +k: Nat, check: Bool, lines: List<&2, U32>) -> E.ResT(C.Named):
  Csv.col.t(name, xs, Csv.infer.col(xs, k), check, lines)

def Csv.cols.k(a: E.ResT(C.Named), b: E.ResT(List<&1, C.Named>)) -> E.ResT(List<&1, C.Named>):
  match a b:
    case Done{x} Done{y}:
      Done{x <> y}
    case Fail{e} _:
      Fail{e}
    case _ Fail{e}:
      Fail{e}

# names x column cells x dtypes (an empty dtype list means: infer every column).
# lines: the physical line of every data record (for error texts only).
# The first column and the others are built in parallel (a parallel let: ~1.8x on the 7-column sales file).
def Csv.cols(names: List<&2, String>, cs: List<&2, List<&2, H.CsvCell>>, ts: List<&2, D.DType>, +k: Nat, +check: Bool, +lines: List<&2, U32>) -> E.ResT(List<&1, C.Named>):
  match names cs ts:
    case n <> nt c <> ct Nil{}:
      a b = Csv.col.inf(n, c, k, check, lines) Csv.cols(nt, ct, Nil{}, k, check, lines)
      Csv.cols.k(a, b)
    case n <> nt c <> ct d <> dt:
      a b = Csv.col.t(n, c, d, True{}, lines) Csv.cols(nt, ct, dt, k, check, lines)
      Csv.cols.k(a, b)
    case _ _ _:
      Done{Nil{}}

def Csv.fin(r: E.ResT(List<&1, C.Named>)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{cols}:
      C.Frame.from_columns(cols)

# ---- records -> columns ---------------------------------------------------------------------------

def Csv.nils(n: Nat) -> List<&2, List<&2, H.CsvCell>>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Nil{} <> Csv.nils(p)

# push the cells of one record onto the head of each column accumulator
def Csv.tr.row(fs: List<&2, H.CsvCell>, accs: List<&2, List<&2, H.CsvCell>>) -> List<&2, List<&2, H.CsvCell>>:
  match fs accs:
    case f <> ft a <> at:
      (f <> a) <> Csv.tr.row(ft, at)
    case _ _:
      Nil{}

# records come LAST first, so the accumulated columns end up in file order
def Csv.tr(rows: List<&2, H.CsvRec>, accs: List<&2, List<&2, H.CsvCell>>) -> List<&2, List<&2, H.CsvCell>>:
  match rows:
    case Nil{}:
      accs
    case H.CsvRec{l, cs} <> rt:
      Csv.tr(rt, Csv.tr.row(cs, accs))

# the physical line each record starts on
def Csv.rec_lines(rows: List<&2, H.CsvRec>) -> List<&2, U32>:
  match rows:
    case Nil{}:
      Nil{}
    case H.CsvRec{l, cs} <> rt:
      l <> Csv.rec_lines(rt)

# the texts of a record's cells (the header names)
def Csv.names(cs: List<&2, H.CsvCell>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case H.CsvCell{f, q} <> rt:
      f <> Csv.names(rt)

def Csv.gen_names(n: Nat, +i: Nat) -> List<&2, String>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      ("column_" ++ Nat.show(i)) <> Csv.gen_names(p, Nat.add(i, 1n))

def Csv.take_rows(k: Nat, rows: List<&2, H.CsvRec>) -> List<&2, H.CsvRec>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      match rows:
        case Nil{}:
          Nil{}
        case r <> rt:
          r <> Csv.take_rows(p, rt)

# first record whose cell count is not n (its own physical line in the error)
def Csv.ragged.pick(found: Maybe<&2, E.Err>, +got: Nat, +want: Nat, line: U32) -> Maybe<&2, E.Err>:
  match found:
    case Some{e}:
      Some{e}
    case None{}:
      Bool.pick(Maybe<&2, E.Err>, Nat.is_eq(got, want), None{}, Some{E.ParseError{line, "expected " ++ Nat.show(want) ++ " fields, got " ++ Nat.show(got)}})

def Csv.ragged(rows: List<&2, H.CsvRec>, +n: Nat, found: Maybe<&2, E.Err>) -> Maybe<&2, E.Err>:
  match rows:
    case Nil{}:
      found
    case H.CsvRec{l, cs} <> rt:
      Csv.ragged(rt, n, Csv.ragged.pick(found, List.length(&2, H.CsvCell, cs), n, l))

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

# ---- blank lines (DESIGN.md 15.6.2) ---------------------------------------------------------------

# a record of one UNQUOTED empty cell is a blank line (a quoted "" is a value)
def Csv.blank.c(c: H.CsvCell) -> Bool:
  match c:
    case H.CsvCell{f, q}:
      Bool.and(Bool.not(q), String.is_empty(f))

def Csv.blank.t(e: Bool, t: List<&2, H.CsvCell>) -> Bool:
  match t:
    case Nil{}:
      e
    case h <> tl:
      False{}

def Csv.is_blank(r: List<&2, H.CsvCell>) -> Bool:
  match r:
    case Nil{}:
      False{}
    case h <> t:
      Csv.blank.t(Csv.blank.c(h), t)

def Csv.drop.k(b: Bool, r: H.CsvRec, rest: List<&2, H.CsvRec>) -> List<&2, H.CsvRec>:
  match b:
    case True{}:
      rest
    case False{}:
      r <> rest

def Csv.drop.r(r: H.CsvRec, rest: List<&2, H.CsvRec>) -> List<&2, H.CsvRec>:
  match r:
    case H.CsvRec{+l, +cs}:
      Csv.drop.k(Csv.is_blank(cs), H.CsvRec{l, cs}, rest)

def Csv.drop_blank(rows: List<&2, H.CsvRec>) -> List<&2, H.CsvRec>:
  match rows:
    case Nil{}:
      Nil{}
    case r <> rt:
      Csv.drop.r(r, Csv.drop_blank(rt))

# with more than one column blank lines are skipped (the records after keep their physical lines)
def Csv.skip_blank(multi: Bool, rows: List<&2, H.CsvRec>) -> List<&2, H.CsvRec>:
  match multi:
    case True{}:
      Csv.drop_blank(rows)
    case False{}:
      rows

# ---- the shape checks: blank lines, ragged records, dtype count ------------------------------------------

def Csv.prep.k(bad: Maybe<&2, E.Err>, names: List<&2, String>, data: List<&2, H.CsvRec>) -> E.Res(Prep):
  match bad:
    case Some{e}:
      Fail{e}
    case None{}:
      Done{Prep{names, data}}

def Csv.prep.d(+names: List<&2, String>, data0: List<&2, H.CsvRec>, +ts: List<&2, D.DType>) -> E.Res(Prep):
  +data = Csv.skip_blank(Nat.is_gt(List.length(&2, String, names), 1n), data0)
  Csv.prep.k(Csv.first_err(Csv.ragged(data, List.length(&2, String, names), None{}), Csv.ts.err(ts, List.length(&2, String, names))), names, data)

# the header names, then the checked data records
def Csv.prep.hn(first: H.CsvRec, rest: List<&2, H.CsvRec>, +ts: List<&2, D.DType>) -> E.Res(Prep):
  match first:
    case H.CsvRec{l, cs}:
      Csv.prep.d(Csv.names(cs), rest, ts)

# no header: the first record is data, the names are column_0 ..
def Csv.prep.gn(first: H.CsvRec, rest: List<&2, H.CsvRec>, +ts: List<&2, D.DType>) -> E.Res(Prep):
  match first:
    case H.CsvRec{+l, +cs}:
      Csv.prep.d(Csv.gen_names(List.length(&2, H.CsvCell, cs), 0n), H.CsvRec{l, cs} <> rest, ts)

def Csv.prep.hd(hdr: Bool, first: H.CsvRec, rest: List<&2, H.CsvRec>, ts: List<&2, D.DType>) -> E.Res(Prep):
  match hdr:
    case True{}:
      Csv.prep.hn(first, rest, ts)
    case False{}:
      Csv.prep.gn(first, rest, ts)

# ---- separator, leading blank lines ----------------------------------------------------------------------------

# a separator that is a quote, CR or LF cannot be told from the quoting and the line ends: reads
# and writes refuse it (DESIGN.md 15.6.2, M1 B02 review)
def Csv.sep_bad(+u: U32) -> Bool:
  Bool.or(U32.is_eq(u, 34), Bool.or(U32.is_eq(u, 10), U32.is_eq(u, 13)))

def Csv.sep_err.k(bad: Bool) -> Maybe<&2, E.Err>:
  match bad:
    case True{}:
      Some{E.InvalidOperation{"csv: separator must not be a double quote, CR or LF"}}
    case False{}:
      None{}

def Csv.sep_err(sep: Char) -> Maybe<&2, E.Err>:
  Csv.sep_err.k(Csv.sep_bad(Char.to_u32(sep)))

# with a header, the blank lines before it are skipped (Polars; the physical line numbers of the
# records after them are unchanged). go: the records so far were all blank. Without a header a
# blank line is data (a null record in one column; skipped in k > 1 columns as always).
def Csv.lead.blank(r: H.CsvRec) -> Bool:
  match r:
    case H.CsvRec{l, cs}:
      Csv.is_blank(cs)

# blank: the head record is blank, res: the answer for the rest (a blank head is dropped)
def Csv.lead.k(blank: Bool, r: H.CsvRec, rt: List<&2, H.CsvRec>, res: List<&2, H.CsvRec>) -> List<&2, H.CsvRec>:
  match blank:
    case True{}:
      res
    case False{}:
      r <> rt

def Csv.lead(rows: List<&2, H.CsvRec>, +go: Bool) -> List<&2, H.CsvRec>:
  match rows go:
    case Nil{} _:
      Nil{}
    case +r <> +rt True{}:
      Csv.lead.k(Csv.lead.blank(r), r, rt, Csv.lead(rt, Csv.lead.blank(r)))
    case other False{}:
      other

# ---- the frame ---------------------------------------------------------------------------------------------

# a row limit of 0 means every row
def Csv.limit(+inf: U32) -> U32:
  Bool.pick(U32, U32.is_eq(inf, 0), 4294967295, inf)

def Csv.rows.h(names: List<&2, String>, cs: List<&2, List<&2, H.CsvCell>>, ts: List<&2, D.DType>, +k: Nat, +check: Bool, lines: List<&2, U32>) -> E.ResT(C.Frame):
  Csv.fin(Csv.cols(names, cs, ts, k, check, lines))

# names, data records: transpose and build (the shape checks passed and the row cap held)
def Csv.rows.g(+names: List<&2, String>, +data: List<&2, H.CsvRec>, +inf: U32, ts: List<&2, D.DType>) -> E.ResT(C.Frame):
  Csv.rows.h(names, Csv.tr(List.reverse(&2, H.CsvRec, data), Csv.nils(List.length(&2, String, names))), ts, U32.to_nat(Csv.limit(inf)), Bool.not(Bool.or(U32.is_eq(inf, 0), U32.is_ge(inf, U32.from_nat(List.length(&2, H.CsvRec, data))))), Csv.rec_lines(data))

# the row cap (DESIGN.md 15.8): the number of data records is counted before any column is built
def Csv.rows.c(over: Maybe<&2, E.Err>, +names: List<&2, String>, +data: List<&2, H.CsvRec>, +inf: U32, ts: List<&2, D.DType>) -> E.ResT(C.Frame):
  match over:
    case Some{e}:
      Fail{e}
    case None{}:
      Csv.rows.g(names, data, inf, ts)

def Csv.rows.p(+cap: U32, p: E.Res(Prep), inf: U32, ts: List<&2, D.DType>) -> E.ResT(C.Frame):
  match p:
    case Fail{e}:
      Fail{e}
    case Done{Prep{names, +data}}:
      Csv.rows.c(K.Kernel.check_rows.cap(cap, U32.from_nat(List.length(&2, H.CsvRec, data))), names, data, inf, ts)

# no records (an empty file, or one of blank lines before a header): the (0, 0) frame, unless
# dtypes were given: they must cover every column, and there are none (15.6.3)
def Csv.rows.none(bad: Maybe<&2, E.Err>) -> E.ResT(C.Frame):
  match bad:
    case Some{e}:
      Fail{e}
    case None{}:
      Done{C.Frame.empty()}

def Csv.rows.n(+cap: U32, rows: List<&2, H.CsvRec>, hdr: Bool, inf: U32, +ts: List<&2, D.DType>) -> E.ResT(C.Frame):
  match rows:
    case Nil{}:
      Csv.rows.none(Csv.ts.err(ts, 0n))
    case first <> rest:
      Csv.rows.p(cap, Csv.prep.hd(hdr, first, rest, ts), inf, ts)

# records -> frame with the row cap as a parameter (the entry the tests use with a lowered cap)
def Csv.rows.cap(+cap: U32, rows: List<&2, H.CsvRec>, +hdr: Bool, inf: U32, ts: List<&2, D.DType>) -> E.ResT(C.Frame):
  Csv.rows.n(cap, Csv.lead(rows, hdr), hdr, inf, ts)

def Csv.rows(rows: List<&2, H.CsvRec>, hdr: Bool, inf: U32, ts: List<&2, D.DType>) -> E.ResT(C.Frame):
  Csv.rows.cap(K.Kernel.max_rows(), rows, hdr, inf, ts)

def Csv.parse.a(+cap: U32, ans: H.Ans, hdr: Bool, inf: U32, ts: List<&2, D.DType>) -> E.ResT(C.Frame):
  match ans:
    case H.Rejected{}:
      Fail{E.ParseError{0, "malformed csv"}}
    case H.Parsed{rows}:
      Csv.rows.cap(cap, rows, hdr, inf, ts)

# Strict schema: dtypes by column position, a value that does not parse is a
# ParseError (no lenient nulls); the dtype count must equal the column count.
# cap: the row cap (K.Kernel.max_rows() for every real read; lowered in the tests)
def Csv.parse_with.k(bad: Maybe<&2, E.Err>, +cap: U32, text: String, sep: Char, hdr: Bool, inf: U32, ts: List<&2, D.DType>) -> E.ResT(C.Frame):
  match bad:
    case Some{e}:
      Fail{e}
    case None{}:
      Csv.parse.a(cap, H.parse_sep(Char.to_u32(sep), text), hdr, inf, ts)

def Csv.parse_with.cap(+cap: U32, text: String, opts: CsvOpts, ts: List<&2, D.DType>) -> E.ResT(C.Frame):
  match opts:
    case CsvOpts{+sep, hdr, inf}:
      Csv.parse_with.k(Csv.sep_err(sep), cap, text, sep, hdr, inf, ts)

def Csv.parse_with(text: String, opts: CsvOpts, ts: List<&2, D.DType>) -> E.ResT(C.Frame):
  Csv.parse_with.cap(K.Kernel.max_rows(), text, opts, ts)

# Inferred schema (first infer_rows rows; 0 = all): bool, u32, i32, f32, str.
def Csv.parse(text: String, opts: CsvOpts) -> E.ResT(C.Frame):
  Csv.parse_with(text, opts, Nil{})

# ---- Csv.infer: names + dtypes only ---------------------------------------------------------------------------

def Csv.infer.fields(names: List<&2, String>, cs: List<&2, List<&2, H.CsvCell>>, +k: Nat) -> List<&2, CsvField>:
  match names cs:
    case n <> nt c <> ct:
      CsvField{n, Csv.infer.col(c, k)} <> Csv.infer.fields(nt, ct, k)
    case _ _:
      Nil{}

def Csv.infer.d(+names: List<&2, String>, data: List<&2, H.CsvRec>, +k: U32) -> List<&2, CsvField>:
  Csv.infer.fields(names, Csv.tr(List.reverse(&2, H.CsvRec, Csv.take_rows(U32.to_nat(k), data)), Csv.nils(List.length(&2, String, names))), U32.to_nat(k))

def Csv.infer.p(p: E.Res(Prep), k: U32) -> E.Res(List<&2, CsvField>):
  match p:
    case Fail{e}:
      Fail{e}
    case Done{Prep{names, data}}:
      Done{Csv.infer.d(names, data, k)}

def Csv.infer.n(rows: List<&2, H.CsvRec>, hdr: Bool, k: U32) -> E.Res(List<&2, CsvField>):
  match rows:
    case Nil{}:
      Done{Nil{}}
    case first <> rest:
      Csv.infer.p(Csv.prep.hd(hdr, first, rest, Nil{}), k)

def Csv.infer.rows(rows: List<&2, H.CsvRec>, +hdr: Bool, k: U32) -> E.Res(List<&2, CsvField>):
  Csv.infer.n(Csv.lead(rows, hdr), hdr, k)

def Csv.infer.a(ans: H.Ans, hdr: Bool, inf: U32) -> E.Res(List<&2, CsvField>):
  match ans:
    case H.Rejected{}:
      Fail{E.ParseError{0, "malformed csv"}}
    case H.Parsed{rows}:
      Csv.infer.rows(rows, hdr, Csv.limit(inf))

# The schema Csv.parse would infer, without building columns. The records are checked
# for shape like a read (blank lines skipped, a ragged record is the same ParseError).
def Csv.infer.k(bad: Maybe<&2, E.Err>, text: String, sep: Char, hdr: Bool, inf: U32) -> E.Res(List<&2, CsvField>):
  match bad:
    case Some{e}:
      Fail{e}
    case None{}:
      Csv.infer.a(H.parse_sep(Char.to_u32(sep), text), hdr, inf)

def Csv.infer(text: String, opts: CsvOpts) -> E.Res(List<&2, CsvField>):
  match opts:
    case CsvOpts{+sep, hdr, inf}:
      Csv.infer.k(Csv.sep_err(sep), text, sep, hdr, inf)

# ---- scan_csv: the bounded prefix (DESIGN.md 15.6.4) ------------------------------------------------
# Reads 64 KiB chunks with File.read_at (bytes) until the text holds infer_rows + 1 line
# ends outside quotes that end a non-blank line (every line end for infer_rows = 0), cuts it
# at the last of them and infers on that. Blank lines are not counted: with k > 1 columns
# the reader skips them, so counting them would leave fewer than infer_rows records in the
# prefix and freeze another schema than Csv.read infers (a 1-column file, where a blank line
# is a null record, only reads a little further; the inference takes the first infer_rows).
# A chunk is cut at its last LF (never inside a UTF-8 sequence) and the bytes after it are
# read again with the next chunk; a line longer than the chunk doubles the chunk. The quote
# state is tracked on the bytes: a quote toggles it, a doubled quote toggles it twice. Only
# the prefix is decoded and parsed; no column is built.

# bytes of a chunk, and 1 + the index of its last LF (0: none)
type Ln is Data:
  Ln{n: U32, last: U32}

def Csv.ln(bs: List<&2, U32>, +i: U32, +last: U32) -> Ln:
  match bs:
    case Nil{}:
      Ln{i, last}
    case +b <> t:
      Csv.ln(t, U32.add(i, 1), Bool.pick(U32, U32.is_eq(b, 10), U32.add(i, 1), last))

# what the first c bytes hold, stopping after the need-th line end outside quotes: quote
# state at the end, line ends outside quotes, 1 + the index of the last such line end
# (0: none), and the bytes looked at
type Sc is Data:
  Sc{inq: Bool, cnt: U32, lastq: U32, end: U32}

# act: this byte is among the bytes still wanted
def Csv.sc.inq(+act: Bool, +b: U32, +inq: Bool) -> Bool:
  Bool.pick(Bool, Bool.and(act, U32.is_eq(b, 34)), Bool.not(inq), inq)

# seen: the line so far holds a byte other than CR and LF (a line of CRs is blank to the reader
# too, but for "\r\r\n", a field "\r", the count is only conservative: the scan reads further)
def Csv.sc.out(+act: Bool, +b: U32, +inq: Bool, +seen: Bool) -> Bool:
  Bool.and(Bool.and(act, seen), Bool.and(U32.is_eq(b, 10), Bool.not(inq)))

# an LF outside quotes starts a new line; inside quotes the line is not blank (it holds the quote)
def Csv.sc.seen(+act: Bool, +b: U32, +inq: Bool, +seen: Bool) -> Bool:
  Bool.pick(Bool, act, Bool.pick(Bool, Bool.and(U32.is_eq(b, 10), Bool.not(inq)), False{}, Bool.or(seen, Bool.not(Bool.or(U32.is_eq(b, 10), U32.is_eq(b, 13))))), seen)

def Csv.sc.cnt(+out: Bool, +cnt: U32) -> U32:
  Bool.pick(U32, out, U32.add(cnt, 1), cnt)

def Csv.sc.lq(+out: Bool, +i: U32, +lastq: U32) -> U32:
  Bool.pick(U32, out, U32.add(i, 1), lastq)

def Csv.sc.i(+act: Bool, +i: U32) -> U32:
  Bool.pick(U32, act, U32.add(i, 1), i)

# the bytes still wanted: none once the need-th line end is seen
def Csv.sc.left(+act: Bool, +out: Bool, +cnt: U32, +need: U32, +m: U32) -> U32:
  Bool.pick(U32, Bool.and(act, Bool.not(Bool.and(out, U32.is_ge(U32.add(cnt, 1), need)))), U32.sub(m, 1), 0)

# the walk is over the whole chunk (a stopped walk only skips the rest). A chunk starts after
# an LF, so the line is blank so far unless that LF was inside quotes: seen starts as inq.
def Csv.sc(bs: List<&2, U32>, +m: U32, +i: U32, +inq: Bool, +cnt: U32, +lastq: U32, +need: U32, +seen: Bool) -> Sc:
  match bs:
    case Nil{}:
      Sc{inq, cnt, lastq, i}
    case +b <> t:
      +act = U32.is_gt(m, 0)
      +out = Csv.sc.out(act, b, inq, seen)
      Csv.sc(t, Csv.sc.left(act, out, cnt, need, m), Csv.sc.i(act, i), Csv.sc.inq(act, b, inq), Csv.sc.cnt(out, cnt), Csv.sc.lq(out, i, lastq), need, Csv.sc.seen(act, b, inq, seen))

# UTF-8 decoding of the first m bytes, byte for byte the rules of the runtime's own decoder
# (`io_str`, which `File.read` uses, so the prefix decodes as `Csv.read` decodes the file):
# a lead byte C2..F4 announces 1..3 continuation bytes in the range [lo, hi] (80..BF, but
# A0..BF after E0, 80..9F after ED, 90..BF after F0, 80..8F after F4); any other byte >= 80
# outside a sequence is U+FFFD; a byte that breaks a sequence makes U+FFFD and is then read
# afresh (it is never swallowed: a ',', '"' or LF after a Latin-1 byte stays one); a
# sequence cut by the end is U+FFFD. A chunk is cut after an LF, where no sequence is open.
# need: continuation bytes still due; cp: the code point so far.
def Csv.u8.in(+b: U32, +lo: U32, +hi: U32) -> Bool:
  Bool.and(U32.is_ge(b, lo), U32.is_le(b, hi))

# the byte breaks an open sequence
def Csv.u8.bad(+b: U32, +need: U32, +lo: U32, +hi: U32) -> Bool:
  Bool.and(U32.is_gt(need, 0), Bool.not(Csv.u8.in(b, lo, hi)))

# a lead byte of a 2..4 byte sequence
def Csv.u8.start(+b: U32) -> Bool:
  Csv.u8.in(b, 194, 244)

# continuation bytes a lead byte announces
def Csv.u8.lead(+b: U32) -> U32:
  Bool.pick(U32, U32.is_lt(b, 224), 1, Bool.pick(U32, U32.is_lt(b, 240), 2, 3))

# the payload bits of a lead byte (b & (3F >> need))
def Csv.u8.lcp(+b: U32) -> U32:
  Bool.pick(U32, U32.is_lt(b, 224), U32.and(b, 31), Bool.pick(U32, U32.is_lt(b, 240), U32.and(b, 15), U32.and(b, 7)))

def Csv.u8.lo(+b: U32) -> U32:
  Bool.pick(U32, U32.is_eq(b, 224), 160, Bool.pick(U32, U32.is_eq(b, 240), 144, 128))

def Csv.u8.hi(+b: U32) -> U32:
  Bool.pick(U32, U32.is_eq(b, 237), 159, Bool.pick(U32, U32.is_eq(b, 244), 143, 191))

# the step after the break check: n is the open sequence's need (0 after a break)
def Csv.u8.emit(+b: U32, +n: U32) -> Bool:
  Bool.pick(Bool, U32.is_gt(n, 0), U32.is_eq(n, 1), Bool.not(Csv.u8.start(b)))

def Csv.u8.cp(+b: U32, +n: U32, +cp: U32) -> U32:
  Bool.pick(U32, U32.is_gt(n, 0), U32.add(U32.mul(cp, 64), U32.and(b, 63)), Bool.pick(U32, U32.is_lt(b, 128), b, 65533))

def Csv.u8.need(+b: U32, +n: U32) -> U32:
  Bool.pick(U32, U32.is_gt(n, 0), U32.sub(n, 1), Bool.pick(U32, Csv.u8.start(b), Csv.u8.lead(b), 0))

def Csv.u8.nxcp(+b: U32, +n: U32, +cp: U32) -> U32:
  Bool.pick(U32, U32.is_gt(n, 0), U32.add(U32.mul(cp, 64), U32.and(b, 63)), Bool.pick(U32, Csv.u8.start(b), Csv.u8.lcp(b), 0))

def Csv.u8.nlo(+b: U32, +n: U32) -> U32:
  Bool.pick(U32, U32.is_gt(n, 0), 128, Csv.u8.lo(b))

def Csv.u8.nhi(+b: U32, +n: U32) -> U32:
  Bool.pick(U32, U32.is_gt(n, 0), 191, Csv.u8.hi(b))

# acc: the decoded text so far, newest char first
def Csv.u8.push(emit: Bool, +x: U32, acc: String) -> String:
  match emit:
    case True{}:
      SCon{Chr{x}, acc}
    case False{}:
      acc

# the end: a sequence still open is U+FFFD
def Csv.u8.end(+need: U32, acc: String) -> String:
  String.reverse(Csv.u8.push(U32.is_gt(need, 0), 65533, acc))

# one byte: a break pushes U+FFFD first, then the byte is read with need n (0 after a break)
def Csv.u8.step(+b: U32, +bad: Bool, +need: U32, +cp: U32, acc: String) -> String:
  Csv.u8.push(Csv.u8.emit(b, Bool.pick(U32, bad, 0, need)), Csv.u8.cp(b, Bool.pick(U32, bad, 0, need), cp), Csv.u8.push(bad, 65533, acc))

def Csv.u8.go(m: Nat, bs: List<&2, U32>, +need: U32, +cp: U32, +lo: U32, +hi: U32, acc: String) -> String:
  match m:
    case 0n:
      Csv.u8.end(need, acc)
    case 1n+p:
      match bs:
        case Nil{}:
          Csv.u8.end(need, acc)
        case +b <> t:
          +n = Bool.pick(U32, Csv.u8.bad(b, need, lo, hi), 0, need)
          Csv.u8.go(p, t, Csv.u8.need(b, n), Csv.u8.nxcp(b, n, cp), Csv.u8.nlo(b, n), Csv.u8.nhi(b, n), Csv.u8.step(b, Csv.u8.bad(b, need, lo, hi), need, cp, acc))

def Csv.u8(m: Nat, bs: List<&2, U32>) -> String:
  Csv.u8.go(m, bs, 0, 0, 128, 191, SNil{})

def Csv.drop_bytes(m: Nat, bs: List<&2, U32>) -> List<&2, U32>:
  match m:
    case 0n:
      bs
    case 1n+p:
      match bs:
        case Nil{}:
          Nil{}
        case b <> t:
          Csv.drop_bytes(p, t)

# the scan state between chunks. done: decoded chunks up to the last line end outside quotes
# (newest first); pend: the decoded text after it (newest first).
type PSt is Type:
  PRun{f: File, off: U32, chunk: U32, need: U32, inq: Bool, cnt: U32, done: List<&2, String>, pend: List<&2, String>}
  PEnd{r: E.Res(String)}

def Csv.pre.fin(f: File, text: String) -> IO(PSt):
  do IO<PSt>:
    File.close(f)
    return PEnd{Done{text}}

def Csv.pre.text(xs: List<&2, String>) -> String:
  String.concat(List.reverse(&2, String, xs))

# a chunk whose bytes hold a last line end outside quotes (lq > 0): the pending text and the
# chunk up to it become done; the rest of the chunk (up to c) is pending. Otherwise the
# whole chunk is pending.
def Csv.pre.rest.k(more: Bool, +len: U32, +lq: U32, bs: List<&2, U32>) -> List<&2, String>:
  match more:
    case True{}:
      Csv.u8(U32.to_nat(len), Csv.drop_bytes(U32.to_nat(lq), bs)) <> Nil{}
    case False{}:
      Nil{}

def Csv.pre.split.k(has: Bool, +lq: U32, +c: U32, +bs: List<&2, U32>, done: List<&2, String>, pend: List<&2, String>) -> List<&2, String> & List<&2, String>:
  match has:
    case True{}:
      (Csv.u8(U32.to_nat(lq), bs) <> List.append(&2, String, pend, done), Csv.pre.rest.k(U32.is_lt(lq, c), U32.sub(c, lq), lq, bs))
    case False{}:
      (done, Csv.u8(U32.to_nat(c), bs) <> pend)

def Csv.pre.split(+lq: U32, +c: U32, +bs: List<&2, U32>, done: List<&2, String>, pend: List<&2, String>) -> List<&2, String> & List<&2, String>:
  Csv.pre.split.k(U32.is_gt(lq, 0), lq, c, bs, done, pend)

def Csv.pre.fst(dp: List<&2, String> & List<&2, String>) -> List<&2, String>:
  (done, pend) = dp
  done

# the file ended: everything; else read on
def Csv.pre.c5(dp: List<&2, String> & List<&2, String>, f: File, eof: Bool, +off: U32, +chunk: U32, +need: U32, +inq: Bool, +cnt: U32) -> IO(PSt):
  (done, pend) = dp
  match eof:
    case True{}:
      Csv.pre.fin(f, Csv.pre.text(List.append(&2, String, pend, done)))
    case False{}:
      IO.pure(PSt, PRun{f, off, chunk, need, inq, cnt, done, pend})

# enough line ends: the text is the done chunks
def Csv.pre.c4(f: File, enough: Bool, eof: Bool, +off: U32, +chunk: U32, +need: U32, +inq: Bool, +cnt: U32, dp: List<&2, String> & List<&2, String>) -> IO(PSt):
  match enough:
    case True{}:
      Csv.pre.fin(f, Csv.pre.text(Csv.pre.fst(dp)))
    case False{}:
      Csv.pre.c5(dp, f, eof, off, chunk, need, inq, cnt)

def Csv.pre.c3(f: File, sc: Sc, +bs: List<&2, U32>, eof: Bool, +off: U32, +chunk: U32, +need: U32, done: List<&2, String>, pend: List<&2, String>) -> IO(PSt):
  match sc:
    case Sc{inq, +cnt, lq, +c}:
      Csv.pre.c4(f, U32.is_ge(cnt, need), eof, U32.add(off, c), chunk, need, inq, cnt, Csv.pre.split(lq, c, bs, done, pend))

# c: the bytes consumed (everything at the end of the file, else up to the last LF)
def Csv.pre.c2b(f: File, empty: Bool, stuck: Bool, +bs: List<&2, U32>, +c: U32, eof: Bool, +off: U32, +chunk: U32, +need: U32, +inq: Bool, +cnt: U32, done: List<&2, String>, pend: List<&2, String>) -> IO(PSt):
  match empty:
    case True{}:
      Csv.pre.fin(f, Csv.pre.text(List.append(&2, String, pend, done)))
    case False{}:
      match stuck:
        case True{}:
          IO.pure(PSt, PRun{f, off, U32.mul(chunk, 2), need, inq, cnt, done, pend})
        case False{}:
          Csv.pre.c3(f, Csv.sc(bs, c, 0, inq, cnt, 0, need, inq), bs, eof, off, chunk, need, done, pend)

def Csv.pre.c2(f: File, ln: Ln, +bs: List<&2, U32>, +off: U32, +chunk: U32, +need: U32, +inq: Bool, +cnt: U32, done: List<&2, String>, pend: List<&2, String>) -> IO(PSt):
  match ln:
    case Ln{+n, +last}:
      Csv.pre.c2b(f, U32.is_eq(n, 0), Bool.and(U32.is_ge(n, chunk), U32.is_eq(last, 0)), bs, Bool.pick(U32, U32.is_lt(n, chunk), n, last), U32.is_lt(n, chunk), off, chunk, need, inq, cnt, done, pend)

def Csv.pre.res(f: File, res: Result<&1, &1, U32 & String, List<&2, U32>>, +off: U32, +chunk: U32, +need: U32, +inq: Bool, +cnt: U32, done: List<&2, String>, pend: List<&2, String>) -> IO(PSt):
  match res:
    case Fail{(code, msg)}:
      do IO<PSt>:
        File.close(f)
        return PEnd{Fail{E.IoError{code, msg}}}
    case Done{+bs}:
      Csv.pre.c2(f, Csv.ln(bs, 0, 0), bs, off, chunk, need, inq, cnt, done, pend)

def Csv.pre.got(r: File & Result<&1, &1, U32 & String, List<&2, U32>>, +off: U32, +chunk: U32, +need: U32, +inq: Bool, +cnt: U32, done: List<&2, String>, pend: List<&2, String>) -> IO(PSt):
  (f, res) = r
  Csv.pre.res(f, res, off, chunk, need, inq, cnt, done, pend)

def Csv.pre.step(st: PSt) -> IO(PSt):
  match st:
    case PEnd{r}:
      IO.pure(PSt, PEnd{r})
    case PRun{f, +off, +chunk, need, inq, cnt, done, pend}:
      do IO<PSt>:
        r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_at(f, off, chunk)
        Csv.pre.got(r, off, chunk, need, inq, cnt, done, pend)

# one step per chunk read; the fuel (file size + 2) can never run out before the file does
def Csv.pre.loop(fuel: Nat, st: PSt) -> IO(PSt):
  match fuel:
    case 0n:
      IO.pure(PSt, st)
    case 1n+p:
      match st:
        case PEnd{r}:
          IO.pure(PSt, PEnd{r})
        case PRun{f, off, chunk, need, inq, cnt, done, pend}:
          do IO<PSt>:
            st2 : PSt <- Csv.pre.step(PRun{f, off, chunk, need, inq, cnt, done, pend})
            Csv.pre.loop(p, st2)

def Csv.pre.fields(r: E.Res(String), opts: CsvOpts) -> E.Res(List<&2, CsvField>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{text}:
      Csv.infer(text, opts)

# an unfinished scan (not reachable) closes its file
def Csv.pre.out(st: PSt, opts: CsvOpts) -> IO(E.Res(List<&2, CsvField>)):
  match st:
    case PEnd{r}:
      IO.pure(E.Res(List<&2, CsvField>), Csv.pre.fields(r, opts))
    case PRun{f, off, chunk, need, inq, cnt, done, pend}:
      do IO<E.Res(List<&2, CsvField>)>:
        File.close(f)
        return Fail{E.InvalidOperation{"scan_csv: prefix read did not finish"}}

# line ends to see: infer_rows + 1 (every line end for infer_rows = 0)
def Csv.pre.need(+inf: U32) -> U32:
  Bool.pick(U32, Bool.or(U32.is_eq(inf, 0), U32.is_ge(inf, 4294967295)), 4294967295, U32.add(inf, 1))

def Csv.pre.sized(+opts: CsvOpts, +chunk: U32, f: File, res: Result<&1, &1, U32 & String, U32>) -> IO(E.Res(List<&2, CsvField>)):
  match res:
    case Done{+n}:
      do IO<E.Res(List<&2, CsvField>)>:
        st : PSt <- Csv.pre.loop(Nat.add(U32.to_nat(n), 2n), PRun{f, 0, chunk, Csv.pre.need(Csv.infer_rows(opts)), False{}, 0, Nil{}, Nil{}})
        Csv.pre.out(st, opts)
    case Fail{(code, msg)}:
      do IO<E.Res(List<&2, CsvField>)>:
        File.close(f)
        return Fail{E.IoError{code, msg}}

def Csv.pre.size(opts: CsvOpts, chunk: U32, r: File & Result<&1, &1, U32 & String, U32>) -> IO(E.Res(List<&2, CsvField>)):
  (f, res) = r
  Csv.pre.sized(opts, chunk, f, res)

def Csv.pre.opened(opts: CsvOpts, chunk: U32, o: Result<&1, &1, U32 & String, File>) -> IO(E.Res(List<&2, CsvField>)):
  match o:
    case Done{f}:
      do IO<E.Res(List<&2, CsvField>)>:
        r : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
        Csv.pre.size(opts, chunk, r)
    case Fail{(code, msg)}:
      IO.pure(E.Res(List<&2, CsvField>), Fail{E.IoError{code, msg}})

# the schema scan_csv freezes: names and dtypes inferred from a bounded prefix, reading
# `chunk` bytes at a time (tests use tiny chunks; Csv.scan_fields uses 64 KiB)
def Csv.scan_fields_open(path: String, opts: CsvOpts, chunk: U32) -> IO(E.Res(List<&2, CsvField>)):
  do IO<E.Res(List<&2, CsvField>)>:
    o : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    Csv.pre.opened(opts, chunk, o)

# a refused separator is answered before the file is opened
def Csv.scan_fields_chk(bad: Maybe<&2, E.Err>, path: String, opts: CsvOpts, chunk: U32) -> IO(E.Res(List<&2, CsvField>)):
  match bad:
    case Some{e}:
      IO.pure(E.Res(List<&2, CsvField>), Fail{e})
    case None{}:
      Csv.scan_fields_open(path, opts, chunk)

def Csv.scan_fields_with(path: String, +opts: CsvOpts, chunk: U32) -> IO(E.Res(List<&2, CsvField>)):
  match opts:
    case CsvOpts{+sep, hdr, inf}:
      Csv.scan_fields_chk(Csv.sep_err(sep), path, CsvOpts{sep, hdr, inf}, chunk)

def Csv.scan_fields(path: String, opts: CsvOpts) -> IO(E.Res(List<&2, CsvField>)):
  Csv.scan_fields_with(path, opts, 65536)

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

# the empty string is quoted too (an empty field is a null; DESIGN.md 15.6.1)
def Csv.quote(+s: String, +sep: U32) -> String:
  Csv.quote.k(Bool.or(String.is_empty(s), Csv.needs_q(s, sep, False{})), s)

def Csv.f32(x: F32, prec: Maybe<&2, U32>) -> String:
  match prec:
    case None{}:
      F32.show(x)
    case Some{p}:
      F.Fmt.fixed(x, p)

# a number or bool is never empty and holds no quote, CR or LF, but it can hold the
# separator ('.', '-', 'e', a digit, a letter of true/false/nan/inf): then it is quoted,
# so every dtype round-trips under any separator (DESIGN.md 15.6.5)
def Csv.quote_val(+s: String, +sep: U32) -> String:
  Csv.quote.k(Csv.needs_q(s, sep, False{}), s)

# null: empty; bool: true/false; floats: shortest digits, or `prec` decimals
def Csv.cell(sc: D.Scalar, prec: Maybe<&2, U32>, +sep: U32) -> String:
  match sc:
    case D.SNull{}:
      ""
    case D.SF32{x}:
      Csv.quote_val(Csv.f32(x, prec), sep)
    case D.SStr{s}:
      Csv.quote(s, sep)
    case other:
      Csv.quote_val(D.Scalar.show(other), sep)

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

def Csv.render.txt(hdr: Bool, hd: String, body: String) -> String:
  match hdr:
    case True{}:
      hd ++ "\n" ++ body
    case False{}:
      body

def Csv.render.t(+h: U32, hdr: Bool, hd: String, r: List<&1, C.Named> & List<&2, String>) -> C.Frame & String:
  (cols, lines) = r
  (C.Frame{h, cols}, Csv.render.txt(hdr, hd, String.concat(lines)))

def Csv.render.m(f: C.Frame, names: List<&2, String>, hdr: Bool, prec: Maybe<&2, U32>, +sep: U32, +sp: String) -> C.Frame & String:
  match f:
    case C.Frame{+h, cols}:
      Csv.render.t(h, hdr, Csv.header(names, sep, sp), Csv.lines(cols, h, prec, sep, sp))

def Csv.render.k(r: C.Frame & List<&2, String>, hdr: Bool, prec: Maybe<&2, U32>, sep: U32, sp: String) -> C.Frame & String:
  (f, names) = r
  Csv.render.m(f, names, hdr, prec, sep, sp)

def Csv.render.w(f: C.Frame, +sep: Char, hdr: Bool, prec: Maybe<&2, U32>) -> C.Frame & String:
  Csv.render.k(C.Frame.names(f), hdr, prec, Char.to_u32(sep), SCon{sep, SNil{}})

# One line per row ("\n" line ends) after the header line (include_header); nulls are empty
# fields, a valid empty string is `""`. Floats print with F32.show when float_precision is
# None, else with exactly that many decimals.
def Csv.render_with(f: C.Frame, w: CsvWriteOpts) -> C.Frame & String:
  match w:
    case CsvWriteOpts{sep, hdr, prec}:
      Csv.render.w(f, sep, hdr, prec)

def Csv.render(f: C.Frame, prec: Maybe<&2, U32>) -> C.Frame & String:
  Csv.render_with(f, CsvWriteOpts{',', True{}, prec})

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

# the write refused for its separator: the frame comes back with an IoError value (EINVAL, 22);
# the facade checks first and answers InvalidOperation (DF.write_csv_opts)
def Csv.write_chk(bad: Maybe<&2, E.Err>, f: C.Frame, path: String, w: CsvWriteOpts) -> IO(C.Frame & Result<&1, &1, U32 & String, Unit>):
  match bad:
    case Some{e}:
      IO.pure(C.Frame & Result<&1, &1, U32 & String, Unit>, (f, Fail{(22, E.Err.show(e))}))
    case None{}:
      Csv.write.go(Csv.render_with(f, w), path)

def Csv.write_sep(w: CsvWriteOpts) -> Maybe<&2, E.Err>:
  match w:
    case CsvWriteOpts{sep, hdr, prec}:
      Csv.sep_err(sep)

# renders with the options and writes the file; the frame comes back
def Csv.write_with(f: C.Frame, path: String, +w: CsvWriteOpts) -> IO(C.Frame & Result<&1, &1, U32 & String, Unit>):
  Csv.write_chk(Csv.write_sep(w), f, path, w)

# renders with F32.show (Csv.render(f, None{})) and writes the file; the frame comes back
def Csv.write(f: C.Frame, path: String) -> IO(C.Frame & Result<&1, &1, U32 & String, Unit>):
  Csv.write_with(f, path, Csv.write_default())
