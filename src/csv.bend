# src/csv.bend -- CSV reading (type inference, explicit schemas), rendering, files.
# DESIGN.md 4.11 and 15.6. Reading goes through src/csvparse.bend (a fork of the hub
# parser that keeps quotedness and physical line numbers), writing is ours.
# Reading is the M4 streaming reader below (pieces of a file -> records -> typed column builders,
# Str cells coded as they are produced). Strings are only ever appended on their right-nested side
# (Csv.join). Per-row loops are stack safe in the interpreter (JS lane: ~2^15 nested non-tail
# calls): tail loops, or 16 rows per call (Csv.cells, Csv.zip, Csv.join; IMPLEMENTING.md "M1 cleanup").
# Idioms: helpers above callers; a match on a parameter; loop state in parameters.
import Base
import ./csvparse.bend as H
import ./dtype.bend as D
import ./err.bend as E
import ./kernels.bend as K
import ./column.bend as C
import ./strs.bend as ST
import ./fmt.bend as F
import ./csvprod.bend as P
import ./csvlane.bend as L
import ./chunks.bend as CH

type CsvOpts is Data:
  CsvOpts{sep: Char, has_header: Bool, infer_rows: U32}

# write options: separator, header line or not, F32 with this many decimals (None: shortest digits)
type CsvWriteOpts is Data:
  CsvWriteOpts{sep: Char, include_header: Bool, float_precision: Maybe<&2, U32>}

# an inferred column: Csv.infer answers these (the schema layer maps them to Field)
type CsvField is Data:
  CsvField{name: String, dtype: D.DType}

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

# ---- columns ------------------------------------------------------------------------------------

def Csv.col.err(+name: String, +t: D.DType, +text: String, +line: U32) -> E.ResT(C.Named):
  Fail{E.ParseError{line, "column " ++ name ++ ": cannot parse \"" ++ text ++ "\" as " ++ D.DType.show(t)}}

def Csv.cols.k(a: E.ResT(C.Named), b: E.ResT(List<&1, C.Named>)) -> E.ResT(List<&1, C.Named>):
  match a b:
    case Done{x} Done{y}:
      Done{x <> y}
    case Fail{e} _:
      Fail{e}
    case _ Fail{e}:
      Fail{e}

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

def Csv.take_rows.go(k: Nat, rows: List<&2, H.CsvRec>, acc: List<&2, H.CsvRec>) -> List<&2, H.CsvRec>:
  match k:
    case 0n:
      acc
    case 1n+p:
      match rows:
        case Nil{}:
          acc
        case r <> rt:
          Csv.take_rows.go(p, rt, r <> acc)

# the first k records (k may be every record: tail recursive)
def Csv.take_rows(k: Nat, rows: List<&2, H.CsvRec>) -> List<&2, H.CsvRec>:
  List.reverse(&2, H.CsvRec, Csv.take_rows.go(k, rows, Nil{}))

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

def Csv.drop.k(b: Bool, r: H.CsvRec, acc: List<&2, H.CsvRec>) -> List<&2, H.CsvRec>:
  match b:
    case True{}:
      acc
    case False{}:
      r <> acc

def Csv.drop.r(r: H.CsvRec, acc: List<&2, H.CsvRec>) -> List<&2, H.CsvRec>:
  match r:
    case H.CsvRec{+l, +cs}:
      Csv.drop.k(Csv.is_blank(cs), H.CsvRec{l, cs}, acc)

def Csv.drop_blank.go(rows: List<&2, H.CsvRec>, acc: List<&2, H.CsvRec>) -> List<&2, H.CsvRec>:
  match rows:
    case Nil{}:
      acc
    case r <> rt:
      Csv.drop_blank.go(rt, Csv.drop.r(r, acc))

# some record is blank (a tail walk that allocates nothing: the usual file has none)
def Csv.any_blank.r(r: H.CsvRec) -> Bool:
  match r:
    case H.CsvRec{l, cs}:
      Csv.is_blank(cs)

def Csv.any_blank(rows: List<&2, H.CsvRec>, found: Bool) -> Bool:
  match rows:
    case Nil{}:
      found
    case r <> rt:
      Csv.any_blank(rt, Bool.or(found, Csv.any_blank.r(r)))

def Csv.drop_blank.k(any: Bool, rows: List<&2, H.CsvRec>) -> List<&2, H.CsvRec>:
  match any:
    case True{}:
      List.reverse(&2, H.CsvRec, Csv.drop_blank.go(rows, Nil{}))
    case False{}:
      rows

def Csv.drop_blank(+rows: List<&2, H.CsvRec>) -> List<&2, H.CsvRec>:
  Csv.drop_blank.k(Csv.any_blank(rows, False{}), rows)

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

# the cell count of the first non-blank record, 1 when every record is blank (go: the records
# so far were all blank; the walk stops at the first non-blank one). Without a header a leading
# blank line is data, not the width: `\n1,2\n` has 2 columns and its blank line is skipped (k > 1)
def Csv.width.k(blank: Bool, +n: Nat, w: Nat) -> Nat:
  match blank:
    case True{}:
      w
    case False{}:
      n

def Csv.width(rows: List<&2, H.CsvRec>, +go: Bool) -> Nat:
  match rows go:
    case Nil{} _:
      1n
    case H.CsvRec{l, +cs} <> rt True{}:
      Csv.width.k(Csv.is_blank(cs), List.length(&2, H.CsvCell, cs), Csv.width(rt, Csv.is_blank(cs)))
    case other False{}:
      0n

def Csv.prep.gw(+rows: List<&2, H.CsvRec>, +ts: List<&2, D.DType>) -> E.Res(Prep):
  Csv.prep.d(Csv.gen_names(Csv.width(rows, True{}), 0n), rows, ts)

# no header: the first record is data, the names are column_0 .. (the width of the first
# non-blank record)
def Csv.prep.gn(first: H.CsvRec, rest: List<&2, H.CsvRec>, +ts: List<&2, D.DType>) -> E.Res(Prep):
  Csv.prep.gw(first <> rest, ts)

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

# no records (an empty file, or one of blank lines before a header): the (0, 0) frame, unless
# dtypes were given: they must cover every column, and there are none (15.6.3)
def Csv.rows.none(bad: Maybe<&2, E.Err>) -> E.ResT(C.Frame):
  match bad:
    case Some{e}:
      Fail{e}
    case None{}:
      Done{C.Frame.empty()}

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

# The rendering loops run once per row. The interpreter (the JS lane) overflows its stack at ~2^15
# nested non-tail calls (IMPLEMENTING.md, "M1 diff fixes"), and an accumulate-then-reverse tail loop
# costs ~20% of the native write of 1M rows (3 more passes per column), so each loop handles 16 rows
# per call: depth n / 16 (500k rows fit), the native speed is unchanged. The `1` variants finish
# the last < 16 rows.
def Csv.cells1(xs: List<&2, D.Scalar>, +prec: Maybe<&2, U32>, +sep: U32) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> tl:
      Csv.cell(h, prec, sep) <> Csv.cells1(tl, prec, sep)

def Csv.cells(xs: List<&2, D.Scalar>, +prec: Maybe<&2, U32>, +sep: U32) -> List<&2, String>:
  match xs:
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> x7 <> x8 <> x9 <> x10 <> x11 <> x12 <> x13 <> x14 <> x15 <> tl:
      Csv.cell(x0, prec, sep) <> Csv.cell(x1, prec, sep) <> Csv.cell(x2, prec, sep) <> Csv.cell(x3, prec, sep) <> Csv.cell(x4, prec, sep) <> Csv.cell(x5, prec, sep) <> Csv.cell(x6, prec, sep) <> Csv.cell(x7, prec, sep) <> Csv.cell(x8, prec, sep) <> Csv.cell(x9, prec, sep) <> Csv.cell(x10, prec, sep) <> Csv.cell(x11, prec, sep) <> Csv.cell(x12, prec, sep) <> Csv.cell(x13, prec, sep) <> Csv.cell(x14, prec, sep) <> Csv.cell(x15, prec, sep) <> Csv.cells(tl, prec, sep)
    case other:
      Csv.cells1(other, prec, sep)

# x ++ y for each pair (right-nested appends: linear)
def Csv.zip1(a: List<&2, String>, b: List<&2, String>) -> List<&2, String>:
  match a b:
    case x <> xt y <> yt:
      (x ++ y) <> Csv.zip1(xt, yt)
    case _ _:
      Nil{}

def Csv.zip(a: List<&2, String>, b: List<&2, String>) -> List<&2, String>:
  match a b:
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> x7 <> x8 <> x9 <> x10 <> x11 <> x12 <> x13 <> x14 <> x15 <> xt y0 <> y1 <> y2 <> y3 <> y4 <> y5 <> y6 <> y7 <> y8 <> y9 <> y10 <> y11 <> y12 <> y13 <> y14 <> y15 <> yt:
      (x0 ++ y0) <> (x1 ++ y1) <> (x2 ++ y2) <> (x3 ++ y3) <> (x4 ++ y4) <> (x5 ++ y5) <> (x6 ++ y6) <> (x7 ++ y7) <> (x8 ++ y8) <> (x9 ++ y9) <> (x10 ++ y10) <> (x11 ++ y11) <> (x12 ++ y12) <> (x13 ++ y13) <> (x14 ++ y14) <> (x15 ++ y15) <> Csv.zip(xt, yt)
    case p q:
      Csv.zip1(p, q)

# the separator, x, y for each pair. The separator is passed as a U32, not as a String: a `+pre: String`
# dup'd once per row overflowed the interpreter's stack at 100,000 rows, however many rows a call took
def Csv.zip_pre1(a: List<&2, String>, b: List<&2, String>, +sep: U32) -> List<&2, String>:
  match a b:
    case x <> xt y <> yt:
      SCon{Chr{sep}, x ++ y} <> Csv.zip_pre1(xt, yt, sep)
    case _ _:
      Nil{}

def Csv.zip_pre(a: List<&2, String>, b: List<&2, String>, +sep: U32) -> List<&2, String>:
  match a b:
    case x0 <> x1 <> x2 <> x3 <> x4 <> x5 <> x6 <> x7 <> x8 <> x9 <> x10 <> x11 <> x12 <> x13 <> x14 <> x15 <> xt y0 <> y1 <> y2 <> y3 <> y4 <> y5 <> y6 <> y7 <> y8 <> y9 <> y10 <> y11 <> y12 <> y13 <> y14 <> y15 <> yt:
      SCon{Chr{sep}, x0 ++ y0} <> SCon{Chr{sep}, x1 ++ y1} <> SCon{Chr{sep}, x2 ++ y2} <> SCon{Chr{sep}, x3 ++ y3} <> SCon{Chr{sep}, x4 ++ y4} <> SCon{Chr{sep}, x5 ++ y5} <> SCon{Chr{sep}, x6 ++ y6} <> SCon{Chr{sep}, x7 ++ y7} <> SCon{Chr{sep}, x8 ++ y8} <> SCon{Chr{sep}, x9 ++ y9} <> SCon{Chr{sep}, x10 ++ y10} <> SCon{Chr{sep}, x11 ++ y11} <> SCon{Chr{sep}, x12 ++ y12} <> SCon{Chr{sep}, x13 ++ y13} <> SCon{Chr{sep}, x14 ++ y14} <> SCon{Chr{sep}, x15 ++ y15} <> Csv.zip_pre(xt, yt, sep)
    case p q:
      Csv.zip_pre1(p, q, sep)

# n lines "\n" (the end of each row)
def Csv.nls(n: Nat, acc: List<&2, String>) -> List<&2, String>:
  match n:
    case 0n:
      acc
    case 1n+p:
      Csv.nls(p, "\n" <> acc)

# the lines, in row order, joined by right-nested appends (each copies one short line), 16 lines per call
def Csv.join1(lines: List<&2, String>) -> String:
  match lines:
    case Nil{}:
      ""
    case h <> tl:
      h ++ Csv.join1(tl)

def Csv.join(lines: List<&2, String>) -> String:
  match lines:
    case l0 <> l1 <> l2 <> l3 <> l4 <> l5 <> l6 <> l7 <> l8 <> l9 <> l10 <> l11 <> l12 <> l13 <> l14 <> l15 <> tl:
      l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7 ++ l8 ++ l9 ++ l10 ++ l11 ++ l12 ++ l13 ++ l14 ++ l15 ++ Csv.join(tl)
    case other:
      Csv.join1(other)

def Csv.col_cells.b(+name: String, prec: Maybe<&2, U32>, +sep: U32, r: C.Column & List<&2, D.Scalar>) -> C.Named & List<&2, String>:
  (c, xs) = r
  (C.Named{name, c}, Csv.cells(xs, prec, sep))

def Csv.col_cells(nc: C.Named, +h: U32, prec: Maybe<&2, U32>, sep: U32) -> C.Named & List<&2, String>:
  match nc:
    case C.Named{name, col}:
      Csv.col_cells.b(name, prec, sep, C.Column.scalars(col, 0, h))

# the lines of columns 1.. : every cell is preceded by the separator, the line ends in "\n"
def Csv.rest.k(sep: U32, r1: C.Named & List<&2, String>, r2: List<&1, C.Named> & List<&2, String>) -> List<&1, C.Named> & List<&2, String>:
  (nc, cells) = r1
  (cols, lines) = r2
  (nc <> cols, Csv.zip_pre(cells, lines, sep))

def Csv.rest(cols: List<&1, C.Named>, +h: U32, +prec: Maybe<&2, U32>, +sep: U32) -> List<&1, C.Named> & List<&2, String>:
  match cols:
    case Nil{}:
      (Nil{}, Csv.nls(U32.to_nat(h), Nil{}))
    case nc <> t:
      Csv.rest.k(sep, Csv.col_cells(nc, h, prec, sep), Csv.rest(t, h, prec, sep))

def Csv.lines.k(r1: C.Named & List<&2, String>, r2: List<&1, C.Named> & List<&2, String>) -> List<&1, C.Named> & List<&2, String>:
  (nc, cells) = r1
  (cols, lines) = r2
  (nc <> cols, Csv.zip(cells, lines))

def Csv.lines(cols: List<&1, C.Named>, +h: U32, +prec: Maybe<&2, U32>, +sep: U32) -> List<&1, C.Named> & List<&2, String>:
  match cols:
    case Nil{}:
      (Nil{}, Nil{})
    case nc <> t:
      Csv.lines.k(Csv.col_cells(nc, h, prec, sep), Csv.rest(t, h, prec, sep))

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
  (C.Frame{h, cols}, Csv.render.txt(hdr, hd, Csv.join(lines)))

def Csv.render.m(f: C.Frame, names: List<&2, String>, hdr: Bool, prec: Maybe<&2, U32>, +sep: U32, +sp: String) -> C.Frame & String:
  match f:
    case C.Frame{+h, cols}:
      Csv.render.t(h, hdr, Csv.header(names, sep, sp), Csv.lines(cols, h, prec, sep))

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

# ---- M4: the streaming reader (plans/M_01.txt section 5) ------------------------------------------
# A file is read in pieces of at most `chunk` bytes, each ending after its last LF: the last 4 KiB
# of the chunk are probed with File.read_at for that LF (a chunk without one doubles), then the
# piece is read with File.read, so the runtime's own UTF-8 decoder (as before M4) sees whole
# sequences. The resumable parser (H.step: its state crosses piece ends, so a quoted field may
# hold line ends across them) turns the piece into records, and one walk per piece (Csv.tw)
# hands their cells to typed column builders: Str cells are coded as they are produced
# (Dictionary: one hash probe per cell), numbers are read from the field text into word / f32
# buffers, each piece filling arrays of its own that are concatenated once at the end. There is
# no list of every record and no per-column Scalar list. What remains transient per piece: its
# text (a cons list of characters), its records and their cells (and, while inference runs, the
# first `infer_rows` records' cells; `infer_rows = 0` keeps every cell until the end).
# A string (Csv.parse_with) is the same machinery fed as one piece.
#
# The default piece is 64 MiB (Csv.chunk), not the plan's 1 MiB: natively, 1 MiB pieces made the
# 41 MB read ~3x slower (the allocator's free lists hand the next piece scattered memory; per
# piece time grew from 65 to ~200 ms, IMPLEMENTING.md M4), while one piece is faster than the old
# whole-file reader. So a file under 64 MiB is still read as one transient string; a larger file
# streams. Csv.read_full takes any chunk size (tests/csv_chunks.bend reads with 1..64 bytes).
def Csv.chunk() -> U32:
  67108864

# Order of errors (as before M4): malformed quoting anywhere; no records -> the empty frame or the
# dtype-count error; the first ragged record; the dtype count; the row cap; then the first column
# (in column order) holding a cell that does not parse, at its first such row.

# a column's first cell that does not parse: the record's line and the field's text
type BadL is Data:
  BadL{line: U32, text: String}

# EncAuto keeps a Dictionary while its entries stay within max(16384, rows / 64), checked at every
# cell (DESIGN.md 14 M4: the threshold measured on 1M-row columns: up to ~1 % distinct the
# Dictionary costs the parse <= 5 % and wins every operation; at 10 % it costs the parse ~33 %);
# past it the column falls back to Raw at once, decoding the rows coded so far (the only rescan:
# of a prefix, at most ~16k rows when the column is distinct from the start). EncAutoAt{floor,
# den} is the same with other numbers (tests); EncDict never falls back.
def Csv.dict_over.at(+k: U32, +n: U32, +floor: U32, +den: U32) -> Bool:
  U32.is_gt(k, U32.max(floor, U32.div(n, U32.max(den, 1))))

def Csv.dict_over(enc: ST.StrEnc, +k: U32, +n: U32) -> Bool:
  match enc:
    case ST.EncAuto{}:
      Csv.dict_over.at(k, n, 16384, 64)
    case ST.EncAutoAt{+floor, +den}:
      Csv.dict_over.at(k, n, floor, den)
    case _:
      False{}

# a word cell: trimmed text, empty is null, else the dtype's reader
def Csv.rd.bool(+s: String) -> Maybe<&2, U32>:
  Bool.pick(Maybe<&2, U32>, Csv.is_bool(s), Some{Bool.to_u32(Bool.or(String.eq(s, "true"), String.eq(s, "True")))}, None{})

def Csv.rd.i32(m: Maybe<&2, D.I32>) -> Maybe<&2, U32>:
  match m:
    case Some{D.I32{x}}:
      Some{x}
    case None{}:
      None{}

def Csv.rd.w(t: D.DType, +s: String) -> Maybe<&2, U32>:
  match t:
    case D.TI32{}:
      Csv.rd.i32(D.I32.read(s))
    case D.TBool{}:
      Csv.rd.bool(s)
    case _:
      U32.read(s)

def Csv.badk(bad: Maybe<&2, BadL>, +line: U32, +f: String) -> Maybe<&2, BadL>:
  match bad:
    case Some{x}:
      Some{x}
    case None{}:
      Some{BadL{line, f}}

# ---- one chunk of one column: a part of m rows in 2^depth_for(m) slots ---------------------------
# Each chunk's cells fill small arrays of their own (one tight loop per column, every column of a
# chunk in parallel); the column is the parts concatenated once, at the end. (A single growing
# column array, set cell by cell between the parser's allocations, was ~3x slower natively: the
# path-copying sets lost all locality, IMPLEMENTING.md M4.)
type Part is Type:
  PW{m: U32, a: Array<U32>, vm: Array<U32>}
  PF{m: U32, a: Array<F32>, vm: Array<U32>}
  PS{m: U32, a: Array<String>, vm: Array<U32>}
  PD{m: U32, c: Array<U32>, vm: Array<U32>}

# loop states (nulls and the first bad cell first: Data before the arrays)
type WS is Type:
  WS{nulls: U32, bad: Maybe<&2, BadL>, a: Array<U32>, vm: Array<U32>}

type FS is Type:
  FS{nulls: U32, bad: Maybe<&2, BadL>, a: Array<F32>, vm: Array<U32>}

type SS is Type:
  SS{nulls: U32, a: Array<String>, vm: Array<U32>}

# k: the dictionary's entries so far
type DS is Type:
  DS{nulls: U32, k: U32, c: Array<U32>, vm: Array<U32>, dict: ST.Dict}

# where a Dictionary chunk loop stopped: every cell coded, or (EncAuto past the threshold at row
# i) switched to Raw with the cells left
type DR is Type:
  DDone{st: DS}
  DSwitch{i: U32, rest: List<&2, H.CsvCell>, st: DS}

def Ws.r(+i: U32, +line: U32, +f: String, st: WS, m: Maybe<&2, U32>) -> WS:
  match st m:
    case WS{nulls, bad, a, vm} Some{x}:
      WS{nulls, bad, Array.set(U32, a, i, x), Array.set(U32, vm, i, 1)}
    case WS{nulls, bad, a, vm} None{}:
      WS{U32.inc(nulls), Csv.badk(bad, line, f), a, vm}

def Ws.e(empty: Bool, +t: D.DType, +i: U32, +line: U32, +f: String, +s: String, st: WS) -> WS:
  match empty st:
    case True{} WS{nulls, bad, a, vm}:
      WS{U32.inc(nulls), bad, a, vm}
    case False{} other:
      Ws.r(i, line, f, other, Csv.rd.w(t, s))

def Ws.cell(+t: D.DType, +i: U32, +line: U32, c: H.CsvCell, st: WS) -> WS:
  match c:
    case H.CsvCell{+f, q}:
      +s = String.trim(f)
      Ws.e(String.is_empty(s), t, i, line, f, s, st)

def Ws.go(cs: List<&2, H.CsvCell>, ls: List<&2, U32>, +t: D.DType, +i: U32, st: WS) -> WS:
  match cs ls:
    case c <> ct l <> lt:
      Ws.go(ct, lt, t, U32.inc(i), Ws.cell(t, i, l, c, st))
    case _ _:
      st

def Fs.r(+i: U32, +line: U32, +f: String, st: FS, m: Maybe<&2, F32>) -> FS:
  match st m:
    case FS{nulls, bad, a, vm} Some{x}:
      FS{nulls, bad, Array.set(F32, a, i, x), Array.set(U32, vm, i, 1)}
    case FS{nulls, bad, a, vm} None{}:
      FS{U32.inc(nulls), Csv.badk(bad, line, f), a, vm}

def Fs.e(empty: Bool, +i: U32, +line: U32, +f: String, +s: String, st: FS) -> FS:
  match empty st:
    case True{} FS{nulls, bad, a, vm}:
      FS{U32.inc(nulls), bad, a, vm}
    case False{} other:
      Fs.r(i, line, f, other, F32.read(s))

def Fs.cell(+i: U32, +line: U32, c: H.CsvCell, st: FS) -> FS:
  match c:
    case H.CsvCell{+f, q}:
      +s = String.trim(f)
      Fs.e(String.is_empty(s), i, line, f, s, st)

def Fs.go(cs: List<&2, H.CsvCell>, ls: List<&2, U32>, +i: U32, st: FS) -> FS:
  match cs ls:
    case c <> ct l <> lt:
      Fs.go(ct, lt, U32.inc(i), Fs.cell(i, l, c, st))
    case _ _:
      st

# a str cell: quoted, or unquoted and non-empty, is valid (15.6.1); a null's text is ""
def Csv.sok(+q: Bool, +f: String) -> U32:
  Bool.to_u32(Bool.or(q, Bool.not(String.is_empty(f))))

def Ss.cell(+i: U32, c: H.CsvCell, st: SS) -> SS:
  match c st:
    case H.CsvCell{+f, +q} SS{+nulls, a, vm}:
      +ok = Csv.sok(q, f)
      SS{U32.add(nulls, U32.sub(1, ok)), Array.set(String, a, i, f), Array.set(U32, vm, i, ok)}

def Ss.go(cs: List<&2, H.CsvCell>, +i: U32, st: SS) -> SS:
  match cs:
    case c <> ct:
      Ss.go(ct, U32.inc(i), Ss.cell(i, c, st))
    case Nil{}:
      st

# go on coding: not (EncAuto and the entries past Csv.dict_over for the rows so far)
def Ds.put(+i: U32, +n0: U32, +auto: ST.StrEnc, +nulls: U32, +k: U32, c: Array<U32>, vm: Array<U32>, r: ST.Dict & U32) -> Bool & DS:
  (dict, +code) = r
  +k2 = Bool.pick(U32, U32.is_eq(code, k), U32.inc(k), k)
  (Bool.not(Csv.dict_over(auto, k2, U32.add(n0, U32.inc(i)))), DS{nulls, k2, Array.set(U32, c, i, code), vm, dict})

# a Dictionary cell: its code (a null's text is "", code 0)
def Ds.cell(c: H.CsvCell, +i: U32, +n0: U32, +auto: ST.StrEnc, st: DS) -> Bool & DS:
  match c st:
    case H.CsvCell{+f, +q} DS{+nulls, +k, codes, vm, dict}:
      +ok = Csv.sok(q, f)
      Ds.put(i, n0, auto, U32.add(nulls, U32.sub(1, ok)), k, codes, Array.set(U32, vm, i, ok), ST.Dict.code(dict, f))

# n0: the column's rows before this chunk; ps: (go on, the state)
def Ds.go(cs: List<&2, H.CsvCell>, +i: U32, +n0: U32, +auto: ST.StrEnc, ps: Bool & DS) -> DR:
  match cs:
    case Nil{}:
      (go, st) = ps
      DDone{st}
    case c <> ct:
      (go, st) = ps
      match go:
        case True{}:
          Ds.go(ct, U32.inc(i), n0, auto, Ds.cell(c, i, n0, auto, st))
        case False{}:
          DSwitch{i, c <> ct, st}

# ---- a column being built ------------------------------------------------------------------------

# a Str column's storage while building: not a Str column, Raw, or a Dictionary (auto: EncAuto,
# may fall back to Raw)
type SK is Type:
  KNone{}
  KRaw{}
  KDict{dict: ST.Dict, auto: ST.StrEnc}

# dtype, rows so far, nulls so far, the first bad cell, the storage, the parts (newest first)
type CB is Type:
  CB{t: D.DType, n: U32, nulls: U32, bad: Maybe<&2, BadL>, sk: SK, parts: List<&1, Part>}

def CB.w.fin(+t: D.DType, +n: U32, +m: U32, +nulls: U32, sk: SK, parts: List<&1, Part>, st: WS) -> CB:
  match st:
    case WS{+k, bad, a, vm}:
      CB{t, U32.add(n, m), U32.add(nulls, k), bad, sk, PW{m, a, vm} <> parts}

def CB.f.fin(+t: D.DType, +n: U32, +m: U32, +nulls: U32, sk: SK, parts: List<&1, Part>, st: FS) -> CB:
  match st:
    case FS{+k, bad, a, vm}:
      CB{t, U32.add(n, m), U32.add(nulls, k), bad, sk, PF{m, a, vm} <> parts}

def CB.s.fin(+t: D.DType, +n: U32, +m: U32, +nulls: U32, bad: Maybe<&2, BadL>, parts: List<&1, Part>, st: SS) -> CB:
  match st:
    case SS{+k, a, vm}:
      CB{t, U32.add(n, m), U32.add(nulls, k), bad, KRaw{}, PS{m, a, vm} <> parts}

# Raw parts of the Dictionary parts so far (EncAuto's fall back); parts newest first, the dict
# threaded through the loop as a pair parameter
def Parts.dec.pd(+m: U32, c: Array<U32>, vm: Array<U32>, acc: List<&1, Part>, r: ST.Dict & ST.Dict) -> ST.Dict & List<&1, Part>:
  (d1, d2) = r
  (d1, PS{m, ST.Dict.decode(m, K.Kernel.depth_for(U32.max(m, 1)), c, d2), vm} <> acc)

def Parts.dec.step(p: Part, st: ST.Dict & List<&1, Part>) -> ST.Dict & List<&1, Part>:
  match p:
    case PD{+m, c, vm}:
      (dict, acc) = st
      Parts.dec.pd(m, c, vm, acc, ST.Dict.clone(dict))
    case other:
      (dict, acc) = st
      (dict, other <> acc)

def Parts.dec(ps: List<&1, Part>, st: ST.Dict & List<&1, Part>) -> List<&1, Part>:
  match ps:
    case Nil{}:
      (dict, acc) = st
      List.reverse(&1, Part, acc)
    case p <> t:
      Parts.dec(t, Parts.dec.step(p, st))

# the fall back: past the threshold the column is Raw from here on
def CB.d.over(over: Bool, +t: D.DType, +n: U32, +nulls: U32, bad: Maybe<&2, BadL>, dict: ST.Dict, +auto: ST.StrEnc, parts: List<&1, Part>) -> CB:
  match over:
    case True{}:
      CB{t, n, nulls, bad, KRaw{}, Parts.dec(parts, (dict, Nil{}))}
    case False{}:
      CB{t, n, nulls, bad, KDict{dict, auto}, parts}

def CB.d.size(+t: D.DType, +n: U32, +nulls: U32, bad: Maybe<&2, BadL>, +auto: ST.StrEnc, parts: List<&1, Part>, r: ST.Dict & U32) -> CB:
  (dict, +k) = r
  CB.d.over(Csv.dict_over(auto, k, n), t, n, nulls, bad, dict, auto, parts)

# the switch inside a chunk: its rows coded so far decoded, the rest read as Raw strings, the
# earlier chunks decoded (Parts.dec)
def CB.d.sw2(+t: D.DType, +n: U32, +m: U32, +d: Nat, +nulls: U32, bad: Maybe<&2, BadL>, parts: List<&1, Part>, +i: U32, rest: List<&2, H.CsvCell>, +k: U32, c: Array<U32>, vm: Array<U32>, dd: ST.Dict & ST.Dict) -> CB:
  (d1, d2) = dd
  CB.s.fin(t, n, m, nulls, bad, Parts.dec(parts, (d1, Nil{})), Ss.go(rest, i, SS{k, ST.Dict.decode(i, d, c, d2), vm}))

def CB.d.sw(+t: D.DType, +n: U32, +m: U32, +d: Nat, +nulls: U32, bad: Maybe<&2, BadL>, parts: List<&1, Part>, +i: U32, rest: List<&2, H.CsvCell>, st: DS) -> CB:
  match st:
    case DS{+k, kd, c, vm, dict}:
      CB.d.sw2(t, n, m, d, nulls, bad, parts, i, rest, k, c, vm, ST.Dict.clone(dict))

def CB.d.fin(+t: D.DType, +n: U32, +m: U32, +d: Nat, +nulls: U32, bad: Maybe<&2, BadL>, +auto: ST.StrEnc, parts: List<&1, Part>, r: DR) -> CB:
  match r:
    case DDone{DS{+k, kd, c, vm, dict}}:
      CB.d.size(t, U32.add(n, m), U32.add(nulls, k), bad, auto, PD{m, c, vm} <> parts, ST.Dict.size(dict))
    case DSwitch{+i, rest, st}:
      CB.d.sw(t, n, m, d, nulls, bad, parts, i, rest, st)

def CB.d.start(cs: List<&2, H.CsvCell>, +t: D.DType, +n: U32, +m: U32, +d: Nat, +nulls: U32, bad: Maybe<&2, BadL>, +auto: ST.StrEnc, parts: List<&1, Part>, r: ST.Dict & U32) -> CB:
  (dict, +k) = r
  CB.d.fin(t, n, m, d, nulls, bad, auto, parts, Ds.go(cs, 0, n, auto, (True{}, DS{0, k, Array.new(U32, d, 0), Array.new(U32, d, 0), dict})))

# one chunk's cells of this column (m of them) with their records' lines, as one more part
def CB.feed.k(+m: U32, +d: Nat, cs: List<&2, H.CsvCell>, ls: List<&2, U32>, +t: D.DType, +n: U32, +nulls: U32, bad: Maybe<&2, BadL>, sk: SK, parts: List<&1, Part>) -> CB:
  match t sk:
    case D.TF32{} other:
      CB.f.fin(t, n, m, nulls, other, parts, Fs.go(cs, ls, 0, FS{0, bad, Array.new(F32, d, 0.0), Array.new(U32, d, 0)}))
    case D.TStr{} KDict{dict, +auto}:
      CB.d.start(cs, t, n, m, d, nulls, bad, auto, parts, ST.Dict.size(dict))
    case D.TStr{} other:
      CB.s.fin(t, n, m, nulls, bad, parts, Ss.go(cs, 0, SS{0, Array.new(String, d, ""), Array.new(U32, d, 0)}))
    case _ other:
      CB.w.fin(t, n, m, nulls, other, parts, Ws.go(cs, ls, t, 0, WS{0, bad, Array.new(U32, d, 0), Array.new(U32, d, 0)}))

def CB.feed(+cs: List<&2, H.CsvCell>, ls: List<&2, U32>, cb: CB) -> CB:
  match cb:
    case CB{+t, +n, +nulls, bad, sk, parts}:
      +m = K.Kernel.count(~H.CsvCell, cs, 0)
      CB.feed.k(m, K.Kernel.depth_for(U32.max(m, 1)), cs, ls, t, n, nulls, bad, sk, parts)

# every column of a chunk in parallel: ONE balanced fork over a tree of (builder, cells) pairs, the builders
# fed at the leaves (DESIGN.md 16.10; v0.1 had a 1-vs-rest chain down the column list, a level per column).
# The tree is built by a sequential prelude, so the forking def does nothing but match and fork; the lists of
# the leaves are joined in column order after the fork (the join runs in place).
type FJ is Type:
  FJE{}
  FJL{cb: CB, cs: List<&2, H.CsvCell>}
  FJN{l: FJ, r: FJ}

def FJ.leaves(cbs: List<&1, CB>, cols: List<&2, List<&2, H.CsvCell>>) -> List<&1, FJ>:
  match cbs cols:
    case cb <> ct c <> cst:
      FJL{cb, c} <> FJ.leaves(ct, cst)
    case _ _:
      Nil{}

def FJ.pair(xs: List<&1, FJ>) -> List<&1, FJ>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{a, Nil{}}:
      a <> Nil{}
    case Con{a, Con{b, u}}:
      FJN{a, b} <> FJ.pair(u)

# the leaves paired level by level (at most f levels; 32 cover any column count)
def FJ.top(f: Nat, xs: List<&1, FJ>) -> FJ:
  match f xs:
    case _ Nil{}:
      FJE{}
    case _ Con{a, Nil{}}:
      a
    case 0n other:
      FJE{}
    case 1n+p other:
      FJ.top(p, FJ.pair(other))

def FJ.feed(+ls: List<&2, U32>, t: FJ) -> List<&1, CB>:
  match t:
    case FJE{}:
      Nil{}
    case FJL{cb, c}:
      CB.feed(c, ls, cb) <> Nil{}
    case FJN{l, r}:
      a b = FJ.feed(ls, l) FJ.feed(ls, r)
      List.append(&1, CB, a, b)

def CBs.feed(cbs: List<&1, CB>, cols: List<&2, List<&2, H.CsvCell>>, +ls: List<&2, U32>) -> List<&1, CB>:
  FJ.feed(ls, FJ.top(32n, FJ.leaves(cbs, cols)))

# a new builder of dtype t (a Str one in the requested storage)
def CB.new.sk(+t: D.DType, enc: ST.StrEnc) -> SK:
  match t enc:
    case D.TStr{} ST.EncRaw{}:
      KRaw{}
    case D.TStr{} other:
      KDict{ST.Dict.empty(), other}
    case _ _:
      KNone{}

def CB.new(+t: D.DType, +enc: ST.StrEnc) -> CB:
  CB{t, 0, 0, None{}, CB.new.sk(t, enc), Nil{}}

def CBs.new(ts: List<&2, D.DType>, +enc: ST.StrEnc) -> List<&1, CB>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> tt:
      CB.new(t, enc) <> CBs.new(tt, enc)

# ---- builders -> columns: the parts (oldest first) concatenated once --------------------------------

type CW is Type:
  CW{off: U32, a: Array<U32>, vm: Array<U32>}

type CF is Type:
  CF{off: U32, a: Array<F32>, vm: Array<U32>}

type CS is Type:
  CS{off: U32, a: Array<String>, vm: Array<U32>}

def Cat.w.one(p: Part, st: CW) -> CW:
  match p st:
    case PW{+m, a, vm} CW{+off, oa, ov}:
      CW{U32.add(off, m), K.Kernel.copy_into(~U32, m, off, oa, a), K.Kernel.copy_into(~U32, m, off, ov, vm)}
    case PD{+m, a, vm} CW{+off, oa, ov}:
      CW{U32.add(off, m), K.Kernel.copy_into(~U32, m, off, oa, a), K.Kernel.copy_into(~U32, m, off, ov, vm)}
    case _ other:
      other

def Cat.w(ps: List<&1, Part>, st: CW) -> CW:
  match ps:
    case Nil{}:
      st
    case p <> t:
      Cat.w(t, Cat.w.one(p, st))

def Cat.f.one(p: Part, st: CF) -> CF:
  match p st:
    case PF{+m, a, vm} CF{+off, oa, ov}:
      CF{U32.add(off, m), K.Kernel.copy_into(~F32, m, off, oa, a), K.Kernel.copy_into(~U32, m, off, ov, vm)}
    case _ other:
      other

def Cat.f(ps: List<&1, Part>, st: CF) -> CF:
  match ps:
    case Nil{}:
      st
    case p <> t:
      Cat.f(t, Cat.f.one(p, st))

def Cat.s.one(p: Part, st: CS) -> CS:
  match p st:
    case PS{+m, a, vm} CS{+off, oa, ov}:
      CS{U32.add(off, m), K.Kernel.copy_into(~String, m, off, oa, a), K.Kernel.copy_into(~U32, m, off, ov, vm)}
    case _ other:
      other

def Cat.s(ps: List<&1, Part>, st: CS) -> CS:
  match ps:
    case Nil{}:
      st
    case p <> t:
      Cat.s(t, Cat.s.one(p, st))

def CB.valid(+nulls: U32, vm: Array<U32>) -> C.Valid:
  Bool.pick(C.Valid, U32.is_zero(nulls), C.AllValid{}, C.Mask{vm})

def CB.col.w(+t: D.DType, +n: U32, +d: Nat, +nulls: U32, st: CW) -> C.Column:
  match st:
    case CW{off, a, vm}:
      C.Column.mk_w(t, n, d, CB.valid(nulls, vm), a)

def CB.col.d(+n: U32, +d: Nat, +nulls: U32, dict: ST.Dict, st: CW) -> C.Column:
  match st:
    case CW{off, a, vm}:
      C.CStr{n, d, CB.valid(nulls, vm), ST.SDict{a, dict}}

def CB.col.f(+n: U32, +d: Nat, +nulls: U32, st: CF) -> C.Column:
  match st:
    case CF{off, a, vm}:
      C.CF32{n, d, CB.valid(nulls, vm), a}

def CB.col.s(+n: U32, +d: Nat, +nulls: U32, st: CS) -> C.Column:
  match st:
    case CS{off, a, vm}:
      C.CStr{n, d, CB.valid(nulls, vm), ST.SRaw{a}}

def CB.col.b(+t: D.DType, +n: U32, +d: Nat, +nulls: U32, sk: SK, ps: List<&1, Part>) -> C.Column:
  match t sk:
    case D.TF32{} other:
      CB.col.f(n, d, nulls, Cat.f(ps, CF{0, Array.new(F32, d, 0.0), Array.new(U32, d, 0)}))
    case D.TStr{} KDict{dict, auto}:
      CB.col.d(n, d, nulls, dict, Cat.w(ps, CW{0, Array.new(U32, d, 0), Array.new(U32, d, 0)}))
    case D.TStr{} other:
      CB.col.s(n, d, nulls, Cat.s(ps, CS{0, Array.new(String, d, ""), Array.new(U32, d, 0)}))
    case _ other:
      CB.col.w(t, n, d, nulls, Cat.w(ps, CW{0, Array.new(U32, d, 0), Array.new(U32, d, 0)}))

# one part (the whole input was one chunk): its arrays are the column's (2^depth_for(n) slots
# already), no copy
def CB.col.one(+t: D.DType, +n: U32, +d: Nat, +nulls: U32, p: Part, sk: SK) -> C.Column:
  match p sk:
    case PW{m, a, vm} _:
      C.Column.mk_w(t, n, d, CB.valid(nulls, vm), a)
    case PF{m, a, vm} _:
      C.CF32{n, d, CB.valid(nulls, vm), a}
    case PS{m, a, vm} _:
      C.CStr{n, d, CB.valid(nulls, vm), ST.SRaw{a}}
    case PD{m, c, vm} KDict{dict, auto}:
      C.CStr{n, d, CB.valid(nulls, vm), ST.SDict{c, dict}}
    case PD{m, c, vm} other:
      C.CStr{n, d, CB.valid(nulls, vm), ST.SDict{c, ST.Dict.empty()}}

def CB.col.n(+t: D.DType, +n: U32, +d: Nat, +nulls: U32, sk: SK, parts: List<&1, Part>) -> C.Column:
  match parts:
    case p <> Nil{}:
      CB.col.one(t, n, d, nulls, p, sk)
    case other:
      CB.col.b(t, n, d, nulls, sk, List.reverse(&1, Part, other))

def CB.col.k(+name: String, bad: Maybe<&2, BadL>, +t: D.DType, +n: U32, +nulls: U32, sk: SK, parts: List<&1, Part>) -> E.ResT(C.Named):
  match bad:
    case Some{BadL{line, text}}:
      Csv.col.err(name, t, text, line)
    case None{}:
      Done{C.Named{name, CB.col.n(t, n, K.Kernel.depth_for(U32.max(n, 1)), nulls, sk, parts)}}

# the column (2^depth_for(n) slots, AllValid without nulls), or the first bad cell's ParseError
def CB.col(+name: String, cb: CB) -> E.ResT(C.Named):
  match cb:
    case CB{+t, +n, +nulls, bad, sk, parts}:
      CB.col.k(name, bad, t, n, nulls, sk, parts)

# the first error in column order, else every column
def CBs.cols(names: List<&2, String>, cbs: List<&1, CB>) -> E.ResT(List<&1, C.Named>):
  match names cbs:
    case n <> nt cb <> ct:
      Csv.cols.k(CB.col(n, cb), CBs.cols(nt, ct))
    case _ _:
      Done{Nil{}}

# ---- the sink: records -> header, inference, builders ---------------------------------------------
# Records arrive NEWEST first (the parser's order: no reversal on the hot path). One walk per batch
# (Csv.tw) skips blank lines (k > 1 columns), notes the first ragged record (newest first, so the
# last one met is the first in the file), counts, collects the lines and pushes every cell onto
# its column, which comes out OLDEST first; each record and cell is taken apart exactly once.

# a batch transposed: records, the first ragged one's error, lines and columns (both oldest first)
type TW is Data:
  TW{n: U32, rag: Maybe<&2, E.Err>, lines: List<&2, U32>, cols: List<&2, List<&2, H.CsvCell>>}

# a record's cells pushed onto the columns (as many as there are), and the cell count
type Rw is Data:
  Rw{accs: List<&2, List<&2, H.CsvCell>>, g: Nat}

def Csv.tw.row.k(c: H.CsvCell, a: List<&2, H.CsvCell>, r: Rw) -> Rw:
  match r:
    case Rw{accs, g}:
      Rw{(c <> a) <> accs, g}

def Csv.tw.row(cs: List<&2, H.CsvCell>, accs: List<&2, List<&2, H.CsvCell>>, +g: Nat) -> Rw:
  match cs accs:
    case c <> ct a <> at:
      Csv.tw.row.k(c, a, Csv.tw.row(ct, at, Nat.add(g, 1n)))
    case c <> ct Nil{}:
      Rw{Nil{}, Nat.add(g, List.length(&2, H.CsvCell, c <> ct))}
    case Nil{} rest:
      Rw{rest, g}

def Csv.tw.rag(ok: Bool, +g: Nat, +w: Nat, +l: U32, rag: Maybe<&2, E.Err>) -> Maybe<&2, E.Err>:
  match ok:
    case True{}:
      rag
    case False{}:
      Some{E.ParseError{l, "expected " ++ Nat.show(w) ++ " fields, got " ++ Nat.show(g)}}

def Csv.tw.push(+n: U32, rag: Maybe<&2, E.Err>, lines: List<&2, U32>, +l: U32, +w: Nat, r: Rw) -> TW:
  match r:
    case Rw{accs, +g}:
      TW{U32.inc(n), Csv.tw.rag(Nat.is_eq(g, w), g, w, l, rag), l <> lines, accs}

def Csv.tw.cells.k(cs: List<&2, H.CsvCell>, +l: U32, +w: Nat, st: TW) -> TW:
  match st:
    case TW{+n, rag, lines, cols}:
      Csv.tw.push(n, rag, lines, l, w, Csv.tw.row(cs, cols, 0n))

# one record: a blank line in k > 1 columns is skipped, else its cells go to the columns
def Csv.tw.cells(cs: List<&2, H.CsvCell>, multi: Bool, +l: U32, +w: Nat, st: TW) -> TW:
  match cs multi:
    case H.CsvCell{SNil{}, False{}} <> Nil{} True{}:
      st
    case other _:
      Csv.tw.cells.k(other, l, w, st)

def Csv.tw.rec(r: H.CsvRec, +multi: Bool, +w: Nat, st: TW) -> TW:
  match r:
    case H.CsvRec{+l, cs}:
      Csv.tw.cells(cs, multi, l, w, st)

def Csv.tw(rs: List<&2, H.CsvRec>, +multi: Bool, +w: Nat, st: TW) -> TW:
  match rs:
    case Nil{}:
      st
    case r <> t:
      Csv.tw(t, multi, w, Csv.tw.rec(r, multi, w, st))

# xs then ys, by two tail loops (Base List.append recurses per element: the interpreter's stack)
def Csv.revonto.c(xs: List<&2, H.CsvCell>, acc: List<&2, H.CsvCell>) -> List<&2, H.CsvCell>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      Csv.revonto.c(t, h <> acc)

def Csv.revonto.u(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      Csv.revonto.u(t, h <> acc)

def Csv.app.u(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  Csv.revonto.u(List.reverse(&2, U32, xs), ys)

# xs (columns, oldest first) followed by ys, column by column
def Csv.cat.cols(xs: List<&2, List<&2, H.CsvCell>>, ys: List<&2, List<&2, H.CsvCell>>) -> List<&2, List<&2, H.CsvCell>>:
  match xs ys:
    case x <> xt y <> yt:
      Csv.revonto.c(List.reverse(&2, H.CsvCell, x), y) <> Csv.cat.cols(xt, yt)
    case _ _:
      Nil{}

# where the records go: hdr, before the header (blank lines skipped); no hdr, before the first
# non-blank record (the blank ones so far kept, newest first); inference (the first data
# records kept as columns and lines, oldest first, nb of them); building; or only counting and
# checking (an error is certain)
type Ph is Type:
  PLead{}
  PPend{blanks: List<&2, H.CsvRec>}
  PInf{names: List<&2, String>, w: Nat, cols: List<&2, List<&2, H.CsvCell>>, lines: List<&2, U32>, nb: U32}
  PBuild{names: List<&2, String>, w: Nat, cbs: List<&1, CB>}
  PDead{w: Nat}

# the phase as Data: before the header, before the width, or past it (width w)
type PM is Data:
  MLead{}
  MPend{}
  MData{w: Nat}

# options (hdr, inference limit k, dtypes, row cap, Str storage), the phase, the first ragged
# record's error, the dtype-count error, the data records so far
type Sink is Type:
  Sink{hdr: Bool, k: U32, ts: List<&2, D.DType>, cap: U32, enc: ST.StrEnc, ph: Ph, rag: Maybe<&2, E.Err>, tse: Maybe<&2, E.Err>, count: U32}

def Sink.ph0(hdr: Bool) -> Ph:
  match hdr:
    case True{}:
      PLead{}
    case False{}:
      PPend{Nil{}}

def Sink.new(+hdr: Bool, +k: U32, ts: List<&2, D.DType>, +cap: U32, enc: ST.StrEnc) -> Sink:
  Sink{hdr, k, ts, cap, enc, Sink.ph0(hdr), None{}, None{}, 0}

def Sink.with_ph(s: Sink, ph: Ph) -> Sink:
  match s:
    case Sink{hdr, k, ts, cap, enc, old, rag, tse, count}:
      Sink{hdr, k, ts, cap, enc, ph, rag, tse, count}

# xs reversed onto acc
def Sink.app(xs: List<&2, H.CsvRec>, acc: List<&2, H.CsvRec>) -> List<&2, H.CsvRec>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      Sink.app(t, h <> acc)

def Sink.infer.ts(cs: List<&2, List<&2, H.CsvCell>>, +k: Nat) -> List<&2, D.DType>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> ct:
      Csv.infer.col(c, k) <> Sink.infer.ts(ct, k)

# inference over the kept columns, then the builders, fed with them
def Sink.infer(+k: U32, +enc: ST.StrEnc, +cols: List<&2, List<&2, H.CsvCell>>, +lines: List<&2, U32>) -> List<&1, CB>:
  CBs.feed(CBs.new(Sink.infer.ts(cols, U32.to_nat(k)), enc), cols, lines)

def Sink.inf(full: Bool, names: List<&2, String>, +w: Nat, +k: U32, +enc: ST.StrEnc, cols: List<&2, List<&2, H.CsvCell>>, lines: List<&2, U32>, +nb: U32) -> Ph:
  match full:
    case True{}:
      PBuild{names, w, Sink.infer(k, enc, cols, lines)}
    case False{}:
      PInf{names, w, cols, lines, nb}

# the phase after a batch: dead when an error is certain, else the kept columns grow (and
# inference runs once k records are kept) or the builders are fed
def Sink.go(dead: Bool, ph: Ph, +k: U32, +enc: ST.StrEnc, tw: TW) -> Ph:
  match dead ph tw:
    case True{} PInf{names, +w, cs, ls, nb} _:
      PDead{w}
    case True{} PBuild{names, +w, cbs} _:
      PDead{w}
    case False{} PInf{names, +w, cs, ls, +nb} TW{+n, rag, lines, cols}:
      Sink.inf(U32.is_ge(U32.add(nb, n), k), names, w, k, enc, Csv.cat.cols(cs, cols), Csv.app.u(ls, lines), U32.add(nb, n))
    case False{} PBuild{names, +w, cbs} TW{n, rag, lines, cols}:
      PBuild{names, w, CBs.feed(cbs, cols, lines)}
    case _ other _:
      other

def Sink.batch.t(+hdr: Bool, +k: U32, ts: List<&2, D.DType>, +cap: U32, +enc: ST.StrEnc, ph: Ph, rag0: Maybe<&2, E.Err>, +tse: Maybe<&2, E.Err>, +count: U32, tw: TW) -> Sink:
  match tw:
    case TW{+n, rag, lines, cols}:
      +rag2 = Csv.first_err(rag0, rag)
      +c2 = U32.add(count, n)
      Sink{hdr, k, ts, cap, enc, Sink.go(Bool.or(Bool.or(Maybe.is_some(&2, E.Err, rag2), Maybe.is_some(&2, E.Err, tse)), U32.is_gt(c2, cap)), ph, k, enc, TW{n, None{}, lines, cols}), rag2, tse, c2}

# a batch of data records (newest first; header and width known)
def Sink.batch(+w: Nat, s: Sink, recs: List<&2, H.CsvRec>) -> Sink:
  match s:
    case Sink{+hdr, +k, ts, +cap, +enc, ph, rag, tse, +count}:
      Sink.batch.t(hdr, k, ts, cap, enc, ph, rag, tse, count, Csv.tw(recs, Nat.is_gt(w, 1n), w, TW{0, None{}, Nil{}, Csv.nils(w)}))

# the header (or the width) is known: dtypes given -> builders at once, else inference
def Sink.begin.ph(ts: List<&2, D.DType>, names: List<&2, String>, +w: Nat, +enc: ST.StrEnc) -> Ph:
  match ts:
    case Nil{}:
      PInf{names, w, Csv.nils(w), Nil{}, 0}
    case t <> tt:
      PBuild{names, w, CBs.new(t <> tt, enc)}

# recs: the data records so far, newest first
def Sink.begin(+names: List<&2, String>, s: Sink, recs: List<&2, H.CsvRec>) -> Sink:
  match s:
    case Sink{+hdr, +k, +ts, +cap, +enc, ph, rag, tse, +count}:
      +w = List.length(&2, String, names)
      Sink.batch(w, Sink{hdr, k, ts, cap, enc, Sink.begin.ph(ts, names, w, enc), rag, Csv.ts.err(ts, w), count}, recs)

def Sink.mark.k(ph: Ph) -> Ph & PM:
  match ph:
    case PLead{}:
      (PLead{}, MLead{})
    case PPend{bl}:
      (PPend{bl}, MPend{})
    case PInf{names, +w, cs, ls, nb}:
      (PInf{names, w, cs, ls, nb}, MData{w})
    case PBuild{names, +w, cbs}:
      (PBuild{names, w, cbs}, MData{w})
    case PDead{+w}:
      (PDead{w}, MData{w})

def Sink.mark.p(+hdr: Bool, +k: U32, ts: List<&2, D.DType>, +cap: U32, enc: ST.StrEnc, rag: Maybe<&2, E.Err>, tse: Maybe<&2, E.Err>, +count: U32, r: Ph & PM) -> Sink & PM:
  (ph, m) = r
  (Sink{hdr, k, ts, cap, enc, ph, rag, tse, count}, m)

def Sink.mark(s: Sink) -> Sink & PM:
  match s:
    case Sink{+hdr, +k, ts, +cap, enc, ph, rag, tse, +count}:
      Sink.mark.p(hdr, k, ts, cap, enc, rag, tse, count, Sink.mark.k(ph))

def Csv.lead.width(r: H.CsvRec) -> Nat:
  match r:
    case H.CsvRec{l, cs}:
      List.length(&2, H.CsvCell, cs)

def Csv.lead.names(r: H.CsvRec) -> List<&2, String>:
  match r:
    case H.CsvRec{l, cs}:
      Csv.names(cs)

# hdr: the records (oldest first) from the first non-blank one (Csv.lead): its cells are the names
def Sink.hdr(rows: List<&2, H.CsvRec>, s: Sink) -> Sink:
  match rows:
    case Nil{}:
      s
    case h <> t:
      Sink.begin(Csv.lead.names(h), s, Sink.app(t, Nil{}))

# no hdr: a chunk of only blank records is kept; else the first non-blank record's width fixes
# the names and every record so far is data (rs: oldest first, recs: the same newest first)
def Sink.pend.k(lead: List<&2, H.CsvRec>, rs: List<&2, H.CsvRec>, recs: List<&2, H.CsvRec>, bl: List<&2, H.CsvRec>, s: Sink) -> Sink:
  match lead:
    case Nil{}:
      Sink.with_ph(s, PPend{Sink.app(List.reverse(&2, H.CsvRec, recs), bl)})
    case h <> t:
      Sink.begin(Csv.gen_names(Csv.lead.width(h), 0n), s, Sink.app(List.reverse(&2, H.CsvRec, recs), bl))

def Sink.pend.r(+rs: List<&2, H.CsvRec>, recs: List<&2, H.CsvRec>, bl: List<&2, H.CsvRec>, s: Sink) -> Sink:
  Sink.pend.k(Csv.lead(rs, True{}), rs, recs, bl, s)

def Sink.pend.b(ph: Ph, +recs: List<&2, H.CsvRec>, s: Sink) -> Sink:
  match ph:
    case PPend{bl}:
      Sink.pend.r(Sink.app(recs, Nil{}), recs, bl, s)
    case other:
      Sink.with_ph(s, other)

def Sink.pend(s: Sink, +recs: List<&2, H.CsvRec>) -> Sink:
  match s:
    case Sink{hdr, k, ts, cap, enc, ph, rag, tse, count}:
      Sink.pend.b(ph, recs, Sink{hdr, k, ts, cap, enc, PLead{}, rag, tse, count})

def Sink.recs.m(r: Sink & PM, recs: List<&2, H.CsvRec>) -> Sink:
  (s, m) = r
  match m:
    case MLead{}:
      Sink.hdr(Csv.lead(Sink.app(recs, Nil{}), True{}), s)
    case MPend{}:
      Sink.pend(s, recs)
    case MData{+w}:
      Sink.batch(w, s, recs)

# a chunk's records (NEWEST first: the parser's order) into the sink
def Sink.recs(recs: List<&2, H.CsvRec>, s: Sink) -> Sink:
  Sink.recs.m(Sink.mark(s), recs)

# ---- the end ----------------------------------------------------------------------------------

def Sink.cols(names: List<&2, String>, cbs: List<&1, CB>) -> E.ResT(C.Frame):
  Csv.fin(CBs.cols(names, cbs))

def Sink.fin.ph(+k: U32, +enc: ST.StrEnc, ph: Ph) -> E.ResT(C.Frame):
  match ph:
    case PInf{names, +w, cs, ls, nb}:
      Sink.cols(names, Sink.infer(k, enc, cs, ls))
    case PBuild{names, w, cbs}:
      Sink.cols(names, cbs)
    case other:
      Fail{E.InvalidOperation{"csv: reader state (not reachable)"}}

def Sink.fin.e(err: Maybe<&2, E.Err>, +k: U32, +enc: ST.StrEnc, ph: Ph) -> E.ResT(C.Frame):
  match err:
    case Some{e}:
      Fail{e}
    case None{}:
      Sink.fin.ph(k, enc, ph)

def Sink.fin.k(+k: U32, ts: List<&2, D.DType>, +cap: U32, +enc: ST.StrEnc, ph: Ph, rag: Maybe<&2, E.Err>, tse: Maybe<&2, E.Err>, +count: U32) -> E.ResT(C.Frame):
  match ph:
    case PLead{}:
      Csv.rows.none(Csv.ts.err(ts, 0n))
    case PPend{bl}:
      Csv.rows.none(Csv.ts.err(ts, 0n))
    case other:
      Sink.fin.e(Csv.first_err(rag, Csv.first_err(tse, K.Kernel.check_rows.cap(cap, count))), k, enc, other)

# kept blank records (newest first): data of width 1
def Sink.fin.bl(s: Sink, bl: List<&2, H.CsvRec>) -> Sink:
  match bl:
    case Nil{}:
      s
    case h <> t:
      Sink.begin(Csv.gen_names(1n, 0n), s, h <> t)

def Sink.fin.pp(+hdr: Bool, +k: U32, ts: List<&2, D.DType>, +cap: U32, +enc: ST.StrEnc, ph: Ph, rag: Maybe<&2, E.Err>, tse: Maybe<&2, E.Err>, +count: U32) -> Sink:
  match ph:
    case PPend{bl}:
      Sink.fin.bl(Sink{hdr, k, ts, cap, enc, PPend{Nil{}}, rag, tse, count}, bl)
    case other:
      Sink{hdr, k, ts, cap, enc, other, rag, tse, count}

# the end of the input: kept blank records (no hdr, all blank) become data of width 1
def Sink.fin.p(s: Sink) -> Sink:
  match s:
    case Sink{+hdr, +k, ts, +cap, +enc, ph, rag, tse, +count}:
      Sink.fin.pp(hdr, k, ts, cap, enc, ph, rag, tse, count)

def Sink.fin.s(s: Sink) -> E.ResT(C.Frame):
  match s:
    case Sink{hdr, +k, ts, +cap, +enc, ph, rag, tse, +count}:
      Sink.fin.k(k, ts, cap, enc, ph, rag, tse, count)

def Sink.fin(s: Sink) -> E.ResT(C.Frame):
  Sink.fin.s(Sink.fin.p(s))

# ---- strings ------------------------------------------------------------------------------------

def Csv.malformed() -> E.Err:
  E.ParseError{0, "malformed csv"}

def Csv.st.close(s: Sink, m: Maybe<&2, List<&2, H.CsvRec>>) -> E.ResT(C.Frame):
  match m:
    case None{}:
      Fail{Csv.malformed()}
    case Some{rows}:
      Sink.fin(Sink.recs(rows, s))

def Csv.st.one(s: Sink, st: H.Step) -> E.ResT(C.Frame):
  match st:
    case H.SRej{}:
      Fail{Csv.malformed()}
    case H.SMore{rows, pst}:
      Csv.st.close(Sink.recs(rows, s), H.close(pst))

# a whole text, as one chunk
def Csv.parse_enc.k(bad: Maybe<&2, E.Err>, +cap: U32, text: String, +sep: Char, +hdr: Bool, +inf: U32, ts: List<&2, D.DType>, enc: ST.StrEnc) -> E.ResT(C.Frame):
  match bad:
    case Some{e}:
      Fail{e}
    case None{}:
      Csv.st.one(Sink.new(hdr, Csv.limit(inf), ts, cap, enc), H.step(Char.to_u32(sep), text, H.start()))

def Csv.parse_enc.cap(+cap: U32, text: String, opts: CsvOpts, ts: List<&2, D.DType>, enc: ST.StrEnc) -> E.ResT(C.Frame):
  match opts:
    case CsvOpts{+sep, hdr, inf}:
      Csv.parse_enc.k(Csv.sep_err(sep), cap, text, sep, hdr, inf, ts, enc)

# the Str storage of the readers that take no option (Csv.read, Csv.read_with, Csv.parse,
# Csv.parse_with, scan_csv's collect): ST.EncAuto, by measured cardinality (the M4 gate passed:
# DESIGN.md 14 M4 and bench/README.md record the decision and its numbers)
def Csv.enc_default() -> ST.StrEnc:
  ST.EncAuto{}

# Csv.parse_with with the Str storage chosen: EncRaw, EncDict (every Str column), EncAuto (by
# measured cardinality, Csv.dict_over)
def Csv.parse_enc(text: String, opts: CsvOpts, ts: List<&2, D.DType>, enc: ST.StrEnc) -> E.ResT(C.Frame):
  Csv.parse_enc.cap(K.Kernel.max_rows(), text, opts, ts, enc)

# Strict schema: dtypes by column position, a value that does not parse is a
# ParseError (no lenient nulls); the dtype count must equal the column count.
# cap: the row cap (K.Kernel.max_rows() for every real read; lowered in the tests)
def Csv.parse_with.cap(+cap: U32, text: String, opts: CsvOpts, ts: List<&2, D.DType>) -> E.ResT(C.Frame):
  Csv.parse_enc.cap(cap, text, opts, ts, Csv.enc_default())

def Csv.parse_with(text: String, opts: CsvOpts, ts: List<&2, D.DType>) -> E.ResT(C.Frame):
  Csv.parse_with.cap(K.Kernel.max_rows(), text, opts, ts)

# Inferred schema (first infer_rows rows; 0 = all): bool, u32, i32, f32, str.
def Csv.parse(text: String, opts: CsvOpts) -> E.ResT(C.Frame):
  Csv.parse_with(text, opts, Nil{})

# ---- files: the chunk loop --------------------------------------------------------------------

# the read state: the file, the next offset, the file size, the chunk size, the parser state, the sink
type RSt is Type:
  RRun{f: File, off: U32, size: U32, chunk: U32, sep: U32, pst: H.St, s: Sink}
  REnd{r: E.ResT(C.Frame)}

def Csv.rd.end(f: File, r: E.ResT(C.Frame)) -> IO(RSt):
  do IO<RSt>:
    File.close(f)
    return REnd{r}

# a parsed piece: on, or (last) the end of the file
def Csv.rd.more(f: File, +off: U32, +size: U32, +chunk: U32, +sep: U32, s: Sink, st: H.Step, last: Bool) -> IO(RSt):
  match st last:
    case H.SRej{} _:
      Csv.rd.end(f, Fail{Csv.malformed()})
    case H.SMore{rows, pst} True{}:
      Csv.rd.end(f, Csv.st.close(Sink.recs(rows, s), H.close(pst)))
    case H.SMore{rows, pst} False{}:
      IO.pure(RSt, RRun{f, off, size, chunk, sep, pst, Sink.recs(rows, s)})

# the text of bytes off .. off + c (File.read: the runtime's own UTF-8 decoder, as before M4; a
# piece always ends after an LF or at the end of the file, so no sequence is ever cut)
def Csv.rd.text(f: File, res: Result<&1, &1, U32 & String, String>, +off: U32, +size: U32, +chunk: U32, +sep: U32, pst: H.St, s: Sink, +last: Bool) -> IO(RSt):
  match res:
    case Fail{(code, msg)}:
      Csv.rd.end(f, Fail{E.IoError{code, msg}})
    case Done{+text}:
      Csv.rd.more(f, off, size, chunk, sep, s, H.step(sep, text, pst), last)

def Csv.rd.got(r: File & Result<&1, &1, U32 & String, String>, +off: U32, +size: U32, +chunk: U32, +sep: U32, pst: H.St, s: Sink, +last: Bool) -> IO(RSt):
  (f, res) = r
  Csv.rd.text(f, res, off, size, chunk, sep, pst, s, last)

def Csv.rd.read(f: File, +c: U32, +off: U32, +size: U32, +chunk: U32, +sep: U32, pst: H.St, s: Sink, +last: Bool) -> IO(RSt):
  do IO<RSt>:
    r : File & Result<&1, &1, U32 & String, String> <- File.read(f, c)
    Csv.rd.got(r, U32.add(off, c), size, chunk, sep, pst, s, last)

def Csv.rd.cut.k(stuck: Bool, f: File, +c: U32, +off: U32, +size: U32, +chunk: U32, +sep: U32, pst: H.St, s: Sink) -> IO(RSt):
  match stuck:
    case True{}:
      IO.pure(RSt, RRun{f, off, size, U32.mul(chunk, 2), sep, pst, s})
    case False{}:
      Csv.rd.read(f, c, off, size, chunk, sep, pst, s, False{})

# the probe's last LF (1 + its index in the probe, 0: none): the piece is the chunk up to it;
# a chunk whose probe holds no LF is read again twice as large
def Csv.rd.cut(f: File, ln: Ln, +p: U32, +off: U32, +size: U32, +chunk: U32, +sep: U32, pst: H.St, s: Sink) -> IO(RSt):
  match ln:
    case Ln{n, +last}:
      Csv.rd.cut.k(U32.is_eq(last, 0), f, U32.add(U32.sub(chunk, p), last), off, size, chunk, sep, pst, s)

def Csv.rd.probe.res(f: File, res: Result<&1, &1, U32 & String, List<&2, U32>>, +p: U32, +off: U32, +size: U32, +chunk: U32, +sep: U32, pst: H.St, s: Sink) -> IO(RSt):
  match res:
    case Fail{(code, msg)}:
      Csv.rd.end(f, Fail{E.IoError{code, msg}})
    case Done{bs}:
      Csv.rd.cut(f, Csv.ln(bs, 0, 0), p, off, size, chunk, sep, pst, s)

def Csv.rd.probe.got(r: File & Result<&1, &1, U32 & String, List<&2, U32>>, +p: U32, +off: U32, +size: U32, +chunk: U32, +sep: U32, pst: H.St, s: Sink) -> IO(RSt):
  (f, res) = r
  Csv.rd.probe.res(f, res, p, off, size, chunk, sep, pst, s)

def Csv.rd.go.k(none: Bool, all: Bool, +rem: U32, f: File, +off: U32, +size: U32, +chunk: U32, +sep: U32, pst: H.St, s: Sink) -> IO(RSt):
  match none all:
    case True{} _:
      Csv.rd.end(f, Csv.st.close(s, H.close(pst)))
    case False{} True{}:
      Csv.rd.read(f, rem, off, size, chunk, sep, pst, s, True{})
    case False{} False{}:
      +p = U32.min(chunk, 4096)
      do IO<RSt>:
        r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_at(f, U32.sub(U32.add(off, chunk), p), p)
        Csv.rd.probe.got(r, p, off, size, chunk, sep, pst, s)

# the bytes left: none -> the end; at most a chunk -> read them all (the last piece); else probe
# the chunk's last p bytes (File.read_at, the position does not move) for its last LF
def Csv.rd.go(+rem: U32, f: File, +off: U32, +size: U32, +chunk: U32, +sep: U32, pst: H.St, s: Sink) -> IO(RSt):
  Csv.rd.go.k(U32.is_zero(rem), U32.is_le(rem, chunk), rem, f, off, size, chunk, sep, pst, s)

def Csv.rd.step(st: RSt) -> IO(RSt):
  match st:
    case REnd{r}:
      IO.pure(RSt, REnd{r})
    case RRun{f, +off, +size, +chunk, +sep, pst, s}:
      Csv.rd.go(U32.sub(size, off), f, off, size, chunk, sep, pst, s)

# one step per read; the fuel (file size + 2) can never run out before the file does
def Csv.rd.loop(fuel: Nat, st: RSt) -> IO(RSt):
  match fuel:
    case 0n:
      IO.pure(RSt, st)
    case 1n+p:
      match st:
        case REnd{r}:
          IO.pure(RSt, REnd{r})
        case RRun{f, off, size, chunk, sep, pst, s}:
          do IO<RSt>:
            st2 : RSt <- Csv.rd.step(RRun{f, off, size, chunk, sep, pst, s})
            Csv.rd.loop(p, st2)

def Csv.rd.out(st: RSt) -> IO(E.ResT(C.Frame)):
  match st:
    case REnd{r}:
      IO.pure(E.ResT(C.Frame), r)
    case RRun{f, off, size, chunk, sep, pst, s}:
      do IO<E.ResT(C.Frame)>:
        File.close(f)
        return Fail{E.InvalidOperation{"csv: read did not finish"}}

def Csv.read.sized(+chunk: U32, +sep: U32, s: Sink, f: File, res: Result<&1, &1, U32 & String, U32>) -> IO(E.ResT(C.Frame)):
  match res:
    case Done{+n}:
      do IO<E.ResT(C.Frame)>:
        st : RSt <- Csv.rd.loop(Nat.add(U32.to_nat(n), 2n), RRun{f, 0, n, chunk, sep, H.start(), s})
        Csv.rd.out(st)
    case Fail{(code, msg)}:
      do IO<E.ResT(C.Frame)>:
        File.close(f)
        return Fail{E.IoError{code, msg}}

def Csv.read.size(+chunk: U32, +sep: U32, s: Sink, r: File & Result<&1, &1, U32 & String, U32>) -> IO(E.ResT(C.Frame)):
  (f, res) = r
  Csv.read.sized(chunk, sep, s, f, res)

def Csv.read.opened(+chunk: U32, +sep: U32, s: Sink, o: Result<&1, &1, U32 & String, File>) -> IO(E.ResT(C.Frame)):
  match o:
    case Done{f}:
      do IO<E.ResT(C.Frame)>:
        r : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
        Csv.read.size(chunk, sep, s, r)
    case Fail{(code, msg)}:
      IO.pure(E.ResT(C.Frame), Fail{E.IoError{code, msg}})

def Csv.read_open(path: String, +chunk: U32, +sep: U32, s: Sink) -> IO(E.ResT(C.Frame)):
  do IO<E.ResT(C.Frame)>:
    o : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    Csv.read.opened(chunk, sep, s, o)

# a refused separator is answered before the file is opened (as Csv.scan_fields_with does)
def Csv.read_chk(bad: Maybe<&2, E.Err>, path: String, +chunk: U32, +sep: U32, s: Sink) -> IO(E.ResT(C.Frame)):
  match bad:
    case Some{e}:
      IO.pure(E.ResT(C.Frame), Fail{e})
    case None{}:
      Csv.read_open(path, chunk, sep, s)

# the reader with every knob: chunk size (tests use tiny chunks), row cap, Str storage
def Csv.read_full(path: String, +opts: CsvOpts, ts: List<&2, D.DType>, enc: ST.StrEnc, +chunk: U32, +cap: U32) -> IO(E.ResT(C.Frame)):
  match opts:
    case CsvOpts{+sep, +hdr, +inf}:
      Csv.read_chk(Csv.sep_err(sep), path, chunk, Char.to_u32(sep), Sink.new(hdr, Csv.limit(inf), ts, cap, enc))

# the v0.1 reader (the pinned reference of the v0.2 reader: CsvV01{}, tests, the CSV fuzz) with the Str
# storage chosen (EncRaw / EncDict / EncAuto)
def Csv.read_enc_v01(path: String, opts: CsvOpts, ts: List<&2, D.DType>, enc: ST.StrEnc) -> IO(E.ResT(C.Frame)):
  Csv.read_full(path, opts, ts, enc, Csv.chunk(), K.Kernel.max_rows())

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

# ==== the v0.2 reader (W6.3; DESIGN.md 17.4 D6, 16.5 D7) =============================================
# The DEFAULT since W8 (D7: flipped separately from any removal; Csv.engine_default): every Csv.read,
# Csv.read_with, Csv.read_enc and scan_csv's collect reads with it. The v0.1 reader (Csv.read_full,
# Csv.read_enc_v01) stays, selectable as CsvV01{} and pinned as the reference of the tests and the CSV
# fuzz. The engine is chosen by a `CsvEngine` value (`Csv.read_eng`, the facade's `read_csv_engine` /
# `read_csv_v02`, and `Exec.run_rd` / `Lazy.collect_rd` for scan_csv's collect; scan_csv's plan-time
# schema inference stays the v0.1 prefix scan, Csv.scan_fields). Same contract as v0.1 (DESIGN.md 15.6):
# the same values, validity, F32 bits, strings, dictionary codes, column order and dtypes, errors and
# their order and lines. Pipeline:
#
#   1. header step (Csv.v2.h*, sequential, bounded): 64 KiB File.read_at pieces walked byte by byte
#      until the first non-blank record ends (an LF at even quote parity, or the end of the file):
#      blank lines ("" or a lone CR before an LF) are skipped and counted; that record's bytes are
#      decoded as File.read decodes (Csv.u8) and parsed by the reference parser (csvparse): rejected
#      -> malformed; with a header its cells are the names, else column_0 .. (its width). It answers
#      the width w, the byte offset off0 where the data starts and the physical line line0 there (no
#      header: 0 and 1; the producer then sees the blank lines, which the lanes skip or keep as v0.1
#      does). No non-blank record: the empty frame or the dtype-count error (a header-less file of
#      blank lines only is one column of null rows, as v0.1).
#   2. producer (src/csvprod.bend Pr.regions from off0, line0): regions at record boundaries; odd
#      final quote parity -> malformed.
#   3. dtypes: explicit (a count != w: every lane only tokenizes, TyN, and the count error comes after
#      malformed / ragged, as v0.1); inferred over the first infer_rows records: infer_rows <= 65536
#      tokenizes and classifies the leading regions SEQUENTIALLY until they hold infer_rows rows
#      (L.Ln.cls; their tokens are kept for the typed pass); infer_rows = 0 (all) or larger: ONE
#      balanced fork classifies every region (L.Ln.clsr), the regions come back and are tokenized
#      again by the typed fork (17.4.5: two passes over the packed bytes, no second read). Either way
#      a column's dtype is v0.1's Csv.pick over the first rows, computed from each region's first
#      failing local row plus the region's row offset (Csv.v2.ci.*).
#   4. lanes: ONE balanced fork over the region tree (P.Rt.of: `a b = lane(l) lane(r)`), L.Ln.lane per
#      leaf; nothing shared but the dtype list.
#   5. combine, sequential, in region order: malformed (a lane rejected) > the first ragged record (the
#      first region with one) > the dtype count > the row cap (the sum of the lanes' rows, checked
#      before any column is allocated) > per column in column order its first bad cell (the first
#      region with one: its line and text) > Frame.from_columns (Csv.fin, as v0.1); every column is
#      its region parts concatenated once (the columns built by one balanced fork over a tree of
#      them, Csv.v2.bfork: each column's concatenation and merge is its own). Str columns: Raw (EncRaw: rows decoded in the lanes) or ONE
#      ST.Dict built from the regions' entries in region order (each region's entries in their local
#      first-appearance order: v0.1's codes exactly). EncAuto falls back to Raw by v0.1's rule
#      (Csv.dict_over at every row: some entry with global code c first appearing at global row r has
#      c + 1 > max(floor, (r + 1) / den)); the merge checks the rule per entry and STOPS at the first
#      hit (a 1M-distinct column merges ~16k entries, not 1M); then the rows coded so far are decoded
#      (Dict.decode) and every later part is decoded from its own entries (one gather). A column of
#      no row is checked once with size 1 and 0 rows, as v0.1's builder does on an empty chunk
#      (Csv.v2.x.zero: Raw under EncAutoAt{0, _}).
#   6. (W6.6, chunk mode CMChk{g}: Csv.read_v02_mode, the chunked engine's scans) the columns of a frame of more
#      than 2^g rows are built straight into chunk trees instead (Csv.v2.cbuild: leaves of 2^g rows cut across
#      the regions' parts, one copy per row; the same merge, codes, fall back and error order); see "the chunk
#      hand-off" below. Every read_csv* builds flat (CMFlat), exactly as before.
# A separator outside ASCII goes to the v0.1 reader (the lane compares bytes).
#
# Parallel shape: forks only in Csv.v2.ftree and Csv.v2.ctree (balanced trees of regions) and
# Csv.v2.bfork / Csv.v2.cfork (a balanced tree of columns); the header step and the rest of the combine are sequential. Hot loops (tokenizer, typed loops, coder) are csvlane's; the
# combine's per-row loops are Kernel.copy_into and Csv.v2.ggo (a gather into an offset), flat loops.
# Idioms: DESIGN 9 (helpers above callers, pairs taken apart in the next helper's parameter, no
# mutual recursion, early exits by a Bool field of the loop record).

# the reader engine (D7): v0.1 (the pinned reference) or v0.2 with its piece size in bytes (the default)
type CsvEngine is Data:
  CsvV01{}
  CsvV02{piece: U32}

def Csv.engine_v01() -> CsvEngine:
  CsvV01{}

def Csv.engine_v02() -> CsvEngine:
  CsvV02{P.Pr.piece()}

# the default reader engine of every read_csv* and of scan_csv's collect: v0.2 at the default piece size
# (W8, D7: G1 exact on every CSV test, 10k fuzz cases x 7 piece sizes and the adversarial corpus; parse
# and RSS in DESIGN.md 14 "W8: the v0.2 reader is the default")
def Csv.engine_default() -> CsvEngine:
  Csv.engine_v02()

def Csv.v2.sel(c: Bool, +a: U32, +b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

# ---- 1. the header step ----------------------------------------------------------------------------
# modes: at a line start (blank so far), a line start then one CR, inside the first non-blank record,
# that record ended (at the LF of offset p)
type QM is Data:
  QM0{}
  QM1{}
  QMR{}
  QMD{}

# the walk: mode, the offset of the next byte (frozen at the record's LF once QMD), the physical line
# the record starts on, quote parity, LFs inside the record, its bytes (newest first)
type QH is Type:
  QH{md: QM, p: U32, ln: U32, q: U32, nlf: U32, rec: List<&2, U32>}

def Csv.v2.h0(lf: Bool, cr: Bool, +b: U32, +p: U32, +ln: U32, rec: List<&2, U32>) -> QH:
  match lf:
    case True{}:
      QH{QM0{}, U32.inc(p), U32.inc(ln), 0, 0, rec}
    case False{}:
      match cr:
        case True{}:
          QH{QM1{}, U32.inc(p), ln, 0, 0, rec}
        case False{}:
          QH{QMR{}, U32.inc(p), ln, Bool.to_u32(U32.is_eq(b, 34)), 0, b <> rec}

def Csv.v2.h1(lf: Bool, +b: U32, +p: U32, +ln: U32, rec: List<&2, U32>) -> QH:
  match lf:
    case True{}:
      QH{QM0{}, U32.inc(p), U32.inc(ln), 0, 0, rec}
    case False{}:
      QH{QMR{}, U32.inc(p), ln, Bool.to_u32(U32.is_eq(b, 34)), 0, b <> (13 <> rec)}

def Csv.v2.hr(end: Bool, +b: U32, +p: U32, +ln: U32, +q: U32, +nlf: U32, rec: List<&2, U32>) -> QH:
  match end:
    case True{}:
      QH{QMD{}, p, ln, q, nlf, b <> rec}
    case False{}:
      QH{QMR{}, U32.inc(p), ln, U32.xor(q, Bool.to_u32(U32.is_eq(b, 34))), U32.add(nlf, Bool.to_u32(U32.is_eq(b, 10))), b <> rec}

def Csv.v2.hstep.k(md: QM, +b: U32, +p: U32, +ln: U32, +q: U32, +nlf: U32, rec: List<&2, U32>) -> QH:
  match md:
    case QM0{}:
      Csv.v2.h0(U32.is_eq(b, 10), U32.is_eq(b, 13), b, p, ln, rec)
    case QM1{}:
      Csv.v2.h1(U32.is_eq(b, 10), b, p, ln, rec)
    case QMR{}:
      Csv.v2.hr(Bool.and(U32.is_eq(b, 10), U32.is_eq(q, 0)), b, p, ln, q, nlf, rec)
    case QMD{}:
      QH{QMD{}, p, ln, q, nlf, rec}

def Csv.v2.hstep(+b: U32, st: QH) -> QH:
  match st:
    case QH{md, +p, +ln, +q, +nlf, rec}:
      Csv.v2.hstep.k(md, b, p, ln, q, nlf, rec)

# the bytes of one piece
def Csv.v2.hgo(bs: List<&2, U32>, st: QH) -> QH:
  match bs:
    case Nil{}:
      st
    case b <> t:
      Csv.v2.hgo(t, Csv.v2.hstep(b, st))

type QS is Type:
  QRun{f: File, off: U32, size: U32, hp: U32, h: QH}
  QEnd{size: U32, h: QH}
  QErr{code: U32, msg: String}

# the header step's piece: 64 KiB, or the reader's piece when smaller (tests read with tiny pieces, so
# the header step crosses pieces in every phase)
def Csv.v2.hpiece(+piece: U32) -> U32:
  U32.max(U32.min(piece, 65536), 1)

def Csv.v2.isd(md: QM) -> Bool:
  match md:
    case QMD{}:
      True{}
    case _:
      False{}

def Csv.v2.hend.k(end: Bool, f: File, +off: U32, +size: U32, +hp: U32, h: QH) -> IO(QS):
  match end:
    case True{}:
      do IO<QS>:
        File.close(f)
        return QEnd{size, h}
    case False{}:
      IO.pure(QS, QRun{f, off, size, hp, h})

# after a piece: the record ended, the file ended, or the read gave no byte: stop; else read on at p
def Csv.v2.hnext(f: File, +off: U32, +size: U32, +hp: U32, h: QH) -> IO(QS):
  match h:
    case QH{+md, +p, ln, q, nlf, rec}:
      Csv.v2.hend.k(Bool.or(Csv.v2.isd(md), Bool.or(U32.is_ge(p, size), U32.is_eq(p, off))), f, p, size, hp, QH{md, p, ln, q, nlf, rec})

def Csv.v2.hres(f: File, res: Result<&1, &1, U32 & String, List<&2, U32>>, +off: U32, +size: U32, +hp: U32, h: QH) -> IO(QS):
  match res:
    case Fail{(code, msg)}:
      do IO<QS>:
        File.close(f)
        return QErr{code, msg}
    case Done{bs}:
      Csv.v2.hnext(f, off, size, hp, Csv.v2.hgo(bs, h))

def Csv.v2.hgot(r: File & Result<&1, &1, U32 & String, List<&2, U32>>, +off: U32, +size: U32, +hp: U32, h: QH) -> IO(QS):
  (f, res) = r
  Csv.v2.hres(f, res, off, size, hp, h)

def Csv.v2.hread(st: QS) -> IO(QS):
  match st:
    case QRun{f, +off, +size, +hp, h}:
      do IO<QS>:
        r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_at(f, off, hp)
        Csv.v2.hgot(r, off, size, hp, h)
    case other:
      IO.pure(QS, other)

# one step per piece; the fuel (pieces + 3) never runs out before the file does
def Csv.v2.hloop(fuel: Nat, st: QS) -> IO(QS):
  match fuel:
    case 0n:
      IO.pure(QS, st)
    case 1n+p:
      match st:
        case QRun{f, off, size, hp, h}:
          do IO<QS>:
            st2 : QS <- Csv.v2.hread(QRun{f, off, size, hp, h})
            Csv.v2.hloop(p, st2)
        case other:
          IO.pure(QS, other)

# the header step's answer: an error (IO, malformed), no record at all, or the names, the width, the
# byte offset and physical line where the data starts
type QD is Type:
  QDErr{e: E.Err}
  QDNone{}
  QDOk{names: List<&2, String>, w: U32, off0: U32, line0: U32}

def Csv.v2.hok(hdr: Bool, +off0: U32, +line0: U32, +cs: List<&2, H.CsvCell>) -> QD:
  match hdr:
    case True{}:
      QDOk{Csv.names(cs), U32.from_nat(List.length(&2, H.CsvCell, cs)), off0, line0}
    case False{}:
      QDOk{Csv.gen_names(List.length(&2, H.CsvCell, cs), 0n), U32.from_nat(List.length(&2, H.CsvCell, cs)), 0, 1}

def Csv.v2.hrecs(+hdr: Bool, +off0: U32, +line0: U32, rs: List<&2, H.CsvRec>) -> QD:
  match rs:
    case Nil{}:
      QDErr{Csv.malformed()}
    case H.CsvRec{l, cs} <> t:
      Csv.v2.hok(hdr, off0, line0, cs)

def Csv.v2.hans(+hdr: Bool, +off0: U32, +line0: U32, ans: H.Ans) -> QD:
  match ans:
    case H.Rejected{}:
      QDErr{Csv.malformed()}
    case H.Parsed{rs}:
      Csv.v2.hrecs(hdr, off0, line0, rs)

# the first non-blank record (its bytes newest first): decoded as File.read decodes, parsed by the
# reference parser (a record cut at an LF at even parity is exactly one record unless malformed)
def Csv.v2.hrec(+hdr: Bool, +sep: U32, +off0: U32, +line0: U32, rec: List<&2, U32>) -> QD:
  Csv.v2.hans(hdr, off0, line0, H.parse_sep(sep, Csv.u8(U32.to_nat(U32.inc(off0)), List.reverse(&2, U32, rec))))

# no non-blank record: with a header, no record; without, the empty file has none and a file of
# blank lines is one column of them
def Csv.v2.hnone(hdr: Bool, +size: U32) -> QD:
  match hdr:
    case True{}:
      QDNone{}
    case False{}:
      Bool.pick(QD, U32.is_eq(size, 0), QDNone{}, QDOk{Csv.gen_names(1n, 0n), 1, 0, 1})

def Csv.v2.hfin.m(md: QM, +hdr: Bool, +sep: U32, +size: U32, +p: U32, +ln: U32, +nlf: U32, rec: List<&2, U32>) -> QD:
  match md:
    case QMD{}:
      Csv.v2.hrec(hdr, sep, U32.inc(p), U32.add(ln, U32.inc(nlf)), rec)
    case QMR{}:
      Csv.v2.hrec(hdr, sep, size, U32.add(ln, U32.inc(nlf)), rec)
    case _:
      Csv.v2.hnone(hdr, size)

def Csv.v2.hfin(+hdr: Bool, +sep: U32, +size: U32, h: QH) -> QD:
  match h:
    case QH{md, +p, +ln, q, +nlf, rec}:
      Csv.v2.hfin.m(md, hdr, sep, size, p, ln, nlf, rec)

def Csv.v2.hout(+hdr: Bool, +sep: U32, st: QS) -> IO(QD):
  match st:
    case QEnd{+size, h}:
      IO.pure(QD, Csv.v2.hfin(hdr, sep, size, h))
    case QErr{code, msg}:
      IO.pure(QD, QDErr{E.IoError{code, msg}})
    case QRun{f, off, size, hp, h}:
      do IO<QD>:
        File.close(f)
        return QDErr{E.InvalidOperation{"csv: header read did not finish"}}

def Csv.v2.hsized(+hdr: Bool, +sep: U32, +hp: U32, f: File, res: Result<&1, &1, U32 & String, U32>) -> IO(QD):
  match res:
    case Done{+size}:
      do IO<QD>:
        st : QS <- Csv.v2.hloop(Nat.add(U32.to_nat(U32.div(size, hp)), 3n), QRun{f, 0, size, hp, QH{QM0{}, 0, 1, 0, 0, Nil{}}})
        Csv.v2.hout(hdr, sep, st)
    case Fail{(code, msg)}:
      do IO<QD>:
        File.close(f)
        return QDErr{E.IoError{code, msg}}

def Csv.v2.hsize(+hdr: Bool, +sep: U32, +hp: U32, r: File & Result<&1, &1, U32 & String, U32>) -> IO(QD):
  (f, res) = r
  Csv.v2.hsized(hdr, sep, hp, f, res)

def Csv.v2.hopened(+hdr: Bool, +sep: U32, +hp: U32, o: Result<&1, &1, U32 & String, File>) -> IO(QD):
  match o:
    case Done{f}:
      do IO<QD>:
        r : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
        Csv.v2.hsize(hdr, sep, hp, r)
    case Fail{(code, msg)}:
      IO.pure(QD, QDErr{E.IoError{code, msg}})

# the header step over the file (pieces of hp bytes)
def Csv.v2.header(path: String, +hdr: Bool, +sep: U32, +hp: U32) -> IO(QD):
  do IO<QD>:
    o : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    Csv.v2.hopened(hdr, sep, hp, o)

# ---- 2. the lanes: ONE balanced fork over the region tree --------------------------------------------

type QT is Type:
  QTE{}
  QTL{o: L.LO}
  QTN{l: QT, r: QT}

def Csv.v2.ftree(+ts: List<&2, L.Ty>, +w: U32, +sep: U32, t: P.Rt) -> QT:
  match t:
    case P.RE{}:
      QTE{}
    case P.RL{rg}:
      QTL{L.Ln.lane(ts, w, sep, rg)}
    case P.RN{l, r}:
      a b = Csv.v2.ftree(ts, w, sep, l) Csv.v2.ftree(ts, w, sep, r)
      QTN{a, b}

# the lanes of the tree, in file order, in front of acc
def Csv.v2.flist(t: QT, acc: List<&1, L.LO>) -> List<&1, L.LO>:
  match t:
    case QTE{}:
      acc
    case QTL{o}:
      o <> acc
    case QTN{l, r}:
      Csv.v2.flist(l, Csv.v2.flist(r, acc))

def Csv.v2.lanes(+ts: List<&2, L.Ty>, +w: U32, +sep: U32, regs: List<&1, P.Rg>) -> List<&1, L.LO>:
  Csv.v2.flist(Csv.v2.ftree(ts, w, sep, P.Rt.of(regs)), Nil{})

# already tokenized leading regions (newest first): their typed columns, in file order, in front of acc
def Csv.v2.hcols(tos: List<&1, L.TO>, +ts: List<&2, L.Ty>, +w: U32, acc: List<&1, L.LO>) -> List<&1, L.LO>:
  match tos:
    case Nil{}:
      acc
    case t <> r:
      Csv.v2.hcols(r, ts, w, L.Ln.cols(ts, w, t) <> acc)

# the lanes' dtypes: Str as per-region Dictionaries (TyS) unless the storage is Raw (TyR)
def Csv.v2.ty(t: D.DType, enc: ST.StrEnc) -> L.Ty:
  match t enc:
    case D.TU32{} _:
      L.TyU{}
    case D.TI32{} _:
      L.TyI{}
    case D.TF32{} _:
      L.TyF{}
    case D.TBool{} _:
      L.TyB{}
    case D.TStr{} ST.EncRaw{}:
      L.TyR{}
    case D.TStr{} _:
      L.TyS{}

def Csv.v2.tys(ts: List<&2, D.DType>, +enc: ST.StrEnc) -> List<&2, L.Ty>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> tt:
      Csv.v2.ty(t, enc) <> Csv.v2.tys(tt, enc)

# every column skipped (the lanes only tokenize: the dtype count is wrong)
def Csv.v2.tyn(n: Nat) -> List<&2, L.Ty>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      L.TyN{} <> Csv.v2.tyn(p)

# ---- 3. inference: the regions' classes combined in file order (v0.1's Csv.pick over the first
# `lim` rows; a class field is the first failing row + 1, 0 for none) ------------------------------------

def Csv.v2.ci.f(+g: U32, +l: U32, +off: U32) -> U32:
  Csv.v2.sel(Bool.and(U32.is_eq(g, 0), U32.is_ne(l, 0)), U32.add(off, l), g)

def Csv.v2.ci.one(+off: U32, g: L.CL, l: L.CL) -> L.CL:
  match g l:
    case L.CL{+gu, +gi, +gf, +gb, +gv} L.CL{+lu, +li, +lf, +lb, +lv}:
      L.CL{Csv.v2.ci.f(gu, lu, off), Csv.v2.ci.f(gi, li, off), Csv.v2.ci.f(gf, lf, off), Csv.v2.ci.f(gb, lb, off), Csv.v2.ci.f(gv, lv, off)}

# the global classes so far, and a region's (its rows start at global row off)
def Csv.v2.ci.zip(+off: U32, gs: List<&1, L.CL>, ls: List<&1, L.CL>) -> List<&1, L.CL>:
  match gs ls:
    case g <> gt l <> lt:
      Csv.v2.ci.one(off, g, l) <> Csv.v2.ci.zip(off, gt, lt)
    case other _:
      other

def Csv.v2.ci.zero(n: Nat) -> List<&1, L.CL>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      L.CL{0, 0, 0, 0, 0} <> Csv.v2.ci.zero(p)

def Csv.v2.ci.ok(+x: U32, +lim: U32) -> Bool:
  Bool.or(U32.is_eq(x, 0), U32.is_gt(x, lim))

# a value among the first lim rows; every one of them fits u32, i32, f32, bool
def Csv.v2.ci.dt(+lim: U32, g: L.CL) -> D.DType:
  match g:
    case L.CL{+u, +i, +f, +b, +v}:
      Csv.pick(Bool.and(U32.is_ne(v, 0), U32.is_le(v, lim)), Csv.v2.ci.ok(u, lim), Csv.v2.ci.ok(i, lim), Csv.v2.ci.ok(f, lim), Csv.v2.ci.ok(b, lim))

def Csv.v2.ci.dts(gs: List<&1, L.CL>, +lim: U32) -> List<&2, D.DType>:
  match gs:
    case Nil{}:
      Nil{}
    case g <> t:
      Csv.v2.ci.dt(lim, g) <> Csv.v2.ci.dts(t, lim)

# the head path (lim <= Csv.v2.headmax()): leading regions tokenized and classified one by one until
# they hold lim rows (or one is rejected); their tokens are kept (newest first)
type QHP is Type:
  QHP{tos: List<&1, L.TO>, g: List<&1, L.CL>, off: U32, go: Bool}

type QHR is Type:
  QHR{hp: QHP, rest: List<&1, P.Rg>}

def Csv.v2.headmax() -> U32:
  65536

def Csv.v2.hp.k(+lim: U32, tos: List<&1, L.TO>, g: List<&1, L.CL>, +off: U32, tc: L.TC) -> QHP:
  match tc:
    case L.TC{L.TO{+n, +rej, rag, rgn, sh, lines}, cl}:
      +off2 = U32.add(off, n)
      QHP{L.TO{n, rej, rag, rgn, sh, lines} <> tos, Csv.v2.ci.zip(off, g, cl), off2, Bool.and(U32.is_lt(off2, lim), U32.is_eq(rej, 0))}

def Csv.v2.hp.go(regs: List<&1, P.Rg>, +w: U32, +sep: U32, +lim: U32, st: QHP) -> QHR:
  match regs st:
    case Nil{} other:
      QHR{other, Nil{}}
    case h <> t QHP{tos, g, off, False{}}:
      QHR{QHP{tos, g, off, False{}}, h <> t}
    case h <> t QHP{tos, g, off, True{}}:
      Csv.v2.hp.go(t, w, sep, lim, Csv.v2.hp.k(lim, tos, g, off, L.Ln.cls(w, L.Ln.tok(w, sep, h))))

# the full path (infer_rows = 0 or > headmax): ONE balanced fork classifies every region; the regions
# come back (their bytes only) in file order
type QC is Type:
  QCE{}
  QCL{cr: L.CR}
  QCN{l: QC, r: QC}

def Csv.v2.ctree(+w: U32, +sep: U32, t: P.Rt) -> QC:
  match t:
    case P.RE{}:
      QCE{}
    case P.RL{rg}:
      QCL{L.Ln.clsr(w, sep, rg)}
    case P.RN{l, r}:
      a b = Csv.v2.ctree(w, sep, l) Csv.v2.ctree(w, sep, r)
      QCN{a, b}

def Csv.v2.clist(t: QC, acc: List<&1, L.CR>) -> List<&1, L.CR>:
  match t:
    case QCE{}:
      acc
    case QCL{c}:
      c <> acc
    case QCN{l, r}:
      Csv.v2.clist(l, Csv.v2.clist(r, acc))

type QCA is Type:
  QCA{regs: List<&1, P.Rg>, g: List<&1, L.CL>, off: U32}

def Csv.v2.cone(c: L.CR, st: QCA) -> QCA:
  match c st:
    case L.CR{rg, +n, cl} QCA{regs, g, +off}:
      QCA{rg <> regs, Csv.v2.ci.zip(off, g, cl), U32.add(off, n)}

def Csv.v2.cacc(crs: List<&1, L.CR>, st: QCA) -> QCA:
  match crs:
    case Nil{}:
      st
    case c <> t:
      Csv.v2.cacc(t, Csv.v2.cone(c, st))

# ---- 5. the combine ---------------------------------------------------------------------------------
# the summary: rows, rejected, the first ragged record in region order

type QSM is Data:
  QSM{n: U32, rej: U32, rag: U32, rgn: U32}

def Csv.v2.sum.add(+n: U32, +rej: U32, +rag: U32, +rgn: U32, s: QSM) -> QSM:
  match s:
    case QSM{+n0, +rj, +rg, +rn}:
      +first = Bool.and(U32.is_ne(rag, 0), U32.is_eq(rg, 0))
      QSM{U32.add(n0, n), U32.or(rj, rej), Csv.v2.sel(first, rag, rg), Csv.v2.sel(first, rgn, rn)}

def Csv.v2.sum.one(x: L.LO, st: List<&1, L.LO> & QSM) -> List<&1, L.LO> & QSM:
  match x:
    case L.LO{+n, +rej, +rag, +rgn, lines, cols}:
      (acc, s) = st
      (L.LO{n, rej, rag, rgn, lines, cols} <> acc, Csv.v2.sum.add(n, rej, rag, rgn, s))

# lanes in order -> (lanes in order, summary)
def Csv.v2.sum(xs: List<&1, L.LO>, st: List<&1, L.LO> & QSM) -> List<&1, L.LO> & QSM:
  match xs:
    case Nil{}:
      (acc, s) = st
      (List.reverse(&1, L.LO, acc), s)
    case h <> t:
      Csv.v2.sum(t, Csv.v2.sum.one(h, st))

# column c of every lane: (rows, part); the lanes keep their other columns

def Csv.v2.dummy() -> L.CO:
  L.OW{Array.new(U32, 0n, 0), Array.new(U32, 0n, 0), 0, 0, 0, ""}

def Csv.v2.take.c.k(here: Bool, h: L.CO, r: List<&1, L.CO> & L.CO) -> List<&1, L.CO> & L.CO:
  match here:
    case True{}:
      (t, x) = r
      (Csv.v2.dummy() <> t, h)
    case False{}:
      (t, x) = r
      (h <> t, x)

def Csv.v2.take.c(cols: List<&1, L.CO>, +c: U32) -> List<&1, L.CO> & L.CO:
  match cols:
    case Nil{}:
      (Nil{}, Csv.v2.dummy())
    case h <> t:
      Csv.v2.take.c.k(U32.is_eq(c, 0), h, Csv.v2.take.c(t, U32.sub(c, 1)))

type QP is Type:
  QP{n: U32, co: L.CO}

def Csv.v2.take.k2(+n: U32, +rej: U32, +rag: U32, +rgn: U32, lines: Array<U32>, rest: List<&1, L.LO> & List<&1, QP>, r: List<&1, L.CO> & L.CO) -> List<&1, L.LO> & List<&1, QP>:
  (los, ps) = rest
  (cols, co) = r
  (L.LO{n, rej, rag, rgn, lines, cols} <> los, QP{n, co} <> ps)

def Csv.v2.take.k(+c: U32, x: L.LO, rest: List<&1, L.LO> & List<&1, QP>) -> List<&1, L.LO> & List<&1, QP>:
  match x:
    case L.LO{+n, rej, rag, rgn, lines, cols}:
      Csv.v2.take.k2(n, rej, rag, rgn, lines, rest, Csv.v2.take.c(cols, c))

def Csv.v2.take(+c: U32, xs: List<&1, L.LO>) -> List<&1, L.LO> & List<&1, QP>:
  match xs:
    case Nil{}:
      (Nil{}, Nil{})
    case h <> t:
      Csv.v2.take.k(c, h, Csv.v2.take(c, t))

# out[off + j] = src[perm[j]] for j < n (src and perm consumed, out comes back): a region's Str part
# remapped to the merged codes, or decoded from its entries, straight into the column
def Csv.v2.gput(~T: Data, out: Array<T>, +j: U32, r: Array<T> & T) -> Array<T> & Array<T>:
  (src, x) = r
  (src, Array.set(T, out, j, x))

def Csv.v2.ggo(~T: Data, n: Nat, +j: U32, +off: U32, so: Array<T> & Array<T>, r: Array<U32> & U32) -> Array<T>:
  match n:
    case 0n:
      (src, out) = so
      (perm, i) = r
      out
    case 1n+p:
      (src, out) = so
      (perm, i) = r
      +j2 = U32.inc(j)
      Csv.v2.ggo(~T, p, j2, off, Csv.v2.gput(~T, out, U32.add(off, j), Array.get(T, src, i)), Array.get(U32, perm, j2))

def Csv.v2.gat(~T: Data, +n: U32, +off: U32, out: Array<T>, src: Array<T>, perm: Array<U32>) -> Array<T>:
  Csv.v2.ggo(~T, U32.to_nat(n), 0, off, (src, out), Array.get(U32, perm, 0))

# the column builders: rows so far (off), the arrays, nulls, the first bad cell (first region with one)
type QW is Type:
  QW{off: U32, a: Array<U32>, v: Array<U32>, nulls: U32, bad: U32, bl: U32, bt: String}

type QF is Type:
  QF{off: U32, a: Array<F32>, v: Array<U32>, nulls: U32, bad: U32, bl: U32, bt: String}

# Str: a Dictionary so far (merged codes) or Raw strings
type QX is Type:
  QXD{off: U32, c: Array<U32>, v: Array<U32>, nulls: U32, dict: ST.Dict}
  QXR{off: U32, a: Array<String>, v: Array<U32>, nulls: U32}

def Csv.v2.w.part(+m: U32, co: L.CO, st: QW) -> QW:
  match co st:
    case L.OW{a, v, +nb, +bd, +bl, bt} QW{+off, oa, ov, +nulls, +bad, +obl, obt}:
      +first = Bool.and(U32.is_eq(bad, 0), U32.is_ne(bd, 0))
      QW{U32.add(off, m), K.Kernel.copy_into(~U32, m, off, oa, a), K.Kernel.copy_into(~U32, m, off, ov, v), U32.add(nulls, nb), Csv.v2.sel(first, bd, bad), Csv.v2.sel(first, bl, obl), Bool.pick(String, first, bt, obt)}
    case _ other:
      other

def Csv.v2.f.part(+m: U32, co: L.CO, st: QF) -> QF:
  match co st:
    case L.OF{a, v, +nb, +bd, +bl, bt} QF{+off, oa, ov, +nulls, +bad, +obl, obt}:
      +first = Bool.and(U32.is_eq(bad, 0), U32.is_ne(bd, 0))
      QF{U32.add(off, m), K.Kernel.copy_into(~F32, m, off, oa, a), K.Kernel.copy_into(~U32, m, off, ov, v), U32.add(nulls, nb), Csv.v2.sel(first, bd, bad), Csv.v2.sel(first, bl, obl), Bool.pick(String, first, bt, obt)}
    case _ other:
      other

# the merge of a region's entries (local id order) into the column's dictionary: map[local id] = code;
# stops at the first entry past EncAuto's threshold (over: the column is Raw)
type QG is Type:
  QG{ents: Array<String>, fr: Array<U32>, dict: ST.Dict, map: Array<U32>, over: Bool}

def Csv.v2.mput(+j: U32, +row: U32, +enc: ST.StrEnc, ents: Array<String>, fr: Array<U32>, map: Array<U32>, r: ST.Dict & U32) -> QG:
  (dict, +code) = r
  QG{ents, fr, dict, Array.set(U32, map, j, code), Csv.dict_over(enc, U32.inc(code), U32.inc(row))}

def Csv.v2.mat(+j: U32, +off: U32, +enc: ST.StrEnc, dict: ST.Dict, map: Array<U32>, re: Array<String> & String, rf: Array<U32> & U32) -> QG:
  (ents, s) = re
  (fr, row) = rf
  Csv.v2.mput(j, U32.add(off, row), enc, ents, fr, map, ST.Dict.code(dict, s))

def Csv.v2.mgo(f: Nat, +j: U32, +off: U32, +enc: ST.StrEnc, st: QG) -> QG:
  match f st:
    case 0n other:
      other
    case _ QG{ents, fr, dict, map, True{}}:
      QG{ents, fr, dict, map, True{}}
    case 1n+p QG{ents, fr, dict, map, False{}}:
      Csv.v2.mgo(p, U32.inc(j), off, enc, Csv.v2.mat(j, off, enc, dict, map, Array.get(String, ents, j), Array.get(U32, fr, j)))

# a part decoded into the Raw column: its rows are its entries by local code (a null row holds the
# empty content's entry, "", as a v0.1 Raw null slot)
def Csv.v2.x.raw(+m: U32, +off: U32, +nulls: U32, oa: Array<String>, ov: Array<U32>, c: Array<U32>, v: Array<U32>, ents: Array<String>) -> QX:
  QXR{U32.add(off, m), Csv.v2.gat(~String, m, off, oa, ents, c), K.Kernel.copy_into(~U32, m, off, ov, v), nulls}

# after the merge loop: codes remapped into the column, or (EncAuto's fall back) the rows so far
# decoded from the dictionary and this part decoded from its entries
def Csv.v2.x.dfin(+m: U32, +off: U32, +nulls: U32, +d: Nat, oc: Array<U32>, ov: Array<U32>, c: Array<U32>, v: Array<U32>, g: QG) -> QX:
  match g:
    case QG{ents, fr, dict, map, False{}}:
      QXD{U32.add(off, m), Csv.v2.gat(~U32, m, off, oc, map, c), K.Kernel.copy_into(~U32, m, off, ov, v), nulls, dict}
    case QG{ents, fr, dict, map, True{}}:
      Csv.v2.x.raw(m, off, nulls, ST.Dict.decode(off, d, oc, dict), ov, c, v, ents)

def Csv.v2.x.part(+m: U32, +d: Nat, +enc: ST.StrEnc, co: L.CO, st: QX) -> QX:
  match co st:
    case L.OS{c, v, +nb, +k, ents, fr} QXD{+off, oc, ov, +nulls, dict}:
      Csv.v2.x.dfin(m, off, U32.add(nulls, nb), d, oc, ov, c, v, Csv.v2.mgo(U32.to_nat(k), 0, off, enc, QG{ents, fr, dict, Array.new(U32, K.Kernel.depth_for(U32.max(k, 1)), 0), False{}}))
    case L.OS{c, v, +nb, k, ents, fr} QXR{+off, oa, ov, +nulls}:
      Csv.v2.x.raw(m, off, U32.add(nulls, nb), oa, ov, c, v, ents)
    case L.OR{a, v, +nb} QXR{+off, oa, ov, +nulls}:
      QXR{U32.add(off, m), K.Kernel.copy_into(~String, m, off, oa, a), K.Kernel.copy_into(~U32, m, off, ov, v), U32.add(nulls, nb)}
    case _ other:
      other

def Csv.v2.cat.w(ps: List<&1, QP>, st: QW) -> QW:
  match ps:
    case Nil{}:
      st
    case QP{+m, co} <> t:
      Csv.v2.cat.w(t, Csv.v2.w.part(m, co, st))

def Csv.v2.cat.f(ps: List<&1, QP>, st: QF) -> QF:
  match ps:
    case Nil{}:
      st
    case QP{+m, co} <> t:
      Csv.v2.cat.f(t, Csv.v2.f.part(m, co, st))

def Csv.v2.cat.x(ps: List<&1, QP>, +d: Nat, +enc: ST.StrEnc, st: QX) -> QX:
  match ps:
    case Nil{}:
      st
    case QP{+m, co} <> t:
      Csv.v2.cat.x(t, d, enc, Csv.v2.x.part(m, d, enc, co, st))

def Csv.v2.w.fin.k(isbad: Bool, +name: String, +t: D.DType, +n: U32, +d: Nat, +nulls: U32, a: Array<U32>, v: Array<U32>, +bl: U32, +bt: String) -> E.ResT(C.Named):
  match isbad:
    case True{}:
      Csv.col.err(name, t, bt, bl)
    case False{}:
      Done{C.Named{name, C.Column.mk_w(t, n, d, CB.valid(nulls, v), a)}}

def Csv.v2.w.fin(+name: String, +t: D.DType, +n: U32, +d: Nat, st: QW) -> E.ResT(C.Named):
  match st:
    case QW{off, a, v, +nulls, +bad, +bl, bt}:
      Csv.v2.w.fin.k(U32.is_ne(bad, 0), name, t, n, d, nulls, a, v, bl, bt)

def Csv.v2.f.fin.k(isbad: Bool, +name: String, +t: D.DType, +n: U32, +d: Nat, +nulls: U32, a: Array<F32>, v: Array<U32>, +bl: U32, +bt: String) -> E.ResT(C.Named):
  match isbad:
    case True{}:
      Csv.col.err(name, t, bt, bl)
    case False{}:
      Done{C.Named{name, C.CF32{n, d, CB.valid(nulls, v), a}}}

def Csv.v2.f.fin(+name: String, +t: D.DType, +n: U32, +d: Nat, st: QF) -> E.ResT(C.Named):
  match st:
    case QF{off, a, v, +nulls, +bad, +bl, bt}:
      Csv.v2.f.fin.k(U32.is_ne(bad, 0), name, t, n, d, nulls, a, v, bl, bt)

# a column of no row: v0.1 checks the storage rule once with the dictionary holding only "" (size 1)
# and no row (its builder is fed an empty chunk), so EncAutoAt{0, _} is Raw there
def Csv.v2.x.zero(over0: Bool, +d: Nat, st: QX) -> QX:
  match over0 st:
    case True{} QXD{+off, c, v, +nulls, dict}:
      QXR{off, ST.Dict.decode(0, d, c, dict), v, nulls}
    case _ other:
      other

def Csv.v2.x.fin(+name: String, +n: U32, +d: Nat, st: QX) -> E.ResT(C.Named):
  match st:
    case QXD{off, c, v, +nulls, dict}:
      Done{C.Named{name, C.CStr{n, d, CB.valid(nulls, v), ST.SDict{c, dict}}}}
    case QXR{off, a, v, +nulls}:
      Done{C.Named{name, C.CStr{n, d, CB.valid(nulls, v), ST.SRaw{a}}}}

# one column (2^depth_for(n) slots, AllValid without nulls) from its parts, or its first bad cell
def Csv.v2.col.k(t: L.Ty, +name: String, +dt: D.DType, +n: U32, +d: Nat, +enc: ST.StrEnc, ps: List<&1, QP>) -> E.ResT(C.Named):
  match t:
    case L.TyF{}:
      Csv.v2.f.fin(name, dt, n, d, Csv.v2.cat.f(ps, QF{0, Array.new(F32, d, 0.0), Array.new(U32, d, 0), 0, 0, 0, ""}))
    case L.TyS{}:
      Csv.v2.x.fin(name, n, d, Csv.v2.x.zero(Bool.and(U32.is_eq(n, 0), Csv.dict_over(enc, 1, 0)), d, Csv.v2.cat.x(ps, d, enc, QXD{0, Array.new(U32, d, 0), Array.new(U32, d, 0), 0, ST.Dict.empty()})))
    case L.TyR{}:
      Csv.v2.x.fin(name, n, d, Csv.v2.cat.x(ps, d, enc, QXR{0, Array.new(String, d, ""), Array.new(U32, d, 0), 0}))
    case _:
      Csv.v2.w.fin(name, dt, n, d, Csv.v2.cat.w(ps, QW{0, Array.new(U32, d, 0), Array.new(U32, d, 0), 0, 0, 0, ""}))

# a column to build: its dtypes, name and parts (one per region, region order)
type QK is Type:
  QK{t: L.Ty, name: String, dt: D.DType, ps: List<&1, QP>}

def Csv.v2.kcols.k(t: L.Ty, +name: String, +dt: D.DType, acc: List<&1, QK>, r: List<&1, L.LO> & List<&1, QP>) -> List<&1, L.LO> & List<&1, QK>:
  (los, ps) = r
  (los, QK{t, name, dt, ps} <> acc)

def Csv.v2.kcols.step(t: L.Ty, +name: String, +dt: D.DType, +c: U32, st: List<&1, L.LO> & List<&1, QK>) -> List<&1, L.LO> & List<&1, QK>:
  (los, acc) = st
  Csv.v2.kcols.k(t, name, dt, acc, Csv.v2.take(c, los))

# every column's parts taken out of the lanes (list surgery only, columns x regions; newest first)
def Csv.v2.kcols(ts: List<&2, L.Ty>, dts: List<&2, D.DType>, names: List<&2, String>, +c: U32, st: List<&1, L.LO> & List<&1, QK>) -> List<&1, L.LO> & List<&1, QK>:
  match ts dts names:
    case t <> tt dt <> dtt nm <> nmt:
      Csv.v2.kcols(tt, dtt, nmt, U32.inc(c), Csv.v2.kcols.step(t, nm, dt, c, st))
    case _ _ _:
      st

def Csv.v2.kone(+n: U32, +d: Nat, +enc: ST.StrEnc, k: QK) -> E.ResT(C.Named):
  match k:
    case QK{t, +name, +dt, ps}:
      Csv.v2.col.k(t, name, dt, n, d, enc, ps)

# the columns built by ONE balanced fork over a tree of the columns (paired as P.Rt.of pairs regions:
# halves of similar size; each column's concatenation and dictionary merge is its own, nothing shared
# but scalars)
type QKT is Type:
  QKE{}
  QKL{k: QK}
  QKN{l: QKT, r: QKT}

def Csv.v2.kt.leaves(xs: List<&1, QK>) -> List<&1, QKT>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      QKL{h} <> Csv.v2.kt.leaves(t)

def Csv.v2.kt.pair(xs: List<&1, QKT>) -> List<&1, QKT>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{a, Nil{}}:
      a <> Nil{}
    case Con{a, Con{b, u}}:
      QKN{a, b} <> Csv.v2.kt.pair(u)

def Csv.v2.kt.top(f: Nat, xs: List<&1, QKT>) -> QKT:
  match f xs:
    case _ Nil{}:
      QKE{}
    case _ Con{a, Nil{}}:
      a
    case 0n other:
      QKE{}
    case 1n+p other:
      Csv.v2.kt.top(p, Csv.v2.kt.pair(other))

type QB is Type:
  QBE{}
  QBL{r: E.ResT(C.Named)}
  QBN{l: QB, r: QB}

def Csv.v2.bfork(+n: U32, +d: Nat, +enc: ST.StrEnc, t: QKT) -> QB:
  match t:
    case QKE{}:
      QBE{}
    case QKL{k}:
      QBL{Csv.v2.kone(n, d, enc, k)}
    case QKN{l, r}:
      a b = Csv.v2.bfork(n, d, enc, l) Csv.v2.bfork(n, d, enc, r)
      QBN{a, b}

# the built columns, LAST first (Csv.v2.fold's order)
def Csv.v2.blist(t: QB, acc: List<&1, E.ResT(C.Named)>) -> List<&1, E.ResT(C.Named)>:
  match t:
    case QBE{}:
      acc
    case QBL{r}:
      r <> acc
    case QBN{l, r}:
      Csv.v2.blist(r, Csv.v2.blist(l, acc))

# the first column (in order) holding an error wins
def Csv.v2.fold(rs: List<&1, E.ResT(C.Named)>, acc: E.ResT(List<&1, C.Named>)) -> E.ResT(List<&1, C.Named>):
  match rs:
    case Nil{}:
      acc
    case r <> t:
      Csv.v2.fold(t, Csv.cols.k(r, acc))

def Csv.v2.build.k(+n: U32, +d: Nat, +enc: ST.StrEnc, r: List<&1, L.LO> & List<&1, QK>) -> E.ResT(C.Frame):
  (los, ks) = r
  Csv.fin(Csv.v2.fold(Csv.v2.blist(Csv.v2.bfork(n, d, enc, Csv.v2.kt.top(32n, Csv.v2.kt.leaves(List.reverse(&1, QK, ks)))), Nil{}), Done{Nil{}}))

def Csv.v2.build(+n: U32, ts: List<&2, L.Ty>, dts: List<&2, D.DType>, names: List<&2, String>, +enc: ST.StrEnc, los: List<&1, L.LO>) -> E.ResT(C.Frame):
  Csv.v2.build.k(n, K.Kernel.depth_for(U32.max(n, 1)), enc, Csv.v2.kcols(ts, dts, names, 0, (los, Nil{})))

# ==== the chunk hand-off (W6.6; DESIGN.md 17.5, 16.1 D1, 16.5 D7) ======================================
# With the chunked engine (cexec.bend Exec.run_with_rd(CsvV02{_}, Chunked{g}, ..): a scan_csv collected
# chunked) the combine builds every column of a frame of MORE than 2^g rows straight into the engine's
# chunk trees (CsvChk), so the runner's IScan needs no CFrame.of_frame:
#   * the regions' parts (row ranges in file order, of any length) are cut into leaves of 2^g rows across
#     region boundaries (the last leaf partial): ONE copy per row from the lane buffers into the leaf
#     buffers (Cut.cp / Cut.ga, flat loops), the same row partition for every column and every validity
#     mask, so the frame is WFCFrame and every tree has CH.CW.of's shape exactly (leaf i = rows i * 2^g ..,
#     depth g, pushed on the same binary-counter stack, CH.CWS.push);
#   * a Dictionary column is CSDict{a code tree, ONE Dict}: the merge runs first, over every part in region
#     order (Csv.v2.mgo, the flat combine's loop and its EncAuto stop: the same codes, the same fall back),
#     then the codes are gathered through each part's merge map into the leaves; after EncAuto's fall back
#     the column is Raw and every part is gathered from its own entries (the strings the flat combine gets
#     from Dict.decode for the rows before the fall back are the same decoded strings);
#   * Raw string parts are copied like words; a column without nulls has no mask (CAllValid);
#   * the first bad cell per column (the first part with one) and the column order of errors are the flat
#     combine's (Csv.v2.fold's rule), then Frame.from_columns' DuplicateColumn check over the names in order.
# A frame of at most 2^g rows is the flat combine's frame (CsvFlat: the engine takes it as today's flat
# frame, one leaf when chunked, its buffers moved). Everything before the build (errors, inference, the
# row cap, EncAuto's per-entry rule) is unchanged: the mode only picks the builder at Csv.v2.build.m.
# Parallel shape: Csv.v2.cfork is the one fork (a balanced tree of the columns, built by the sequential
# Csv.v2.kt.* prelude, as Csv.v2.bfork); each column's cut and merge is sequential inside its leaf.

# what the v0.2 reader answers: v0.1's flat frame, or (chunk mode, more than 2^g rows) a chunk frame
type CsvOut is Type:
  CsvFlat{f: C.Frame}
  CsvChk{f: CH.CFrame}

# how the combine builds the columns: flat (every read_csv*) or leaves of 2^g rows (the chunked engine)
type CsvMode is Data:
  CMFlat{}
  CMChk{g: Nat}

# a part to copy (m rows of a lane buffer) / to gather (out[j] = tbl[idx[j]] for j < m)
type CP<-T: Data> is Type:
  CP{m: U32, a: Array<T>}

type GP<-T: Data> is Type:
  GP{m: U32, idx: Array<U32>, tbl: Array<T>}

# the leaves being cut: rows in the current leaf, rows written so far, the current leaf's buffer (2^g
# slots), the full leaves (newest first)
type QL<-T: Data> is Type:
  QL{k: U32, done: U32, cur: Array<T>, full: List<&1, Array<T>>}

def Cut.ql0(~T: Data, +g: Nat, +z: T) -> QL<T>:
  QL{0, 0, Array.new(T, g, z), Nil{}}

# out[doff + j] = src[soff + j] for j < m; both come back (a range of a lane buffer into a leaf)
def Cut.cp.go(~T: Data, f: Nat, +j: U32, +soff: U32, +doff: U32, out: Array<T>, r: Array<T> & T) -> Array<T> & Array<T>:
  match f:
    case 0n:
      (src, x) = r
      (out, src)
    case 1n+p:
      (src, x) = r
      +j2 = U32.inc(j)
      Cut.cp.go(~T, p, j2, soff, doff, Array.set(T, out, U32.add(doff, j), x), Array.get(T, src, U32.add(soff, j2)))

def Cut.cp(~T: Data, +m: U32, +soff: U32, +doff: U32, out: Array<T>, src: Array<T>) -> Array<T> & Array<T>:
  Cut.cp.go(~T, U32.to_nat(m), 0, soff, doff, out, Array.get(T, src, U32.add(soff, 0)))

# out[doff + j] = tbl[idx[soff + j]] for j < m; the three come back as (out, tbl, idx)
def Cut.ga.go(~T: Data, f: Nat, +j: U32, +soff: U32, +doff: U32, to: Array<T> & Array<T>, r: Array<U32> & U32) -> Array<T> & Array<T> & Array<U32>:
  match f:
    case 0n:
      (tbl, out) = to
      (idx, i) = r
      (out, tbl, idx)
    case 1n+p:
      (tbl, out) = to
      (idx, i) = r
      +j2 = U32.inc(j)
      Cut.ga.go(~T, p, j2, soff, doff, Csv.v2.gput(~T, out, U32.add(doff, j), Array.get(T, tbl, i)), Array.get(U32, idx, U32.add(soff, j2)))

def Cut.ga(~T: Data, +m: U32, +soff: U32, +doff: U32, out: Array<T>, tbl: Array<T>, idx: Array<U32>) -> Array<T> & Array<T> & Array<U32>:
  Cut.ga.go(~T, U32.to_nat(m), 0, soff, doff, (tbl, out), Array.get(U32, idx, U32.add(soff, 0)))

# the current leaf after its rows reached k: kept while it has room, else it joins the full leaves and the
# next one starts (a fresh 2^g buffer, or a 1-slot placeholder once all n rows are written)
def Cut.roll(~T: Data, full: Bool, +g: Nat, +n: U32, +k: U32, +done: U32, +z: T, cur: Array<T>, fl: List<&1, Array<T>>) -> QL<T>:
  match full:
    case True{}:
      QL{0, done, Array.new(T, Bool.pick(Nat, U32.is_lt(done, n), g, 0n), z), cur <> fl}
    case False{}:
      QL{k, done, cur, fl}

# ---- copy a part: segments of at most the current leaf's room ----

type QFC<-T: Data> is Type:
  QFC{more: Bool, soff: U32, src: Array<T>, l: QL<T>}

def Cut.cstep.k(~T: Data, +g: Nat, +n: U32, +m: U32, +soff: U32, +t: U32, +room: U32, +k: U32, +done: U32, +z: T, fl: List<&1, Array<T>>, r: Array<T> & Array<T>) -> QFC<T>:
  (cur, src) = r
  +s2 = U32.add(soff, t)
  QFC{U32.is_lt(s2, m), s2, src, Cut.roll(~T, U32.is_eq(t, room), g, n, U32.add(k, t), U32.add(done, t), z, cur, fl)}

def Cut.cstep(~T: Data, +g: Nat, +n: U32, +m: U32, +z: T, +soff: U32, src: Array<T>, l: QL<T>) -> QFC<T>:
  match l:
    case QL{+k, +done, cur, fl}:
      +room = U32.sub(U32.shln(1, g), k)
      +t = U32.min(room, U32.sub(m, soff))
      Cut.cstep.k(~T, g, n, m, soff, t, room, k, done, z, fl, Cut.cp(~T, t, soff, k, cur, src))

def Cut.cfeed(~T: Data, f: Nat, +g: Nat, +n: U32, +m: U32, +z: T, st: QFC<T>) -> QL<T>:
  match f st:
    case 0n QFC{more, soff, src, l}:
      l
    case _ QFC{False{}, soff, src, l}:
      l
    case 1n+p QFC{True{}, +soff, src, l}:
      Cut.cfeed(~T, p, g, n, m, z, Cut.cstep(~T, g, n, m, z, soff, src, l))

# the segments of a part of m rows: at most (m >> g) + 2
def Cut.fuel(+m: U32, +g: Nat) -> Nat:
  1n+1n+U32.to_nat(U32.shrn(m, g))

# every part, in order, cut into the leaves
def Cut.copy(~T: Data, +g: Nat, +n: U32, +z: T, ps: List<&1, CP<T>>, l: QL<T>) -> QL<T>:
  match ps:
    case Nil{}:
      l
    case CP{+m, a} <> t:
      Cut.copy(~T, g, n, z, t, Cut.cfeed(~T, Cut.fuel(m, g), g, n, m, z, QFC{U32.is_lt(0, m), 0, a, l}))

# ---- gather a part: the same segments, out[j] = tbl[idx[j]] ----

type QFG<-T: Data> is Type:
  QFG{more: Bool, soff: U32, idx: Array<U32>, tbl: Array<T>, l: QL<T>}

def Cut.gstep.k(~T: Data, +g: Nat, +n: U32, +m: U32, +soff: U32, +t: U32, +room: U32, +k: U32, +done: U32, +z: T, fl: List<&1, Array<T>>, r: Array<T> & Array<T> & Array<U32>) -> QFG<T>:
  (cur, tbl, idx) = r
  +s2 = U32.add(soff, t)
  QFG{U32.is_lt(s2, m), s2, idx, tbl, Cut.roll(~T, U32.is_eq(t, room), g, n, U32.add(k, t), U32.add(done, t), z, cur, fl)}

def Cut.gstep(~T: Data, +g: Nat, +n: U32, +m: U32, +z: T, +soff: U32, idx: Array<U32>, tbl: Array<T>, l: QL<T>) -> QFG<T>:
  match l:
    case QL{+k, +done, cur, fl}:
      +room = U32.sub(U32.shln(1, g), k)
      +t = U32.min(room, U32.sub(m, soff))
      Cut.gstep.k(~T, g, n, m, soff, t, room, k, done, z, fl, Cut.ga(~T, t, soff, k, cur, tbl, idx))

def Cut.gfeed(~T: Data, f: Nat, +g: Nat, +n: U32, +m: U32, +z: T, st: QFG<T>) -> QL<T>:
  match f st:
    case 0n QFG{more, soff, idx, tbl, l}:
      l
    case _ QFG{False{}, soff, idx, tbl, l}:
      l
    case 1n+p QFG{True{}, +soff, idx, tbl, l}:
      Cut.gfeed(~T, p, g, n, m, z, Cut.gstep(~T, g, n, m, z, soff, idx, tbl, l))

def Cut.gath(~T: Data, +g: Nat, +n: U32, +z: T, ps: List<&1, GP<T>>, l: QL<T>) -> QL<T>:
  match ps:
    case Nil{}:
      l
    case GP{+m, idx, tbl} <> t:
      Cut.gath(~T, g, n, z, t, Cut.gfeed(~T, Cut.fuel(m, g), g, n, m, z, QFG{U32.is_lt(0, m), 0, idx, tbl, l}))

# ---- the leaves in row order, folded into a tree ----

def Cut.last(~T: Data, empty: Bool, cur: Array<T>, fl: List<&1, Array<T>>) -> List<&1, Array<T>>:
  match empty:
    case True{}:
      fl
    case False{}:
      cur <> fl

# the full leaves and the current one if it holds rows, oldest first
def Cut.leaves(~T: Data, l: QL<T>) -> List<&1, Array<T>>:
  match l:
    case QL{+k, done, cur, fl}:
      List.reverse(&1, Array<T>, Cut.last(~T, U32.is_eq(k, 0), cur, fl))

# leaf i's rows: 2^g, the last one n - i * 2^g
def Cut.rows(+g: Nat, +n: U32, +i: U32) -> U32:
  U32.min(U32.shln(1, g), U32.sub(n, U32.shln(i, g)))

def Cut.w.fold(ls: List<&1, Array<U32>>, +i: U32, +g: Nat, +n: U32, s: CH.CWS) -> CH.CW:
  match ls:
    case Nil{}:
      CH.CWS.collapse(s)
    case a <> t:
      +r = Cut.rows(g, n, i)
      Cut.w.fold(t, U32.inc(i), g, n, CH.CWS.push(i, r, CH.WL{r, g, a}, s))

def Cut.f.fold(ls: List<&1, Array<F32>>, +i: U32, +g: Nat, +n: U32, s: CH.CFS) -> CH.CF:
  match ls:
    case Nil{}:
      CH.CFS.collapse(s)
    case a <> t:
      +r = Cut.rows(g, n, i)
      Cut.f.fold(t, U32.inc(i), g, n, CH.CFS.push(i, r, CH.FL{r, g, a}, s))

def Cut.s.fold(ls: List<&1, Array<String>>, +i: U32, +g: Nat, +n: U32, s: CH.CSS) -> CH.CS:
  match ls:
    case Nil{}:
      CH.CSS.collapse(s)
    case a <> t:
      +r = Cut.rows(g, n, i)
      Cut.s.fold(t, U32.inc(i), g, n, CH.CSS.push(i, r, CH.SL{r, g, a}, s))

def Cut.w.tree(+g: Nat, +n: U32, l: QL<U32>) -> CH.CW:
  Cut.w.fold(Cut.leaves(~U32, l), 0, g, n, CH.CWNil{})

def Cut.f.tree(+g: Nat, +n: U32, l: QL<F32>) -> CH.CF:
  Cut.f.fold(Cut.leaves(~F32, l), 0, g, n, CH.CFNil{})

def Cut.s.tree(+g: Nat, +n: U32, l: QL<String>) -> CH.CS:
  Cut.s.fold(Cut.leaves(~String, l), 0, g, n, CH.CSNil{})

# ---- the columns ----

# a column's parts in order: payload parts, validity parts, nulls, the first bad cell (the first part with
# one: its row + 1, line, text)
type QV<-T: Data> is Type:
  QV{ds: List<&1, CP<T>>, vs: List<&1, CP<U32>>, nulls: U32, bad: U32, bl: U32, bt: String}

# a part of an unexpected kind (never: a lane answers its column's kind) as m zero rows
def Cut.zw(+m: U32) -> Array<U32>:
  Array.new(U32, K.Kernel.depth_for(U32.max(m, 1)), 0)

def Csv.v2.ch.w.k(+m: U32, co: L.CO, r: QV<U32>) -> QV<U32>:
  match co r:
    case L.OW{a, v, +nb, +bd, +bl, bt} QV{ds, vs, +nulls, +bad, +obl, obt}:
      +here = U32.is_ne(bd, 0)
      QV{CP{m, a} <> ds, CP{m, v} <> vs, U32.add(nulls, nb), Csv.v2.sel(here, bd, bad), Csv.v2.sel(here, bl, obl), Bool.pick(String, here, bt, obt)}
    case _ QV{ds, vs, +nulls, +bad, +obl, obt}:
      QV{CP{m, Cut.zw(m)} <> ds, CP{m, Cut.zw(m)} <> vs, nulls, bad, obl, obt}

def Csv.v2.ch.w(ps: List<&1, QP>) -> QV<U32>:
  match ps:
    case Nil{}:
      QV{Nil{}, Nil{}, 0, 0, 0, ""}
    case QP{+m, co} <> t:
      Csv.v2.ch.w.k(m, co, Csv.v2.ch.w(t))

def Csv.v2.ch.f.k(+m: U32, co: L.CO, r: QV<F32>) -> QV<F32>:
  match co r:
    case L.OF{a, v, +nb, +bd, +bl, bt} QV{ds, vs, +nulls, +bad, +obl, obt}:
      +here = U32.is_ne(bd, 0)
      QV{CP{m, a} <> ds, CP{m, v} <> vs, U32.add(nulls, nb), Csv.v2.sel(here, bd, bad), Csv.v2.sel(here, bl, obl), Bool.pick(String, here, bt, obt)}
    case _ QV{ds, vs, +nulls, +bad, +obl, obt}:
      QV{CP{m, Array.new(F32, K.Kernel.depth_for(U32.max(m, 1)), 0.0)} <> ds, CP{m, Cut.zw(m)} <> vs, nulls, bad, obl, obt}

def Csv.v2.ch.f(ps: List<&1, QP>) -> QV<F32>:
  match ps:
    case Nil{}:
      QV{Nil{}, Nil{}, 0, 0, 0, ""}
    case QP{+m, co} <> t:
      Csv.v2.ch.f.k(m, co, Csv.v2.ch.f(t))

def Csv.v2.ch.r.k(+m: U32, co: L.CO, r: QV<String>) -> QV<String>:
  match co r:
    case L.OR{a, v, +nb} QV{ds, vs, +nulls, bad, bl, bt}:
      QV{CP{m, a} <> ds, CP{m, v} <> vs, U32.add(nulls, nb), bad, bl, bt}
    case _ QV{ds, vs, +nulls, bad, bl, bt}:
      QV{CP{m, Array.new(String, K.Kernel.depth_for(U32.max(m, 1)), "")} <> ds, CP{m, Cut.zw(m)} <> vs, nulls, bad, bl, bt}

def Csv.v2.ch.r(ps: List<&1, QP>) -> QV<String>:
  match ps:
    case Nil{}:
      QV{Nil{}, Nil{}, 0, 0, 0, ""}
    case QP{+m, co} <> t:
      Csv.v2.ch.r.k(m, co, Csv.v2.ch.r(t))

# the validity tree (the data's partition) or none when no row is null
def Csv.v2.ch.valid(none: Bool, +g: Nat, +n: U32, vs: List<&1, CP<U32>>) -> CH.CValid:
  match none:
    case True{}:
      CH.CAllValid{}
    case False{}:
      CH.CMask{Cut.w.tree(g, n, Cut.copy(~U32, g, n, 0, vs, Cut.ql0(~U32, g, 0)))}

# a bad cell's error as a chunk column's (Csv.col.err's text)
def Csv.v2.ch.err(r: E.ResT(C.Named)) -> E.ResT(CH.CNamed):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{nc}:
      Done{CH.CNamed.of(0n, nc)}

def Csv.v2.ch.wcol.k(isbad: Bool, +name: String, +t: D.DType, +g: Nat, +n: U32, ds: List<&1, CP<U32>>, vs: List<&1, CP<U32>>, +nulls: U32, +bl: U32, +bt: String) -> E.ResT(CH.CNamed):
  match isbad:
    case True{}:
      Csv.v2.ch.err(Csv.col.err(name, t, bt, bl))
    case False{}:
      Done{CH.CNamed{name, CH.CColumn.mk_w(t, n, Csv.v2.ch.valid(U32.is_eq(nulls, 0), g, n, vs), Cut.w.tree(g, n, Cut.copy(~U32, g, n, 0, ds, Cut.ql0(~U32, g, 0))))}}

def Csv.v2.ch.wcol(+name: String, +t: D.DType, +g: Nat, +n: U32, s: QV<U32>) -> E.ResT(CH.CNamed):
  match s:
    case QV{ds, vs, +nulls, +bad, +bl, bt}:
      Csv.v2.ch.wcol.k(U32.is_ne(bad, 0), name, t, g, n, ds, vs, nulls, bl, bt)

def Csv.v2.ch.fcol.k(isbad: Bool, +name: String, +t: D.DType, +g: Nat, +n: U32, ds: List<&1, CP<F32>>, vs: List<&1, CP<U32>>, +nulls: U32, +bl: U32, +bt: String) -> E.ResT(CH.CNamed):
  match isbad:
    case True{}:
      Csv.v2.ch.err(Csv.col.err(name, t, bt, bl))
    case False{}:
      Done{CH.CNamed{name, CH.CF32{n, Csv.v2.ch.valid(U32.is_eq(nulls, 0), g, n, vs), Cut.f.tree(g, n, Cut.copy(~F32, g, n, 0.0, ds, Cut.ql0(~F32, g, 0.0)))}}}

def Csv.v2.ch.fcol(+name: String, +t: D.DType, +g: Nat, +n: U32, s: QV<F32>) -> E.ResT(CH.CNamed):
  match s:
    case QV{ds, vs, +nulls, +bad, +bl, bt}:
      Csv.v2.ch.fcol.k(U32.is_ne(bad, 0), name, t, g, n, ds, vs, nulls, bl, bt)

def Csv.v2.ch.rcol(+name: String, +g: Nat, +n: U32, s: QV<String>) -> E.ResT(CH.CNamed):
  match s:
    case QV{ds, vs, +nulls, bad, bl, bt}:
      Done{CH.CNamed{name, CH.CStr{n, Csv.v2.ch.valid(U32.is_eq(nulls, 0), g, n, vs), CH.CSRaw{Cut.s.tree(g, n, Cut.copy(~String, g, n, "", ds, Cut.ql0(~String, g, "")))}}}}

# ---- a Dictionary column: the merge over every part first (region order), then the cut ----

# a part after the merge: rows, local codes, entries, the merge map (local id -> code; a placeholder for
# the parts after EncAuto's fall back)
type QSP is Type:
  QSP{m: U32, c: Array<U32>, ents: Array<String>, map: Array<U32>}

# the merge state: the column's dictionary, rows so far, fallen back to Raw, the parts and the validity
# parts (newest first), the nulls
type QMS is Type:
  QMS{dict: ST.Dict, off: U32, over: Bool, ps: List<&1, QSP>, vs: List<&1, CP<U32>>, nulls: U32}

def Csv.v2.ch.sg(+m: U32, c: Array<U32>, v: Array<U32>, +nb: U32, ps: List<&1, QSP>, vs: List<&1, CP<U32>>, +nulls: U32, +off: U32, g: QG) -> QMS:
  match g:
    case QG{ents, fr, dict, map, over}:
      QMS{dict, U32.add(off, m), over, QSP{m, c, ents, map} <> ps, CP{m, v} <> vs, U32.add(nulls, nb)}

# one part: merged as Csv.v2.x.part merges it (Csv.v2.mgo from the rows so far, the same stop), or after
# the fall back kept with its entries only
def Csv.v2.ch.sm.one(+m: U32, +enc: ST.StrEnc, co: L.CO, st: QMS) -> QMS:
  match co st:
    case L.OS{c, v, +nb, +k, ents, fr} QMS{dict, +off, False{}, ps, vs, +nulls}:
      Csv.v2.ch.sg(m, c, v, nb, ps, vs, nulls, off, Csv.v2.mgo(U32.to_nat(k), 0, off, enc, QG{ents, fr, dict, Array.new(U32, K.Kernel.depth_for(U32.max(k, 1)), 0), False{}}))
    case L.OS{c, v, +nb, k, ents, fr} QMS{dict, +off, True{}, ps, vs, +nulls}:
      QMS{dict, U32.add(off, m), True{}, QSP{m, c, ents, Array.new(U32, 0n, 0)} <> ps, CP{m, v} <> vs, U32.add(nulls, nb)}
    case _ QMS{dict, +off, over, ps, vs, +nulls}:
      QMS{dict, U32.add(off, m), over, QSP{m, Cut.zw(m), Array.new(String, 0n, ""), Array.new(U32, 0n, 0)} <> ps, CP{m, Cut.zw(m)} <> vs, nulls}

def Csv.v2.ch.sm(+enc: ST.StrEnc, ps: List<&1, QP>, st: QMS) -> QMS:
  match ps:
    case Nil{}:
      st
    case QP{+m, co} <> t:
      Csv.v2.ch.sm(enc, t, Csv.v2.ch.sm.one(m, enc, co, st))

# the merged parts (newest first) as gathers through their maps / from their entries, oldest first
def Csv.v2.ch.gmap(ps: List<&1, QSP>, acc: List<&1, GP<U32>>) -> List<&1, GP<U32>>:
  match ps:
    case Nil{}:
      acc
    case QSP{+m, c, ents, map} <> t:
      Csv.v2.ch.gmap(t, GP{m, c, map} <> acc)

def Csv.v2.ch.gents(ps: List<&1, QSP>, acc: List<&1, GP<String>>) -> List<&1, GP<String>>:
  match ps:
    case Nil{}:
      acc
    case QSP{+m, c, ents, map} <> t:
      Csv.v2.ch.gents(t, GP{m, c, ents} <> acc)

def Csv.v2.ch.scol.k(over: Bool, +name: String, +g: Nat, +n: U32, dict: ST.Dict, ps: List<&1, QSP>, valid: CH.CValid) -> E.ResT(CH.CNamed):
  match over:
    case False{}:
      Done{CH.CNamed{name, CH.CStr{n, valid, CH.CSDict{Cut.w.tree(g, n, Cut.gath(~U32, g, n, 0, Csv.v2.ch.gmap(ps, Nil{}), Cut.ql0(~U32, g, 0))), dict}}}}
    case True{}:
      Done{CH.CNamed{name, CH.CStr{n, valid, CH.CSRaw{Cut.s.tree(g, n, Cut.gath(~String, g, n, "", Csv.v2.ch.gents(ps, Nil{}), Cut.ql0(~String, g, "")))}}}}

def Csv.v2.ch.scol(+name: String, +g: Nat, +n: U32, st: QMS) -> E.ResT(CH.CNamed):
  match st:
    case QMS{dict, off, over, ps, vs, +nulls}:
      Csv.v2.ch.scol.k(over, name, g, n, dict, ps, Csv.v2.ch.valid(U32.is_eq(nulls, 0), g, n, List.reverse(&1, CP<U32>, vs)))

# one column (n > 2^g rows) from its parts, or its first bad cell
def Csv.v2.ch.col(t: L.Ty, +name: String, +dt: D.DType, +g: Nat, +n: U32, +enc: ST.StrEnc, ps: List<&1, QP>) -> E.ResT(CH.CNamed):
  match t:
    case L.TyF{}:
      Csv.v2.ch.fcol(name, dt, g, n, Csv.v2.ch.f(ps))
    case L.TyS{}:
      Csv.v2.ch.scol(name, g, n, Csv.v2.ch.sm(enc, ps, QMS{ST.Dict.empty(), 0, False{}, Nil{}, Nil{}, 0}))
    case L.TyR{}:
      Csv.v2.ch.rcol(name, g, n, Csv.v2.ch.r(ps))
    case _:
      Csv.v2.ch.wcol(name, dt, g, n, Csv.v2.ch.w(ps))

def Csv.v2.ch.kone(+g: Nat, +n: U32, +enc: ST.StrEnc, k: QK) -> E.ResT(CH.CNamed):
  match k:
    case QK{t, +name, +dt, ps}:
      Csv.v2.ch.col(t, name, dt, g, n, enc, ps)

# the columns built by ONE balanced fork over the tree of the columns (Csv.v2.bfork's shape)
type QCB is Type:
  QCBE{}
  QCBL{r: E.ResT(CH.CNamed)}
  QCBN{l: QCB, r: QCB}

def Csv.v2.cfork(+g: Nat, +n: U32, +enc: ST.StrEnc, t: QKT) -> QCB:
  match t:
    case QKE{}:
      QCBE{}
    case QKL{k}:
      QCBL{Csv.v2.ch.kone(g, n, enc, k)}
    case QKN{l, r}:
      a b = Csv.v2.cfork(g, n, enc, l) Csv.v2.cfork(g, n, enc, r)
      QCBN{a, b}

# the built columns, LAST first (Csv.v2.cfold's order)
def Csv.v2.cblist(t: QCB, acc: List<&1, E.ResT(CH.CNamed)>) -> List<&1, E.ResT(CH.CNamed)>:
  match t:
    case QCBE{}:
      acc
    case QCBL{r}:
      r <> acc
    case QCBN{l, r}:
      Csv.v2.cblist(r, Csv.v2.cblist(l, acc))

def Csv.v2.ccons(a: E.ResT(CH.CNamed), b: E.ResT(List<&1, CH.CNamed>)) -> E.ResT(List<&1, CH.CNamed>):
  match a b:
    case Done{x} Done{y}:
      Done{x <> y}
    case Fail{e} _:
      Fail{e}
    case _ Fail{e}:
      Fail{e}

# the first column (in order) holding an error wins (Csv.v2.fold's rule)
def Csv.v2.cfold(rs: List<&1, E.ResT(CH.CNamed)>, acc: E.ResT(List<&1, CH.CNamed>)) -> E.ResT(List<&1, CH.CNamed>):
  match rs:
    case Nil{}:
      acc
    case r <> t:
      Csv.v2.cfold(t, Csv.v2.ccons(r, acc))

# Frame.from_columns' check: the first name (in column order) seen before is a DuplicateColumn
def Csv.v2.dup(ns: List<&2, String>, +seen: List<&2, String>) -> Maybe<&2, E.Err>:
  match ns:
    case Nil{}:
      None{}
    case +x <> t:
      Bool.pick(Maybe<&2, E.Err>, C.Names.has(seen, x), Some{E.DuplicateColumn{x}}, Csv.v2.dup(t, x <> seen))

def Csv.v2.cfin(r: E.ResT(List<&1, CH.CNamed>), +n: U32, dup: Maybe<&2, E.Err>) -> E.ResT(CsvOut):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{cols}:
      match dup:
        case Some{e}:
          Fail{e}
        case None{}:
          Done{CsvChk{CH.CFrame{n, cols}}}

def Csv.v2.cbuild.k(+g: Nat, +n: U32, +enc: ST.StrEnc, dup: Maybe<&2, E.Err>, r: List<&1, L.LO> & List<&1, QK>) -> E.ResT(CsvOut):
  (los, ks) = r
  Csv.v2.cfin(Csv.v2.cfold(Csv.v2.cblist(Csv.v2.cfork(g, n, enc, Csv.v2.kt.top(32n, Csv.v2.kt.leaves(List.reverse(&1, QK, ks)))), Nil{}), Done{Nil{}}), n, dup)

# the chunk frame of n > 2^g rows (the flat build's column parts, cut into leaves)
def Csv.v2.cbuild(+g: Nat, +n: U32, ts: List<&2, L.Ty>, dts: List<&2, D.DType>, +names: List<&2, String>, +enc: ST.StrEnc, los: List<&1, L.LO>) -> E.ResT(CsvOut):
  Csv.v2.cbuild.k(g, n, enc, Csv.v2.dup(names, Nil{}), Csv.v2.kcols(ts, dts, names, 0, (los, Nil{})))

def Csv.v2.flat(r: E.ResT(C.Frame)) -> E.ResT(CsvOut):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      Done{CsvFlat{f}}

def Csv.v2.build.c(big: Bool, +g: Nat, +n: U32, ts: List<&2, L.Ty>, dts: List<&2, D.DType>, +names: List<&2, String>, +enc: ST.StrEnc, los: List<&1, L.LO>) -> E.ResT(CsvOut):
  match big:
    case True{}:
      Csv.v2.cbuild(g, n, ts, dts, names, enc, los)
    case False{}:
      Csv.v2.flat(Csv.v2.build(n, ts, dts, names, enc, los))

# the combine's builder by mode: flat columns, or (chunk mode, more than 2^g rows) chunk trees
def Csv.v2.build.m(cm: CsvMode, +n: U32, ts: List<&2, L.Ty>, dts: List<&2, D.DType>, +names: List<&2, String>, +enc: ST.StrEnc, los: List<&1, L.LO>) -> E.ResT(CsvOut):
  match cm:
    case CMFlat{}:
      Csv.v2.flat(Csv.v2.build(n, ts, dts, names, enc, los))
    case CMChk{+g}:
      Csv.v2.build.c(U32.is_lt(U32.shln(1, g), n), g, n, ts, dts, names, enc, los)

# the error order after malformed and ragged: the dtype count, the row cap, then the columns
def Csv.v2.comb.cap(cm: CsvMode, capd: Maybe<&2, E.Err>, +n: U32, ts: List<&2, L.Ty>, dts: List<&2, D.DType>, names: List<&2, String>, +enc: ST.StrEnc, los: List<&1, L.LO>) -> E.ResT(CsvOut):
  match capd:
    case Some{e}:
      Fail{e}
    case None{}:
      Csv.v2.build.m(cm, n, ts, dts, names, enc, los)

def Csv.v2.comb.c(cm: CsvMode, cnt: Maybe<&2, E.Err>, +cap: U32, +n: U32, ts: List<&2, L.Ty>, dts: List<&2, D.DType>, names: List<&2, String>, +enc: ST.StrEnc, los: List<&1, L.LO>) -> E.ResT(CsvOut):
  match cnt:
    case Some{e}:
      Fail{e}
    case None{}:
      Csv.v2.comb.cap(cm, K.Kernel.check_rows.cap(cap, n), n, ts, dts, names, enc, los)

def Csv.v2.comb.r(cm: CsvMode, rag: Bool, cnt: Maybe<&2, E.Err>, +w: U32, +rg: U32, +line: U32, +cap: U32, +n: U32, ts: List<&2, L.Ty>, dts: List<&2, D.DType>, names: List<&2, String>, +enc: ST.StrEnc, los: List<&1, L.LO>) -> E.ResT(CsvOut):
  match rag:
    case True{}:
      Fail{E.ParseError{line, "expected " ++ U32.show(w) ++ " fields, got " ++ U32.show(rg)}}
    case False{}:
      Csv.v2.comb.c(cm, cnt, cap, n, ts, dts, names, enc, los)

def Csv.v2.comb.m(cm: CsvMode, rej: Bool, cnt: Maybe<&2, E.Err>, +w: U32, +rag: U32, +rg: U32, +cap: U32, +n: U32, ts: List<&2, L.Ty>, dts: List<&2, D.DType>, names: List<&2, String>, +enc: ST.StrEnc, los: List<&1, L.LO>) -> E.ResT(CsvOut):
  match rej:
    case True{}:
      Fail{Csv.malformed()}
    case False{}:
      Csv.v2.comb.r(cm, U32.is_ne(rag, 0), cnt, w, rg, rag, cap, n, ts, dts, names, enc, los)

def Csv.v2.comb.k(cm: CsvMode, sm: QSM, cnt: Maybe<&2, E.Err>, +w: U32, +cap: U32, ts: List<&2, L.Ty>, dts: List<&2, D.DType>, names: List<&2, String>, +enc: ST.StrEnc, los: List<&1, L.LO>) -> E.ResT(CsvOut):
  match sm:
    case QSM{+n, +rej, +rag, +rgn}:
      Csv.v2.comb.m(cm, U32.is_ne(rej, 0), cnt, w, rag, rgn, cap, n, ts, dts, names, enc, los)

def Csv.v2.comb.s(cm: CsvMode, r: List<&1, L.LO> & QSM, cnt: Maybe<&2, E.Err>, +w: U32, +cap: U32, ts: List<&2, L.Ty>, dts: List<&2, D.DType>, names: List<&2, String>, +enc: ST.StrEnc) -> E.ResT(CsvOut):
  (los, sm) = r
  Csv.v2.comb.k(cm, sm, cnt, w, cap, ts, dts, names, enc, los)

# the lanes (file order) combined: cnt is the dtype-count error, if any
def Csv.v2.fin(cm: CsvMode, cnt: Maybe<&2, E.Err>, ts: List<&2, L.Ty>, dts: List<&2, D.DType>, names: List<&2, String>, +w: U32, +cap: U32, +enc: ST.StrEnc, los: List<&1, L.LO>) -> E.ResT(CsvOut):
  Csv.v2.comb.s(cm, Csv.v2.sum(los, (Nil{}, QSM{0, 0, 0, 0})), cnt, w, cap, ts, dts, names, enc)

# ---- the paths by schema --------------------------------------------------------------------------------

# inferred, head path: the kept tokens' columns, then the fork over the rest
def Csv.v2.head.t(cm: CsvMode, +tys: List<&2, L.Ty>, dts: List<&2, D.DType>, +w: U32, +sep: U32, +cap: U32, +enc: ST.StrEnc, names: List<&2, String>, tos: List<&1, L.TO>, rest: List<&1, P.Rg>) -> E.ResT(CsvOut):
  Csv.v2.fin(cm, None{}, tys, dts, names, w, cap, enc, Csv.v2.hcols(tos, tys, w, Csv.v2.lanes(tys, w, sep, rest)))

def Csv.v2.head.d(cm: CsvMode, +dts: List<&2, D.DType>, +w: U32, +sep: U32, +cap: U32, +enc: ST.StrEnc, names: List<&2, String>, tos: List<&1, L.TO>, rest: List<&1, P.Rg>) -> E.ResT(CsvOut):
  Csv.v2.head.t(cm, Csv.v2.tys(dts, enc), dts, w, sep, cap, enc, names, tos, rest)

def Csv.v2.head.k(cm: CsvMode, +w: U32, +sep: U32, +cap: U32, +lim: U32, +enc: ST.StrEnc, names: List<&2, String>, r: QHR) -> E.ResT(CsvOut):
  match r:
    case QHR{QHP{tos, g, off, go}, rest}:
      Csv.v2.head.d(cm, Csv.v2.ci.dts(g, lim), w, sep, cap, enc, names, tos, rest)

# inferred, full path, and explicit dtypes: one fork of whole lanes over the regions
def Csv.v2.whole(cm: CsvMode, cnt: Maybe<&2, E.Err>, +tys: List<&2, L.Ty>, dts: List<&2, D.DType>, +w: U32, +sep: U32, +cap: U32, +enc: ST.StrEnc, names: List<&2, String>, regs: List<&1, P.Rg>) -> E.ResT(CsvOut):
  Csv.v2.fin(cm, cnt, tys, dts, names, w, cap, enc, Csv.v2.lanes(tys, w, sep, regs))

def Csv.v2.full.d(cm: CsvMode, +dts: List<&2, D.DType>, +w: U32, +sep: U32, +cap: U32, +enc: ST.StrEnc, names: List<&2, String>, regs: List<&1, P.Rg>) -> E.ResT(CsvOut):
  Csv.v2.whole(cm, None{}, Csv.v2.tys(dts, enc), dts, w, sep, cap, enc, names, regs)

def Csv.v2.full.k(cm: CsvMode, +w: U32, +sep: U32, +cap: U32, +lim: U32, +enc: ST.StrEnc, names: List<&2, String>, st: QCA) -> E.ResT(CsvOut):
  match st:
    case QCA{regs, g, off}:
      Csv.v2.full.d(cm, Csv.v2.ci.dts(g, lim), w, sep, cap, enc, names, List.reverse(&1, P.Rg, regs))

def Csv.v2.infer(cm: CsvMode, head: Bool, +w: U32, +sep: U32, +cap: U32, +lim: U32, +enc: ST.StrEnc, names: List<&2, String>, regs: List<&1, P.Rg>) -> E.ResT(CsvOut):
  match head:
    case True{}:
      Csv.v2.head.k(cm, w, sep, cap, lim, enc, names, Csv.v2.hp.go(regs, w, sep, lim, QHP{Nil{}, Csv.v2.ci.zero(U32.to_nat(w)), 0, True{}}))
    case False{}:
      Csv.v2.full.k(cm, w, sep, cap, lim, enc, names, Csv.v2.cacc(Csv.v2.clist(Csv.v2.ctree(w, sep, P.Rt.of(regs)), Nil{}), QCA{Nil{}, Csv.v2.ci.zero(U32.to_nat(w)), 0}))

# explicit dtypes: a wrong count only tokenizes (malformed and ragged outrank it)
def Csv.v2.exp(cm: CsvMode, cnt: Maybe<&2, E.Err>, +ts: List<&2, D.DType>, +w: U32, +sep: U32, +cap: U32, +enc: ST.StrEnc, names: List<&2, String>, regs: List<&1, P.Rg>) -> E.ResT(CsvOut):
  match cnt:
    case Some{e}:
      Csv.v2.whole(cm, Some{e}, Csv.v2.tyn(U32.to_nat(w)), ts, w, sep, cap, enc, names, regs)
    case None{}:
      Csv.v2.whole(cm, None{}, Csv.v2.tys(ts, enc), ts, w, sep, cap, enc, names, regs)

def Csv.v2.mode(cm: CsvMode, ts: List<&2, D.DType>, +w: U32, +sep: U32, +lim: U32, +cap: U32, +enc: ST.StrEnc, names: List<&2, String>, regs: List<&1, P.Rg>) -> E.ResT(CsvOut):
  match ts:
    case Nil{}:
      Csv.v2.infer(cm, U32.is_le(lim, Csv.v2.headmax()), w, sep, cap, lim, enc, names, regs)
    case +t <> +tt:
      Csv.v2.exp(cm, Csv.ts.err(t <> tt, U32.to_nat(w)), t <> tt, w, sep, cap, enc, names, regs)

def Csv.v2.odd(cm: CsvMode, odd: Bool, ts: List<&2, D.DType>, +w: U32, +sep: U32, +lim: U32, +cap: U32, +enc: ST.StrEnc, names: List<&2, String>, regs: List<&1, P.Rg>) -> E.ResT(CsvOut):
  match odd:
    case True{}:
      Fail{Csv.malformed()}
    case False{}:
      Csv.v2.mode(cm, ts, w, sep, lim, cap, enc, names, regs)

def Csv.v2.prod(cm: CsvMode, o: P.PrOut, ts: List<&2, D.DType>, +w: U32, +sep: U32, +lim: U32, +cap: U32, +enc: ST.StrEnc, names: List<&2, String>) -> E.ResT(CsvOut):
  match o:
    case P.PrErr{code, msg}:
      Fail{E.IoError{code, msg}}
    case P.PrOk{nr, odd, regs}:
      Csv.v2.odd(cm, U32.is_ne(odd, 0), ts, w, sep, lim, cap, enc, names, regs)

def Csv.v2.go(cm: CsvMode, hd: QD, path: String, +sep: U32, +lim: U32, +piece: U32, +cap: U32, ts: List<&2, D.DType>, +enc: ST.StrEnc) -> IO(E.ResT(CsvOut)):
  match hd:
    case QDErr{e}:
      IO.pure(E.ResT(CsvOut), Fail{e})
    case QDNone{}:
      IO.pure(E.ResT(CsvOut), Csv.v2.flat(Csv.rows.none(Csv.ts.err(ts, 0n))))
    case QDOk{names, +w, off0, line0}:
      do IO<E.ResT(CsvOut)>:
        o : P.PrOut <- P.Pr.regions(path, off0, line0, piece)
        return Csv.v2.prod(cm, o, ts, w, sep, lim, cap, enc, names)

def Csv.v2.start(cm: CsvMode, +path: String, +hdr: Bool, +sep: U32, +lim: U32, +piece: U32, +cap: U32, ts: List<&2, D.DType>, +enc: ST.StrEnc) -> IO(E.ResT(CsvOut)):
  do IO<E.ResT(CsvOut)>:
    hd : QD <- Csv.v2.header(path, hdr, sep, Csv.v2.hpiece(piece))
    Csv.v2.go(cm, hd, path, sep, lim, piece, cap, ts, enc)

# an ASCII separator: the v0.2 path; any other: the v0.1 reader (the lane compares bytes)
def Csv.v2.ascii(cm: CsvMode, ascii: Bool, path: String, +sep: Char, +hdr: Bool, +inf: U32, +piece: U32, +cap: U32, ts: List<&2, D.DType>, +enc: ST.StrEnc) -> IO(E.ResT(CsvOut)):
  match ascii:
    case True{}:
      Csv.v2.start(cm, path, hdr, Char.to_u32(sep), Csv.limit(inf), piece, cap, ts, enc)
    case False{}:
      do IO<E.ResT(CsvOut)>:
        r : E.ResT(C.Frame) <- Csv.read_full(path, CsvOpts{sep, hdr, inf}, ts, enc, Csv.chunk(), cap)
        return Csv.v2.flat(r)

def Csv.v2.chk(cm: CsvMode, bad: Maybe<&2, E.Err>, path: String, +sep: Char, +hdr: Bool, +inf: U32, +piece: U32, +cap: U32, ts: List<&2, D.DType>, +enc: ST.StrEnc) -> IO(E.ResT(CsvOut)):
  match bad:
    case Some{e}:
      IO.pure(E.ResT(CsvOut), Fail{e})
    case None{}:
      Csv.v2.ascii(cm, U32.is_lt(Char.to_u32(sep), 128), path, sep, hdr, inf, piece, cap, ts, enc)

# the v0.2 reader by build mode (W6.6): CMFlat answers CsvFlat (Csv.read_v02_full's frame); CMChk{g}
# answers, for a frame of more than 2^g rows, its chunk frame (CsvChk: leaves of 2^g rows built by the
# combine, DESIGN.md 17.5), else the same flat frame. The same errors in the same order either way.
def Csv.read_v02_mode(cm: CsvMode, path: String, +opts: CsvOpts, ts: List<&2, D.DType>, enc: ST.StrEnc, +piece: U32, +cap: U32) -> IO(E.ResT(CsvOut)):
  match opts:
    case CsvOpts{+sep, +hdr, +inf}:
      Csv.v2.chk(cm, Csv.sep_err(sep), path, sep, hdr, inf, piece, cap, ts, enc)

# a flat answer (a chunk frame is flattened: never met under CMFlat)
def Csv.v2.unflat(r: E.ResT(CsvOut)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{o}:
      match o:
        case CsvFlat{f}:
          Done{f}
        case CsvChk{f}:
          Done{CH.CFrame.to_frame(f)}

# the v0.2 reader with every knob (Csv.read_full's): the piece size in bytes (tests use tiny ones), the
# row cap, the Str storage. Answers what Csv.read_full answers (DESIGN.md 15.6, 17.4).
def Csv.read_v02_full(path: String, +opts: CsvOpts, ts: List<&2, D.DType>, enc: ST.StrEnc, +piece: U32, +cap: U32) -> IO(E.ResT(C.Frame)):
  do IO<E.ResT(C.Frame)>:
    r : E.ResT(CsvOut) <- Csv.read_v02_mode(CMFlat{}, path, opts, ts, enc, piece, cap)
    return Csv.v2.unflat(r)

# the reader by engine: Csv.read_enc_v01 (v0.1) or the v0.2 reader at its piece size
def Csv.read_eng(eng: CsvEngine, path: String, opts: CsvOpts, ts: List<&2, D.DType>, enc: ST.StrEnc) -> IO(E.ResT(C.Frame)):
  match eng:
    case CsvV01{}:
      Csv.read_enc_v01(path, opts, ts, enc)
    case CsvV02{+piece}:
      Csv.read_v02_full(path, opts, ts, enc, piece, K.Kernel.max_rows())

# the reader by engine for the chunked runner (W6.6, src/cexec.bend's scans): v0.1 answers its flat frame;
# v0.2 by the build mode (CMChk{g}: a frame of more than 2^g rows straight into chunk leaves, Csv.read_v02_mode)
def Csv.read_eng_m(eng: CsvEngine, cm: CsvMode, path: String, opts: CsvOpts, ts: List<&2, D.DType>, enc: ST.StrEnc) -> IO(E.ResT(CsvOut)):
  match eng:
    case CsvV01{}:
      do IO<E.ResT(CsvOut)>:
        r : E.ResT(C.Frame) <- Csv.read_enc_v01(path, opts, ts, enc)
        return Csv.v2.flat(r)
    case CsvV02{+piece}:
      Csv.read_v02_mode(cm, path, opts, ts, enc, piece, K.Kernel.max_rows())

# ---- the default readers (W8: by Csv.engine_default, the v0.2 reader) --------------------------------
# Csv.read_with with the Str storage chosen (EncRaw / EncDict / EncAuto), by the DEFAULT reader engine
# (Csv.engine_default: the v0.2 reader since W8, DESIGN.md 14 "W8: the v0.2 reader is the default")
def Csv.read_enc(path: String, opts: CsvOpts, ts: List<&2, D.DType>, enc: ST.StrEnc) -> IO(E.ResT(C.Frame)):
  Csv.read_eng(Csv.engine_default(), path, opts, ts, enc)

# Strict explicit dtypes (by column position), see Csv.parse_with.
def Csv.read_with(path: String, opts: CsvOpts, ts: List<&2, D.DType>) -> IO(E.ResT(C.Frame)):
  Csv.read_enc(path, opts, ts, Csv.enc_default())

def Csv.read(path: String, opts: CsvOpts) -> IO(E.ResT(C.Frame)):
  Csv.read_with(path, opts, Nil{})
