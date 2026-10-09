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

def CBs.feed.k(a: CB, r: List<&1, CB>) -> List<&1, CB>:
  a <> r

# every column of a chunk in parallel (a parallel let per column, as Csv.cols built them)
def CBs.feed(cbs: List<&1, CB>, cols: List<&2, List<&2, H.CsvCell>>, +ls: List<&2, U32>) -> List<&1, CB>:
  match cbs cols:
    case cb <> ct c <> cst:
      a r = CB.feed(c, ls, cb) CBs.feed(ct, cst, ls)
      CBs.feed.k(a, r)
    case _ _:
      Nil{}

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

# Csv.read_with with the Str storage chosen (EncRaw / EncDict / EncAuto)
def Csv.read_enc(path: String, opts: CsvOpts, ts: List<&2, D.DType>, enc: ST.StrEnc) -> IO(E.ResT(C.Frame)):
  Csv.read_full(path, opts, ts, enc, Csv.chunk(), K.Kernel.max_rows())

# Strict explicit dtypes (by column position), see Csv.parse_with.
def Csv.read_with(path: String, opts: CsvOpts, ts: List<&2, D.DType>) -> IO(E.ResT(C.Frame)):
  Csv.read_enc(path, opts, ts, Csv.enc_default())

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
