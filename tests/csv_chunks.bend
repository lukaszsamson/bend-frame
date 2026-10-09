# M4 streaming reader: a file read in tiny chunks (1, 2, 3, 7 and 64 bytes: records, quoted
# fields with line ends, CRLF pairs and UTF-8 sequences cut across chunk ends; a chunk without a
# line end doubles) gives the same dump as one read in 1 MiB chunks, and the Dictionary and
# by-cardinality Str storages (EncDict, EncAuto) give the same dump as Raw. Each line names a
# file and options; `same` means every variant's DF.dump equals the 1 MiB Raw read's (which the
# CSV tests pin: tests/csv_*, tests/regress/B02_*).
import Base
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/csv.bend as V
import ./../src/strs.bend as ST

def rd(+path: String, +opts: V.CsvOpts, +ts: List<&2, D.DType>, enc: ST.StrEnc, +chunk: U32) -> IO(String):
  do IO<String>:
    r : E.ResT(C.Frame) <- V.Csv.read_full(path, opts, ts, enc, chunk, 8388608)
    return DF.dump(r)

def verdict(+tag: String, +base: String, +xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      tag ++ ": same"
    case h <> t:
      Bool.pick(String, String.eq(h, base), verdict(tag, base, t), tag ++ ": DIFF\n" ++ base ++ "\n" ++ h)

# "frame" or the error dump's text
def first.line(+s: String) -> String:
  Bool.pick(String, String.starts_with(s, "frame"), "frame", String.trim(s))

# the 1 MiB Raw read against the other chunk sizes and storages; the first dump line too
# (frame or error) so a test of errors cannot pass by accident
def chk(+tag: String, +path: String, +opts: V.CsvOpts, +ts: List<&2, D.DType>) -> IO(Unit):
  do IO<Unit>:
    +base : String <- rd(path, opts, ts, ST.EncRaw{}, 1048576)
    c1 : String <- rd(path, opts, ts, ST.EncRaw{}, 1)
    c2 : String <- rd(path, opts, ts, ST.EncRaw{}, 2)
    c3 : String <- rd(path, opts, ts, ST.EncDict{}, 3)
    c7 : String <- rd(path, opts, ts, ST.EncAuto{}, 7)
    c64 : String <- rd(path, opts, ts, ST.EncRaw{}, 64)
    d0 : String <- rd(path, opts, ts, ST.EncDict{}, 1048576)
    a0 : String <- rd(path, opts, ts, ST.EncAuto{}, 1048576)
    IO.print(verdict(tag ++ " (" ++ first.line(base) ++ ")", base, [c1, c2, c3, c7, c64, d0, a0]))

def o(+hdr: Bool, +inf: U32) -> V.CsvOpts:
  V.CsvOpts{',', hdr, inf}

def main() -> IO(Unit):
  do IO<Unit>:
    chk("tiny", "bench/fixtures/tiny.csv", V.Csv.default(), [])
    chk("products", "bench/fixtures/products.csv", V.Csv.default(), [])
    chk("orders", "bench/fixtures/orders.csv", V.Csv.default(), [])
    chk("signups_sep", "bench/fixtures/signups_sep.csv", V.Csv.default(), [])
    chk("blocked", "bench/fixtures/blocked.csv", V.Csv.default(), [])
    chk("dirty", "examples/data/dirty.csv", V.Csv.default(), [])
    chk("numeric", "tests/regress/data/B02_a_numeric.csv", V.Csv.default(), [])
    chk("one col", "tests/regress/data/B02_a_one_col.csv", V.Csv.default(), [])
    chk("quoted empty", "tests/regress/data/B02_a_quoted_empty.csv", V.Csv.default(), [])
    chk("tail bad value", "tests/regress/data/B02_c_tail_badvalue.csv", o(True{}, 2), [])
    chk("tail malformed", "tests/regress/data/B02_c_tail_malformed.csv", V.Csv.default(), [])
    chk("semicolon", "tests/regress/data/B02_e_semicolon.csv", V.CsvOpts{';', True{}, 100}, [])
    chk("line", "tests/regress/data/B02_f_line.csv", V.Csv.default(), [])
    chk("one col blanks", "tests/regress/data/B02_f_one_col.csv", V.Csv.default(), [])
    chk("two col blanks", "tests/regress/data/B02_f_two_col.csv", V.Csv.default(), [])
    chk("long record", "tests/regress/data/B02_g_long.csv", V.Csv.default(), [])
    chk("short record", "tests/regress/data/B02_g_short.csv", V.Csv.default(), [])
    chk("crlf", "tests/regress/data/B02_h_crlf.csv", V.Csv.default(), [])
    chk("h line", "tests/regress/data/B02_h_line.csv", V.Csv.default(), [])
    chk("h text", "tests/regress/data/B02_h_text.csv", V.Csv.default(), [])
    chk("trim", "tests/regress/data/B02_j_trim.csv", V.Csv.default(), [])
    chk("scan blank", "tests/regress/data/B02_scan_blank.csv", V.Csv.default(), [])
    chk("scan blank no header", "tests/regress/data/B02_scan_blank.csv", o(False{}, 100), [])
    chk("scan blank crlf", "tests/regress/data/B02_scan_blank_crlf.csv", o(True{}, 2), [])
    chk("scan blank infer", "tests/regress/data/B02_scan_blank_infer.csv", o(True{}, 2), [])
    chk("scan blank one", "tests/regress/data/B02_scan_blank_one.csv", V.Csv.default(), [])
    chk("scan blank one no header", "tests/regress/data/B02_scan_blank_one.csv", o(False{}, 0), [])
    chk("scan blank quoted", "tests/regress/data/B02_scan_blank_quoted.csv", o(True{}, 1), [])
    chk("scan empty", "tests/regress/data/B02_scan_empty.csv", V.Csv.default(), [])
    chk("scan empty dtypes", "tests/regress/data/B02_scan_empty.csv", V.Csv.default(), [D.TU32{}])
    chk("scan header", "tests/regress/data/B02_scan_header.csv", V.Csv.default(), [])
    chk("scan latin1", "tests/regress/data/B02_scan_latin1.csv", V.Csv.default(), [])
    chk("scan long", "tests/regress/data/B02_scan_long.csv", o(True{}, 0), [])
    chk("scan long infer 2", "tests/regress/data/B02_scan_long.csv", o(True{}, 2), [])
    chk("scan quotes", "tests/regress/data/B02_scan_quotes.csv", V.Csv.default(), [])
    chk("scan ragged", "tests/regress/data/B02_scan_ragged.csv", o(True{}, 1), [])
    chk("scan unicode", "tests/regress/data/B02_scan_unicode.csv", V.Csv.default(), [])
    chk("scan utf8 bad", "tests/regress/data/B02_scan_utf8_bad.bin", V.Csv.default(), [])
    chk("tiny dtypes", "bench/fixtures/tiny.csv", V.Csv.default(), [D.TU32{}, D.TStr{}, D.TStr{}, D.TU32{}, D.TF32{}, D.TF32{}, D.TBool{}])
    chk("tiny bad dtypes", "bench/fixtures/tiny.csv", V.Csv.default(), [D.TU32{}, D.TU32{}, D.TStr{}, D.TU32{}, D.TF32{}, D.TF32{}, D.TBool{}])
    chk("tiny dtype count", "bench/fixtures/tiny.csv", V.Csv.default(), [D.TU32{}])
    chk("tiny no header", "bench/fixtures/tiny.csv", o(False{}, 100), [])

#|tiny (frame): same
#|products (frame): same
#|orders (frame): same
#|signups_sep (frame): same
#|blocked (frame): same
#|dirty (frame): same
#|numeric (frame): same
#|one col (frame): same
#|quoted empty (frame): same
#|tail bad value (error	ParseError at line 5001: column id: cannot parse "x" as u32): same
#|tail malformed (error	ParseError at line 0: malformed csv): same
#|semicolon (frame): same
#|line (error	ParseError at line 4: expected 2 fields, got 1): same
#|one col blanks (frame): same
#|two col blanks (frame): same
#|long record (error	ParseError at line 3: expected 2 fields, got 3): same
#|short record (error	ParseError at line 3: expected 2 fields, got 1): same
#|crlf (frame): same
#|h line (error	ParseError at line 4: expected 2 fields, got 1): same
#|h text (frame): same
#|trim (frame): same
#|scan blank (frame): same
#|scan blank no header (frame): same
#|scan blank crlf (frame): same
#|scan blank infer (frame): same
#|scan blank one (frame): same
#|scan blank one no header (frame): same
#|scan blank quoted (error	ParseError at line 6: column b: cannot parse "q" as u32): same
#|scan empty (frame): same
#|scan empty dtypes (error	InvalidOperation: csv schema: 1 dtypes for 0 columns): same
#|scan header (frame): same
#|scan latin1 (frame): same
#|scan long (frame): same
#|scan long infer 2 (error	ParseError at line 5: column id: cannot parse "foo" as u32): same
#|scan quotes (frame): same
#|scan ragged (error	ParseError at line 3: expected 2 fields, got 1): same
#|scan unicode (frame): same
#|scan utf8 bad (error	ParseError at line 0: malformed csv): same
#|tiny dtypes (frame): same
#|tiny bad dtypes (error	ParseError at line 2: column region: cannot parse "inland" as u32): same
#|tiny dtype count (error	InvalidOperation: csv schema: 1 dtypes for 7 columns): same
#|tiny no header (frame): same
