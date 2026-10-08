# B02-c: Csv.scan_fields_with -- the bounded prefix read of scan_csv (DESIGN.md 15.6.4),
# with tiny chunks so that the chunk logic is exercised: a chunk cut inside a multi-byte
# character or inside a quoted field, a line longer than the chunk, a quote state carried
# across chunks, a file without a final newline, an empty file, errors in the prefix.
# Every chunk size of a case must print the same schema.
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/csv.bend as V

def fields.go(xs: List<&2, V.CsvField>) -> String:
  match xs:
    case Nil{}:
      "."
    case V.CsvField{name, dtype} <> t:
      name ++ ":" ++ D.DType.show(dtype) ++ " " ++ fields.go(t)

def fields(r: E.Res(List<&2, V.CsvField>)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{xs}:
      fields.go(xs)

def scan(+tag: String, +path: String, +opts: V.CsvOpts, +chunk: U32) -> IO(Unit):
  do IO<Unit>:
    r : E.Res(List<&2, V.CsvField>) <- V.Csv.scan_fields_with(path, opts, chunk)
    IO.print(tag ++ " chunk " ++ U32.show(chunk) ++ ": " ++ fields(r) ++ "\n")

def main() -> IO(Unit):
  do IO<Unit>:
    scan("unicode", "tests/regress/data/B02_scan_unicode.csv", V.Csv.default(), 3)
    scan("unicode", "tests/regress/data/B02_scan_unicode.csv", V.Csv.default(), 7)
    scan("unicode", "tests/regress/data/B02_scan_unicode.csv", V.Csv.default(), 64)
    scan("unicode", "tests/regress/data/B02_scan_unicode.csv", V.Csv.default(), 65536)
    scan("quotes", "tests/regress/data/B02_scan_quotes.csv", V.Csv.default(), 5)
    scan("quotes", "tests/regress/data/B02_scan_quotes.csv", V.Csv.default(), 16)
    scan("quotes", "tests/regress/data/B02_scan_quotes.csv", V.Csv.default(), 65536)
    scan("long all", "tests/regress/data/B02_scan_long.csv", V.CsvOpts{',', True{}, 0}, 4)
    scan("long all", "tests/regress/data/B02_scan_long.csv", V.CsvOpts{',', True{}, 0}, 64)
    scan("long 2 rows", "tests/regress/data/B02_scan_long.csv", V.CsvOpts{',', True{}, 2}, 4)
    scan("long 2 rows", "tests/regress/data/B02_scan_long.csv", V.CsvOpts{',', True{}, 2}, 65536)
    scan("blank crlf", "tests/regress/data/B02_scan_blank.csv", V.Csv.default(), 6)
    scan("blank crlf", "tests/regress/data/B02_scan_blank.csv", V.Csv.default(), 65536)
    scan("ragged", "tests/regress/data/B02_scan_ragged.csv", V.Csv.default(), 5)
    scan("ragged", "tests/regress/data/B02_scan_ragged.csv", V.Csv.default(), 65536)
    scan("ragged beyond the prefix", "tests/regress/data/B02_scan_ragged.csv", V.CsvOpts{',', True{}, 1}, 65536)
    scan("empty", "tests/regress/data/B02_scan_empty.csv", V.Csv.default(), 8)
    scan("header only", "tests/regress/data/B02_scan_header.csv", V.Csv.default(), 2)
    scan("header only", "tests/regress/data/B02_scan_header.csv", V.Csv.default(), 65536)
    scan("no header", "tests/regress/data/B02_scan_blank.csv", V.CsvOpts{',', False{}, 100}, 5)
    scan("missing", "tests/regress/data/B02_scan_missing.csv", V.Csv.default(), 8)
#|unicode chunk 3: 名前:str n:u32 ü:str .
#|
#|unicode chunk 7: 名前:str n:u32 ü:str .
#|
#|unicode chunk 64: 名前:str n:u32 ü:str .
#|
#|unicode chunk 65536: 名前:str n:u32 ü:str .
#|
#|quotes chunk 5: a:str b:u32 .
#|
#|quotes chunk 16: a:str b:u32 .
#|
#|quotes chunk 65536: a:str b:u32 .
#|
#|long all chunk 4: id:str s:str .
#|
#|long all chunk 64: id:str s:str .
#|
#|long 2 rows chunk 4: id:u32 s:str .
#|
#|long 2 rows chunk 65536: id:u32 s:str .
#|
#|blank crlf chunk 6: a:u32 b:str .
#|
#|blank crlf chunk 65536: a:u32 b:str .
#|
#|ragged chunk 5: error: ParseError at line 3: expected 2 fields, got 1
#|
#|ragged chunk 65536: error: ParseError at line 3: expected 2 fields, got 1
#|
#|ragged beyond the prefix chunk 65536: a:u32 b:str .
#|
#|empty chunk 8: .
#|
#|header only chunk 2: a:str b:str c:str .
#|
#|header only chunk 65536: a:str b:str c:str .
#|
#|no header chunk 5: column_0:str column_1:str .
#|
#|missing chunk 8: error: IoError 2: No such file or directory
#|
