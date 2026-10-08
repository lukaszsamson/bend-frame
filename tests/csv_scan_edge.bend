# B02 review: scan_csv's bounded prefix must freeze the schema Csv.read infers (DESIGN.md
# 15.6.4, G4: one data semantics eager and lazy).
#  - blank lines: the reader skips them (k > 1 columns), so the prefix must hold infer_rows
#    NON-BLANK records; it used to count every line end, saw only one data record of
#    "a,b / 1,2 / blank x3 / x,y" for infer_rows = 2 and froze u32 where the read infers str
#    (collect then failed with a ParseError on a file read_csv reads);
#  - malformed UTF-8 (a Latin-1 file): the prefix decoder used to swallow the byte after a
#    broken sequence ("caf\xe9,1" lost its ',': a ragged-row error the read does not raise);
#    it now follows the runtime's decoder (File.read) byte for byte, checked on a fixture of
#    overlong, surrogate, out-of-range, stray and truncated sequences (expected code points:
#    Python's bytes.decode('utf-8', 'replace'), the same WHATWG rule).
# Every chunk size of a case must print the same schema; chunk 1 exercises the doubling.
import Base
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/plan.bend as P
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
    IO.print(tag ++ " scan chunk " ++ U32.show(chunk) ++ ": " ++ fields(r) ++ "\n")

def read(+tag: String, +path: String, +opts: V.CsvOpts) -> IO(Unit):
  do IO<Unit>:
    r : E.ResT(C.Frame) <- V.Csv.read(path, opts)
    IO.print("-- " ++ tag ++ " read\n" ++ DF.dump(r) ++ "\n")

def collect.k(+tag: String, rp: E.Res(P.Plan)) -> IO(Unit):
  match rp:
    case Fail{e}:
      IO.print("-- " ++ tag ++ " scan failed: " ++ E.Err.show(e) ++ "\n")
    case Done{p}:
      do IO<Unit>:
        r : E.ResT(C.Frame) <- DF.collect(p, DF.empty_env())
        IO.print("-- " ++ tag ++ " scan+collect\n" ++ DF.dump(r) ++ "\n")

def collect(+tag: String, +path: String, +opts: V.CsvOpts) -> IO(Unit):
  do IO<Unit>:
    rp : E.Res(P.Plan) <- DF.scan_csv_opts(path, opts)
    collect.k(tag, rp)

# ---- the prefix decoder vs the runtime's ------------------------------------------------------

def cps(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{c, t}:
      U32.show(Char.to_u32(c)) ++ " " ++ cps(t)

def bytes.k(r: Result<&1, &1, U32 & String, List<&2, U32>>) -> String:
  match r:
    case Fail{(c, m)}:
      "read failed: " ++ m
    case Done{bs}:
      cps(V.Csv.u8(1000n, bs))

def bytes(r: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> String:
  (f, res) = r
  bytes.k(res)

def text.k(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Fail{(c, m)}:
      "read failed: " ++ m
    case Done{s}:
      cps(s)

def text(r: File & Result<&1, &1, U32 & String, String>) -> String:
  (f, res) = r
  text.k(res)

def dec.bytes(o: Result<&1, &1, U32 & String, File>) -> IO(Unit):
  match o:
    case Fail{(c, m)}:
      IO.print("open failed\n")
    case Done{f}:
      do IO<Unit>:
        a : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_at(f, 0, 1000)
        IO.print("Csv.u8:    " ++ bytes(a) ++ "\n")

def dec.text(o: Result<&1, &1, U32 & String, File>) -> IO(Unit):
  match o:
    case Fail{(c, m)}:
      IO.print("open failed\n")
    case Done{f}:
      do IO<Unit>:
        b : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1000)
        IO.print("File.read: " ++ text(b) ++ "\n")

def main() -> IO(Unit):
  do IO<Unit>:
    read("blank k=2", "tests/regress/data/B02_scan_blank_infer.csv", V.CsvOpts{',', True{}, 2})
    scan("blank k=2", "tests/regress/data/B02_scan_blank_infer.csv", V.CsvOpts{',', True{}, 2}, 1)
    scan("blank k=2", "tests/regress/data/B02_scan_blank_infer.csv", V.CsvOpts{',', True{}, 2}, 3)
    scan("blank k=2", "tests/regress/data/B02_scan_blank_infer.csv", V.CsvOpts{',', True{}, 2}, 65536)
    collect("blank k=2", "tests/regress/data/B02_scan_blank_infer.csv", V.CsvOpts{',', True{}, 2})
    scan("blank crlf", "tests/regress/data/B02_scan_blank_crlf.csv", V.CsvOpts{',', True{}, 2}, 1)
    scan("blank crlf", "tests/regress/data/B02_scan_blank_crlf.csv", V.CsvOpts{',', True{}, 2}, 65536)
    scan("blank inside quotes", "tests/regress/data/B02_scan_blank_quoted.csv", V.CsvOpts{',', True{}, 2}, 1)
    scan("blank inside quotes", "tests/regress/data/B02_scan_blank_quoted.csv", V.CsvOpts{',', True{}, 2}, 2)
    scan("blank inside quotes", "tests/regress/data/B02_scan_blank_quoted.csv", V.CsvOpts{',', True{}, 2}, 5)
    scan("blank inside quotes", "tests/regress/data/B02_scan_blank_quoted.csv", V.CsvOpts{',', True{}, 2}, 65536)
    read("blank inside quotes", "tests/regress/data/B02_scan_blank_quoted.csv", V.CsvOpts{',', True{}, 2})
    scan("blank k=1", "tests/regress/data/B02_scan_blank_one.csv", V.CsvOpts{',', True{}, 2}, 1)
    scan("blank k=1", "tests/regress/data/B02_scan_blank_one.csv", V.CsvOpts{',', True{}, 2}, 65536)
    read("blank k=1", "tests/regress/data/B02_scan_blank_one.csv", V.CsvOpts{',', True{}, 2})
    read("latin1", "tests/regress/data/B02_scan_latin1.csv", V.Csv.default())
    scan("latin1", "tests/regress/data/B02_scan_latin1.csv", V.Csv.default(), 1)
    scan("latin1", "tests/regress/data/B02_scan_latin1.csv", V.Csv.default(), 4)
    scan("latin1", "tests/regress/data/B02_scan_latin1.csv", V.Csv.default(), 65536)
    collect("latin1", "tests/regress/data/B02_scan_latin1.csv", V.Csv.default())
    o1 : Result<&1, &1, U32 & String, File> <- File.open("tests/regress/data/B02_scan_utf8_bad.bin", "r")
    dec.bytes(o1)
    o2 : Result<&1, &1, U32 & String, File> <- File.open("tests/regress/data/B02_scan_utf8_bad.bin", "r")
    dec.text(o2)
#|-- blank k=2 read
#|frame
#|height	2
#|width	2
#|col	str	"a"
#|col	str	"b"
#|row	"1"	"2"
#|row	"x"	"y"
#|
#|
#|blank k=2 scan chunk 1: a:str b:str .
#|
#|blank k=2 scan chunk 3: a:str b:str .
#|
#|blank k=2 scan chunk 65536: a:str b:str .
#|
#|-- blank k=2 scan+collect
#|frame
#|height	2
#|width	2
#|col	str	"a"
#|col	str	"b"
#|row	"1"	"2"
#|row	"x"	"y"
#|
#|
#|blank crlf scan chunk 1: a:str b:str .
#|
#|blank crlf scan chunk 65536: a:str b:str .
#|
#|blank inside quotes scan chunk 1: a:str b:str .
#|
#|blank inside quotes scan chunk 2: a:str b:str .
#|
#|blank inside quotes scan chunk 5: a:str b:str .
#|
#|blank inside quotes scan chunk 65536: a:str b:str .
#|
#|-- blank inside quotes read
#|frame
#|height	2
#|width	2
#|col	str	"a"
#|col	str	"b"
#|row	"x\n\ny"	"1"
#|row	"2"	"q"
#|
#|
#|blank k=1 scan chunk 1: a:str .
#|
#|blank k=1 scan chunk 65536: a:str .
#|
#|-- blank k=1 read
#|frame
#|height	4
#|width	1
#|col	str	"a"
#|row	null
#|row	null
#|row	"5"
#|row	"x"
#|
#|
#|-- latin1 read
#|frame
#|height	3
#|width	2
#|col	str	"a"
#|col	u32	"b"
#|row	"caf�"	1
#|row	"x�"	2
#|row	"ok"	3
#|
#|
#|latin1 scan chunk 1: a:str b:u32 .
#|
#|latin1 scan chunk 4: a:str b:u32 .
#|
#|latin1 scan chunk 65536: a:str b:u32 .
#|
#|-- latin1 scan+collect
#|frame
#|height	3
#|width	2
#|col	str	"a"
#|col	u32	"b"
#|row	"caf�"	1
#|row	"x�"	2
#|row	"ok"	3
#|
#|
#|Csv.u8:    97 65533 65533 98 65533 65533 65533 99 65533 65533 65533 100 65533 65533 65533 65533 101 65533 102 65533 103 65533 104 65533 44 65533 10 65533 34 128512 233 2048 55295 1114111 65533
#|
#|File.read: 97 65533 65533 98 65533 65533 65533 99 65533 65533 65533 100 65533 65533 65533 65533 101 65533 102 65533 103 65533 104 65533 44 65533 10 65533 34 128512 233 2048 55295 1114111 65533
