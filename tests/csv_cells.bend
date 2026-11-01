# B02: the csvparse fork (quotedness, physical lines) and the reader / writer rules of
# DESIGN.md 15.6 at text level: strings read through tests/lib/ctext.bend, render_with.
import Base
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/csvparse.bend as H
import ./../src/csv.bend as V
import ./lib/ctext.bend as X
import ./../src/dump.bend as Y

# ---- the parser: every cell as text/quoted, every record with its line ---------------------

def cells.go(cs: List<&2, H.CsvCell>) -> String:
  match cs:
    case Nil{}:
      ""
    case H.CsvCell{t, q} <> rest:
      Bool.pick(String, q, "Q[", "U[") ++ t ++ "] " ++ cells.go(rest)

def recs.go(rs: List<&2, H.CsvRec>) -> String:
  match rs:
    case Nil{}:
      ""
    case H.CsvRec{l, cs} <> rest:
      "L" ++ U32.show(l) ++ ": " ++ cells.go(cs) ++ "\n" ++ recs.go(rest)

def recs(ans: H.Ans) -> String:
  match ans:
    case H.Rejected{}:
      "rejected\n"
    case H.Parsed{rs}:
      recs.go(rs)

def parse(+tag: String, +text: String) -> String:
  "-- " ++ tag ++ "\n" ++ recs(H.parse_sep(44, text))

# ---- frames ---------------------------------------------------------------------------------

def dump(+tag: String, r: E.ResT(C.Frame)) -> String:
  "-- " ++ tag ++ "\n" ++ DF.dump(r)

def rd(+tag: String, +text: String) -> IO(String):
  IO.bind(E.ResT(C.Frame), String, X.Tx.parse("cells", text, V.Csv.default()), r => IO.pure(String, dump(tag, r)))

def rs(+tag: String, +text: String, +ts: List<&2, D.DType>) -> IO(String):
  IO.bind(E.ResT(C.Frame), String, X.Tx.parse_with("cells", text, V.Csv.default(), ts), r => IO.pure(String, dump(tag, r)))

def snd(r: C.Frame & String) -> String:
  (f, s) = r
  s

def rend.k(r: E.ResT(C.Frame), w: V.CsvWriteOpts) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e) ++ "\n"
    case Done{f}:
      Y.Dump.quote(snd(V.Csv.render_with(f, w))) ++ "\n"

# parse, then write with the options, as an escaped one-line text
def rend(+tag: String, +text: String, w: V.CsvWriteOpts) -> IO(String):
  IO.bind(E.ResT(C.Frame), String, X.Tx.parse("cells", text, V.Csv.default()), r => IO.pure(String, "-- " ++ tag ++ "\n" ++ rend.k(r, w)))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(parse("quotedness", "a,\"\",\"b\",,c\n"))
    IO.print(parse("blank and multi-line lines", "h\n\n\"x\ny\"\nz\r\n\nlast"))
    IO.print(parse("escaped quote", "\"a\"\"b\",c\n"))
    IO.print(parse("empty final field", "a,\n,\n"))
    IO.print(parse("rejected", "a\"b\n"))
    X.Tx.out(rd("quoted empty vs null", "a,b\n\"\",\n,\"\"\n"))
    X.Tx.out(rd("quoted spaces stay in str", "s,n\n\" \",\" \"\n x ,5\n"))
    X.Tx.out(rd("only quoted empties: str", "a,b\n\"\",1\n\"\",2\n"))
    X.Tx.out(rd("whitespace-only column is str", "a,b\n  ,1\n ,2\n"))
    X.Tx.out(rd("quoted number is a number", "a\n\"5\"\n\"6\"\n"))
    X.Tx.out(rs("explicit: blank numeric is null", "a,b\n\" \",x\n2,\"\"\n", [D.TU32{}, D.TStr{}]))
    X.Tx.out(rs("explicit: unquoted empty str is null", "a,b\n,\n", [D.TStr{}, D.TStr{}]))
    X.Tx.out(rs("bad value after a multi-line field", "n,s\n1,\"a\nb\"\n\n x ,c\n", [D.TU32{}, D.TStr{}]))
    X.Tx.out(rd("blank lines in two columns are skipped", "a,b\n1,x\n\n\n3,y\n"))
    X.Tx.out(rd("blank line in one column is a null row", "a\n1\n\n3\n"))
    X.Tx.out(rd("ragged after blank and multi-line", "a,b\n\"x\ny\",1\n\n2\n"))
    X.Tx.out(rd("long row", "a,b\n1,2,3\n"))
    X.Tx.out(rd("header only", "a,b\n"))
    X.Tx.out(rd("empty file", ""))
    X.Tx.out(rd("duplicate names", "a,a\n1,2\n"))
    X.Tx.out(rend("write default", "a,b\n\"\",1\n,2\nx,\n", V.Csv.write_default()))
    X.Tx.out(rend("write ; no header", "a,b\n\"x;y\",1.5\n\"\",2\n", V.CsvWriteOpts{';', False{}, None{}}))
    X.Tx.out(rend("write precision", "a,b\n1.005,x\n2.5,\"\"\n", V.CsvWriteOpts{',', True{}, Some{1}}))
    X.Tx.out(rend("write empty header name", "\"\",b\n1,2\n", V.Csv.write_default()))
#|-- quotedness
#|L1: U[a] Q[] Q[b] U[] U[c] 
#|
#|-- blank and multi-line lines
#|L1: U[h] 
#|L2: U[] 
#|L3: Q[x
#|y] 
#|L5: U[z] 
#|L6: U[] 
#|L7: U[last] 
#|
#|-- escaped quote
#|L1: Q[a"b] U[c] 
#|
#|-- empty final field
#|L1: U[a] U[] 
#|L2: U[] U[] 
#|
#|-- rejected
#|rejected
#|
#|-- quoted empty vs null
#|frame
#|height	2
#|width	2
#|col	str	"a"
#|col	str	"b"
#|row	""	null
#|row	null	""
#|
#|-- quoted spaces stay in str
#|frame
#|height	2
#|width	2
#|col	str	"s"
#|col	u32	"n"
#|row	" "	null
#|row	" x "	5
#|
#|-- only quoted empties: str
#|frame
#|height	2
#|width	2
#|col	str	"a"
#|col	u32	"b"
#|row	""	1
#|row	""	2
#|
#|-- whitespace-only column is str
#|frame
#|height	2
#|width	2
#|col	str	"a"
#|col	u32	"b"
#|row	"  "	1
#|row	" "	2
#|
#|-- quoted number is a number
#|frame
#|height	2
#|width	1
#|col	u32	"a"
#|row	5
#|row	6
#|
#|-- explicit: blank numeric is null
#|frame
#|height	2
#|width	2
#|col	u32	"a"
#|col	str	"b"
#|row	null	"x"
#|row	2	""
#|
#|-- explicit: unquoted empty str is null
#|frame
#|height	1
#|width	2
#|col	str	"a"
#|col	str	"b"
#|row	null	null
#|
#|-- bad value after a multi-line field
#|error	ParseError at line 5: column n: cannot parse " x " as u32
#|
#|-- blank lines in two columns are skipped
#|frame
#|height	2
#|width	2
#|col	u32	"a"
#|col	str	"b"
#|row	1	"x"
#|row	3	"y"
#|
#|-- blank line in one column is a null row
#|frame
#|height	3
#|width	1
#|col	u32	"a"
#|row	1
#|row	null
#|row	3
#|
#|-- ragged after blank and multi-line
#|error	ParseError at line 5: expected 2 fields, got 1
#|
#|-- long row
#|error	ParseError at line 2: expected 2 fields, got 3
#|
#|-- header only
#|frame
#|height	0
#|width	2
#|col	str	"a"
#|col	str	"b"
#|
#|-- empty file
#|frame
#|height	0
#|width	0
#|
#|-- duplicate names
#|error	DuplicateColumn: a
#|
#|-- write default
#|"a,b\n\"\",1\n,2\nx,\n"
#|
#|-- write ; no header
#|"\"x;y\";1.5\n\"\";2\n"
#|
#|-- write precision
#|"a,b\n1.0,x\n2.5,\"\"\n"
#|
#|-- write empty header name
#|"\"\",b\n1,2\n"
#|
