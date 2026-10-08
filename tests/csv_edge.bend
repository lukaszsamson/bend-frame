# B02 review: CSV reader / writer edge cases at text level (DESIGN.md 15.6): separators other
# than ',', escaped quotes, CR / LF / CRLF mixtures and a lone CR, no final newline, round
# trips (write -> read, with the schema and with inference) of "" vs null and of fields that
# need quoting, infer_rows boundaries with physical lines, explicit-schema errors.
# Defect fixed here: a number or bool that holds the separator ('.' in 1.5, '-' in -4, 'e'
# in true) was written bare, so a frame written with such a separator did not read back
# (15.6.5 claims the round trip for every dtype); non-str cells are now quoted like str ones.
import Base
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/csvparse.bend as H
import ./../src/csv.bend as V
import ./../src/dump.bend as Y

def cells.go(cs: List<&2, H.CsvCell>) -> String:
  match cs:
    case Nil{}:
      ""
    case H.CsvCell{t, q} <> rest:
      Bool.pick(String, q, "Q[", "U[") ++ Y.Dump.quote(t) ++ "] " ++ cells.go(rest)

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

def parse(+tag: String, +sep: Char, +text: String) -> String:
  "-- " ++ tag ++ "\n" ++ recs(H.parse_sep(Char.to_u32(sep), text))

def dump(+tag: String, r: E.ResT(C.Frame)) -> String:
  "-- " ++ tag ++ "\n" ++ DF.dump(r)

def rd(+tag: String, +opts: V.CsvOpts, +text: String, +ts: List<&2, D.DType>) -> String:
  dump(tag, V.Csv.parse_with(text, opts, ts))

def mk.k(name: String, r: E.ResT(C.Column)) -> C.Named:
  match r:
    case Fail{e}:
      C.Named{E.Err.show(e), C.CU32{0, 0n, C.AllValid{}, [0 : U32*1n]}}
    case Done{c}:
      C.Named{name, c}

def mk(name: String, xs: List<&2, D.Scalar>, +t: D.DType) -> C.Named:
  mk.k(name, C.Column.from_scalars(xs, t))

def strs() -> List<&2, D.Scalar>:
  [D.SStr{""}, D.SNull{}, D.SStr{"x,y"}, D.SStr{"q\"q"}, D.SStr{" s "}, D.SStr{"m\nl"}, D.SStr{"c\rr"}, D.SStr{"e\r"}, D.SStr{"\r\n"}, D.SStr{"日本;\t"}, D.SStr{"\"\""}, D.SStr{" "}]

def nums() -> List<&2, D.Scalar>:
  [D.SU32{1}, D.SNull{}, D.SU32{3}, D.SU32{4}, D.SU32{5}, D.SU32{6}, D.SU32{7}, D.SU32{8}, D.SU32{9}, D.SU32{10}, D.SU32{11}, D.SNull{}]

def frame() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("s,1", strs(), D.TStr{}), mk("n", nums(), D.TU32{})])

def frame1() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("s", strs(), D.TStr{})])

def snd(r: C.Frame & String) -> String:
  (f, s) = r
  s

def rt.t(+text: String, +o: V.CsvOpts, +ts: List<&2, D.DType>) -> String:
  Y.Dump.quote(text) ++ "\n" ++ DF.dump(V.Csv.parse_with(text, o, ts))

def rt.k(r: E.ResT(C.Frame), +w: V.CsvWriteOpts, +o: V.CsvOpts, +ts: List<&2, D.DType>) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e) ++ "\n"
    case Done{f}:
      rt.t(snd(V.Csv.render_with(f, w)), o, ts)

def rt(+tag: String, r: E.ResT(C.Frame), +w: V.CsvWriteOpts, +o: V.CsvOpts, +ts: List<&2, D.DType>) -> String:
  "-- " ++ tag ++ "\n" ++ rt.k(r, w, o, ts)

def numf() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("f", [D.SF32{1.5}, D.SNull{}, D.SF32{F32.neg(2.25)}], D.TF32{}), mk("i", [D.SI32{D.I32.neg(D.I32{4})}, D.SI32{D.I32{7}}, D.SNull{}], D.TI32{}), mk("b", [D.SBool{True{}}, D.SNull{}, D.SBool{False{}}], D.TBool{})])

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(rt("sep . numbers", numf(), V.CsvWriteOpts{'.', True{}, None{}}, V.CsvOpts{'.', True{}, 100}, [D.TF32{}, D.TI32{}, D.TBool{}]))
    IO.print(rt("sep - numbers", numf(), V.CsvWriteOpts{'-', True{}, Some{2}}, V.CsvOpts{'-', True{}, 100}, [D.TF32{}, D.TI32{}, D.TBool{}]))
    IO.print(rt("sep e numbers", numf(), V.CsvWriteOpts{'e', True{}, None{}}, V.CsvOpts{'e', True{}, 100}, [D.TF32{}, D.TI32{}, D.TBool{}]))
    IO.print(parse("semicolon", ';', "a;\"b;c\";\"d,e\"\n1,2;;\"\"\n"))
    IO.print(parse("tab", '\t', "a\t\"b\tc\"\n"))
    IO.print(parse("escaped quotes", ',', "\"\"\"\",\"a\"\"\"\"b\",\"\"\"\"\"\"\n"))
    IO.print(parse("crlf mix", ',', "a,b\r\n1,x\n2,y\r\n\r\n3,\"p\r\nq\"\r\n"))
    IO.print(parse("lone cr", ',', "a\rb,c\r,\r\n\r,x\nlast\r"))
    IO.print(parse("no final newline quoted", ',', "a,\"b\""))
    IO.print(parse("final sep", ',', "a,"))
    IO.print(parse("only newline", ',', "\n"))
    IO.print(rt("roundtrip schema", frame(), V.Csv.write_default(), V.Csv.default(), [D.TStr{}, D.TU32{}]))
    IO.print(rt("roundtrip infer", frame(), V.Csv.write_default(), V.Csv.default(), []))
    IO.print(rt("roundtrip ; infer", frame(), V.CsvWriteOpts{';', True{}, None{}}, V.CsvOpts{';', True{}, 100}, []))
    IO.print(rt("roundtrip tab no header", frame(), V.CsvWriteOpts{'\t', False{}, None{}}, V.CsvOpts{'\t', False{}, 100}, []))
    IO.print(rt("roundtrip 1 col", frame1(), V.Csv.write_default(), V.Csv.default(), []))
    IO.print(rd("infer_rows 1", V.CsvOpts{',', True{}, 1}, "a\n1\nx\n", []))
    IO.print(rd("infer_rows 2", V.CsvOpts{',', True{}, 2}, "a\n1\nx\n", []))
    IO.print(rd("infer_rows 1 multi-line", V.CsvOpts{',', True{}, 1}, "a,b\n1,\"p\nq\"\n\n\nx,y\n", []))
    IO.print(rd("schema count header only", V.Csv.default(), "a,b\n", [D.TU32{}]))
    IO.print(rd("schema count empty", V.Csv.default(), "", [D.TU32{}]))
    IO.print(rd("schema bool", V.Csv.default(), "a,b\ntrue,1\n\"\"\"x\",2\n", [D.TBool{}, D.TI32{}]))
    IO.print(rd("schema i32 range", V.Csv.default(), "a\n-5\n3000000000\n", [D.TI32{}]))
    IO.print(rd("schema u32 neg", V.Csv.default(), "a\n\r\n-1\n", [D.TU32{}]))
    IO.print(rd("schema f32", V.Csv.default(), "a\n nan \n\"\"\n1e3\nx\n", [D.TF32{}]))
#|-- sep . numbers
#|"f.i.b\n\"1.5\".-4.true\n.7.\n\"-2.25\"..false\n"
#|frame
#|height	3
#|width	3
#|col	f32	"f"
#|col	i32	"i"
#|col	bool	"b"
#|row	0x3fc00000	-4	true
#|row	null	7	null
#|row	0xc0100000	null	false
#|
#|-- sep - numbers
#|"f-i-b\n1.50-\"-4\"-true\n-7-\n\"-2.25\"--false\n"
#|frame
#|height	3
#|width	3
#|col	f32	"f"
#|col	i32	"i"
#|col	bool	"b"
#|row	0x3fc00000	-4	true
#|row	null	7	null
#|row	0xc0100000	null	false
#|
#|-- sep e numbers
#|"feieb\n1.5e-4e\"true\"\ne7e\n-2.25ee\"false\"\n"
#|frame
#|height	3
#|width	3
#|col	f32	"f"
#|col	i32	"i"
#|col	bool	"b"
#|row	0x3fc00000	-4	true
#|row	null	7	null
#|row	0xc0100000	null	false
#|
#|-- semicolon
#|L1: U["a"] Q["b;c"] Q["d,e"] 
#|L2: U["1,2"] U[""] Q[""] 
#|
#|-- tab
#|L1: U["a"] Q["b\tc"] 
#|
#|-- escaped quotes
#|L1: Q["\""] Q["a\"\"b"] Q["\"\""] 
#|
#|-- crlf mix
#|L1: U["a"] U["b"] 
#|L2: U["1"] U["x"] 
#|L3: U["2"] U["y"] 
#|L4: U[""] 
#|L5: U["3"] Q["p\r\nq"] 
#|
#|-- lone cr
#|L1: U["a\rb"] U["c\r"] U[""] 
#|L2: U["\r"] U["x"] 
#|L3: U["last"] 
#|
#|-- no final newline quoted
#|L1: U["a"] Q["b"] 
#|
#|-- final sep
#|L1: U["a"] U[""] 
#|
#|-- only newline
#|L1: U[""] 
#|
#|-- roundtrip schema
#|"\"s,1\",n\n\"\",1\n,\n\"x,y\",3\n\"q\"\"q\",4\n s ,5\n\"m\nl\",6\n\"c\rr\",7\n\"e\r\",8\n\"\r\n\",9\n日本;\t,10\n\"\"\"\"\"\",11\n ,\n"
#|frame
#|height	12
#|width	2
#|col	str	"s,1"
#|col	u32	"n"
#|row	""	1
#|row	null	null
#|row	"x,y"	3
#|row	"q\"q"	4
#|row	" s "	5
#|row	"m\nl"	6
#|row	"c\rr"	7
#|row	"e\r"	8
#|row	"\r\n"	9
#|row	"日本;\t"	10
#|row	"\"\""	11
#|row	" "	null
#|
#|-- roundtrip infer
#|"\"s,1\",n\n\"\",1\n,\n\"x,y\",3\n\"q\"\"q\",4\n s ,5\n\"m\nl\",6\n\"c\rr\",7\n\"e\r\",8\n\"\r\n\",9\n日本;\t,10\n\"\"\"\"\"\",11\n ,\n"
#|frame
#|height	12
#|width	2
#|col	str	"s,1"
#|col	u32	"n"
#|row	""	1
#|row	null	null
#|row	"x,y"	3
#|row	"q\"q"	4
#|row	" s "	5
#|row	"m\nl"	6
#|row	"c\rr"	7
#|row	"e\r"	8
#|row	"\r\n"	9
#|row	"日本;\t"	10
#|row	"\"\""	11
#|row	" "	null
#|
#|-- roundtrip ; infer
#|"s,1;n\n\"\";1\n;\nx,y;3\n\"q\"\"q\";4\n s ;5\n\"m\nl\";6\n\"c\rr\";7\n\"e\r\";8\n\"\r\n\";9\n\"日本;\t\";10\n\"\"\"\"\"\";11\n ;\n"
#|frame
#|height	12
#|width	2
#|col	str	"s,1"
#|col	u32	"n"
#|row	""	1
#|row	null	null
#|row	"x,y"	3
#|row	"q\"q"	4
#|row	" s "	5
#|row	"m\nl"	6
#|row	"c\rr"	7
#|row	"e\r"	8
#|row	"\r\n"	9
#|row	"日本;\t"	10
#|row	"\"\""	11
#|row	" "	null
#|
#|-- roundtrip tab no header
#|"\"\"\t1\n\t\nx,y\t3\n\"q\"\"q\"\t4\n s \t5\n\"m\nl\"\t6\n\"c\rr\"\t7\n\"e\r\"\t8\n\"\r\n\"\t9\n\"日本;\t\"\t10\n\"\"\"\"\"\"\t11\n \t\n"
#|frame
#|height	12
#|width	2
#|col	str	"column_0"
#|col	u32	"column_1"
#|row	""	1
#|row	null	null
#|row	"x,y"	3
#|row	"q\"q"	4
#|row	" s "	5
#|row	"m\nl"	6
#|row	"c\rr"	7
#|row	"e\r"	8
#|row	"\r\n"	9
#|row	"日本;\t"	10
#|row	"\"\""	11
#|row	" "	null
#|
#|-- roundtrip 1 col
#|"s\n\"\"\n\n\"x,y\"\n\"q\"\"q\"\n s \n\"m\nl\"\n\"c\rr\"\n\"e\r\"\n\"\r\n\"\n日本;\t\n\"\"\"\"\"\"\n \n"
#|frame
#|height	12
#|width	1
#|col	str	"s"
#|row	""
#|row	null
#|row	"x,y"
#|row	"q\"q"
#|row	" s "
#|row	"m\nl"
#|row	"c\rr"
#|row	"e\r"
#|row	"\r\n"
#|row	"日本;\t"
#|row	"\"\""
#|row	" "
#|
#|-- infer_rows 1
#|error	ParseError at line 3: column a: cannot parse "x" as u32
#|
#|-- infer_rows 2
#|frame
#|height	2
#|width	1
#|col	str	"a"
#|row	"1"
#|row	"x"
#|
#|-- infer_rows 1 multi-line
#|error	ParseError at line 6: column a: cannot parse "x" as u32
#|
#|-- schema count header only
#|error	InvalidOperation: csv schema: 1 dtypes for 2 columns
#|
#|-- schema count empty
#|error	InvalidOperation: csv schema: 1 dtypes for 0 columns
#|
#|-- schema bool
#|error	ParseError at line 3: column a: cannot parse ""x" as bool
#|
#|-- schema i32 range
#|error	ParseError at line 3: column a: cannot parse "3000000000" as i32
#|
#|-- schema u32 neg
#|error	ParseError at line 3: column a: cannot parse "-1" as u32
#|
#|-- schema f32
#|error	ParseError at line 5: column a: cannot parse "x" as f32
#|
