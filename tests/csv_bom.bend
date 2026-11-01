# D2 (v0.3 decision): a UTF-8 byte order mark (the bytes EF BB BF) at the start of a file is an encoding
# marker, not content, and is dropped, as Polars 2.0.0 does (read_csv and scan_csv both name the column
# "a"): by the reader's header step (src/csv.bend Csv.v2.hbom: the walk starts at byte 3) and by scan_csv's
# schema inference (Csv.unbom). Line numbers are unchanged (the mark is on line 1).
#
# Files: 15 bytes EF BB BF "a,b\n1,2\n3,4\n" (a header of two names, two rows); the same without a header
# (EF BB BF "1,2\n3,4\n"); a file that is only the mark; and EF BB BF "a\nx\n" whose header breaks a
# later cell (the error names line 2). Expected, derived by hand: names printed as code points, so the
# expectations hold no invisible character: [97,] [98,], two u32 columns (1, 2), (3, 4); without a
# header column_0 / column_1 with (1, 2), (3, 4); the mark alone: the empty frame (0 x 0) with or without a
# header; at reader pieces of 1 and 2 bytes (the mark split across the header step's reads)
# the same frame.
import Base
import ./../frame.bend as DF
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/schema.bend as S
import ./../src/plan.bend as P
import ./../bench/w6/hx.bend as X
import ./../src/csv.bend as V
import ./../src/strs.bend as ST

# the code points of a string, comma separated
def cps(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{Chr{c}, t}:
      U32.show(c) ++ "," ++ cps(t)

def fields(fs: List<&2, S.Field>) -> String:
  match fs:
    case Nil{}:
      ""
    case S.Field{n, t} <> rest:
      "[" ++ cps(n) ++ "] " ++ fields(rest)

def renamed(r: E.ResT(C.Frame)) -> String:
  DF.dump(r)

def desc.k(r: C.Frame & List<&2, S.Field>) -> String:
  (f, sc) = r
  "names " ++ fields(sc) ++ "\n" ++ renamed(Done{f})

def desc(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      desc.k(DF.schema(f))

def scan_names(r: E.Res(List<&2, S.Field>)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{s}:
      "plan " ++ fields(s)

def bom_bytes() -> List<&2, U32>:
  [239, 187, 191, 97, 44, 98, 10, 49, 44, 50, 10, 51, 44, 52, 10]

def bom_nohdr() -> List<&2, U32>:
  [239, 187, 191, 49, 44, 50, 10, 51, 44, 52, 10]

def bom_only() -> List<&2, U32>:
  [239, 187, 191]

def bom_bad() -> List<&2, U32>:
  [239, 187, 191, 97, 10, 120, 10]

def at(+piece: U32, +path: String, +hdr: Bool) -> IO(E.ResT(C.Frame)):
  V.Csv.read_v02_full(path, V.CsvOpts{',', hdr, 100}, [], ST.EncAuto{}, piece, 8388608)

def scanned.k(+s: String, p: P.Plan) -> IO(String):
  do IO<String>:
    c : E.ResT(C.Frame) <- DF.collect(p, DF.empty_env())
    return s ++ "\n" ++ desc(c)

def scanned(r: E.Res(P.Plan)) -> IO(String):
  match r:
    case Fail{e}:
      IO.pure(String, "error: " ++ E.Err.show(e))
    case Done{+p}:
      scanned.k(scan_names(DF.collect_schema(p)), p)

def main() -> IO(Unit):
  do IO<Unit>:
    X.Hx.write_bytes("/tmp/bend_frame_bom.csv", bom_bytes())
    X.Hx.write_bytes("/tmp/bend_frame_bom_nohdr.csv", bom_nohdr())
    X.Hx.write_bytes("/tmp/bend_frame_bom_only.csv", bom_only())
    a : E.ResT(C.Frame) <- DF.read_csv("/tmp/bend_frame_bom.csv")
    IO.print("-- read_csv\n" ++ desc(a))
    a1 : E.ResT(C.Frame) <- at(1, "/tmp/bend_frame_bom.csv", True{})
    IO.print("-- piece 1\n" ++ desc(a1))
    a2 : E.ResT(C.Frame) <- at(2, "/tmp/bend_frame_bom.csv", True{})
    IO.print("-- piece 2\n" ++ desc(a2))
    b : E.ResT(C.Frame) <- DF.read_csv_opts("/tmp/bend_frame_bom_nohdr.csv", DF.csv_opts(',', False{}, 100))
    IO.print("-- no header\n" ++ desc(b))
    b1 : E.ResT(C.Frame) <- at(1, "/tmp/bend_frame_bom_nohdr.csv", False{})
    IO.print("-- no header, piece 1\n" ++ desc(b1))
    c : E.ResT(C.Frame) <- DF.read_csv("/tmp/bend_frame_bom_only.csv")
    IO.print("-- the mark only\n" ++ desc(c))
    c2 : E.ResT(C.Frame) <- DF.read_csv_opts("/tmp/bend_frame_bom_only.csv", DF.csv_opts(',', False{}, 100))
    IO.print("-- the mark only, no header\n" ++ desc(c2))
    X.Hx.write_bytes("/tmp/bend_frame_bom_bad.csv", bom_bad())
    d : E.ResT(C.Frame) <- DF.read_csv_schema("/tmp/bend_frame_bom_bad.csv", DF.csv_opts(',', True{}, 100), [DF.t_u32()])
    IO.print("-- a bad cell keeps its line\n" ++ desc(d))
    p : E.Res(P.Plan) <- DF.scan_csv("/tmp/bend_frame_bom.csv")
    t : String <- scanned(p)
    IO.print("-- scan_csv, collect_schema, then collect\n" ++ t)
#|-- read_csv
#|names [97,] [98,] 
#|frame
#|height	2
#|width	2
#|col	u32	"a"
#|col	u32	"b"
#|row	1	2
#|row	3	4
#|
#|-- piece 1
#|names [97,] [98,] 
#|frame
#|height	2
#|width	2
#|col	u32	"a"
#|col	u32	"b"
#|row	1	2
#|row	3	4
#|
#|-- piece 2
#|names [97,] [98,] 
#|frame
#|height	2
#|width	2
#|col	u32	"a"
#|col	u32	"b"
#|row	1	2
#|row	3	4
#|
#|-- no header
#|names [99,111,108,117,109,110,95,48,] [99,111,108,117,109,110,95,49,] 
#|frame
#|height	2
#|width	2
#|col	u32	"column_0"
#|col	u32	"column_1"
#|row	1	2
#|row	3	4
#|
#|-- no header, piece 1
#|names [99,111,108,117,109,110,95,48,] [99,111,108,117,109,110,95,49,] 
#|frame
#|height	2
#|width	2
#|col	u32	"column_0"
#|col	u32	"column_1"
#|row	1	2
#|row	3	4
#|
#|-- the mark only
#|names 
#|frame
#|height	0
#|width	0
#|
#|-- the mark only, no header
#|names 
#|frame
#|height	0
#|width	0
#|
#|-- a bad cell keeps its line
#|error: ParseError at line 2: column a: cannot parse "x" as u32
#|-- scan_csv, collect_schema, then collect
#|plan [97,] [98,] 
#|names [97,] [98,] 
#|frame
#|height	2
#|width	2
#|col	u32	"a"
#|col	u32	"b"
#|row	1	2
#|row	3	4
#|
