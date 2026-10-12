# B2 (plans/REVIEW_V02_FABLE.txt; documented in README "Differences from Polars" and DESIGN.md 15.6):
# a UTF-8 byte order mark at the start of a file is ordinary content, not an encoding marker. Both
# readers (v0.1 and v0.2, through read_csv_engine) and the scan path keep it: the first header name is
# the BOM U+FEFF followed by the name's own characters, so the column is named "<BOM>a", not "a". Polars
# 2.0.0 strips it (read_csv and scan_csv both name the column "a"; checked in bench's uv project).
# This test PINS bend-frame's behaviour; it is a documented difference, not a claim that it is right.
#
# The file holds the 15 bytes EF BB BF "a,b\n1,2\n3,4\n": a header of two names and two rows. Expected,
# derived by hand from the contract: a 2-row frame of two u32 columns; the first name is the two code
# points U+FEFF = 65279 and 'a' = 97, the second is "b" = 98; the cells (1, 2) and (3, 4). The names are
# printed as code points and the frame is dumped after renaming the first column to "bom_a", so the
# expectations hold no invisible character.
import Base
import ./../frame.bend as DF
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/schema.bend as S
import ./../src/plan.bend as P
import ./../bench/w6/hx.bend as X

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

# the first name: BOM + "a"
def bom_a() -> String:
  SCon{Chr{65279}, "a"}

def renamed(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      DF.dump(DF.rename(f, [(bom_a(), "bom_a")]))

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
    a : E.ResT(C.Frame) <- DF.read_csv("/tmp/bend_frame_bom.csv")
    IO.print("-- v0.2 reader (the default)\n" ++ desc(a))
    b : E.ResT(C.Frame) <- DF.read_csv_engine(DF.csv_engine_v01(), "/tmp/bend_frame_bom.csv", DF.csv_opts(',', True{}, 100), Nil{}, DF.str_auto())
    IO.print("-- v0.1 reader\n" ++ desc(b))
    p : E.Res(P.Plan) <- DF.scan_csv("/tmp/bend_frame_bom.csv")
    t : String <- scanned(p)
    IO.print("-- scan_csv, collect_schema, then collect\n" ++ t)
#|-- v0.2 reader (the default)
#|names [65279,97,] [98,] 
#|frame
#|height	2
#|width	2
#|col	u32	"bom_a"
#|col	u32	"b"
#|row	1	2
#|row	3	4
#|
#|-- v0.1 reader
#|names [65279,97,] [98,] 
#|frame
#|height	2
#|width	2
#|col	u32	"bom_a"
#|col	u32	"b"
#|row	1	2
#|row	3	4
#|
#|-- scan_csv, collect_schema, then collect
#|plan [65279,97,] [98,] 
#|names [65279,97,] [98,] 
#|frame
#|height	2
#|width	2
#|col	u32	"bom_a"
#|col	u32	"b"
#|row	1	2
#|row	3	4
#|
