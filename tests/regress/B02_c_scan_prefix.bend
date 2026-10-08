#! xfail B02-c
# B02-c (Astra G3, Fable 4): scan_csv reads and parses the whole file when the plan is
# built (and again at collect). DESIGN.md 15.6.4: scan_csv reads a bounded prefix (64 KiB
# chunks until infer_rows + 1 line ends, cut at the last line end) to infer the schema and
# never builds columns; collect reads the file once, strictly. Observable consequence
# tested here: a defect AFTER the first 64 KiB cannot fail the scan; it fails collect.
#   B02_c_tail_malformed.csv: 6000 good records, then an unterminated quote (line 6002)
#   B02_c_tail_badvalue.csv:  id = "x" at physical line 5001 (byte ~70000)
# Eager read_csv reads everything: both files fail there (15.6.2, 15.6.3).
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def scan.k(+tag: String, rp: E.Res(P.Plan)) -> IO(Unit):
  match rp:
    case Fail{e}:
      IO.print("-- " ++ tag ++ " scan\nscan failed: " ++ E.Err.show(e) ++ "\n")
    case Done{+p}:
      do IO<Unit>:
        IO.print("-- " ++ tag ++ " scan\nscan ok, schema " ++ DF.schema_show(DF.collect_schema(p)) ++ "\n")
        R.lazy2(tag, p, DF.empty_env(), DF.empty_env())

def scen(+tag: String, +path: String) -> IO(Unit):
  do IO<Unit>:
    r0 : E.ResT(C.Frame) <- DF.read_csv(path)
    IO.print(R.show(tag, "eager", r0))
    rp : E.Res(P.Plan) <- DF.scan_csv(path)
    scan.k(tag, rp)

def main() -> IO(Unit):
  do IO<Unit>:
    scen("B02-c tail-malformed", "tests/regress/data/B02_c_tail_malformed.csv")
    scen("B02-c tail-badvalue", "tests/regress/data/B02_c_tail_badvalue.csv")
#|-- B02-c tail-malformed eager
#|error	ParseError at line 0: malformed csv
#|
#|-- B02-c tail-malformed scan
#|scan ok, schema id:u32, s:str
#|
#|-- B02-c tail-malformed raw
#|error	ParseError at line 0: malformed csv
#|
#|-- B02-c tail-malformed opt
#|error	ParseError at line 0: malformed csv
#|
#|-- B02-c tail-badvalue eager
#|error	ParseError at line 5001: column id: cannot parse "x" as u32
#|
#|-- B02-c tail-badvalue scan
#|scan ok, schema id:u32, s:str
#|
#|-- B02-c tail-badvalue raw
#|error	ParseError at line 5001: column id: cannot parse "x" as u32
#|
#|-- B02-c tail-badvalue opt
#|error	ParseError at line 5001: column id: cannot parse "x" as u32
#|
