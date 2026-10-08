# B02: DF.scan_csv_schema (DESIGN.md 15.2.7): pure, no inference and no IO at plan time;
# collect reads the file once, strictly, with the given dtypes, and checks the header
# names. Also DF.scan_csv_opts with an explicit separator.
import Base
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/schema.bend as S
import ./../src/plan.bend as P

def schema(+tag: String, p: P.Plan) -> String:
  "-- " ++ tag ++ " schema\n" ++ DF.schema_show(DF.collect_schema(p)) ++ "\n"

def run(+tag: String, +p: P.Plan) -> IO(Unit):
  do IO<Unit>:
    IO.print(schema(tag, p))
    r : E.ResT(C.Frame) <- DF.collect(p, DF.empty_env())
    IO.print("-- " ++ tag ++ " collect\n" ++ DF.dump(r) ++ "\n")

def sch(a: String, ta: D.DType, b: String, tb: D.DType) -> List<&2, S.Field>:
  [S.Field{a, ta}, S.Field{b, tb}]

def scan.k(rp: E.Res(P.Plan)) -> IO(Unit):
  match rp:
    case Fail{e}:
      IO.print("scan failed: " ++ E.Err.show(e) ++ "\n")
    case Done{p}:
      run("scan-opts", p)

def main() -> IO(Unit):
  do IO<Unit>:
    # the file holds s:str, n:u32; n is read as i32 under the given schema
    run("given", DF.scan_csv_schema("tests/regress/data/B02_h_crlf.csv", DF.csv_opts(',', True{}, 100), sch("s", D.TStr{}, "n", D.TI32{})))
    # the given dtype does not parse: a strict ParseError with the physical line
    run("bad-cell", DF.scan_csv_schema("tests/regress/data/B02_h_crlf.csv", DF.csv_opts(',', True{}, 100), sch("s", D.TU32{}, "n", D.TI32{})))
    # another name than the header's: the error names the file
    run("renamed", DF.scan_csv_schema("tests/regress/data/B02_h_crlf.csv", DF.csv_opts(',', True{}, 100), sch("s", D.TStr{}, "m", D.TI32{})))
    # no file: plan time is pure (the schema is answered), collect is an IoError
    run("missing", DF.scan_csv_schema("tests/regress/data/B02_no_such.csv", DF.csv_opts(',', True{}, 100), sch("s", D.TStr{}, "n", D.TI32{})))
    rp : E.Res(P.Plan) <- DF.scan_csv_opts("tests/regress/data/B02_e_semicolon.csv", DF.csv_opts(';', True{}, 100))
    scan.k(rp)
#|-- given schema
#|s:str, n:i32
#|
#|-- given collect
#|frame
#|height	2
#|width	2
#|col	str	"s"
#|col	i32	"n"
#|row	"a,b"	1
#|row	"c"	2
#|
#|
#|-- bad-cell schema
#|s:u32, n:i32
#|
#|-- bad-cell collect
#|error	ParseError at line 2: column s: cannot parse "a,b" as u32
#|
#|
#|-- renamed schema
#|s:str, m:i32
#|
#|-- renamed collect
#|error	InvalidOperation: scan_csv tests/regress/data/B02_h_crlf.csv: data schema [s:str, n:i32] differs from the plan's [s:str, m:i32]
#|
#|
#|-- missing schema
#|s:str, n:i32
#|
#|-- missing collect
#|error	IoError 2: No such file or directory
#|
#|
#|-- scan-opts schema
#|a:u32, b:str
#|
#|-- scan-opts collect
#|frame
#|height	2
#|width	2
#|col	u32	"a"
#|col	str	"b"
#|row	1	"x,y"
#|row	2	"z"
#|
#|
