# B04-e: a scan's frozen schema vs a file that changed before collect: the error names
# the file (existed, untested). DESIGN.md 15.6.4: a header whose names differ is
# InvalidOperation{"scan_csv <path>: data schema [<file>] differs from the plan's
# [<plan>]"}; a value that does not parse under the frozen dtype is
# ParseError{line, "column <name>: cannot parse \"<text>\" as <dtype>"}. collect_schema
# keeps answering the frozen schema (no IO). Raw and optimised lazy only (eager has no
# plan). Passes today.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/schema.bend as S
import ./../../src/expr.bend as X
import ./../../src/join.bend as J
import ./../../src/groupby.bend as G
import ./../../src/plan.bend as P
import ./lib/rx.bend as R

def path() -> String:
  "/tmp/bend_frame_regress_B04_e.csv"

def v1() -> E.ResT(C.Frame):
  R.frame([R.mk("a", [R.u(1), R.u(2)], D.TU32{}), R.mk("b", [R.u(3), R.u(4)], D.TU32{})])

# the header changes: b -> c
def v2() -> E.ResT(C.Frame):
  R.frame([R.mk("a", [R.u(1), R.u(2)], D.TU32{}), R.mk("c", [R.u(3), R.u(4)], D.TU32{})])

# same names, b holds "x" on line 3
def v3() -> E.ResT(C.Frame):
  R.frame([R.mk("a", [R.u(1), R.u(2)], D.TU32{}), R.mk("b", [R.s("3"), R.s("x")], D.TStr{})])

def after(+tag: String, rp: E.Res(P.Plan), r: E.ResT(C.Frame)) -> IO(Unit):
  match rp:
    case Fail{e}:
      IO.print("-- " ++ tag ++ " scan\nscan failed: " ++ E.Err.show(e) ++ "\n")
    case Done{+p}:
      do IO<Unit>:
        w : E.ResT(C.Frame) <- DF.write_csv(r, path())
        IO.print(R.schema(tag, p))
        R.lazy2(tag, p, DF.empty_env(), DF.empty_env())

def scen(+tag: String, r: E.ResT(C.Frame)) -> IO(Unit):
  do IO<Unit>:
    w : E.ResT(C.Frame) <- DF.write_csv(v1(), path())
    rp : E.Res(P.Plan) <- DF.scan_csv(path())
    after(tag, rp, r)

def main() -> IO(Unit):
  do IO<Unit>:
    scen("B04-e renamed-column", v2())
    scen("B04-e bad-value", v3())
#|-- B04-e renamed-column schema
#|a:u32, b:u32
#|
#|-- B04-e renamed-column raw
#|error	InvalidOperation: scan_csv /tmp/bend_frame_regress_B04_e.csv: data schema [a:u32, c:u32] differs from the plan's [a:u32, b:u32]
#|
#|-- B04-e renamed-column opt
#|error	InvalidOperation: scan_csv /tmp/bend_frame_regress_B04_e.csv: data schema [a:u32, c:u32] differs from the plan's [a:u32, b:u32]
#|
#|-- B04-e bad-value schema
#|a:u32, b:u32
#|
#|-- B04-e bad-value raw
#|error	ParseError at line 3: column b: cannot parse "x" as u32
#|
#|-- B04-e bad-value opt
#|error	ParseError at line 3: column b: cannot parse "x" as u32
#|
