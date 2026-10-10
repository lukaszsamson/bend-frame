# V01-a (plans/REVIEW_V01_ASTRA.txt [P1]): a scan's frame must never be read by a user Source.
# Before the fix Exec.run bound scan k's frame in env under "#scan<k>" and rewrote the ScanCsv
# to Source "#scan<k>", so a user DF.source("#scan0", ..) validated and then read the CSV's
# frame: concat([source "#scan0" x=[1], scan x=[2]]) collected x=[2, 2]. Now scans live in
# their own, unnamed Env namespace (DESIGN.md 14 "v0.1 review: scan source identity"), so a
# user Source of ANY name reads the user's frame. Cases: the repro (frozen and inferred
# scans) and its control; two and three scans (the same file twice) next to user Sources
# named "#scan0" / "#scan1" / "#scan2"; equal and different schemas; scans in inner / left /
# semi / anti joins, a self-join of a scan, concat; validate_bindings and collect_schema of
# these plans; the error order (static, bindings, then scans in postfix order, before any
# operator: DESIGN.md 15.9 "lazy error order with scans"); Exec.run_pure on a scan plan.
# Each lazy run is DF.collect_raw (Exec.run), DF.collect and DF.collect_full, against the
# eager result over the same data (in-memory frames holding the files' cells).
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/schema.bend as S
import ./../../src/expr.bend as X
import ./../../src/plan.bend as P
import ./../../src/exec.bend as Q
import ./../../src/csv.bend as V
import ./lib/rx.bend as R

# ---- files and their cells ------------------------------------------------------------

def x2p() -> String:
  "tests/regress/data/V01_scan_x2.csv"

def x3p() -> String:
  "tests/regress/data/V01_scan_x3.csv"

def kvp() -> String:
  "tests/regress/data/V01_scan_kv.csv"

def kwp() -> String:
  "tests/regress/data/V01_scan_kw.csv"

def badp() -> String:
  "tests/regress/data/V01_scan_bad.csv"

def missp() -> String:
  "tests/regress/data/V01_scan_missing.csv"

def xs() -> List<&2, S.Field>:
  [S.Field{"x", D.TU32{}}]

def kvs() -> List<&2, S.Field>:
  [S.Field{"k", D.TU32{}}, S.Field{"v", D.TStr{}}]

def kws() -> List<&2, S.Field>:
  [S.Field{"k", D.TU32{}}, S.Field{"w", D.TU32{}}]

# a scan with a frozen schema (DF.scan_csv_schema: no IO until collect)
def scan(path: String, s: List<&2, S.Field>) -> P.Plan:
  DF.scan_csv_schema(path, V.Csv.default(), s)

def x(v: U32) -> E.ResT(C.Frame):
  R.frame([R.mk("x", [R.u(v)], D.TU32{})])

# V01_scan_kv.csv and V01_scan_kw.csv as frames
def kv() -> E.ResT(C.Frame):
  R.frame([R.mk("k", [R.u(1), R.u(2), R.u(3)], D.TU32{}), R.mk("v", [R.s("a"), R.s("b"), R.s("c")], D.TStr{})])

def kw() -> E.ResT(C.Frame):
  R.frame([R.mk("k", [R.u(2), R.u(3), R.u(4)], D.TU32{}), R.mk("w", [R.u(20), R.u(30), R.u(40)], D.TU32{})])

# a user frame with the scans' key column (semi / anti filter)
def k31() -> E.ResT(C.Frame):
  R.frame([R.mk("k", [R.u(3), R.u(1)], D.TU32{})])

def ks() -> List<&2, String>:
  ["k"]

# ---- eager helpers -----------------------------------------------------------------------

def cat.go(rs: List<&1, E.ResT(C.Frame)>, acc: List<&1, C.Frame>) -> E.ResT(C.Frame):
  match rs:
    case Nil{}:
      DF.concat_vertical(List.reverse(&1, C.Frame, acc))
    case Fail{e} <> t:
      Fail{e}
    case Done{f} <> t:
      cat.go(t, f <> acc)

# eager concat_vertical of results (the first error passes through)
def cat(rs: List<&1, E.ResT(C.Frame)>) -> E.ResT(C.Frame):
  cat.go(rs, Nil{})

def e_semi.k(l: C.Frame, r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{fr}:
      DF.semi_join(l, fr, ks(), ks())

def e_semi(l: E.ResT(C.Frame), r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match l:
    case Fail{e}:
      Fail{e}
    case Done{fl}:
      e_semi.k(fl, r)

def e_anti.k(l: C.Frame, r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{fr}:
      DF.anti_join(l, fr, ks(), ks())

def e_anti(l: E.ResT(C.Frame), r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match l:
    case Fail{e}:
      Fail{e}
    case Done{fl}:
      e_anti.k(fl, r)

# ---- the plans ---------------------------------------------------------------------------

# the review's repro: a user Source `nm` holding x=[1], then a scan holding x=[2]
def repro(+nm: String) -> P.Plan:
  DF.lazy_concat_vertical([R.src(nm, x(1)), scan(x2p(), xs())])

# two scans around a user Source "#scan1" (the second scan's old internal name)
def two() -> P.Plan:
  DF.lazy_concat_vertical([scan(x2p(), xs()), R.src("#scan1", x(11)), scan(x3p(), xs())])

def two_env() -> P.Env:
  R.env1("#scan1", x(11))

# three scans (V01_scan_x2.csv twice) and user Sources named "#scan0", "#scan1", "#scan2"
def three() -> P.Plan:
  DF.lazy_concat_vertical([scan(x2p(), xs()), R.src("#scan0", x(10)), scan(x3p(), xs()), R.src("#scan1", x(11)), scan(x2p(), xs()), R.src("#scan2", x(12))])

def three_env() -> P.Env:
  R.env_add(R.env_add(R.env1("#scan0", x(10)), "#scan1", x(11)), "#scan2", x(12))

# a different schema: a scan of k,v joined with the user Source "#scan0" of k,w
def diff_join() -> P.Plan:
  DF.lazy_inner_join(scan(kvp(), kvs()), R.src("#scan0", kw()), ks(), ks())

def kw_env() -> P.Env:
  R.env1("#scan0", kw())

# a scan's own frame twice: the plan node itself on both sides (each scan is read once)
def self_join() -> P.Plan:
  DF.lazy_inner_join(scan(kvp(), kvs()), scan(kvp(), kvs()), ks(), ks())

def k31_env() -> P.Env:
  R.env1("#scan0", k31())

# ---- printing ----------------------------------------------------------------------------

def sh.k(x: P.Env & E.Res(Unit)) -> String:
  (env, r) = x
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{u}:
      "ok"

def check(+tag: String, p: P.Plan, env: P.Env) -> String:
  "-- " ++ tag ++ " validate_bindings\n" ++ sh.k(DF.validate_bindings(p, env)) ++ "\n"

# raw / default / full lazy results, printed in full (no eager counterpart: an error case)
def lazy3(+tag: String, +p: P.Plan, env_raw: P.Env, env_opt: P.Env, env_full: P.Env) -> IO(Unit):
  do IO<Unit>:
    r1 : E.ResT(C.Frame) <- DF.collect_raw(p, env_raw)
    r2 : E.ResT(C.Frame) <- DF.collect(p, env_opt)
    r3 : E.ResT(C.Frame) <- DF.collect_full(p, env_full)
    IO.print(R.show(tag, "raw", r1))
    IO.print(R.show(tag, "opt", r2))
    IO.print(R.show(tag, "full", r3))

# the review's repro with a scan whose schema is inferred (DF.scan_csv), as it was reported
def inferred(+nm: String, rp: E.Res(P.Plan)) -> IO(Unit):
  match rp:
    case Fail{e}:
      IO.print("scan failed: " ++ E.Err.show(e))
    case Done{+sp}:
      R.agree("V01-a inferred " ++ nm, cat([x(1), x(2)]), DF.lazy_concat_vertical([R.src(nm, x(1)), sp]), R.env1(nm, x(1)), R.env1(nm, x(1)), R.env1(nm, x(1)))

# a str column "s" holding "q": a strict cast of it to u32 fails at run time
def q() -> E.ResT(C.Frame):
  R.frame([R.mk("s", [R.s("q")], D.TStr{})])

def cast_q() -> P.Plan:
  DF.lazy_select(R.src("#scan0", q()), [DF.alias(DF.cast(DF.col("s"), D.TU32{}), "x")])

def main() -> IO(Unit):
  do IO<Unit>:
    # the repro and its control: the same answer whatever the Source is called
    R.agree("V01-a repro #scan0", cat([x(1), x(2)]), repro("#scan0"), R.env1("#scan0", x(1)), R.env1("#scan0", x(1)), R.env1("#scan0", x(1)))
    R.agree("V01-a control user_source", cat([x(1), x(2)]), repro("user_source"), R.env1("user_source", x(1)), R.env1("user_source", x(1)), R.env1("user_source", x(1)))
    rp : E.Res(P.Plan) <- DF.scan_csv(x2p())
    inferred("#scan0", rp)
    # several scans next to Sources named like the old internal names
    R.agree("V01-a two scans #scan1", cat([x(2), x(11), x(3)]), two(), two_env(), two_env(), two_env())
    R.agree("V01-a three scans #scan0-2", cat([x(2), x(10), x(3), x(11), x(2), x(12)]), three(), three_env(), three_env(), three_env())
    R.agree("V01-a only scans", cat([x(2), x(3), x(2)]), DF.lazy_concat_vertical([scan(x2p(), xs()), scan(x3p(), xs()), scan(x2p(), xs())]), DF.empty_env(), DF.empty_env(), DF.empty_env())
    # different schemas, joins
    R.agree("V01-a inner join scan x #scan0 (k,w)", R.e_inner(kv(), kw(), ks(), ks()), diff_join(), kw_env(), kw_env(), kw_env())
    R.agree("V01-a left join scan x scan", R.e_left(kv(), kw(), ks(), ks()), DF.lazy_left_join(scan(kvp(), kvs()), scan(kwp(), kws()), ks(), ks()), DF.empty_env(), DF.empty_env(), DF.empty_env())
    R.agree("V01-a self-join of a scan", R.e_inner(kv(), kv(), ks(), ks()), self_join(), DF.empty_env(), DF.empty_env(), DF.empty_env())
    R.agree("V01-a semi join scan x #scan0", e_semi(kv(), k31()), DF.lazy_semi_join(scan(kvp(), kvs()), R.src("#scan0", k31()), ks(), ks()), k31_env(), k31_env(), k31_env())
    R.agree("V01-a anti join scan x #scan0", e_anti(kv(), k31()), DF.lazy_anti_join(scan(kvp(), kvs()), R.src("#scan0", k31()), ks(), ks()), k31_env(), k31_env(), k31_env())
    R.agree("V01-a join of two concats", R.e_inner(cat([kw(), kw()]), kv(), ks(), ks()), DF.lazy_inner_join(DF.lazy_concat_vertical([R.src("#scan0", kw()), scan(kwp(), kws())]), scan(kvp(), kvs()), ks(), ks()), kw_env(), kw_env(), kw_env())
    # validate_bindings and collect_schema: a scan binds no name
    IO.print(check("V01-a repro", repro("#scan0"), R.env1("#scan0", x(1))))
    IO.print(check("V01-a repro empty env", repro("#scan0"), DF.empty_env()))
    IO.print(check("V01-a repro bound twice", repro("#scan0"), R.env_add(R.env1("#scan0", x(1)), "#scan0", x(1))))
    IO.print(check("V01-a three scans", three(), three_env()))
    IO.print(check("V01-a only scans", scan(x2p(), xs()), DF.empty_env()))
    IO.print(check("V01-a different schema", diff_join(), kw_env()))
    IO.print(check("V01-a #scan0 with the scan's schema", diff_join(), R.env1("#scan0", kv())))
    IO.print(R.schema("V01-a repro", repro("#scan0")))
    IO.print(R.schema("V01-a three scans", three()))
    IO.print(R.schema("V01-a different schema", diff_join()))
    # errors: bindings before scans; scans in postfix order, before any operator
    lazy3("V01-a unbound #scan0 before a missing scan", DF.lazy_concat_vertical([R.src("#scan0", x(1)), scan(missp(), xs())]), DF.empty_env(), DF.empty_env(), DF.empty_env())
    lazy3("V01-a missing scan then bad scan", DF.lazy_concat_vertical([R.src("#scan0", x(1)), scan(missp(), xs()), scan(badp(), xs())]), R.env1("#scan0", x(1)), R.env1("#scan0", x(1)), R.env1("#scan0", x(1)))
    lazy3("V01-a bad scan then missing scan", DF.lazy_concat_vertical([R.src("#scan0", x(1)), scan(badp(), xs()), scan(missp(), xs())]), R.env1("#scan0", x(1)), R.env1("#scan0", x(1)), R.env1("#scan0", x(1)))
    lazy3("V01-a frozen-schema error then missing scan", DF.lazy_concat_vertical([scan(x2p(), [S.Field{"y", D.TU32{}}]), scan(missp(), [S.Field{"y", D.TU32{}}])]), DF.empty_env(), DF.empty_env(), DF.empty_env())
    lazy3("V01-a cast error before a missing scan", DF.lazy_concat_vertical([cast_q(), scan(missp(), xs())]), R.env1("#scan0", q()), R.env1("#scan0", q()), R.env1("#scan0", q()))
    lazy3("V01-a static error before scans", DF.lazy_concat_vertical([R.src("#scan0", x(1)), scan(missp(), kvs())]), DF.empty_env(), DF.empty_env(), DF.empty_env())
    # the pure runner never reads a user frame for a scan
    IO.print(R.show("V01-a run_pure on a scan plan", "pure", Q.Exec.run_pure(repro("#scan0"), R.env_add(R.env1("#scan0", x(1)), "#scan1", x(5)))))
#|-- V01-a repro #scan0
#|frame
#|height	2
#|width	1
#|col	u32	"x"
#|row	1
#|row	2
#|raw=eager opt=eager full=eager
#|
#|-- V01-a control user_source
#|frame
#|height	2
#|width	1
#|col	u32	"x"
#|row	1
#|row	2
#|raw=eager opt=eager full=eager
#|
#|-- V01-a inferred #scan0
#|frame
#|height	2
#|width	1
#|col	u32	"x"
#|row	1
#|row	2
#|raw=eager opt=eager full=eager
#|
#|-- V01-a two scans #scan1
#|frame
#|height	3
#|width	1
#|col	u32	"x"
#|row	2
#|row	11
#|row	3
#|raw=eager opt=eager full=eager
#|
#|-- V01-a three scans #scan0-2
#|frame
#|height	6
#|width	1
#|col	u32	"x"
#|row	2
#|row	10
#|row	3
#|row	11
#|row	2
#|row	12
#|raw=eager opt=eager full=eager
#|
#|-- V01-a only scans
#|frame
#|height	3
#|width	1
#|col	u32	"x"
#|row	2
#|row	3
#|row	2
#|raw=eager opt=eager full=eager
#|
#|-- V01-a inner join scan x #scan0 (k,w)
#|frame
#|height	2
#|width	3
#|col	u32	"k"
#|col	str	"v"
#|col	u32	"w"
#|row	2	"b"	20
#|row	3	"c"	30
#|raw=eager opt=eager full=eager
#|
#|-- V01-a left join scan x scan
#|frame
#|height	3
#|width	3
#|col	u32	"k"
#|col	str	"v"
#|col	u32	"w"
#|row	1	"a"	null
#|row	2	"b"	20
#|row	3	"c"	30
#|raw=eager opt=eager full=eager
#|
#|-- V01-a self-join of a scan
#|frame
#|height	3
#|width	3
#|col	u32	"k"
#|col	str	"v"
#|col	str	"v_right"
#|row	1	"a"	"a"
#|row	2	"b"	"b"
#|row	3	"c"	"c"
#|raw=eager opt=eager full=eager
#|
#|-- V01-a semi join scan x #scan0
#|frame
#|height	2
#|width	2
#|col	u32	"k"
#|col	str	"v"
#|row	1	"a"
#|row	3	"c"
#|raw=eager opt=eager full=eager
#|
#|-- V01-a anti join scan x #scan0
#|frame
#|height	1
#|width	2
#|col	u32	"k"
#|col	str	"v"
#|row	2	"b"
#|raw=eager opt=eager full=eager
#|
#|-- V01-a join of two concats
#|frame
#|height	4
#|width	3
#|col	u32	"k"
#|col	u32	"w"
#|col	str	"v"
#|row	2	20	"b"
#|row	3	30	"c"
#|row	2	20	"b"
#|row	3	30	"c"
#|raw=eager opt=eager full=eager
#|
#|-- V01-a repro validate_bindings
#|ok
#|
#|-- V01-a repro empty env validate_bindings
#|error: InvalidOperation: source not in env: #scan0
#|
#|-- V01-a repro bound twice validate_bindings
#|error: InvalidOperation: source bound twice in env: #scan0
#|
#|-- V01-a three scans validate_bindings
#|ok
#|
#|-- V01-a only scans validate_bindings
#|ok
#|
#|-- V01-a different schema validate_bindings
#|ok
#|
#|-- V01-a #scan0 with the scan's schema validate_bindings
#|error: InvalidOperation: source #scan0: data schema [k:u32, v:str] differs from the plan's [k:u32, w:u32]
#|
#|-- V01-a repro schema
#|x:u32
#|
#|-- V01-a three scans schema
#|x:u32
#|
#|-- V01-a different schema schema
#|k:u32, v:str, w:u32
#|
#|-- V01-a unbound #scan0 before a missing scan raw
#|error	InvalidOperation: source not in env: #scan0
#|
#|-- V01-a unbound #scan0 before a missing scan opt
#|error	InvalidOperation: source not in env: #scan0
#|
#|-- V01-a unbound #scan0 before a missing scan full
#|error	InvalidOperation: source not in env: #scan0
#|
#|-- V01-a missing scan then bad scan raw
#|error	IoError 2: No such file or directory
#|
#|-- V01-a missing scan then bad scan opt
#|error	IoError 2: No such file or directory
#|
#|-- V01-a missing scan then bad scan full
#|error	IoError 2: No such file or directory
#|
#|-- V01-a bad scan then missing scan raw
#|error	ParseError at line 3: column x: cannot parse "z" as u32
#|
#|-- V01-a bad scan then missing scan opt
#|error	ParseError at line 3: column x: cannot parse "z" as u32
#|
#|-- V01-a bad scan then missing scan full
#|error	ParseError at line 3: column x: cannot parse "z" as u32
#|
#|-- V01-a frozen-schema error then missing scan raw
#|error	InvalidOperation: scan_csv tests/regress/data/V01_scan_x2.csv: data schema [x:u32] differs from the plan's [y:u32]
#|
#|-- V01-a frozen-schema error then missing scan opt
#|error	InvalidOperation: scan_csv tests/regress/data/V01_scan_x2.csv: data schema [x:u32] differs from the plan's [y:u32]
#|
#|-- V01-a frozen-schema error then missing scan full
#|error	InvalidOperation: scan_csv tests/regress/data/V01_scan_x2.csv: data schema [x:u32] differs from the plan's [y:u32]
#|
#|-- V01-a cast error before a missing scan raw
#|error	IoError 2: No such file or directory
#|
#|-- V01-a cast error before a missing scan opt
#|error	IoError 2: No such file or directory
#|
#|-- V01-a cast error before a missing scan full
#|error	IoError 2: No such file or directory
#|
#|-- V01-a static error before scans raw
#|error	InvalidOperation: concat_vertical: input 1 schema [k:u32, v:str] differs from input 0's [x:u32]
#|
#|-- V01-a static error before scans opt
#|error	InvalidOperation: concat_vertical: input 1 schema [k:u32, v:str] differs from input 0's [x:u32]
#|
#|-- V01-a static error before scans full
#|error	InvalidOperation: concat_vertical: input 1 schema [k:u32, v:str] differs from input 0's [x:u32]
#|
#|-- V01-a run_pure on a scan plan pure
#|error	InvalidOperation: exec: scan_csv not materialised: tests/regress/data/V01_scan_x2.csv
#|
