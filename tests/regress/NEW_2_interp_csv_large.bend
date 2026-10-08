# NEW-2 remainder (CSV): the interpreter (`bend file.bend`, the JS lane) overflows its stack at
# ~2^15 nested non-tail calls, so every per-row loop on the CSV paths must be a tail call:
# Csv.conv / Csv.rec_lines / Csv.take_rows / Csv.drop_blank and the record counts on the read
# side (read_csv of bench/data/sales_100000.csv crashed), Csv.cells / Csv.zip / Csv.zip_pre /
# List.replicate / String.concat on the write side (write_csv and Csv.render of >= 2^15 rows).
#
# A 50,000-row frame (u32 id, str s with commas, quotes and nulls, f32 x, i32 v with nulls,
# bool b) is rendered, written, read back eagerly and lazily (scan_csv, raw and optimised),
# and each text / dump is summarised: chars, lines, FNV-1a over the code points
# (bench/contract/regress_expect.py builds the same CSV text and dump in Python). A read-back
# frame has the dump of the written one. One big frame is alive at a time.
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/plan.bend as P
import ./../../src/exec.bend as Q
import ./../../src/csv.bend as V
import ./lib/rx.bend as R

def path() -> String:
  "/tmp/bend_frame_regress_NEW_2_csv_large.csv"

# row i: id = i; s = "r<i>", or `a,b"c<i>` when i % 13 = 5, or null when i % 17 = 3;
# x = i / 4; v = i - 25000, null when i % 7 = 3; b = (i % 3 = 0)
def sv(+i: U32) -> D.Scalar:
  Bool.pick(D.Scalar, U32.is_eq(U32.mod(i, 17), 3), R.null(), Bool.pick(D.Scalar, U32.is_eq(U32.mod(i, 13), 5), R.s("a,b\"c" ++ U32.show(i)), R.s("r" ++ U32.show(i))))

def vv(+i: U32) -> D.Scalar:
  Bool.pick(D.Scalar, U32.is_eq(U32.mod(i, 7), 3), R.null(), D.SI32{D.I32{U32.sub(i, 25000)}})

def ids(+n: Nat, acc: List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  match n:
    case 0n:
      acc
    case 1n+p:
      ids(p, R.u(U32.from_nat(p)) <> acc)

def ss(+n: Nat, acc: List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  match n:
    case 0n:
      acc
    case 1n+p:
      ss(p, sv(U32.from_nat(p)) <> acc)

def xs(+n: Nat, acc: List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  match n:
    case 0n:
      acc
    case 1n+p:
      xs(p, R.f(F32.div(U32.to_f32(U32.from_nat(p)), 4.0)) <> acc)

def vs(+n: Nat, acc: List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  match n:
    case 0n:
      acc
    case 1n+p:
      vs(p, vv(U32.from_nat(p)) <> acc)

def bs(+n: Nat, acc: List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  match n:
    case 0n:
      acc
    case 1n+p:
      bs(p, R.b(U32.is_eq(U32.mod(U32.from_nat(p), 3), 0)) <> acc)

def t() -> E.ResT(C.Frame):
  R.frame([R.mk("id", ids(50000n, Nil{}), D.TU32{}), R.mk("s", ss(50000n, Nil{}), D.TStr{}), R.mk("x", xs(50000n, Nil{}), D.TF32{}), R.mk("v", vs(50000n, Nil{}), D.TI32{}), R.mk("b", bs(50000n, Nil{}), D.TBool{})])

# ---- the summary of a text: chars, lines, FNV-1a (32 bit, over code points) -----------------

def sum.go(s: String, +n: U32, +l: U32, +h: U32) -> String:
  match s:
    case SNil{}:
      "chars " ++ U32.show(n) ++ " lines " ++ U32.show(l) ++ " fnv " ++ U32.show(h) ++ "\n"
    case SCon{Chr{+c}, t}:
      sum.go(t, U32.inc(n), U32.add(l, Bool.to_u32(U32.is_eq(c, 10))), U32.mul(U32.xor(h, c), 16777619))

def summary(+tag: String, how: String, text: String) -> String:
  "-- " ++ tag ++ " " ++ how ++ "\n" ++ sum.go(text, 0, 0, 2166136261)

def rendered.k(r: C.Frame & String) -> String:
  (f, text) = r
  text

# the text Csv.render (and so write_csv) produces
def rendered(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e) ++ "\n"
    case Done{f}:
      rendered.k(V.Csv.render(f, None{}))

def lazy(+tag: String, rp: E.Res(P.Plan)) -> IO(Unit):
  match rp:
    case Fail{e}:
      IO.print("-- " ++ tag ++ " scan\nerror: " ++ E.Err.show(e) ++ "\n")
    case Done{p}:
      do IO<Unit>:
        r1 : E.ResT(C.Frame) <- Q.Exec.run(p, DF.empty_env())
        IO.print(summary(tag, "raw", DF.dump(r1)))

def lazy.opt(+tag: String, rp: E.Res(P.Plan)) -> IO(Unit):
  match rp:
    case Fail{e}:
      IO.print("-- " ++ tag ++ " scan\nerror: " ++ E.Err.show(e) ++ "\n")
    case Done{p}:
      do IO<Unit>:
        r2 : E.ResT(C.Frame) <- DF.collect(p, DF.empty_env())
        IO.print(summary(tag, "opt", DF.dump(r2)))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(summary("NEW-2 csv-50000 render", "text", rendered(t())))
    w : E.ResT(C.Frame) <- DF.write_csv(t(), path())
    IO.print(summary("NEW-2 csv-50000 write", "frame", DF.dump(w)))
    r0 : E.ResT(C.Frame) <- DF.read_csv(path())
    IO.print(summary("NEW-2 csv-50000 read", "eager", DF.dump(r0)))
    rp : E.Res(P.Plan) <- DF.scan_csv(path())
    lazy("NEW-2 csv-50000 read", rp)
    rq : E.Res(P.Plan) <- DF.scan_csv(path())
    lazy.opt("NEW-2 csv-50000 read", rq)
#|-- NEW-2 csv-50000 render text
#|chars 1541705 lines 50001 fnv 1183987056
#|
#|-- NEW-2 csv-50000 write frame
#|chars 2063437 lines 50008 fnv 3093569577
#|
#|-- NEW-2 csv-50000 read eager
#|chars 2063437 lines 50008 fnv 3093569577
#|
#|-- NEW-2 csv-50000 read raw
#|chars 2063437 lines 50008 fnv 3093569577
#|
#|-- NEW-2 csv-50000 read opt
#|chars 2063437 lines 50008 fnv 3093569577
#|
