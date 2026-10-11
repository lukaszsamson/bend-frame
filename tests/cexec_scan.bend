# W6.6: scan_csv collected by the chunked engine with the v0.2 reader (Lazy.collect_with_rd(CsvV02{piece},
# Chunked{g}, ..)): the reader builds the scans' chunk leaves in its combine and the runner's IScan takes
# them as they are (no CFrame.of_frame), DESIGN.md 17.5. Every answer is compared exactly (DF.dump) with the
# reference engine over the v0.1 reader (Lazy.collect):
#   * q1..q5 (bench/queries.bend) over bench/fixtures/tiny.csv (20 rows) and products.csv (64 rows) at grains
#     2^0 (one row per leaf), 2^2 and 2^4 and pieces 7 / 64 / 4096 bytes (region edges inside the leaves); q5
#     joins two scans (taken in postfix order); q6's describe over a collected scan;
#   * row cuts and chains over a scan (head, slice, filter + with_columns, a concat of two scans of one file);
#   * errors: a cell that does not parse past the inferred prefix, a scan_csv_schema whose names differ from
#     the header, a missing file, and (reader level) a header with a duplicate name (Frame.from_columns'
#     DuplicateColumn, checked by the chunk build over the names);
#   * the runner's counters (CStats): a scan whose consumer runs chunked (q1, q2, a head then a filter) is read
#     into leaves and converts nothing on the way in (conv_in 0, bytes_in 0) where the v0.1 reader's flat scan
#     frame is converted once (conv_in 1); a scan whose consumer runs flat (q4's sort, q5's join, a head then a
#     sort, the scan as the result) is read flat (conv_in 0 and no flatten: conv_out 0).
import Base
import ./../frame.bend as DF
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/csv.bend as R
import ./../src/plan.bend as P
import ./../src/schema.bend as S
import ./../src/exec.bend as Q
import ./../src/chunks.bend as CH
import ./../src/cexec.bend as QC
import ./../bench/queries.bend as QS

def same(+tag: String, +a: String, +b: String) -> String:
  Bool.pick(String, String.eq(a, b), tag ++ ": same", tag ++ ": DIFF\nreference:\n" ++ a ++ "\nchunked:\n" ++ b)

def cand(+g: Nat, +piece: U32, +p: P.Plan) -> IO(E.ResT(C.Frame)):
  QC.Lazy.collect_with_rd(R.CsvV02{piece}, QC.Chunked{g}, p, P.Env.empty())

# the plan by the reference (v0.1 reader) and by the chunked engine over the v0.2 reader's leaves
def cmp(+tag: String, +g: Nat, +piece: U32, +p: P.Plan) -> IO(String):
  do IO<String>:
    a : E.ResT(C.Frame) <- Q.Lazy.collect(p, P.Env.empty())
    b : E.ResT(C.Frame) <- cand(g, piece, p)
    return same(tag ++ " g" ++ Nat.show(g) ++ " piece " ++ U32.show(piece), DF.dump(a), DF.dump(b))

def q6.r(r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      QS.Q.q6(f)

def cmp6(+g: Nat, +piece: U32, +s: P.Plan) -> IO(String):
  do IO<String>:
    a : E.ResT(C.Frame) <- Q.Lazy.collect(s, P.Env.empty())
    b : E.ResT(C.Frame) <- cand(g, piece, s)
    return same("q6 g" ++ Nat.show(g) ++ " piece " ++ U32.show(piece), DF.dump(q6.r(a)), DF.dump(q6.r(b)))

type TP is Data:
  TP{tag: String, p: P.Plan}

def plans(+s: P.Plan, +pr: P.Plan) -> List<&2, TP>:
  [TP{"q1", QS.Q.q1(s, pr)}, TP{"q2", QS.Q.q2(s, pr)}, TP{"q3", QS.Q.q3(s, pr)}, TP{"q4", QS.Q.q4(s, pr)}, TP{"q5", QS.Q.q5(s, pr)},
   TP{"head 7", DF.lazy_head(s, 7)}, TP{"slice 3 9", DF.lazy_slice(s, 3, 9)},
   TP{"filter + with_columns", DF.lazy_with_columns(DF.lazy_filter(s, DF.gt(DF.col("qty"), DF.lit_u32(30))), [DF.alias(DF.add(DF.col("qty"), DF.col("id")), "qi")])},
   TP{"concat of two scans", DF.lazy_filter(DF.lazy_concat_vertical([s, DF.lazy_head(s, 6)]), DF.col("ok"))},
   TP{"products", pr}]

def runs(+g: Nat, +piece: U32, ps: List<&2, TP>) -> IO(Unit):
  match ps:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case TP{+tag, +p} <> t:
      do IO<Unit>:
        +line : String <- cmp(tag, g, piece, p)
        IO.print(line)
        runs(g, piece, t)

type GPc is Data:
  GPc{g: Nat, piece: U32}

def cfgs(+s: P.Plan, +pr: P.Plan, cs: List<&2, GPc>) -> IO(Unit):
  match cs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case GPc{+g, +piece} <> t:
      do IO<Unit>:
        runs(g, piece, plans(s, pr))
        +l6 : String <- cmp6(g, piece, s)
        IO.print(l6)
        cfgs(s, pr, t)

# ---- the runner's counters ----

def st.show(r: QC.CStats & E.ResT(C.Frame)) -> String:
  (st, x) = r
  match st:
    case QC.CStats{ci, bi, co, bo, w, fl}:
      "conv_in " ++ U32.show(ci) ++ " bytes_in " ++ U32.show(bi) ++ " conv_out " ++ U32.show(co) ++ Bool.pick(String, U32.is_ne(w, 0), " walks > 0", " no walk")

def st.k2(+g: Nat, +p: P.Plan, ep: P.Env & List<&1, QC.PNF>) -> String:
  (env, pre) = ep
  st.show(QC.CX.run(g, p, env, pre))

def st.k(+g: Nat, +p: P.Plan, r: E.ResT(P.Env & List<&1, QC.PNF>)) -> String:
  match r:
    case Fail{e}:
      "error " ++ E.Err.show(e)
    case Done{ep}:
      st.k2(g, p, ep)

def st.v1(+g: Nat, +p: P.Plan, r: E.ResT(P.Env)) -> String:
  match r:
    case Fail{e}:
      "error " ++ E.Err.show(e)
    case Done{env}:
      st.show(QC.CX.run(g, p, env, Nil{}))

# the counters of one plan: chunked scans from the v0.2 reader, and the v0.1 reader's flat scan frame
def stats(+tag: String, +g: Nat, +p: P.Plan) -> IO(Unit):
  do IO<Unit>:
    a : E.ResT(P.Env & List<&1, QC.PNF>) <- QC.CX.prep.k(P.Plan.schema(p), g, R.CsvV02{4096}, p, P.Env.empty())
    b : E.ResT(P.Env) <- Q.Exec.prep(R.CsvV01{}, p, P.Env.empty())
    IO.print(tag ++ " v02 scan: " ++ st.k(g, p, a) ++ " | v01 scan: " ++ st.v1(g, p, b))

# ---- files written for the error cases ----

def wr.k(f: File, r: Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  do IO<Unit>:
    File.close(f)
    return Unit{}

def wr.got(r: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (f, res) = r
  wr.k(f, res)

def wr.open(+text: String, o: Result<&1, &1, U32 & String, File>) -> IO(Unit):
  match o:
    case Done{f}:
      do IO<Unit>:
        r : File & Result<&1, &1, U32 & String, Unit> <- File.write(f, text)
        wr.got(r)
    case Fail{(code, msg)}:
      IO.print("cannot write: " ++ msg)

def wr(+path: String, +text: String) -> IO(Unit):
  do IO<Unit>:
    o : Result<&1, &1, U32 & String, File> <- File.open(path, "w")
    wr.open(text, o)

# rows 1..150 of one u32 column, row 120 "x": inference over 100 rows freezes u32
def late.rows(f: Nat, +i: U32, acc: String) -> String:
  match f:
    case 0n:
      acc
    case 1n+p:
      late.rows(p, U32.sub(i, 1), Bool.pick(String, U32.is_eq(i, 120), "x", U32.show(i)) ++ "\n" ++ acc)

# 12 rows under the header a,b,a
def dup.rows(f: Nat, +i: U32, acc: String) -> String:
  match f:
    case 0n:
      acc
    case 1n+p:
      dup.rows(p, U32.sub(i, 1), U32.show(i) ++ ",x" ++ U32.show(i) ++ "," ++ U32.show(U32.mul(i, 2)) ++ "\n" ++ acc)

def late.path() -> String:
  "/tmp/bend_frame_cexec_scan_late.csv"

def dup.path() -> String:
  "/tmp/bend_frame_cexec_scan_dup.csv"

def ref.out(r: E.ResT(C.Frame)) -> E.ResT(C.Frame) & String:
  match r:
    case Fail{+e}:
      (Fail{e}, " | " ++ E.Err.show(e))
    case Done{f}:
      (Done{f}, " | a frame")

def cmp.e.k(+tag: String, rb: E.ResT(C.Frame), ra: E.ResT(C.Frame) & String) -> String:
  (a, +o) = ra
  same(tag, DF.dump(a), DF.dump(rb)) ++ o

# an error case at grain 2^2, piece 64: the comparison and the reference's error text
def cmp.e(+tag: String, +p: P.Plan) -> IO(String):
  do IO<String>:
    a : E.ResT(C.Frame) <- Q.Lazy.collect(p, P.Env.empty())
    b : E.ResT(C.Frame) <- cand(2n, 64, p)
    return cmp.e.k(tag, b, ref.out(a))

def scan.err(+tag: String, rp: E.Res(P.Plan)) -> IO(Unit):
  match rp:
    case Fail{e}:
      IO.print(tag ++ ": plan " ++ E.Err.show(e))
    case Done{+p}:
      do IO<Unit>:
        +l : String <- cmp.e(tag, p)
        IO.print(l)

# the duplicate header at the reader level: v0.1 and the chunk build (12 rows > 2^2)
def dup.out(r: E.ResT(R.CsvOut)) -> String:
  match r:
    case Fail{e}:
      "error " ++ E.Err.show(e)
    case Done{o}:
      match o:
        case R.CsvFlat{f}:
          "flat " ++ DF.dump(Done{f})
        case R.CsvChk{f}:
          "chunks " ++ DF.dump(Done{CH.CFrame.to_frame(f)})

def dup.cmp() -> IO(String):
  do IO<String>:
    a : E.ResT(C.Frame) <- R.Csv.read_full(dup.path(), R.Csv.default(), [], R.Csv.enc_default(), 1048576, 8388608)
    b : E.ResT(R.CsvOut) <- R.Csv.read_v02_mode(R.CMChk{2n}, dup.path(), R.Csv.default(), [], R.Csv.enc_default(), 16, 8388608)
    return "duplicate header: v01 " ++ dup.out(R.Csv.v2.flat(a)) ++ " | chunk mode " ++ dup.out(b)

def go(s: E.Res(P.Plan), pr: E.Res(P.Plan)) -> IO(Unit):
  match s pr:
    case Done{+a} Done{+b}:
      do IO<Unit>:
        cfgs(a, b, [GPc{0n, 31}, GPc{2n, 7}, GPc{2n, 4096}, GPc{4n, 64}])
        stats("q1", 2n, QS.Q.q1(a, b))
        stats("q2", 2n, QS.Q.q2(a, b))
        stats("q4", 2n, QS.Q.q4(a, b))
        stats("q5", 2n, QS.Q.q5(a, b))
        stats("scan alone", 2n, a)
        stats("head then filter", 2n, DF.lazy_filter(DF.lazy_head(a, 15), DF.col("ok")))
        stats("head then sort", 2n, DF.lazy_sort(DF.lazy_head(a, 15), [DF.asc("id")]))
        stats("q1 at 2^5 (one leaf)", 5n, QS.Q.q1(a, b))
    case Fail{e} _:
      IO.print("scan error: " ++ E.Err.show(e))
    case _ Fail{e}:
      IO.print("scan error: " ++ E.Err.show(e))

def main() -> IO(Unit):
  do IO<Unit>:
    s : E.Res(P.Plan) <- P.Lazy.scan_csv("bench/fixtures/tiny.csv", R.Csv.default())
    pr : E.Res(P.Plan) <- P.Lazy.scan_csv("bench/fixtures/products.csv", R.Csv.default())
    go(s, pr)
    wr(late.path(), "n\n" ++ late.rows(150n, 150, ""))
    wr(dup.path(), "a,b,a\n" ++ dup.rows(12n, 12, ""))
    l : E.Res(P.Plan) <- P.Lazy.scan_csv(late.path(), R.Csv.default())
    scan.err("late bad cell", l)
    scan.err("schema dtype count", Done{DF.scan_csv_schema("bench/fixtures/tiny.csv", R.Csv.default(), [S.Field{"id", DF.t_u32()}])})
    scan.err("schema names differ", Done{DF.scan_csv_schema("bench/fixtures/tiny.csv", R.Csv.default(), [S.Field{"id", DF.t_u32()}, S.Field{"label", DF.t_str()}, S.Field{"product", DF.t_str()}, S.Field{"qty", DF.t_u32()}, S.Field{"price", DF.t_f32()}, S.Field{"discount", DF.t_f32()}, S.Field{"ok", DF.t_bool()}])})
    scan.err("missing file", Done{DF.scan_csv_schema("/tmp/bend_frame_no_such_file.csv", R.Csv.default(), [S.Field{"id", DF.t_u32()}])})
    +d : String <- dup.cmp()
    IO.print(d)
#|q1 g0 piece 31: same
#|q2 g0 piece 31: same
#|q3 g0 piece 31: same
#|q4 g0 piece 31: same
#|q5 g0 piece 31: same
#|head 7 g0 piece 31: same
#|slice 3 9 g0 piece 31: same
#|filter + with_columns g0 piece 31: same
#|concat of two scans g0 piece 31: same
#|products g0 piece 31: same
#|q6 g0 piece 31: same
#|q1 g2 piece 7: same
#|q2 g2 piece 7: same
#|q3 g2 piece 7: same
#|q4 g2 piece 7: same
#|q5 g2 piece 7: same
#|head 7 g2 piece 7: same
#|slice 3 9 g2 piece 7: same
#|filter + with_columns g2 piece 7: same
#|concat of two scans g2 piece 7: same
#|products g2 piece 7: same
#|q6 g2 piece 7: same
#|q1 g2 piece 4096: same
#|q2 g2 piece 4096: same
#|q3 g2 piece 4096: same
#|q4 g2 piece 4096: same
#|q5 g2 piece 4096: same
#|head 7 g2 piece 4096: same
#|slice 3 9 g2 piece 4096: same
#|filter + with_columns g2 piece 4096: same
#|concat of two scans g2 piece 4096: same
#|products g2 piece 4096: same
#|q6 g2 piece 4096: same
#|q1 g4 piece 64: same
#|q2 g4 piece 64: same
#|q3 g4 piece 64: same
#|q4 g4 piece 64: same
#|q5 g4 piece 64: same
#|head 7 g4 piece 64: same
#|slice 3 9 g4 piece 64: same
#|filter + with_columns g4 piece 64: same
#|concat of two scans g4 piece 64: same
#|products g4 piece 64: same
#|q6 g4 piece 64: same
#|q1 v02 scan: conv_in 0 bytes_in 0 conv_out 1 walks > 0 | v01 scan: conv_in 1 bytes_in 400 conv_out 1 walks > 0
#|q2 v02 scan: conv_in 0 bytes_in 0 conv_out 1 walks > 0 | v01 scan: conv_in 1 bytes_in 640 conv_out 1 walks > 0
#|q4 v02 scan: conv_in 0 bytes_in 0 conv_out 0 no walk | v01 scan: conv_in 0 bytes_in 0 conv_out 0 no walk
#|q5 v02 scan: conv_in 0 bytes_in 0 conv_out 0 no walk | v01 scan: conv_in 0 bytes_in 0 conv_out 0 no walk
#|scan alone v02 scan: conv_in 0 bytes_in 0 conv_out 0 no walk | v01 scan: conv_in 0 bytes_in 0 conv_out 0 no walk
#|head then filter v02 scan: conv_in 0 bytes_in 0 conv_out 1 walks > 0 | v01 scan: conv_in 1 bytes_in 480 conv_out 1 walks > 0
#|head then sort v02 scan: conv_in 0 bytes_in 0 conv_out 0 no walk | v01 scan: conv_in 0 bytes_in 0 conv_out 0 no walk
#|q1 at 2^5 (one leaf) v02 scan: conv_in 0 bytes_in 0 conv_out 0 no walk | v01 scan: conv_in 0 bytes_in 0 conv_out 0 no walk
#|late bad cell: same | ParseError at line 121: column n: cannot parse "x" as u32
#|schema dtype count: same | InvalidOperation: csv schema: 1 dtypes for 7 columns
#|schema names differ: same | InvalidOperation: scan_csv bench/fixtures/tiny.csv: data schema [id:u32, region:str, product:str, qty:u32, price:f32, discount:f32, ok:bool] differs from the plan's [id:u32, label:str, product:str, qty:u32, price:f32, discount:f32, ok:bool]
#|missing file: same | IoError 2: No such file or directory
#|duplicate header: v01 error DuplicateColumn: a | chunk mode error DuplicateColumn: a
