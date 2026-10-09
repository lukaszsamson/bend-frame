# M4 string-experiment driver (plans/M_01.txt section 5). Native only:
#   ~/.bend/bin/bend bench/strbench.bend -o build/strbench
#   ./build/strbench [--threads N] <file.csv> <op> <raw|dict|auto> [dim.csv]
# The CSV (bench/data/str/, bench/gen_str.py) is read with Csv.read_enc and the given Str storage,
# every buffer is walked once, then ONE operation is timed (IO.now, ms) with its result kept alive
# past the clock. stdout: one JSON line {"op","enc","rows","ms","parse_ms","walk_ms","chk"}.
# Ops (column s is the str column, v u32, x f32; dim.csv: every distinct s once with a u32 w):
#   parse    the read itself (parse_ms) and the first walk (walk_ms); ms = their sum
#   encode   C.Frame.encode(f, True): Dictionary-encode the read frame's Str columns
#   decode   C.Frame.encode(f, False): back to Raw
#   gather   s gathered by a random permutation (an argsort by x, untimed)
#   sort     sort by s (every column gathered)
#   sortx    sort by x (a numeric control; every column gathered, s among them)
#   group    group_by s: len, sum v
#   groupv   group_by v: len, max s (a control keyed on a number)
#   join     inner join on s with dim.csv (read with the same storage: other codes for equal values)
#   eq       filter s == (row 1's value)
#   lt       filter s < (row 1's value)
#   pred     with_columns starts_with(s, "a"), len_chars(s)
#   render   Csv.render of the frame (every cell written)
#   drop     free the frame (consumed inside the timed region)
#   group5   group_by s five times, each over its own clone (repeated-query memory: run under
#            /usr/bin/time -l and compare with `group`)
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/kernels.bend as K
import ./../src/column.bend as C
import ./../src/strs.bend as ST
import ./../src/csv.bend as V
import ./../src/expr.bend as X
import ./../src/sort.bend as O
import ./../src/join.bend as J
import ./../src/eval.bend as EV
import ./../src/groupby.bend as G
import ./../frame.bend as DF

# ---- forcing: every buffer read once (untimed) -------------------------------------------------

def fw.k(t: D.DType, +n: U32, d: Nat, v: C.Valid, r: Array<U32> & U32) -> C.Column & U32:
  (x, h) = r
  (C.Column.mk_w(t, n, d, v, x), h)

def ff.k(+n: U32, d: Nat, v: C.Valid, r: Array<F32> & F32) -> C.Column & U32:
  (x, h) = r
  (C.CF32{n, d, v, x}, F32.to_u32(h))

def fs.k(+n: U32, d: Nat, v: C.Valid, r: ST.Strs & U32) -> C.Column & U32:
  (x, h) = r
  (C.CStr{n, d, v, x}, h)

def fs.r(r: Array<String> & U32) -> ST.Strs & U32:
  (a, h) = r
  (ST.SRaw{a}, h)

def fs.d(dict: ST.Dict, r: Array<U32> & U32) -> ST.Strs & U32:
  (c, h) = r
  (ST.SDict{c, dict}, h)

def fs.walk(+n: U32, x: ST.Strs) -> ST.Strs & U32:
  match x:
    case ST.SRaw{a}:
      fs.r(K.Kernel.fold(~String, ~U32, ~(a => y => U32.add(a, J.Str.hash(y, 0))), n, a, 0))
    case ST.SDict{c, dict}:
      fs.d(dict, K.Kernel.fold(~U32, ~U32, ~(a => y => U32.add(a, y)), n, c, 0))

def force.col(c: C.Column) -> C.Column & U32:
  match c:
    case C.CBool{+n, d, v, x}:
      fw.k(D.TBool{}, n, d, v, K.Kernel.fold(~U32, ~U32, ~(a => y => U32.add(a, y)), n, x, 0))
    case C.CU32{+n, d, v, x}:
      fw.k(D.TU32{}, n, d, v, K.Kernel.fold(~U32, ~U32, ~(a => y => U32.add(a, y)), n, x, 0))
    case C.CI32{+n, d, v, x}:
      fw.k(D.TI32{}, n, d, v, K.Kernel.fold(~U32, ~U32, ~(a => y => U32.add(a, y)), n, x, 0))
    case C.CF32{+n, d, v, x}:
      ff.k(n, d, v, K.Kernel.fold(~F32, ~F32, ~(a => y => F32.add(a, y)), n, x, 0.0))
    case C.CStr{+n, d, v, x}:
      fs.k(n, d, v, fs.walk(n, x))

def force.add(n: String, acc: List<&1, C.Named>, +h: U32, r: C.Column & U32) -> List<&1, C.Named> & U32:
  (c, x) = r
  (C.Named{n, c} <> acc, U32.add(h, x))

def force.step(n: String, c: C.Column, st: List<&1, C.Named> & U32) -> List<&1, C.Named> & U32:
  (acc, +h) = st
  force.add(n, acc, h, force.col(c))

def force.go(cols: List<&1, C.Named>, st: List<&1, C.Named> & U32) -> List<&1, C.Named> & U32:
  match cols:
    case Nil{}:
      st
    case C.Named{n, c} <> rest:
      force.go(rest, force.step(n, c, st))

def force.fin(+h: U32, r: List<&1, C.Named> & U32) -> C.Frame & U32:
  (acc, x) = r
  (C.Frame{h, List.reverse(&1, C.Named, acc)}, x)

def force(f: C.Frame) -> C.Frame & U32:
  match f:
    case C.Frame{+h, cols}:
      force.fin(h, force.go(cols, (Nil{}, 0)))

# ---- helpers ------------------------------------------------------------------------------------

def enc.of(+s: String) -> ST.StrEnc:
  Bool.pick(ST.StrEnc, String.eq(s, "dict"), ST.EncDict{}, Bool.pick(ST.StrEnc, String.eq(s, "auto"), ST.EncAuto{}, ST.EncRaw{}))

def height.k(r: C.Frame & U32) -> U32:
  (f, h) = r
  h

def height(r: E.ResT(C.Frame)) -> U32:
  match r:
    case Fail{e}:
      4294967295
    case Done{f}:
      height.k(C.Frame.height(f))

def snd.f(r: C.Frame & C.Frame) -> C.Frame:
  (a, b) = r
  b

def fst.f(r: C.Frame & C.Frame) -> C.Frame:
  (a, b) = r
  a

def lit.c(r: C.Column & D.Scalar) -> String:
  (c, s) = r
  match s:
    case D.SStr{x}:
      x
    case _:
      ""

# row 1's s (the literal of eq / lt)
def lit.s(r: C.Frame & E.ResT(C.Column)) -> String:
  (f, rc) = r
  match rc:
    case Fail{e}:
      ""
    case Done{c}:
      lit.c(C.Column.cell(c, 1))

def is_str(c: C.Column) -> Bool:
  match c:
    case C.CStr{n, d, v, x}:
      True{}
    case _:
      False{}

def storage.k(r: C.Column & Bool) -> String:
  (c, b) = r
  Bool.pick(String, b, "dict", "raw")

# ---- the operations --------------------------------------------------------------------------------

# the column a Str column's storage is reported by: dict or raw
def storage(r: C.Frame & E.ResT(C.Column)) -> String:
  (f, rc) = r
  match rc:
    case Fail{e}:
      "none"
    case Done{c}:
      storage.k(C.Column.is_dict(c))

type Res is Type:
  RF{r: E.ResT(C.Frame)}
  RS{s: String}
  RU{u: U32}
  RFs{rs: List<&1, E.ResT(C.Frame)>}

def res.chk.l(rs: List<&1, E.ResT(C.Frame)>, +acc: U32) -> U32:
  match rs:
    case Nil{}:
      acc
    case r <> t:
      res.chk.l(t, U32.add(acc, height(r)))

def res.chk(r: Res) -> U32:
  match r:
    case RF{x}:
      height(x)
    case RS{s}:
      U32.from_nat(String.length(s))
    case RU{u}:
      u
    case RFs{rs}:
      res.chk.l(rs, 0)

def op.gather.h(r: C.Column & U32) -> U32:
  (c, n) = r
  n

def op.gather.k(r: C.Column & Array<U32>) -> Res:
  (c, perm) = r
  RU{op.gather.h(C.Column.len(c))}

def op.gather.c(perm: Array<U32>, +h: U32, rc: C.Frame & E.ResT(C.Column)) -> Res:
  (f, r) = rc
  match r:
    case Fail{e}:
      RU{0}
    case Done{c}:
      op.gather.k(C.Column.gather(c, perm, h))

def op.render.k(r: C.Frame & String) -> Res:
  (f, s) = r
  RS{s}

def drop(f: C.Frame) -> U32:
  match f:
    case C.Frame{h, cols}:
      h

def group(f: C.Frame) -> E.ResT(C.Frame):
  DF.group_by(f, [DF.col("s")], [DF.alias(DF.len(), "n"), DF.alias(DF.sum(DF.col("v")), "sv")])

def group5.k(acc: List<&1, E.ResT(C.Frame)>, r: C.Frame & C.Frame) -> C.Frame & List<&1, E.ResT(C.Frame)>:
  (a, b) = r
  (a, group(b) <> acc)

def group5.step(st: C.Frame & List<&1, E.ResT(C.Frame)>) -> C.Frame & List<&1, E.ResT(C.Frame)>:
  (f, acc) = st
  group5.k(acc, C.Frame.clone(f))

def group5.fin(st: C.Frame & List<&1, E.ResT(C.Frame)>) -> List<&1, E.ResT(C.Frame)>:
  (f, acc) = st
  acc

def group5.go(n: Nat, st: C.Frame & List<&1, E.ResT(C.Frame)>) -> List<&1, E.ResT(C.Frame)>:
  match n:
    case 0n:
      group5.fin(st)
    case 1n+p:
      group5.go(p, group5.step(st))

type Op is Data:
  OParse{}
  OEncode{}
  ODecode{}
  OGather{}
  OSort{}
  OSortx{}
  OGroup{}
  OGroupv{}
  OJoin{}
  OEq{}
  OLt{}
  OPred{}
  ORender{}
  ODrop{}
  OGroup5{}

def op.of(+s: String) -> Op:
  Bool.pick(Op, String.eq(s, "encode"), OEncode{},
  Bool.pick(Op, String.eq(s, "decode"), ODecode{},
  Bool.pick(Op, String.eq(s, "gather"), OGather{},
  Bool.pick(Op, String.eq(s, "sort"), OSort{},
  Bool.pick(Op, String.eq(s, "sortx"), OSortx{},
  Bool.pick(Op, String.eq(s, "group"), OGroup{},
  Bool.pick(Op, String.eq(s, "groupv"), OGroupv{},
  Bool.pick(Op, String.eq(s, "join"), OJoin{},
  Bool.pick(Op, String.eq(s, "eq"), OEq{},
  Bool.pick(Op, String.eq(s, "lt"), OLt{},
  Bool.pick(Op, String.eq(s, "pred"), OPred{},
  Bool.pick(Op, String.eq(s, "render"), ORender{},
  Bool.pick(Op, String.eq(s, "drop"), ODrop{},
  Bool.pick(Op, String.eq(s, "group5"), OGroup5{}, OParse{}))))))))))))))

def run.op(op: Op, +lit: String, f: C.Frame, dim: C.Frame, perm: Array<U32>, +h: U32) -> Res:
  match op:
    case OEncode{}:
      RF{Done{C.Frame.encode(f, True{})}}
    case ODecode{}:
      RF{Done{C.Frame.encode(f, False{})}}
    case OGather{}:
      op.gather.c(perm, h, C.Frame.get_cloned(f, "s"))
    case OSort{}:
      RF{DF.sort(f, [DF.asc("s")])}
    case OSortx{}:
      RF{DF.sort(f, [DF.asc("x")])}
    case OGroup{}:
      RF{group(f)}
    case OGroupv{}:
      RF{DF.group_by(f, [DF.col("v")], [DF.alias(DF.len(), "n"), DF.alias(DF.max(DF.col("s")), "ms")])}
    case OJoin{}:
      RF{DF.inner_join(f, dim, ["s"], ["s"])}
    case OEq{}:
      RF{DF.filter(f, DF.eq(DF.col("s"), DF.lit_str(lit)))}
    case OLt{}:
      RF{DF.filter(f, DF.lt(DF.col("s"), DF.lit_str(lit)))}
    case OPred{}:
      RF{DF.with_columns(f, [DF.alias(DF.starts_with(DF.col("s"), "a"), "sw"), DF.alias(DF.len_chars(DF.col("s")), "lc")])}
    case ORender{}:
      op.render.k(V.Csv.render(f, None{}))
    case ODrop{}:
      RU{drop(f)}
    case OGroup5{}:
      RFs{group5.go(5n, (f, Nil{}))}
    case OParse{}:
      RU{0}

# ---- output -------------------------------------------------------------------------------------

def q(+s: String) -> String:
  "\"" ++ s ++ "\""

def json(+op: String, +enc: String, +rows: U32, +ms: Nat, +pms: Nat, +wms: Nat, +chk: U32, +st: String) -> String:
  "{" ++ q("op") ++ ":" ++ q(op) ++ "," ++ q("enc") ++ ":" ++ q(enc) ++ "," ++ q("storage") ++ ":" ++ q(st) ++ "," ++ q("rows") ++ ":" ++ U32.show(rows) ++ "," ++ q("ms") ++ ":" ++ Nat.show(ms) ++ "," ++ q("parse_ms") ++ ":" ++ Nat.show(pms) ++ "," ++ q("walk_ms") ++ ":" ++ Nat.show(wms) ++ "," ++ q("chk") ++ ":" ++ U32.show(chk) ++ "}"

# ---- the run ------------------------------------------------------------------------------------

# after the clock: the result's check value, printed (the result is freed after that)
def fin(+op: String, +enc: String, +h: U32, +t0: Nat, +t1: Nat, +t2: Nat, +st: String, r: Res, +t3: Nat, +t4: Nat) -> IO(Unit):
  IO.print(json(op, enc, h, Bool.pick(Nat, String.eq(op, "parse"), Nat.sub(t2, t0), Nat.sub(t4, t3)), Nat.sub(t1, t0), Nat.sub(t2, t1), res.chk(r), st))

def timed(+op: String, +enc: String, +h: U32, +t0: Nat, +t1: Nat, +t2: Nat, +st: String, +lit: String, f: C.Frame, dim: C.Frame, perm: Array<U32>) -> IO(Unit):
  do IO<Unit>:
    +t3 : Nat <- IO.now()
    r : Res <- IO.pure(Res, run.op(op.of(op), lit, f, dim, perm, h))
    +t4 : Nat <- IO.now()
    fin(op, enc, h, t0, t1, t2, st, r, t3, t4)

# the permutation of gather: an argsort by x (untimed)
def perm.k(r: C.Frame & E.ResT(Array<U32>)) -> C.Frame & Array<U32>:
  (f, rp) = r
  match rp:
    case Fail{e}:
      (f, Array.new(U32, 0n, 0))
    case Done{p}:
      (f, p)

def prep.p(+op: String, +enc: String, +h: U32, +t0: Nat, +t1: Nat, +t2: Nat, +st: String, +lit: String, dim: C.Frame, r: C.Frame & Array<U32>) -> IO(Unit):
  (f, perm) = r
  timed(op, enc, h, t0, t1, t2, st, lit, f, dim, perm)

# the literal (row 1's s) and the storage of s, then the permutation
def prep.s(+op: String, +enc: String, +h: U32, +t0: Nat, +t1: Nat, +t2: Nat, dim: C.Frame, +lit: String, r: C.Frame & E.ResT(C.Column)) -> IO(Unit):
  (f, rc) = r
  prep.p(op, enc, h, t0, t1, t2, storage((C.Frame.empty(), rc)), lit, dim, perm.k(O.Sort.argsort(f, [O.SortKey{"x", False{}, False{}}])))

def prep.l(+op: String, +enc: String, +h: U32, +t0: Nat, +t1: Nat, +t2: Nat, dim: C.Frame, r: C.Frame & E.ResT(C.Column)) -> IO(Unit):
  (f, rc) = r
  prep.s(op, enc, h, t0, t1, t2, dim, lit.s((C.Frame.empty(), rc)), C.Frame.get_cloned(f, "s"))

def walked.h(+op: String, +enc: String, +t0: Nat, +t1: Nat, +t2: Nat, dim: C.Frame, r: C.Frame & U32) -> IO(Unit):
  (f, +h) = r
  prep.l(op, enc, h, t0, t1, t2, dim, C.Frame.get_cloned(f, "s"))

def walked(+op: String, +enc: String, +t0: Nat, +t1: Nat, dim: C.Frame, r: C.Frame & U32) -> IO(Unit):
  (f, x) = r
  do IO<Unit>:
    +t2 : Nat <- IO.now()
    walked.h(op, enc, t0, t1, t2, dim, C.Frame.height(f))

def loaded(+op: String, +enc: String, +t0: Nat, rs: E.ResT(C.Frame), rd: E.ResT(C.Frame)) -> IO(Unit):
  match rs rd:
    case Done{f} Done{dim}:
      do IO<Unit>:
        +t1 : Nat <- IO.now()
        walked(op, enc, t0, t1, dim, force(f))
    case Fail{e} _:
      IO.print("error: " ++ E.Err.show(e))
    case _ Fail{e}:
      IO.print("error (dim): " ++ E.Err.show(e))

def go3.dim.k(none: Bool, +dpath: String, +enc: String) -> IO(E.ResT(C.Frame)):
  match none:
    case True{}:
      IO.pure(E.ResT(C.Frame), Done{C.Frame.empty()})
    case False{}:
      V.Csv.read_enc(dpath, V.Csv.default(), Nil{}, enc.of(enc))

def go3.dim(+dpath: String, +enc: String) -> IO(E.ResT(C.Frame)):
  go3.dim.k(String.is_empty(dpath), dpath, enc)

def go3(+path: String, +op: String, +enc: String, +dpath: String) -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    rs : E.ResT(C.Frame) <- V.Csv.read_enc(path, V.Csv.default(), Nil{}, enc.of(enc))
    rd : E.ResT(C.Frame) <- go3.dim(dpath, enc)
    loaded(op, enc, t0, rs, rd)

def nth(+i: Nat, xs: List<&2, String>, +d: String) -> String:
  match i xs:
    case _ Nil{}:
      d
    case 0n h <> t:
      h
    case 1n+j h <> t:
      nth(j, t, d)

def promote(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> promote(t)

def go(+xs: List<&2, String>) -> IO(Unit):
  go3(nth(0n, xs, "bench/data/str/short_8_1000.csv"), nth(1n, xs, "parse"), nth(2n, xs, "raw"), nth(3n, xs, ""))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(List.tail(&2, String, promote(args)))
