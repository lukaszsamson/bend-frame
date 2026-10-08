# Native timing of Join.run (q5's join: sales x products on the str key
# `product`). Parsing is untimed and the parsed frames are forced (every cell
# read once) before the clock starts; one join per process (repeated parses or
# clones in one process skew timings: see IMPLEMENTING.md "M5 join").
#   ~/.bend/bin/bend bench/join_bench.bend -o build/join_bench
#   ./build/join_bench bench/data/sales_1000000.csv [inner|left|id]
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/kernels.bend as K
import ./../src/column.bend as C
import ./../src/csv.bend as V
import ./../src/join.bend as J

def wsum.m(r: C.Frame & E.ResT(C.Column)) -> C.Frame & F32:
  (f, rc) = r
  match rc:
    case Done{C.CF32{n, d, v, x}}:
      (f, K.Kernel.fsum(~F32, ~(y => y), n, x))
    case _:
      (f, 0.0)

def wsum.k(+h: U32, r: C.Frame & F32) -> E.ResT(C.Frame) & String:
  (f, w) = r
  (Done{f}, "rows=" ++ U32.show(h) ++ " sum(weight)=" ++ F32.show(w))

def summ.h(r: C.Frame & U32) -> E.ResT(C.Frame) & String:
  (f, +h) = r
  wsum.k(h, wsum.m(C.Frame.get_cloned(f, "weight")))

# rows and the sum of the joined `weight` column (0 when absent); the result
# frame comes back so that freeing it is not timed
def summ(r: E.ResT(C.Frame)) -> E.ResT(C.Frame) & String:
  match r:
    case Fail{+e}:
      (Fail{e}, "error: " ++ E.Err.show(e))
    case Done{f}:
      summ.h(C.Frame.height(f))

def cols(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "-"
    case Done{f}:
      match f:
        case C.Frame{h, cs}:
          Nat.show(List.length(&1, C.Named, cs))

def fin(+how: J.JoinHow, +label: String, t0: Nat, r: E.ResT(C.Frame) & String) -> IO(Unit):
  (f, out) = r
  do IO<Unit>:
    t1 : Nat <- IO.now()
    IO.print(label ++ " " ++ J.JoinHow.show(how) ++ ": " ++ out ++ " in " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms")
    t2 : Nat <- IO.now()
    +nc : String = cols(f)
    t3 : Nat <- IO.now()
    IO.print("  (" ++ nc ++ " columns; freeing the result took " ++ Nat.show(Nat.sub(t3, t2)) ++ " ms, untimed)")

# ---- forcing: Csv.read hands back a frame whose last work is still pending
# (summing a parsed 1M-row u32 column right after the read takes ~400 ms, on
# a forced one ~1 ms), so every buffer is walked once, untimed ----

def fw.k(t: D.DType, +n: U32, d: Nat, v: C.Valid, r: Array<U32> & U32) -> C.Column & U32:
  (x, h) = r
  (C.Column.mk_w(t, n, d, v, x), h)

def ff.k(+n: U32, d: Nat, v: C.Valid, r: Array<F32> & F32) -> C.Column & U32:
  (x, h) = r
  (C.CF32{n, d, v, x}, F32.to_u32(h))

def fs.k(+n: U32, d: Nat, v: C.Valid, r: Array<String> & U32) -> C.Column & U32:
  (x, h) = r
  (C.CStr{n, d, v, x}, h)

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
      fs.k(n, d, v, K.Kernel.fold(~String, ~U32, ~(a => y => U32.add(a, J.Str.hash(y, 0))), n, x, 0))

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

# every cell read once; a checksum comes back with the frame
def force(f: C.Frame) -> C.Frame & U32:
  match f:
    case C.Frame{+h, cols}:
      force.fin(h, force.go(cols, (Nil{}, 0)))

def time(+how: J.JoinHow, +key: String, +label: String, s: C.Frame, p: C.Frame) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    fin(how, label, t0, summ(J.Join.run(how, s, p, [key], [key])))

def time.k(+how: J.JoinHow, +key: String, +label: String, rs: C.Frame & U32, rp: C.Frame & U32) -> IO(Unit):
  (s, x) = rs
  (p, y) = rp
  time(how, key, label ++ " [forced " ++ U32.show(U32.add(x, y)) ++ "]", s, p)

def go.b(+how: J.JoinHow, +key: String, +label: String, rs: E.ResT(C.Frame), rp: E.ResT(C.Frame)) -> IO(Unit):
  match rs:
    case Fail{e}:
      IO.print("error: " ++ E.Err.show(e))
    case Done{s}:
      match rp:
        case Fail{e}:
          IO.print("error: " ++ E.Err.show(e))
        case Done{p}:
          time.k(how, key, label, force(s), force(p))

# key `product` against products.csv; how = "id": inner join on the u32
# `id` against the first 100k sales rows (a big right side, pair-table path)
def go(+how: J.JoinHow, +id: Bool, +path: String) -> IO(Unit):
  do IO<Unit>:
    rs : E.ResT(C.Frame) <- V.Csv.read(path, V.Csv.default())
    rp : E.ResT(C.Frame) <- V.Csv.read(Bool.pick(String, id, "bench/data/sales_100000.csv", "bench/fixtures/products.csv"), V.Csv.default())
    go.b(how, Bool.pick(String, id, "id", "product"), path, rs, rp)

def promote(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> promote(t)

def how_of(+s: String) -> J.JoinHow:
  Bool.pick(J.JoinHow, String.eq(s, "left"), J.Left{}, J.Inner{})

def run(as: List<&2, String>) -> IO(Unit):
  match as:
    case path <> rest:
      match rest:
        case +h <> t:
          go(how_of(h), String.eq(h, "id"), path)
        case Nil{}:
          go(J.Inner{}, False{}, path)
    case Nil{}:
      go(J.Inner{}, False{}, "bench/data/sales_100000.csv")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    run(List.tail(&2, String, promote(args)))
