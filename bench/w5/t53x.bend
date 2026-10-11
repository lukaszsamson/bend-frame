# bench/w5/t53x.bend -- T5.3 probe: why the chunked runner's per-leaf walks scale 1.6x where T5.2's wrappers
# scale 4x. The same 64 leaves of 2^14 rows ({qty u32, price f32}, AllValid), forked in a balanced tree over a
# list (CH.Lst.pmap), each leaf running:
#   eval   the flat evaluator's predicate chain, as the runner's filter walk 1 does (V.Eval.full of
#          `qty > 50` on the leaf frame, V.Eval.pred, Kernel.popcount)
#   kern   the same predicate by one flat kernel (Kernel.map of qty > 50, Kernel.popcount): T5.2's shape
#   wc     the flat evaluator's with_columns expression of q2's first half: f32(qty) * price (V.Eval.full)
#   walk   the runner itself: CX.p1 (walk 1 of a filter) over a CFrame of the same rows
# Each rep builds its input before the clock and sums the leaves' answers inside it.
#   bend bench/w5/t53x.bend -o build/t53/t53x; build/t53/t53x [--threads N] <mode> <reps>
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/kernels.bend as K
import ./../../src/column.bend as C
import ./../../src/expr.bend as X
import ./../../src/eval.bend as V
import ./../../src/chunks.bend as CH
import ./../../src/cexec.bend as QC

def leaf(+i: U32) -> C.Frame:
  C.Frame{16384, [C.Named{"qty", C.CU32{16384, 14n, C.AllValid{}, K.Kernel.map(~U32, ~U32, ~(x => U32.mod(U32.mul(x, 37), 100)), 16384, 14n, K.Kernel.iota_from(16384, 14n, U32.mul(i, 16384)), 0)}}, C.Named{"price", C.CF32{16384, 14n, C.AllValid{}, K.Kernel.map(~U32, ~F32, ~(x => U32.to_f32(x)), 16384, 14n, K.Kernel.iota_from(16384, 14n, 0), 0.0)}}]}

def leaves.go(n: Nat, +i: U32, acc: List<&1, C.Frame>) -> List<&1, C.Frame>:
  match n:
    case 0n:
      acc
    case 1n+k:
      leaves.go(k, U32.inc(i), leaf(i) <> acc)

# 256 leaves: 2^22 rows (the 1 ms clock needs a few ms of work)
def leaves() -> List<&1, C.Frame>:
  leaves.go(256n, 0, Nil{})

# the same rows as one chunked frame (built before the clock)
def big() -> C.Frame:
  C.Frame{4194304, [C.Named{"qty", C.CU32{4194304, 22n, C.AllValid{}, K.Kernel.map(~U32, ~U32, ~(x => U32.mod(U32.mul(x, 37), 100)), 4194304, 22n, K.Kernel.iota_from(4194304, 22n, 0), 0)}}, C.Named{"price", C.CF32{4194304, 22n, C.AllValid{}, K.Kernel.map(~U32, ~F32, ~(x => U32.to_f32(U32.and(x, 16383))), 4194304, 22n, K.Kernel.iota_from(4194304, 22n, 0), 0.0)}}]}

type In is Type:
  InL{fs: List<&1, C.Frame>}
  InC{f: CH.CFrame, sk: CH.Skel}

def prep.c(r: CH.CFrame & CH.Skel) -> In:
  (f, sk) = r
  InC{f, sk}

def prep(+m: U32) -> In:
  match m:
    case 3:
      prep.c(QC.CX.skel(CH.CFrame.of_frame(14n, big())))
    case _:
      InL{leaves()}

def pred() -> X.Expr:
  DF.gt(DF.col("qty"), DF.lit_u32(50))

def wce() -> X.Expr:
  DF.mul(DF.cast_f32(DF.col("qty")), DF.col("price"))

def cnt.k(r: Array<U32> & U32) -> U32:
  (m, +k) = r
  k

def cnt.p(r: Array<U32> & U32) -> U32:
  (m, +n) = r
  cnt.k(K.Kernel.popcount(n, m))

def cnt.c(r: C.Frame & E.ResT(C.Column)) -> U32:
  (f, rc) = r
  match rc:
    case Fail{e}:
      0
    case Done{c}:
      cnt.p(V.Eval.pred(c))

def len.k(r: C.Column & U32) -> U32:
  (c, +n) = r
  n

def len.c(r: C.Frame & E.ResT(C.Column)) -> U32:
  (f, rc) = r
  match rc:
    case Fail{e}:
      0
    case Done{c}:
      len.k(C.Column.len(c))

def leaf.eval(+e: X.Expr, f: C.Frame) -> U32:
  cnt.c(V.Eval.full(f, e))

def leaf.wc(+e: X.Expr, f: C.Frame) -> U32:
  len.c(V.Eval.full(f, e))

def leaf.kern.k(r: List<&1, C.Named> & U32) -> U32:
  (cols, k) = r
  k

def leaf.kern(+u: U32, f: C.Frame) -> U32:
  match f:
    case C.Frame{h, cols}:
      match cols:
        case C.Named{n, c} <> rest:
          match c:
            case C.CU32{+len, d, v, x}:
              cnt.k(K.Kernel.popcount(len, K.Kernel.map(~U32, ~U32, ~(q => Bool.to_u32(U32.is_lt(50, q))), len, 14n, x, 0)))
            case _:
              0
        case _:
          0

def sum(xs: List<&1, U32>, +acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case x <> t:
      sum(t, U32.add(acc, x))

def walk.w(w: QC.W1) -> U32:
  match w:
    case QC.W1{f, m, ok}:
      Bool.to_u32(ok)

def walk(f: CH.CFrame, sk: CH.Skel) -> U32:
  walk.w(QC.CX.p1(pred(), sk, QC.CX.cut(f), (Nil{}, Nil{})))

def run.l(+m: U32, fs: List<&1, C.Frame>) -> U32:
  match m:
    case 0:
      sum(CH.Lst.pmap(~C.Frame, ~U32, ~X.Expr, ~(e => f => leaf.eval(e, f)), pred(), fs), 0)
    case 1:
      sum(CH.Lst.pmap(~C.Frame, ~U32, ~U32, ~(u => f => leaf.kern(u, f)), 0, fs), 0)
    case 2:
      sum(CH.Lst.pmap(~C.Frame, ~U32, ~X.Expr, ~(e => f => leaf.wc(e, f)), wce(), fs), 0)
    case _:
      0

def run.mode(+m: U32, i: In) -> U32:
  match i:
    case InC{f, sk}:
      walk(f, sk)
    case InL{fs}:
      run.l(m, fs)

def loop(left: Nat, +m: U32, +acc: String) -> IO(Unit):
  match left:
    case 0n:
      IO.print(acc ++ "]")
    case 1n+k:
      do IO<Unit>:
        fs : In <- IO.pure(In, prep(m))
        +t0 : Nat <- IO.now()
        +r : U32 <- IO.pure(U32, run.mode(m, fs))
        +t1 : Nat <- IO.now()
        loop(k, m, acc ++ Nat.show(Nat.sub(t1, t0)) ++ "/" ++ U32.show(r) ++ ",")

def go(args: List<String>) -> IO(Unit):
  match args:
    case exe <> +mode <> reps <> Nil{}:
      loop(Maybe.default(&2, Nat, Nat.read(reps), 10n), U32.from_nat(Maybe.default(&2, Nat, Nat.read(mode), 0n)), "[")
    case _:
      IO.print("usage: t53x MODE REPS")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
