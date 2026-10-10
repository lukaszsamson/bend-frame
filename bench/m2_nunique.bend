# M2 W1b: global n_unique micro-benchmark (native, one measurement per process):
#   ~/.bend/bin/bend bench/m2_nunique.bend -o build/m2_nunique
#   ./build/m2_nunique --threads 1 [n [kind [mode]]]      n default 1048576
#     kind 0 = U32, 1 = I32, 2 = F32, 3 = Bool, 4 = U32 with null on every 8th row   (default 0)
#     mode 0 = generate the column and run n_unique (default), 1 = generate only (the baseline to
#     subtract: the generator is a Kernel.map over an iota, not the code under test)
# Every row is a distinct value (kinds 0, 1: word i * 2654435761; kind 2: to_f32(i), exact below
# 2^24), so the answer is n. Kind 4 nulls every 8th row (i mod 8 == 7): n - n/8 valid values + 1.
# Kind 3 answers 2. The result is printed after the clock so it can be
# checked against the expected value in the second field.
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/kernels.bend as K
import ./../src/column.bend as C
import ./../src/expr.bend as X
import ./../src/eval.bend as V

def promote(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> promote(t)

def word(+i: U32) -> U32:
  U32.mul(i, 2654435761)

def every8(+i: U32) -> U32:
  Bool.to_u32(U32.is_ne(U32.and(i, 7), 7))

def wordn(+i: U32) -> U32:
  Bool.pick(U32, U32.is_ne(U32.and(i, 7), 7), word(i), 0)

def col.k3(p: Nat, +n: U32, +d: Nat) -> C.Column:
  match p:
    case 0n:
      C.CBool{n, d, C.AllValid{}, K.Kernel.map(~U32, ~U32, ~(i => U32.and(i, 1)), n, d, K.Kernel.iota(n, d), 0)}
    case 1n+q:
      C.CU32{n, d, C.Mask{K.Kernel.map(~U32, ~U32, ~(i => every8(i)), n, d, K.Kernel.iota(n, d), 0)}, K.Kernel.map(~U32, ~U32, ~(i => wordn(i)), n, d, K.Kernel.iota(n, d), 0)}

def col.k2(p: Nat, +n: U32, +d: Nat) -> C.Column:
  match p:
    case 0n:
      C.CF32{n, d, C.AllValid{}, K.Kernel.map(~U32, ~F32, ~(i => U32.to_f32(i)), n, d, K.Kernel.iota(n, d), 0.0)}
    case 1n+q:
      col.k3(q, n, d)

def col.k(p: Nat, +n: U32, +d: Nat) -> C.Column:
  match p:
    case 0n:
      C.CI32{n, d, C.AllValid{}, K.Kernel.map(~U32, ~U32, ~(i => word(i)), n, d, K.Kernel.iota(n, d), 0)}
    case 1n+q:
      col.k2(q, n, d)

def col(kind: Nat, +n: U32, +d: Nat) -> C.Column:
  match kind:
    case 0n:
      C.CU32{n, d, C.AllValid{}, K.Kernel.map(~U32, ~U32, ~(i => word(i)), n, d, K.Kernel.iota(n, d), 0)}
    case 1n+p:
      col.k(p, n, d)

def frame(kind: Nat, +n: U32) -> C.Frame:
  C.Frame{n, [C.Named{"x", col(kind, n, K.Kernel.depth_for(n))}]}

def cs.k(r: C.Column & List<&2, D.Scalar>) -> String:
  (c, xs) = r
  List.show(~&2, ~D.Scalar, ~(s => D.Scalar.show(s)), xs)

def cs(c: C.Column) -> String:
  cs.k(C.Column.to_scalars(c))

def cols.show(cols: List<&1, C.Named>) -> String:
  match cols:
    case Nil{}:
      ""
    case C.Named{n, c} <> t:
      cs(c)

def height(f: C.Frame) -> String:
  match f:
    case C.Frame{h, cols}:
      U32.show(h)

def one.g(f: C.Frame) -> String:
  match f:
    case C.Frame{h, cols}:
      cols.show(cols)

def one.f(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      E.Err.show(e)
    case Done{f}:
      one.g(f)

def run.u(+mode: Nat, +kind: Nat, +n: U32) -> String:
  match mode:
    case 0n:
      one.f(V.Eval.select(frame(kind, n), [X.Alias{X.Agg{X.NUnique{}, X.Col{"x"}}, "u"}]))
    case 1n+q:
      height(frame(kind, n))

def stamp(label: String, t0: Nat) -> IO(Nat):
  do IO<Nat>:
    t1 : Nat <- IO.now()
    IO.print(label ++ ": " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms")
    IO.now()

def run(+n: U32, +kind: Nat, +mode: Nat) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    +s : String = run.u(mode, kind, n)
    t1 : Nat <- stamp("m2_nunique n=" ++ U32.show(n) ++ " kind=" ++ Nat.show(kind) ++ " mode=" ++ Nat.show(mode), t0)
    IO.print("result: " ++ s)
    return Unit{}

def arg(as: List<&2, String>, i: Nat, z: U32) -> U32:
  Maybe.default(&2, U32, U32.read(Maybe.default(&2, String, List.get(&2, String, as, i), "")), z)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    +as : List<&2, String> = promote(args)
    run(arg(as, 1n, 1048576), U32.to_nat(arg(as, 2n, 0)), U32.to_nat(arg(as, 3n, 0)))
