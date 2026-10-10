import Base
import ./../../frame.bend as DF
import ./../../src/column.bend as C
import ./../../src/kernels.bend as K

def input(+n: U32) -> DF.Frame():
  C.Frame{n, [C.Named{"x", C.CU32{n, K.Kernel.depth_for(n), C.AllValid{}, K.Kernel.iota(n, K.Kernel.depth_for(n))}}]}

def op(mode: String, f: DF.Frame()) -> DF.ResT(DF.Frame()):
  match mode:
    case "select":
      DF.select(f, [DF.col("x")])
    case "headselect":
      DF.select(f, [DF.col("x")])
    case "move":
      C.Frame.select_names(f, ["x"])
    case "nunique":
      DF.select(f, [DF.n_unique(DF.col("x"))])
    case _:
      DF.then(DF.unique(f, ["x"]), g => DF.select(g, [DF.alias(DF.len(), "x")]))

def loop(k: Nat, +mode: String, r: DF.ResT(DF.Frame())) -> DF.ResT(DF.Frame()):
  match k r:
    case 0n r2:
      r2
    case 1n+p Done{f}:
      loop(p, mode, op(mode, f))
    case _ Fail{e}:
      Fail{e}

def summary(r: DF.ResT(DF.Frame())) -> String:
  DF.dump(DF.then(r, f => DF.select(f, [DF.alias(DF.sum(DF.col("x")), "sum"), DF.alias(DF.len(), "rows")])))

def timed(+mode: String, +reps: Nat, f: DF.Frame()) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    r : DF.ResT(DF.Frame()) <- IO.pure(DF.ResT(DF.Frame()), loop(reps, mode, Done{f}))
    t1 : Nat <- IO.now()
    IO.print(mode ++ " ms=" ++ Nat.show(Nat.sub(t1, t0)))
    IO.print(summary(r))

def prepare(mode: String, f: DF.Frame()) -> DF.Frame():
  match mode:
    case "headselect":
      C.Frame.head(f, 1)
    case _:
      f

def go(args: List<String>) -> IO(Unit):
  match args:
    case exe <> +mode <> Nil{}:
      timed(mode, Bool.pick(Nat, Bool.or(String.eq(mode, "select"), Bool.or(String.eq(mode, "move"), String.eq(mode, "headselect"))), 64n, 1n), prepare(mode, input(1048576)))
    case _:
      IO.print("usage: ops select|headselect|move|nunique|unique")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(args)
