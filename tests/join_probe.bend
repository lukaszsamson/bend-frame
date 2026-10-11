# Join probe paths with 70000 left rows (>= 65536, so the left key column is probed in 2^4 forked
# blocks; the build side is 1000 rows, a table of 2048 slots <= 4096) and the cases W1a touched
# (one owned table, a copy only at a split): Raw and Dictionary key columns, duplicate keys on the
# build side, null keys on both sides, an empty build side, all-null keys, a duplicate-heavy build
# side. Each line prints the row count and an FNV-1a hash of DF.dump of the result (row order,
# values and validity); the expected values were computed by an independent reference
# implementation (a Python join of the same generated data, same dump text) and agree with the
# pre-W1a build.
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/join.bend as J

def mk.k(name: String, r: E.ResT(C.Column)) -> C.Named:
  match r:
    case Fail{e}:
      C.Named{E.Err.show(e), C.CU32{0, 0n, C.AllValid{}, [0 : U32*1n]}}
    case Done{c}:
      C.Named{name, c}

def mk(name: String, xs: List<&2, D.Scalar>, +t: D.DType) -> C.Named:
  mk.k(name, C.Column.from_scalars(xs, t))

# [f(0), .., f(n - 1)]
def gen.go(~f: U32 -> D.Scalar, n: Nat, +i: U32, acc: List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +j = U32.sub(i, 1)
      gen.go(~f, p, j, f(j) <> acc)

def gen(~f: U32 -> D.Scalar, +n: U32) -> List<&2, D.Scalar>:
  gen.go(~f, U32.to_nat(n), n, Nil{})

def strk(+i: U32) -> D.Scalar:
  D.SStr{"k" ++ U32.show(i)}

# left key of row i: null when i mod 7 = 3, else "k<i mod 1000>"
def kl(+i: U32) -> D.Scalar:
  Bool.pick(D.Scalar, U32.is_eq(U32.mod(i, 7), 3), D.SNull{}, strk(U32.mod(i, 1000)))

# right key of row j: null when j mod 97 = 5, else "k<j / 2>" (every key twice, k0..k499)
def kr(+j: U32) -> D.Scalar:
  Bool.pick(D.Scalar, U32.is_eq(U32.mod(j, 97), 5), D.SNull{}, strk(U32.div(j, 2)))

# right key of the duplicate-heavy build side: one key, 1000 times
def kd(+j: U32) -> D.Scalar:
  D.SStr{"k0"}

# distinct right keys k0 .. k999
def kx(+j: U32) -> D.Scalar:
  strk(j)

def kn(+j: U32) -> D.Scalar:
  D.SNull{}

def vl(+i: U32) -> D.Scalar:
  D.SU32{i}

def wr(+j: U32) -> D.Scalar:
  D.SU32{U32.add(U32.mul(j, 3), 1)}

def left(+n: U32) -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("k", gen(~(i => kl(i)), n), D.TStr{}), mk("v", gen(~(i => vl(i)), n), D.TU32{})])

def left_null(+n: U32) -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("k", gen(~(i => kn(i)), n), D.TStr{}), mk("v", gen(~(i => vl(i)), n), D.TU32{})])

def right(~f: U32 -> D.Scalar, +n: U32) -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("k", gen(~f, n), D.TStr{}), mk("w", gen(~(j => wr(j)), n), D.TU32{})])

def enc.k(+dict: Bool, r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      Done{C.Frame.encode(f, dict)}

def jn.b(+how: J.JoinHow, l: C.Frame, r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{rf}:
      J.Join.run(how, l, rf, ["k"], ["k"])

def jn(+how: J.JoinHow, l: E.ResT(C.Frame), r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match l:
    case Fail{e}:
      Fail{e}
    case Done{lf}:
      jn.b(how, lf, r)

def sum.k(r: C.Frame & U32) -> String:
  (f, +h) = r
  "h=" ++ U32.show(h) ++ " hash=" ++ U32.show(J.Str.hash(DF.dump(Done{f}), 0))

def sum(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      sum.k(C.Frame.height(f))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("-- raw x raw, duplicate and null keys")
    IO.print(sum(jn(J.Inner{}, left(70000), right(~(j => kr(j)), 1000))))
    IO.print(sum(jn(J.Left{}, left(70000), right(~(j => kr(j)), 1000))))
    IO.print("-- dictionary x dictionary")
    IO.print(sum(jn(J.Inner{}, enc.k(True{}, left(70000)), enc.k(True{}, right(~(j => kr(j)), 1000)))))
    IO.print(sum(jn(J.Left{}, enc.k(True{}, left(70000)), enc.k(True{}, right(~(j => kr(j)), 1000)))))
    IO.print("-- raw x dictionary, dictionary x raw")
    IO.print(sum(jn(J.Inner{}, left(70000), enc.k(True{}, right(~(j => kr(j)), 1000)))))
    IO.print(sum(jn(J.Inner{}, enc.k(True{}, left(70000)), right(~(j => kr(j)), 1000))))
    IO.print("-- distinct build keys k0 .. k999")
    IO.print(sum(jn(J.Inner{}, left(70000), right(~(j => kx(j)), 1000))))
    IO.print(sum(jn(J.Left{}, left(70000), right(~(j => kx(j)), 1000))))
    IO.print("-- empty build side")
    IO.print(sum(jn(J.Inner{}, left(70000), right(~(j => kx(j)), 0))))
    IO.print(sum(jn(J.Left{}, left(70000), right(~(j => kx(j)), 0))))
    IO.print(sum(jn(J.Left{}, enc.k(True{}, left(70000)), enc.k(True{}, right(~(j => kx(j)), 0)))))
    IO.print("-- all-null keys")
    IO.print(sum(jn(J.Inner{}, left_null(70000), right(~(j => kx(j)), 1000))))
    IO.print(sum(jn(J.Left{}, left_null(70000), right(~(j => kx(j)), 1000))))
    IO.print(sum(jn(J.Inner{}, left(70000), right(~(j => kn(j)), 1000))))
    IO.print(sum(jn(J.Left{}, left(70000), right(~(j => kn(j)), 1000))))
    IO.print("-- duplicate-heavy build side (one key, 1000 rows)")
    IO.print(sum(jn(J.Inner{}, left(70000), right(~(j => kd(j)), 1000))))
    IO.print(sum(jn(J.Left{}, enc.k(True{}, left(70000)), enc.k(True{}, right(~(j => kd(j)), 1000)))))
#|-- raw x raw, duplicate and null keys
#|h=59340 hash=1818593661
#|h=99340 hash=3352282401
#|-- dictionary x dictionary
#|h=59340 hash=1818593661
#|h=99340 hash=3352282401
#|-- raw x dictionary, dictionary x raw
#|h=59340 hash=1818593661
#|h=59340 hash=1818593661
#|-- distinct build keys k0 .. k999
#|h=60000 hash=1342354740
#|h=70000 hash=3924967553
#|-- empty build side
#|h=0 hash=84065074
#|h=70000 hash=2601504171
#|h=70000 hash=2601504171
#|-- all-null keys
#|h=0 hash=84065074
#|h=70000 hash=3820173877
#|h=0 hash=84065074
#|h=70000 hash=2601504171
#|-- duplicate-heavy build side (one key, 1000 rows)
#|h=60000 hash=359580296
#|h=129940 hash=220824734
