# T5.1 (DESIGN.md 16.1 D1): chunked frames (src/chunks.bend CFrame) against the flat v0.1 frame. Every
# dtype with nulls, F32 NaN / -0.0 / inf (compared by bits through DF.dump), Raw and Dictionary strings
# (one Dict per column; the storage kind is printed), validity masks (AllValid and Mask sides), the empty
# frame, a zero-column frame. At grains 2^1 and 2^2 every frame here is many leaves (ragged after head /
# slice, empty leaves after drops), so each line exercises the builder, flatten, the cut and the
# rechunk across all trees of a frame: `same` means DF.dump of the round trip equals DF.dump of the v0.1
# answer, `wf` that CFrame.check (WFCFrame: one shape per frame, heights, unique names) holds.
import Base
import ./../frame.bend as DF
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/strs.bend as ST
import ./../src/kernels.bend as K
import ./../src/chunks.bend as CH

def nan() -> F32:
  F32.div(0.0, 0.0)

def inf() -> F32:
  F32.div(1.0, 0.0)

def sb(+i: U32) -> D.Scalar:
  Bool.pick(D.Scalar, U32.is_eq(U32.mod(i, 3), 2), D.SNull{}, D.SBool{U32.is_eq(U32.mod(i, 2), 0)})

def su(+i: U32) -> D.Scalar:
  Bool.pick(D.Scalar, U32.is_eq(U32.mod(i, 4), 3), D.SNull{}, D.SU32{U32.mul(i, 7)})

def si(+i: U32) -> D.Scalar:
  D.SI32{D.I32.neg(D.I32{i})}

def sf.v(+i: U32) -> F32:
  Bool.pick(F32, U32.is_eq(i, 2), nan(), Bool.pick(F32, U32.is_eq(i, 3), F32.neg(0.0), Bool.pick(F32, U32.is_eq(i, 5), inf(), F32.div(U32.to_f32(i), 4.0))))

def sf(+i: U32) -> D.Scalar:
  Bool.pick(D.Scalar, U32.is_eq(U32.mod(i, 5), 4), D.SNull{}, D.SF32{sf.v(i)})

def ss(+i: U32) -> D.Scalar:
  Bool.pick(D.Scalar, U32.is_eq(U32.mod(i, 6), 1), D.SNull{}, Bool.pick(D.Scalar, U32.is_eq(i, 7), D.SStr{""}, D.SStr{"s" ++ U32.show(U32.mod(U32.mul(i, 5), 7))}))

# another string order (the second frame of a concat: its dictionary's codes differ from the first's)
def ss2(+i: U32) -> D.Scalar:
  Bool.pick(D.Scalar, U32.is_eq(U32.mod(i, 4), 2), D.SNull{}, D.SStr{"s" ++ U32.show(U32.mod(U32.add(U32.mul(i, 3), 2), 9))})

# no nulls: an AllValid column
def sk(+i: U32) -> D.Scalar:
  D.SU32{U32.add(i, 1000)}

def gen.go(f: Nat, +i: U32, +k: U32, acc: List<&2, D.Scalar>) -> List<&2, D.Scalar>:
  match f:
    case 0n:
      acc
    case 1n+p:
      +j = U32.sub(i, 1)
      gen.go(p, j, k, Bool.pick(D.Scalar, U32.is_eq(k, 0), sb(j), Bool.pick(D.Scalar, U32.is_eq(k, 1), su(j), Bool.pick(D.Scalar, U32.is_eq(k, 2), si(j), Bool.pick(D.Scalar, U32.is_eq(k, 3), sf(j), Bool.pick(D.Scalar, U32.is_eq(k, 4), ss(j), Bool.pick(D.Scalar, U32.is_eq(k, 6), ss2(j), sk(j))))))) <> acc)

# rows 0 .. n - 1 of generator k, in order
def gen(+n: U32, +k: U32) -> List<&2, D.Scalar>:
  gen.go(U32.to_nat(n), n, k, Nil{})

def mk.k(name: String, r: E.ResT(C.Column)) -> C.Named:
  match r:
    case Fail{e}:
      C.Named{E.Err.show(e), C.CU32{0, 0n, C.AllValid{}, [0 : U32*1n]}}
    case Done{c}:
      C.Named{name, c}

def mk(name: String, +n: U32, +k: U32, +t: D.DType) -> C.Named:
  mk.k(name, C.Column.from_scalars(gen(n, k), t))

def wide.r(r: E.ResT(C.Frame)) -> C.Frame:
  match r:
    case Fail{e}:
      C.Frame.empty()
    case Done{f}:
      f

def wide.raw(+n: U32, +sg: U32) -> C.Frame:
  wide.r(C.Frame.from_columns([mk("b", n, 0, D.TBool{}), mk("u", n, 1, D.TU32{}), mk("i", n, 2, D.TI32{}), mk("f", n, 3, D.TF32{}), mk("s", n, sg, D.TStr{}), mk("k", n, 5, D.TU32{})]))

def wide2(+n: U32, dict: Bool) -> C.Frame:
  match dict:
    case True{}:
      DF.encode_strings(wide.raw(n, 6), True{})
    case False{}:
      wide.raw(n, 6)

# the same frame, its string column Raw or Dictionary
def wide(+n: U32, dict: Bool) -> C.Frame:
  match dict:
    case True{}:
      DF.encode_strings(wide.raw(n, 4), True{})
    case False{}:
      wide.raw(n, 4)

def ok_show(b: Bool) -> String:
  match b:
    case True{}:
      "wf"
    case False{}:
      "NOT-WF"

def cmp_show(eq: Bool, +a: String, +b: String) -> String:
  match eq:
    case True{}:
      "same"
    case False{}:
      "DIFF\n" ++ a ++ "\n-- vs v0.1 --\n" ++ b

def cmp(+a: String, +b: String) -> String:
  cmp_show(String.eq(a, b), a, b)

def kind.s(r: ST.Strs & Bool) -> String:
  (s, b) = r
  match b:
    case True{}:
      "dict"
    case False{}:
      "raw"

# the storage of the column "s": dict or raw (absent: -)
def kind.c(c: C.Column) -> String:
  match c:
    case C.CStr{len, depth, valid, data}:
      kind.s(ST.Strs.is_dict(data))
    case _:
      "-"

def kind.p(hit: Bool, c: C.Column, +k: String) -> String:
  match hit:
    case True{}:
      kind.c(c)
    case False{}:
      k

def kind.l(cols: List<&1, C.Named>) -> String:
  match cols:
    case Nil{}:
      "-"
    case C.Named{n, c} <> rest:
      kind.p(String.eq(n, "s"), c, kind.l(rest))

def kind(f: C.Frame) -> String:
  match f:
    case C.Frame{h, cols}:
      kind.l(cols)

def kind.r(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "-"
    case Done{f}:
      kind(f)

# the WFCFrame check, then back to a flat frame
def back.k(r: CH.CFrame & Bool) -> String & C.Frame:
  (f, ok) = r
  (ok_show(ok), CH.CFrame.to_frame(f))

def back(f: CH.CFrame) -> String & C.Frame:
  back.k(CH.CFrame.check(f))

def line.c(+label: String, +flat: String, +ok: String, r: C.Frame & C.Frame) -> String:
  (f1, f2) = r
  label ++ " " ++ ok ++ " " ++ kind(f1) ++ " " ++ cmp(DF.dump_frame(f2), flat)

def line.k(+label: String, +flat: String, r: String & C.Frame) -> String:
  (+ok, f) = r
  line.c(label, flat, ok, C.Frame.clone(f))

def line(+label: String, +flat: String, f: CH.CFrame) -> String:
  line.k(label, flat, back(f))

def rline.k(+label: String, +flat: String, r: E.ResT(CH.CFrame)) -> String:
  match r:
    case Fail{e}:
      label ++ " " ++ cmp(DF.dump(Fail{e}), flat)
    case Done{f}:
      line(label, flat, f)

def of(+g: Nat, f: C.Frame) -> CH.CFrame:
  CH.CFrame.of_frame(g, f)

def rt(+g: Nat, +n: U32, +dict: Bool) -> String:
  line("rt g=" ++ Nat.show(g) ++ " n=" ++ U32.show(n), DF.dump_frame(wide(n, dict)), of(g, wide(n, dict)))

def cat2(+g: Nat, +na: U32, +da: Bool, +nb: U32, +db: Bool) -> String:
  rline.k("concat " ++ U32.show(na) ++ "+" ++ U32.show(nb), DF.dump(DF.concat_vertical([wide(na, da), wide2(nb, db)])), CH.CFrame.concat(of(g, wide(na, da)), of(g, wide2(nb, db)))) ++ " v0.1:" ++ kind.r(DF.concat_vertical([wide(na, da), wide2(nb, db)]))

# two columns of different shapes (13 rows at grain 2 vs one leaf of 13): not WFCFrame
def misaligned() -> CH.CFrame:
  CH.CFrame{13, [CH.CNamed{"a", CH.CU32{13, CH.CAllValid{}, CH.CW.of(13, 4n, 2n, K.Kernel.iota(13, 4n))}}, CH.CNamed{"b", CH.CU32{13, CH.CAllValid{}, CH.CW.of(13, 4n, 4n, K.Kernel.iota(13, 4n))}}]}

def dupnames() -> CH.CFrame:
  CH.CFrame{3, [CH.CNamed{"a", CH.CU32{3, CH.CAllValid{}, CH.CW.of(3, 2n, 2n, K.Kernel.iota(3, 2n))}}, CH.CNamed{"a", CH.CU32{3, CH.CAllValid{}, CH.CW.of(3, 2n, 2n, K.Kernel.iota(3, 2n))}}]}

def chk.k(r: CH.CFrame & Bool) -> String:
  (f, ok) = r
  ok_show(ok)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(rt(2n, 0, False{}))
    IO.print(rt(2n, 1, False{}))
    IO.print(rt(2n, 4, False{}))
    IO.print(rt(2n, 5, False{}))
    IO.print(rt(2n, 11, False{}))
    IO.print(rt(1n, 11, True{}))
    IO.print(rt(2n, 33, True{}))
    IO.print(rt(1n, 33, False{}))
    IO.print(line("head 6", DF.dump(DF.head(wide(11, False{}), 6)), CH.CFrame.head(of(2n, wide(11, False{})), 6)))
    IO.print(line("head 0", DF.dump(DF.head(wide(11, True{}), 0)), CH.CFrame.head(of(2n, wide(11, True{})), 0)))
    IO.print(line("head 40", DF.dump(DF.head(wide(11, True{}), 40)), CH.CFrame.head(of(2n, wide(11, True{})), 40)))
    IO.print(line("slice 3 5", DF.dump(DF.slice(wide(11, False{}), 3, 5)), CH.CFrame.slice(of(2n, wide(11, False{})), 3, 5)))
    IO.print(line("slice 9 10", DF.dump(DF.slice(wide(11, True{}), 9, 10)), CH.CFrame.slice(of(1n, wide(11, True{})), 9, 10)))
    IO.print(line("slice 20 3", DF.dump(DF.slice(wide(11, False{}), 20, 3)), CH.CFrame.slice(of(2n, wide(11, False{})), 20, 3)))
    IO.print(line("slice 1 31 rechunk", DF.dump(DF.slice(wide(33, True{}), 1, 31)), CH.CFrame.rechunk(2n, CH.CFrame.slice(of(1n, wide(33, True{})), 1, 31))))
    IO.print(line("slice 5 3 rebalance", DF.dump(DF.slice(wide(33, False{}), 5, 3)), CH.CFrame.rebalance(2n, CH.CFrame.slice(of(1n, wide(33, False{})), 5, 3))))
    IO.print(cat2(2n, 5, False{}, 7, False{}))
    IO.print(cat2(2n, 5, True{}, 7, True{}))
    IO.print(cat2(1n, 9, True{}, 2, False{}))
    IO.print(cat2(1n, 2, False{}, 9, True{}))
    IO.print(cat2(2n, 0, True{}, 6, True{}))
    IO.print(cat2(2n, 2, False{}, 0, False{}))
    IO.print(line("zero-col", DF.dump_frame(C.Frame{3, Nil{}}), CH.CFrame.of_frame(2n, C.Frame{3, Nil{}})))
    IO.print(rline.k("zero-col concat", DF.dump_frame(C.Frame{7, Nil{}}), CH.CFrame.concat(CH.CFrame.of_frame(2n, C.Frame{3, Nil{}}), CH.CFrame.of_frame(2n, C.Frame{4, Nil{}}))))
    IO.print(line("empty", DF.dump_frame(C.Frame.empty()), CH.CFrame.of_frame(2n, C.Frame.empty())))
    IO.print("misaligned " ++ chk.k(CH.CFrame.check(misaligned())))
    IO.print("dupnames " ++ chk.k(CH.CFrame.check(dupnames())))
#|rt g=2 n=0 wf raw same
#|rt g=2 n=1 wf raw same
#|rt g=2 n=4 wf raw same
#|rt g=2 n=5 wf raw same
#|rt g=2 n=11 wf raw same
#|rt g=1 n=11 wf dict same
#|rt g=2 n=33 wf dict same
#|rt g=1 n=33 wf raw same
#|head 6 wf raw same
#|head 0 wf dict same
#|head 40 wf dict same
#|slice 3 5 wf raw same
#|slice 9 10 wf dict same
#|slice 20 3 wf raw same
#|slice 1 31 rechunk wf dict same
#|slice 5 3 rebalance wf raw same
#|concat 5+7 wf raw same v0.1:raw
#|concat 5+7 wf dict same v0.1:dict
#|concat 9+2 wf raw same v0.1:raw
#|concat 2+9 wf raw same v0.1:raw
#|concat 0+6 wf dict same v0.1:dict
#|concat 2+0 wf raw same v0.1:raw
#|zero-col wf - same
#|zero-col concat wf - same
#|empty wf - same
#|misaligned NOT-WF
#|dupnames NOT-WF
