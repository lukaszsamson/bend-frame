# Join cases: multi-key with different right key names (dropped), key order,
# i32 keys with nulls on both sides and many-to-many matches, bool and f32
# keys (0.0 == -0.0, NaN == NaN), empty left/right sides, null-slot invariant
# of a left join's right columns, Join.schema, and the early errors. Row
# expectations checked against Polars 2.0 join(.., maintain_order="left_right");
# Polars casts u32 vs i32 keys to a supertype, bend-frame is strict.
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/schema.bend as S
import ./../src/fmt.bend as F
import ./../src/join.bend as J

def mk.k(name: String, r: E.ResT(C.Column)) -> C.Named:
  match r:
    case Fail{e}:
      C.Named{E.Err.show(e), C.CU32{0, 0n, C.AllValid{}, [0 : U32*1n]}}
    case Done{c}:
      C.Named{name, c}

def mk(name: String, xs: List<&2, D.Scalar>, +t: D.DType) -> C.Named:
  mk.k(name, C.Column.from_scalars(xs, t))

def scal(xs: List<&2, D.Scalar>) -> String:
  List.show(~&2, ~D.Scalar, ~(s => D.Scalar.show(s)), xs)

def cs.b(t: D.DType, r: C.Column & List<&2, D.Scalar>) -> String:
  (c, xs) = r
  D.DType.show(t) ++ "=" ++ scal(xs)

def cs.a(r: C.Column & D.DType) -> String:
  (c, t) = r
  cs.b(t, C.Column.to_scalars(c))

def cs(c: C.Column) -> String:
  cs.a(C.Column.dtype(c))

def ncols(cols: List<&1, C.Named>) -> List<&2, String>:
  match cols:
    case Nil{}:
      Nil{}
    case C.Named{n, c} <> t:
      (n ++ ":" ++ cs(c)) <> ncols(t)

def fs(f: C.Frame) -> String:
  match f:
    case C.Frame{h, cols}:
      "h=" ++ U32.show(h) ++ " " ++ String.join(ncols(cols), " | ")

def fr(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      fs(f)

def snd(r: C.Frame & String) -> String:
  (f, s) = r
  s

def table(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      snd(F.Fmt.show(f))

def jn.b(+how: J.JoinHow, +lo: List<&2, String>, +ro: List<&2, String>, l: C.Frame, r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{rf}:
      J.Join.run(how, l, rf, lo, ro)

def jn(+how: J.JoinHow, +lo: List<&2, String>, +ro: List<&2, String>, l: E.ResT(C.Frame), r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match l:
    case Fail{e}:
      Fail{e}
    case Done{lf}:
      jn.b(how, lo, ro, lf, r)

def u(x: U32) -> D.Scalar:
  D.SU32{x}

def i(x: U32) -> D.Scalar:
  D.SI32{D.I32{x}}

def ni(x: U32) -> D.Scalar:
  D.SI32{D.I32.neg(D.I32{x})}

def s(x: String) -> D.Scalar:
  D.SStr{x}

def b(x: Bool) -> D.Scalar:
  D.SBool{x}

def f(x: F32) -> D.Scalar:
  D.SF32{x}

def nul() -> D.Scalar:
  D.SNull{}

def l2() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("a", [u(1), u(1), u(2), u(2), nul(), u(3)], D.TU32{}), mk("b", [s("x"), s("y"), s("x"), nul(), s("x"), s("z")], D.TStr{}), mk("v", [ni(1), ni(2), ni(3), ni(4), ni(5), ni(6)], D.TI32{})])

def r2() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("a2", [u(1), u(2), u(1), u(1), u(2), u(3)], D.TU32{}), mk("b2", [s("x"), s("x"), s("x"), s("y"), nul(), s("q")], D.TStr{}), mk("w", [b(True{}), b(False{}), b(True{}), b(False{}), b(True{}), b(False{})], D.TBool{})])

def l3() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("k", [ni(1), nul(), i(2), ni(1), i(7)], D.TI32{}), mk("s", [s("p"), s("q"), s("r"), s("s"), s("t")], D.TStr{})])

def r3() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("k", [i(2), ni(1), nul(), ni(1), i(2)], D.TI32{}), mk("t", [s("A"), s("B"), s("C"), s("D"), s("E")], D.TStr{})])

def l4() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("f", [b(True{}), b(False{}), nul(), b(True{})], D.TBool{}), mk("n", [u(1), u(2), u(3), u(4)], D.TU32{})])

def r4() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("f", [b(False{}), b(True{})], D.TBool{}), mk("m", [f(10.0), f(20.0)], D.TF32{})])

def l5() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("z", [f(0.0), f(F32.neg(0.0)), f(F32.div(0.0, 0.0)), f(1.5), f(2.0)], D.TF32{}), mk("i", [u(0), u(1), u(2), u(3), u(4)], D.TU32{})])

def r5() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("z", [f(F32.neg(0.0)), f(F32.div(0.0, 0.0)), f(1.5)], D.TF32{}), mk("j", [u(0), u(1), u(2)], D.TU32{})])

def lk() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("k", [s("a"), s("b"), s("c"), nul(), s("b")], D.TStr{}), mk("v", [u(1), u(2), u(3), u(4), u(5)], D.TU32{}), mk("x", [u(10), u(20), u(30), u(40), u(50)], D.TU32{})])

def rk() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("k", [s("b"), s("a"), s("b"), nul(), s("d")], D.TStr{}), mk("x", [u(100), u(200), u(300), u(400), u(500)], D.TU32{}), mk("w", [f(1.5), f(2.5), f(3.5), f(4.5), f(5.5)], D.TF32{})])

def le() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("k", [], D.TStr{}), mk("v", [], D.TU32{})])

def re() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("k", [], D.TStr{}), mk("x", [], D.TU32{}), mk("w", [], D.TF32{})])

def l6() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("k", [s("a")], D.TStr{}), mk("x", [u(1)], D.TU32{}), mk("x_right", [u(2)], D.TU32{})])

def l7() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("k", [s("b"), s("a"), s("a")], D.TStr{}), mk("v", [u(1), u(2), u(3)], D.TU32{})])

def r7() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("k", [s("a"), s("b"), s("c")], D.TStr{}), mk("w", [u(10), u(20), u(30)], D.TU32{})])

def ru() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("k", [u(1)], D.TU32{})])

# raw data slots of the named column (null rows must hold the default)
def slots.go(k: Nat, +i: U32, acc: List<&2, D.Scalar>, r: C.Column & D.Scalar) -> List<&2, D.Scalar>:
  match k:
    case 0n:
      List.reverse(&2, D.Scalar, acc)
    case 1n+p:
      (c, x) = r
      +j = U32.inc(i)
      slots.go(p, j, x <> acc, C.Column.data_cell(c, j))

def slots.m(m: Maybe<&1, C.Column>, +n: U32) -> String:
  match m:
    case None{}:
      "missing"
    case Some{c}:
      scal(slots.go(U32.to_nat(n), 0, Nil{}, C.Column.data_cell(c, 0)))

def slots.t(+h: U32, r: C.Frame & Maybe<&1, C.Column>) -> String:
  (f, m) = r
  slots.m(m, h)

def slots(+name: String, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{fr}:
      match fr:
        case C.Frame{+h, cols}:
          slots.t(h, C.Frame.take(C.Frame{h, cols}, name))

def sch.b(r: E.Res(List<&2, S.Field>)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{fs}:
      S.Schema.show(fs)

def sch.a(+lo: List<&2, String>, +ro: List<&2, String>, rl: C.Frame & List<&2, S.Field>, rr: C.Frame & List<&2, S.Field>) -> String:
  (a, ls) = rl
  (b, rs) = rr
  sch.b(J.Join.schema(ls, rs, lo, ro))

def sch(+lo: List<&2, String>, +ro: List<&2, String>, l: E.ResT(C.Frame), r: E.ResT(C.Frame)) -> String:
  match l:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{lf}:
      match r:
        case Fail{e}:
          "error: " ++ E.Err.show(e)
        case Done{rf}:
          sch.a(lo, ro, S.Frame.schema(lf), S.Frame.schema(rf))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("-- multi-key, right keys renamed (dropped)")
    IO.print(fr(jn(J.Inner{}, ["a", "b"], ["a2", "b2"], l2(), r2())))
    IO.print(fr(jn(J.Left{}, ["a", "b"], ["a2", "b2"], l2(), r2())))
    IO.print(fr(jn(J.Left{}, ["b", "a"], ["b2", "a2"], l2(), r2())))
    IO.print("-- i32 keys, nulls on both sides, many-to-many")
    IO.print(fr(jn(J.Inner{}, ["k"], ["k"], l3(), r3())))
    IO.print(fr(jn(J.Left{}, ["k"], ["k"], l3(), r3())))
    IO.print("-- bool and f32 keys")
    IO.print(fr(jn(J.Inner{}, ["f"], ["f"], l4(), r4())))
    IO.print(fr(jn(J.Left{}, ["f"], ["f"], l4(), r4())))
    IO.print(fr(jn(J.Left{}, ["z"], ["z"], l5(), r5())))
    IO.print("-- one match per left row (perm_l = identity)")
    IO.print(fr(jn(J.Inner{}, ["k"], ["k"], l7(), r7())))
    IO.print(fr(jn(J.Left{}, ["k"], ["k"], l7(), r7())))
    IO.print("-- empty sides")
    IO.print(fr(jn(J.Inner{}, ["k"], ["k"], le(), rk())))
    IO.print(fr(jn(J.Left{}, ["k"], ["k"], le(), rk())))
    IO.print(fr(jn(J.Inner{}, ["k"], ["k"], lk(), re())))
    IO.print(fr(jn(J.Left{}, ["k"], ["k"], lk(), re())))
    IO.print("-- null slots hold the default")
    IO.print(slots("x_right", jn(J.Left{}, ["k"], ["k"], lk(), rk())))
    IO.print(slots("w", jn(J.Left{}, ["k"], ["k"], lk(), re())))
    IO.print("-- schema")
    IO.print(sch(["k"], ["k"], lk(), rk()))
    IO.print(sch(["a", "b"], ["a2", "b2"], l2(), r2()))
    IO.print("-- errors")
    IO.print(fr(jn(J.Inner{}, ["k"], ["k"], l3(), ru())))
    IO.print(fr(jn(J.Inner{}, ["nope"], ["k"], lk(), rk())))
    IO.print(fr(jn(J.Inner{}, ["k"], ["nope"], lk(), rk())))
    IO.print(fr(jn(J.Inner{}, ["k"], ["k", "x"], lk(), rk())))
    IO.print(fr(jn(J.Inner{}, [], [], lk(), rk())))
    IO.print(fr(jn(J.Inner{}, ["k"], ["k"], l6(), rk())))

#|-- multi-key, right keys renamed (dropped)
#|h=4 a:u32=[1, 1, 1, 2] | b:str=[x, x, y, x] | v:i32=[-1, -1, -2, -3] | w:bool=[true, true, false, false]
#|h=7 a:u32=[1, 1, 1, 2, 2, null, 3] | b:str=[x, x, y, x, null, x, z] | v:i32=[-1, -1, -2, -3, -4, -5, -6] | w:bool=[true, true, false, false, null, null, null]
#|h=7 a:u32=[1, 1, 1, 2, 2, null, 3] | b:str=[x, x, y, x, null, x, z] | v:i32=[-1, -1, -2, -3, -4, -5, -6] | w:bool=[true, true, false, false, null, null, null]
#|-- i32 keys, nulls on both sides, many-to-many
#|h=6 k:i32=[-1, -1, 2, 2, -1, -1] | s:str=[p, p, r, r, s, s] | t:str=[B, D, A, E, B, D]
#|h=8 k:i32=[-1, -1, null, 2, 2, -1, -1, 7] | s:str=[p, p, q, r, r, s, s, t] | t:str=[B, D, null, A, E, B, D, null]
#|-- bool and f32 keys
#|h=3 f:bool=[true, false, true] | n:u32=[1, 2, 4] | m:f32=[20, 10, 20]
#|h=4 f:bool=[true, false, null, true] | n:u32=[1, 2, 3, 4] | m:f32=[20, 10, null, 20]
#|h=5 z:f32=[0, -0, nan, 1.5, 2] | i:u32=[0, 1, 2, 3, 4] | j:u32=[0, 0, 1, 2, null]
#|-- one match per left row (perm_l = identity)
#|h=3 k:str=[b, a, a] | v:u32=[1, 2, 3] | w:u32=[20, 10, 10]
#|h=3 k:str=[b, a, a] | v:u32=[1, 2, 3] | w:u32=[20, 10, 10]
#|-- empty sides
#|h=0 k:str=[] | v:u32=[] | x:u32=[] | w:f32=[]
#|h=0 k:str=[] | v:u32=[] | x:u32=[] | w:f32=[]
#|h=0 k:str=[] | v:u32=[] | x:u32=[] | x_right:u32=[] | w:f32=[]
#|h=5 k:str=[a, b, c, null, b] | v:u32=[1, 2, 3, 4, 5] | x:u32=[10, 20, 30, 40, 50] | x_right:u32=[null, null, null, null, null] | w:f32=[null, null, null, null, null]
#|-- null slots hold the default
#|[200, 100, 300, 0, 0, 100, 300]
#|[0, 0, 0, 0, 0]
#|-- schema
#|k:str, v:u32, x:u32, x_right:u32, w:f32
#|a:u32, b:str, v:i32, w:bool
#|-- errors
#|error: TypeMismatch in join: expected i32, got u32
#|error: ColumnNotFound: nope
#|error: ColumnNotFound: nope
#|error: InvalidOperation: join: left_on and right_on must have the same length
#|error: InvalidOperation: join: no key columns
#|error: DuplicateColumn: x_right
