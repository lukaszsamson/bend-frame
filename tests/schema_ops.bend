# Schema: find / has / names / project / with / show / eq, Frame.schema.
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/schema.bend as S

def sch() -> List<&2, S.Field>:
  [S.Field{"id", D.TU32{}}, S.Field{"name", D.TStr{}}, S.Field{"score", D.TF32{}}]

def fd(m: Maybe<&2, D.DType>) -> String:
  match m:
    case None{}:
      "none"
    case Some{t}:
      D.DType.show(t)

def pr(r: E.Res(List<&2, S.Field>)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{s}:
      "[" ++ S.Schema.show(s) ++ "]"

def bs(b: Bool) -> String:
  D.Scalar.show(D.SBool{b})

def mk.k(name: String, r: E.ResT(C.Column)) -> C.Named:
  match r:
    case Fail{e}:
      C.Named{E.Err.show(e), C.CU32{0, 0n, C.AllValid{}, [0 : U32*1n]}}
    case Done{c}:
      C.Named{name, c}

def mk(name: String, xs: List<&2, D.Scalar>, +t: D.DType) -> C.Named:
  mk.k(name, C.Column.from_scalars(xs, t))

def fsch.k(r: C.Frame & List<&2, S.Field>) -> String:
  (f, s) = r
  S.Schema.show(s)

def fsch(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      fsch.k(S.Frame.schema(f))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(S.Schema.show(sch()))
    IO.print(fd(S.Schema.find(sch(), "score")))
    IO.print(fd(S.Schema.find(sch(), "id")))
    IO.print(fd(S.Schema.find(sch(), "nope")))
    IO.print(bs(S.Schema.has(sch(), "name")) ++ " " ++ bs(S.Schema.has(sch(), "x")))
    IO.print(List.show(~&2, ~String, ~(s => s), S.Schema.names(sch())))
    # project: request order; the first missing name; duplicates
    IO.print(pr(S.Schema.project(["score", "id"], sch())))
    IO.print(pr(S.Schema.project(["id", "x", "y"], sch())))
    IO.print(pr(S.Schema.project(["id", "id"], sch())))
    IO.print(pr(S.Schema.project(Nil{}, sch())))
    # with: replace in place or append
    IO.print(S.Schema.show(S.Schema.with(sch(), S.Field{"name", D.TBool{}})))
    IO.print(S.Schema.show(S.Schema.with(sch(), S.Field{"extra", D.TI32{}})))
    IO.print(S.Schema.show(S.Schema.with(Nil{}, S.Field{"x", D.TI32{}})))
    # eq: names, dtypes and order
    IO.print(bs(S.Schema.eq(sch(), sch())) ++ " " ++ bs(S.Schema.eq(sch(), S.Schema.with(sch(), S.Field{"id", D.TI32{}}))) ++ " " ++ bs(S.Schema.eq(sch(), Nil{})))
    # Frame.schema
    IO.print(fsch(C.Frame.from_columns([mk("k", [D.SStr{"a"}, D.SNull{}], D.TStr{}), mk("v", [D.SF32{1.0}, D.SF32{2.0}], D.TF32{}), mk("ok", [D.SNull{}, D.SBool{True{}}], D.TBool{})])))
    IO.print("[" ++ fsch(Done{C.Frame.empty()}) ++ "]")
#|id:u32, name:str, score:f32
#|f32
#|u32
#|none
#|true false
#|[id, name, score]
#|[score:f32, id:u32]
#|error: ColumnNotFound: x
#|error: DuplicateColumn: id
#|[]
#|id:u32, name:bool, score:f32
#|id:u32, name:str, score:f32, extra:i32
#|x:i32
#|true false false
#|k:str, v:f32, ok:bool
#|[]
