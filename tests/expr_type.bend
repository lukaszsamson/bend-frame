# Expr.type: every row of the DESIGN.md 4.6 typing table, its mismatches, the
# cast table; Expr.name / refs / is_agg / split_agg / show.
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/schema.bend as S
import ./../src/expr.bend as X

def sch() -> List<&2, S.Field>:
  [S.Field{"a", D.TU32{}}, S.Field{"i", D.TI32{}}, S.Field{"f", D.TF32{}}, S.Field{"b", D.TBool{}}, S.Field{"s", D.TStr{}}]

def ty.r(r: E.Res(D.DType)) -> String:
  match r:
    case Fail{e}:
      E.Err.show(e)
    case Done{t}:
      D.DType.show(t)

# `<expr> : <dtype or error>`
def ty(+e: X.Expr) -> String:
  X.Expr.show(e) ++ " : " ++ ty.r(X.Expr.type(e, sch()))

def col(n: String) -> X.Expr:
  X.Col{n}

def lu(v: U32) -> X.Expr:
  X.Lit{D.SU32{v}}

def un(op: X.UnOp, e: X.Expr) -> X.Expr:
  X.Un{op, e}

def bin(op: X.BinOp, a: X.Expr, b: X.Expr) -> X.Expr:
  X.Bin{op, a, b}

def agg(op: X.AggOp, e: X.Expr) -> X.Expr:
  X.Agg{op, e}

def cast(e: X.Expr, t: D.DType) -> X.Expr:
  X.Cast{e, t}

def names(+e: X.Expr) -> String:
  X.Expr.show(e) ++ " name=" ++ X.Expr.name(e) ++ " refs=" ++ List.show(~&2, ~String, ~(s => s), X.Expr.refs(e)) ++ " is_agg=" ++ D.Scalar.show(D.SBool{X.Expr.is_agg(e)})

def split.r(m: Maybe<&2, X.AggSplit>) -> String:
  match m:
    case None{}:
      "none"
    case Some{X.AggSplit{op, e}}:
      X.AggOp.name(op) ++ " of " ++ X.Expr.show(e)

def main() -> IO(Unit):
  do IO<Unit>:
    # Col, Lit, Alias
    IO.print(ty(col("a")))
    IO.print(ty(col("zz")))
    IO.print(ty(lu(1)))
    IO.print(ty(X.Lit{D.SI32{D.I32.neg(D.I32{3})}}))
    IO.print(ty(X.Lit{D.SF32{1.5}}))
    IO.print(ty(X.Lit{D.SBool{True{}}}))
    IO.print(ty(X.Lit{D.SStr{"x"}}))
    IO.print(ty(X.Lit{D.SNull{}}))
    IO.print(ty(X.Alias{col("f"), "g"}))
    # Cast: the table, a refused pair, the typed null literal
    IO.print(ty(cast(col("a"), D.TF32{})))
    IO.print(ty(cast(col("a"), D.TI32{})))
    IO.print(ty(cast(col("i"), D.TU32{})))
    IO.print(ty(cast(col("f"), D.TI32{})))
    IO.print(ty(cast(col("b"), D.TI32{})))
    IO.print(ty(cast(col("b"), D.TStr{})))
    IO.print(ty(cast(col("s"), D.TU32{})))
    IO.print(ty(cast(col("s"), D.TBool{})))
    IO.print(ty(cast(col("f"), D.TF32{})))
    IO.print(ty(cast(col("f"), D.TBool{})))
    IO.print(ty(cast(col("a"), D.TBool{})))
    IO.print(ty(cast(X.Lit{D.SNull{}}, D.TStr{})))
    # unary ops
    IO.print(ty(un(X.Neg{}, col("i"))))
    IO.print(ty(un(X.Neg{}, col("f"))))
    IO.print(ty(un(X.Neg{}, col("a"))))
    IO.print(ty(un(X.Not{}, col("b"))))
    IO.print(ty(un(X.Not{}, col("a"))))
    IO.print(ty(un(X.IsNull{}, col("s"))))
    IO.print(ty(un(X.IsNotNull{}, col("f"))))
    IO.print(ty(un(X.Abs{}, col("i"))))
    IO.print(ty(un(X.Abs{}, col("s"))))
    IO.print(ty(un(X.Sqrt{}, col("f"))))
    IO.print(ty(un(X.Sqrt{}, col("i"))))
    # arithmetic
    IO.print(ty(bin(X.Add{}, col("a"), lu(1))))
    IO.print(ty(bin(X.Mul{}, col("i"), col("i"))))
    IO.print(ty(bin(X.Div{}, col("f"), col("f"))))
    IO.print(ty(bin(X.Mod{}, col("i"), col("i"))))
    IO.print(ty(bin(X.Add{}, col("a"), col("f"))))
    IO.print(ty(bin(X.Sub{}, col("s"), col("s"))))
    IO.print(ty(bin(X.Mod{}, col("f"), col("f"))))
    # comparisons and boolean ops
    IO.print(ty(bin(X.Lt{}, col("s"), X.Lit{D.SStr{"x"}})))
    IO.print(ty(bin(X.Eq{}, col("b"), col("b"))))
    IO.print(ty(bin(X.Ge{}, col("a"), col("i"))))
    IO.print(ty(bin(X.And{}, col("b"), bin(X.Gt{}, col("a"), lu(1)))))
    IO.print(ty(bin(X.Or{}, col("b"), col("a"))))
    # fill_null
    IO.print(ty(X.FillNull{col("f"), X.Lit{D.SF32{0.0}}}))
    IO.print(ty(X.FillNull{col("f"), lu(0)}))
    # aggregations
    IO.print(ty(agg(X.Sum{}, col("a"))))
    IO.print(ty(agg(X.Sum{}, col("s"))))
    IO.print(ty(agg(X.Mean{}, col("i"))))
    IO.print(ty(agg(X.Mean{}, col("b"))))
    IO.print(ty(agg(X.Min{}, col("s"))))
    IO.print(ty(agg(X.Max{}, col("b"))))
    IO.print(ty(agg(X.Count{}, col("s"))))
    IO.print(ty(agg(X.Len{}, lu(1))))
    IO.print(ty(agg(X.NUnique{}, col("f"))))
    IO.print(ty(agg(X.First{}, col("s"))))
    IO.print(ty(agg(X.Last{}, col("b"))))
    IO.print(ty(bin(X.Add{}, agg(X.Sum{}, col("a")), lu(1))))
    # the leftmost error wins
    IO.print(ty(bin(X.Add{}, col("zz"), col("s"))))
    IO.print(ty(bin(X.Add{}, col("s"), col("zz"))))
    # name / refs / is_agg / split_agg
    IO.print(names(bin(X.Add{}, col("a"), lu(1))))
    IO.print(names(bin(X.Add{}, lu(1), col("b"))))
    IO.print(names(bin(X.Add{}, lu(1), lu(2))))
    IO.print(names(bin(X.Add{}, X.Alias{col("x"), "y"}, col("z"))))
    IO.print(names(X.Alias{bin(X.Sub{}, col("a"), agg(X.Mean{}, col("a"))), "d"}))
    IO.print(names(X.FillNull{col("a"), agg(X.Max{}, col("b"))}))
    IO.print(split.r(X.Expr.split_agg(X.Alias{agg(X.Len{}, lu(1)), "count"})))
    IO.print(split.r(X.Expr.split_agg(bin(X.Add{}, agg(X.Sum{}, col("a")), lu(1)))))
#|col("a") : u32
#|col("zz") : ColumnNotFound: zz
#|lit(1) : u32
#|lit(-3) : i32
#|lit(1.5) : f32
#|lit(true) : bool
#|lit("x") : str
#|lit(null) : TypeMismatch in lit: expected a typed literal, got null
#|col("f").alias("g") : f32
#|col("a").cast(f32) : f32
#|col("a").cast(i32) : i32
#|col("i").cast(u32) : u32
#|col("f").cast(i32) : i32
#|col("b").cast(i32) : i32
#|col("b").cast(str) : str
#|col("s").cast(u32) : u32
#|col("s").cast(bool) : bool
#|col("f").cast(f32) : f32
#|col("f").cast(bool) : TypeMismatch in cast: expected castable to bool, got f32
#|col("a").cast(bool) : TypeMismatch in cast: expected castable to bool, got u32
#|lit(null).cast(str) : str
#|col("i").neg() : i32
#|col("f").neg() : f32
#|col("a").neg() : TypeMismatch in neg: expected i32 or f32, got u32
#|col("b").not() : bool
#|col("a").not() : TypeMismatch in not: expected bool, got u32
#|col("s").is_null() : bool
#|col("f").is_not_null() : bool
#|col("i").abs() : i32
#|col("s").abs() : TypeMismatch in abs: expected i32 or f32, got str
#|col("f").sqrt() : f32
#|col("i").sqrt() : TypeMismatch in sqrt: expected f32, got i32
#|(col("a") + lit(1)) : u32
#|(col("i") * col("i")) : i32
#|(col("f") / col("f")) : f32
#|(col("i") % col("i")) : i32
#|(col("a") + col("f")) : TypeMismatch in add: expected u32, got f32
#|(col("s") - col("s")) : TypeMismatch in sub: expected numeric, got str
#|(col("f") % col("f")) : TypeMismatch in mod: expected u32 or i32, got f32
#|(col("s") < lit("x")) : bool
#|(col("b") == col("b")) : bool
#|(col("a") >= col("i")) : TypeMismatch in ge: expected u32, got i32
#|(col("b") & (col("a") > lit(1))) : bool
#|(col("b") | col("a")) : TypeMismatch in or: expected bool, got u32
#|col("f").fill_null(lit(0)) : f32
#|col("f").fill_null(lit(0)) : TypeMismatch in fill_null: expected f32, got u32
#|col("a").sum() : u32
#|col("s").sum() : TypeMismatch in sum: expected numeric, got str
#|col("i").mean() : f32
#|col("b").mean() : TypeMismatch in mean: expected numeric, got bool
#|col("s").min() : str
#|col("b").max() : bool
#|col("s").count() : u32
#|lit(1).len() : u32
#|col("f").n_unique() : u32
#|col("s").first() : str
#|col("b").last() : bool
#|(col("a").sum() + lit(1)) : u32
#|(col("zz") + col("s")) : ColumnNotFound: zz
#|(col("s") + col("zz")) : ColumnNotFound: zz
#|(col("a") + lit(1)) name=a refs=[a] is_agg=false
#|(lit(1) + col("b")) name=b refs=[b] is_agg=false
#|(lit(1) + lit(2)) name=literal refs=[] is_agg=false
#|(col("x").alias("y") + col("z")) name=y refs=[x, z] is_agg=false
#|(col("a") - col("a").mean()).alias("d") name=d refs=[a, a] is_agg=true
#|col("a").fill_null(col("b").max()) name=a refs=[a, b] is_agg=true
#|len of lit(1)
#|none
