# Plan.schema (collect_schema, M4): a Select/WithColumns/Filter/GroupBy/Join/
# Head chain over Sources, and the strict early errors (unknown column, filter
# on u32, aggregation in select, ...), all without any data.
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/schema.bend as S
import ./../src/expr.bend as X
import ./../src/sort.bend as O
import ./../src/join.bend as J
import ./../src/plan.bend as P

def sch(r: E.Res(List<&2, S.Field>)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{s}:
      S.Schema.show(s)

def show(p: P.Plan) -> String:
  sch(P.Plan.schema(p))

def col(n: String) -> X.Expr:
  X.Col{n}

def u32(v: U32) -> X.Expr:
  X.Lit{D.SU32{v}}

def al(e: X.Expr, n: String) -> X.Expr:
  X.Alias{e, n}

def bin(op: X.BinOp, a: X.Expr, b: X.Expr) -> X.Expr:
  X.Bin{op, a, b}

def agg(op: X.AggOp, e: X.Expr) -> X.Expr:
  X.Agg{op, e}

def key(n: String, d: Bool) -> O.SortKey:
  O.SortKey{n, d, False{}}

def sales() -> P.Plan:
  P.Source{"sales", [S.Field{"id", D.TU32{}}, S.Field{"region", D.TStr{}}, S.Field{"product", D.TStr{}}, S.Field{"qty", D.TU32{}}, S.Field{"price", D.TF32{}}, S.Field{"ok", D.TBool{}}]}

def prods() -> P.Plan:
  P.Source{"products", [S.Field{"product", D.TStr{}}, S.Field{"category", D.TStr{}}, S.Field{"price", D.TF32{}}]}

def joined() -> P.Plan:
  P.Join{J.Inner{}, ["product"], ["product"], sales(), prods()}

def revenue() -> X.Expr:
  al(bin(X.Mul{}, X.Cast{col("qty"), D.TF32{}}, col("price")), "revenue")

def with_rev() -> P.Plan:
  P.WithColumns{[revenue(), al(bin(X.Gt{}, col("qty"), u32(50)), "big")], joined()}

def filtered() -> P.Plan:
  P.Filter{bin(X.And{}, col("ok"), col("big")), with_rev()}

def grouped() -> P.Plan:
  P.GroupBy{[col("category")], [al(agg(X.Sum{}, col("revenue")), "rev"), al(agg(X.Len{}, u32(1)), "n"), agg(X.Mean{}, col("price_right"))], True{}, filtered()}

def chain() -> P.Plan:
  P.Head{3, P.Sort{[key("rev", True{})], grouped()}}

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("source:  " ++ show(sales()))
    IO.print("join:    " ++ show(joined()))
    IO.print("with:    " ++ show(with_rev()))
    IO.print("filter:  " ++ show(filtered()))
    IO.print("groupby: " ++ show(grouped()))
    IO.print("head:    " ++ show(chain()))
    IO.print("select:  " ++ show(P.Select{[col("price"), al(col("id"), "key"), bin(X.Add{}, col("qty"), u32(1))], sales()}))
    IO.print("wc repl: " ++ show(P.WithColumns{[al(X.Cast{col("id"), D.TStr{}}, "qty")], sales()}))
    IO.print("left:    " ++ show(P.Join{J.Left{}, ["product", "price"], ["product", "price"], sales(), prods()}))
    IO.print("-- errors")
    IO.print(show(P.Select{[col("id"), col("nope")], sales()}))
    IO.print(show(P.Filter{col("qty"), sales()}))
    IO.print(show(P.Select{[agg(X.Sum{}, col("qty"))], sales()}))
    IO.print(show(P.Select{[col("id"), al(col("qty"), "id")], sales()}))
    IO.print(show(P.Select{[col("nope"), col("id"), col("id")], sales()}))
    IO.print(show(P.WithColumns{[al(u32(1), "x"), al(u32(2), "x")], sales()}))
    IO.print(show(P.WithColumns{[agg(X.Max{}, col("qty"))], sales()}))
    IO.print(show(P.Filter{bin(X.Gt{}, col("qty"), agg(X.Max{}, col("qty"))), sales()}))
    IO.print(show(P.Filter{bin(X.Gt{}, col("price"), u32(3)), sales()}))
    IO.print(show(P.Sort{[key("id", False{}), key("zz", True{})], sales()}))
    IO.print(show(P.GroupBy{[col("region")], [col("qty")], False{}, sales()}))
    IO.print(show(P.GroupBy{[col("region")], [agg(X.Sum{}, agg(X.Sum{}, col("qty")))], False{}, sales()}))
    IO.print(show(P.GroupBy{[agg(X.Sum{}, col("qty"))], [agg(X.Sum{}, col("qty"))], False{}, sales()}))
    IO.print(show(P.GroupBy{Nil{}, [agg(X.Sum{}, col("qty"))], False{}, sales()}))
    IO.print(show(P.GroupBy{[col("region")], [agg(X.Sum{}, col("region"))], False{}, sales()}))
    IO.print(show(P.GroupBy{[col("qty")], [agg(X.Max{}, col("qty"))], False{}, sales()}))
    IO.print(show(P.Join{J.Inner{}, ["id"], ["product"], sales(), prods()}))
    IO.print(show(P.Join{J.Inner{}, ["product"], ["nope"], sales(), prods()}))
    IO.print(show(P.Join{J.Inner{}, ["product", "id"], ["product"], sales(), prods()}))
    IO.print(show(P.Join{J.Inner{}, Nil{}, Nil{}, sales(), prods()}))
    IO.print(show(P.Head{1, P.Select{[col("x")], P.Filter{col("ok"), sales()}}}))
    IO.print(show(P.Select{[col("id")], P.Filter{col("qty"), P.Select{[col("nope")], sales()}}}))

#|source:  id:u32, region:str, product:str, qty:u32, price:f32, ok:bool
#|join:    id:u32, region:str, product:str, qty:u32, price:f32, ok:bool, category:str, price_right:f32
#|with:    id:u32, region:str, product:str, qty:u32, price:f32, ok:bool, category:str, price_right:f32, revenue:f32, big:bool
#|filter:  id:u32, region:str, product:str, qty:u32, price:f32, ok:bool, category:str, price_right:f32, revenue:f32, big:bool
#|groupby: category:str, rev:f32, n:u32, price_right:f32
#|head:    category:str, rev:f32, n:u32, price_right:f32
#|select:  price:f32, key:u32, qty:u32
#|wc repl: id:u32, region:str, product:str, qty:str, price:f32, ok:bool
#|left:    id:u32, region:str, product:str, qty:u32, price:f32, ok:bool, category:str
#|-- errors
#|error: ColumnNotFound: nope
#|error: TypeMismatch in filter: expected bool, got u32
#|error: InvalidOperation: aggregation in select (v1: use group_by)
#|error: DuplicateColumn: id
#|error: ColumnNotFound: nope
#|error: DuplicateColumn: x
#|error: InvalidOperation: aggregation in with_columns (v1: use group_by)
#|error: InvalidOperation: aggregation in filter (v1: use group_by)
#|error: TypeMismatch in gt: expected f32, got u32
#|error: ColumnNotFound: zz
#|error: InvalidOperation: agg expects an aggregation: col("qty")
#|error: InvalidOperation: nested aggregation in agg: col("qty").sum().sum()
#|error: InvalidOperation: group_by key is an aggregation: col("qty").sum()
#|error: InvalidOperation: group_by needs at least one key
#|error: TypeMismatch in sum: expected numeric, got str
#|error: DuplicateColumn: qty
#|error: TypeMismatch in join: expected u32, got str
#|error: ColumnNotFound: nope
#|error: InvalidOperation: join: left_on and right_on must have the same length
#|error: InvalidOperation: join: no key columns
#|error: ColumnNotFound: x
#|error: ColumnNotFound: nope
