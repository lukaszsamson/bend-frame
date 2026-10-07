# p08: a miniature of the schema layer: dtypes, a schema as a list of
# (name, dtype), a plan with Select/Filter/WithColumn, and the pure
# `schema_of` that LAWS.bend states facts about. The point is that schema
# inference is a total pure function over a Data plan, so laws about it are
# provable by induction with no Arrays involved.
#   ~/.bend/bin/bend probes/p08_laws/PROOF.bend
import Base

type DType is Data:
  TBool{}
  TU32{}
  TI32{}
  TF32{}
  TStr{}

def DType.eq(a: DType, b: DType) -> Bool:
  match a b:
    case TBool{} TBool{}:
      True{}
    case TU32{} TU32{}:
      True{}
    case TI32{} TI32{}:
      True{}
    case TF32{} TF32{}:
      True{}
    case TStr{} TStr{}:
      True{}
    case _ _:
      False{}

# a field is a (name, dtype) pair; a schema is an ordered list of fields
type Field is Data:
  Field{name: String, dtype: DType}

def Schema() -> Data:
  List<&2, Field>

# a tiny expression language over column references and literals
type Expr is Data:
  Col{name: String}
  LitU32{v: U32}
  LitF32{v: F32}
  Add{a: Expr, b: Expr}
  Gt{a: Expr, b: Expr}

type Plan is Data:
  Source{schema: List<&2, Field>}
  Filter{pred: Expr, input: Plan}
  Select{names: List<&2, String>, input: Plan}
  WithColumn{name: String, expr: Expr, input: Plan}

# look a column up in a schema. The hit test for the head is computed by
# the CALLER of the next step and matched as a parameter (a match cannot
# scrutinize a computed value, and a helper may not call a def below it)
def Schema.find.go(s: List<&2, Field>, +n: String, hit: Bool, found: DType) -> Maybe<&2, DType>:
  match s hit:
    case _ True{}:
      Some{found}
    case Nil{} False{}:
      None{}
    case Field{+k, +t} <> rest False{}:
      Schema.find.go(rest, n, String.eq(k, n), t)

def Schema.find(s: List<&2, Field>, +n: String) -> Maybe<&2, DType>:
  Schema.find.go(s, n, False{}, TBool{})

def Expr.type.same.if(a: DType, ok: Bool) -> Maybe<&2, DType>:
  match ok:
    case True{}:
      Some{a}
    case False{}:
      None{}

def Expr.type.same(x: Maybe<&2, DType>, y: Maybe<&2, DType>) -> Maybe<&2, DType>:
  match x y:
    case Some{+a} Some{+b}:
      Expr.type.same.if(a, DType.eq(a, b))
    case _ _:
      None{}

def Expr.type.bool(m: Maybe<&2, DType>) -> Maybe<&2, DType>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      Some{TBool{}}

# the type of an expression under a schema; None on an unknown column or
# a mismatch (strict: no implicit casts)
def Expr.type(e: Expr, +s: List<&2, Field>) -> Maybe<&2, DType>:
  match e:
    case Col{n}:
      Schema.find(s, n)
    case LitU32{v}:
      Some{TU32{}}
    case LitF32{v}:
      Some{TF32{}}
    case Add{a, b}:
      Expr.type.same(Expr.type(a, s), Expr.type(b, s))
    case Gt{a, b}:
      Expr.type.bool(Expr.type.same(Expr.type(a, s), Expr.type(b, s)))

def Schema.project.put(n: String, t: Maybe<&2, DType>, r: Maybe<&2, List<&2, Field>>) -> Maybe<&2, List<&2, Field>>:
  match t r:
    case Some{t2} Some{fs}:
      Some{Field{n, t2} <> fs}
    case _ _:
      None{}

# projection: the named columns, in the requested order, each found
def Schema.project(names: List<&2, String>, +s: List<&2, Field>) -> Maybe<&2, List<&2, Field>>:
  match names:
    case Nil{}:
      Some{Nil{}}
    case +n <> rest:
      Schema.project.put(n, Schema.find(s, n), Schema.project(rest, s))

def schema_of.filter.if(s: List<&2, Field>, t: Maybe<&2, DType>) -> Maybe<&2, List<&2, Field>>:
  match t:
    case Some{TBool{}}:
      Some{s}
    case _:
      None{}

def schema_of.filter(pred: Expr, m: Maybe<&2, List<&2, Field>>) -> Maybe<&2, List<&2, Field>>:
  match m:
    case None{}:
      None{}
    case Some{+s}:
      schema_of.filter.if(s, Expr.type(pred, s))

def schema_of.select(names: List<&2, String>, m: Maybe<&2, List<&2, Field>>) -> Maybe<&2, List<&2, Field>>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      Schema.project(names, s)

def schema_of.with.if(name: String, s: List<&2, Field>, t: Maybe<&2, DType>) -> Maybe<&2, List<&2, Field>>:
  match t:
    case None{}:
      None{}
    case Some{t2}:
      Some{List.append(&2, Field, s, [Field{name, t2}])}

def schema_of.with(name: String, expr: Expr, m: Maybe<&2, List<&2, Field>>) -> Maybe<&2, List<&2, Field>>:
  match m:
    case None{}:
      None{}
    case Some{+s}:
      schema_of.with.if(name, s, Expr.type(expr, s))

# the output schema of a plan, or None when the plan is ill-typed
def schema_of(p: Plan) -> Maybe<&2, List<&2, Field>>:
  match p:
    case Source{s}:
      Some{s}
    case Filter{pred, input}:
      schema_of.filter(pred, schema_of(input))
    case Select{names, input}:
      schema_of.select(names, schema_of(input))
    case WithColumn{name, expr, input}:
      schema_of.with(name, expr, schema_of(input))

def DType.show(t: DType) -> String:
  match t:
    case TBool{}:
      "bool"
    case TU32{}:
      "u32"
    case TI32{}:
      "i32"
    case TF32{}:
      "f32"
    case TStr{}:
      "str"

def Field.show(f: Field) -> String:
  match f:
    case Field{n, t}:
      n ++ ":" ++ DType.show(t)

def main() -> IO(Unit):
  do IO<Unit>:
    src : Plan = Source{[Field{"a", TU32{}}, Field{"b", TF32{}}, Field{"s", TStr{}}]}
    p : Plan = Select{["b", "a"], WithColumn{"c", Add{Col{"a"}, LitU32{1}}, Filter{Gt{Col{"a"}, LitU32{3}}, src}}}
    IO.print(Maybe.show(~&2, ~List<&2, Field>, ~(fs => List.show(~&2, ~Field, ~Field.show, fs)), schema_of(p)))
    bad : Plan = Filter{Gt{Col{"a"}, LitF32{3.0}}, Source{[Field{"a", TU32{}}]}}
    IO.print(Maybe.show(~&2, ~List<&2, Field>, ~(fs => List.show(~&2, ~Field, ~Field.show, fs)), schema_of(bad)))

#|Some([b:f32, a:u32])
#|None
