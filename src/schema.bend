# src/schema.bend -- Field, Schema ops, Frame.schema. DESIGN.md 4.5.
# A schema is a List<&2, Field>: ordered, unique names, pure Data (copyable,
# comparable, usable by Plan.schema without any column data).
# Idioms (DESIGN.md section 9): helpers above callers; match only on params;
# a pair result is taken apart in the next helper's parameter.
import Base
import ./dtype.bend as D
import ./err.bend as E
import ./column.bend as C

type Field is Data:
  Field{name: String, dtype: D.DType}

# ---- lookups --------------------------------------------------------------------

# p08 shape: the hit test for the head is computed by the caller of the next
# step and matched as a parameter; `found` carries the head's dtype
def Schema.find.go(s: List<&2, Field>, +n: String, hit: Bool, found: D.DType) -> Maybe<&2, D.DType>:
  match s hit:
    case _ True{}:
      Some{found}
    case Nil{} False{}:
      None{}
    case Field{+k, +t} <> rest False{}:
      Schema.find.go(rest, n, String.eq(k, n), t)

# the dtype of the named field, None when absent
def Schema.find(s: List<&2, Field>, +name: String) -> Maybe<&2, D.DType>:
  Schema.find.go(s, name, False{}, D.TBool{})

def Schema.has(s: List<&2, Field>, +name: String) -> Bool:
  Maybe.is_some(&2, D.DType, Schema.find(s, name))

def Schema.names(s: List<&2, Field>) -> List<&2, String>:
  match s:
    case Nil{}:
      Nil{}
    case Field{n, t} <> rest:
      n <> Schema.names(rest)

# ---- project ----------------------------------------------------------------------

# the earliest miss (request order) wins: the outer step is the earlier name
def Schema.project.put(n: String, t: Maybe<&2, D.DType>, r: E.Res(List<&2, Field>)) -> E.Res(List<&2, Field>):
  match t r:
    case None{} _:
      Fail{E.ColumnNotFound{n}}
    case Some{t2} Fail{e}:
      Fail{e}
    case Some{t2} Done{fs}:
      Done{Field{n, t2} <> fs}

def Schema.project.go(names: List<&2, String>, +s: List<&2, Field>) -> E.Res(List<&2, Field>):
  match names:
    case Nil{}:
      Done{Nil{}}
    case +n <> rest:
      Schema.project.put(n, Schema.find(s, n), Schema.project.go(rest, s))

def Schema.project.dup(d: Maybe<&2, String>, fs: List<&2, Field>) -> E.Res(List<&2, Field>):
  match d:
    case Some{n}:
      Fail{E.DuplicateColumn{n}}
    case None{}:
      Done{fs}

def Schema.project.chk(r: E.Res(List<&2, Field>)) -> E.Res(List<&2, Field>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+fs}:
      Schema.project.dup(C.Names.dup(Schema.names(fs), Nil{}, None{}), fs)

# the named fields in request order; ColumnNotFound for the first missing name
# (request order), then DuplicateColumn for the first repeated one
def Schema.project(names: List<&2, String>, +s: List<&2, Field>) -> E.Res(List<&2, Field>):
  Schema.project.chk(Schema.project.go(names, s))

# ---- with ---------------------------------------------------------------------------

def Schema.with.pick(eq: Bool, h: Field, +f: Field) -> Field:
  match eq:
    case True{}:
      f
    case False{}:
      h

def Schema.with.go(s: List<&2, Field>, +n: String, +f: Field) -> List<&2, Field>:
  match s:
    case Nil{}:
      Nil{}
    case Field{+k, t} <> rest:
      Schema.with.pick(String.eq(k, n), Field{k, t}, f) <> Schema.with.go(rest, n, f)

def Schema.with.fin(has: Bool, s: List<&2, Field>, +n: String, +f: Field) -> List<&2, Field>:
  match has:
    case True{}:
      Schema.with.go(s, n, f)
    case False{}:
      List.append(&2, Field, s, f <> Nil{})

def Schema.with.a(+s: List<&2, Field>, +f: Field, +n: String) -> List<&2, Field>:
  Schema.with.fin(Schema.has(s, n), s, n, f)

# replace the field of the same name in place, or append it (with_columns)
def Schema.with(s: List<&2, Field>, f: Field) -> List<&2, Field>:
  match f:
    case Field{+n, t}:
      Schema.with.a(s, Field{n, t}, n)

# ---- show / eq ------------------------------------------------------------------------

def Field.show(f: Field) -> String:
  match f:
    case Field{n, t}:
      n ++ ":" ++ D.DType.show(t)

def Field.eq(a: Field, b: Field) -> Bool:
  match a b:
    case Field{n1, t1} Field{n2, t2}:
      Bool.and(String.eq(n1, n2), D.DType.eq(t1, t2))

# `a:u32, b:f32` (empty schema: "")
def Schema.show.go(s: List<&2, Field>) -> List<&2, String>:
  match s:
    case Nil{}:
      Nil{}
    case f <> rest:
      Field.show(f) <> Schema.show.go(rest)

def Schema.show(s: List<&2, Field>) -> String:
  String.join(Schema.show.go(s), ", ")

def Schema.eq(a: List<&2, Field>, b: List<&2, Field>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case x <> xs y <> ys:
      Bool.and(Field.eq(x, y), Schema.eq(xs, ys))
    case _ _:
      False{}

# ---- Frame.schema ----------------------------------------------------------------------

def Cols.schema.k(+n: String, cr: C.Column & D.DType, r: List<&1, C.Named> & List<&2, Field>) -> List<&1, C.Named> & List<&2, Field>:
  (c, t) = cr
  (rest, fs) = r
  (C.Named{n, c} <> rest, Field{n, t} <> fs)

def Cols.schema(cols: List<&1, C.Named>) -> List<&1, C.Named> & List<&2, Field>:
  match cols:
    case Nil{}:
      (Nil{}, Nil{})
    case C.Named{+n, col} <> rest:
      Cols.schema.k(n, C.Column.dtype(col), Cols.schema(rest))

def Frame.schema.k(+h: U32, r: List<&1, C.Named> & List<&2, Field>) -> C.Frame & List<&2, Field>:
  (cols, fs) = r
  (C.Frame{h, cols}, fs)

# the frame's schema; the frame comes back unchanged
def Frame.schema(f: C.Frame) -> C.Frame & List<&2, Field>:
  match f:
    case C.Frame{+h, cols}:
      Frame.schema.k(h, Cols.schema(cols))
