# M3: Csv.parse -- quotes, escaped quotes, CRLF, empty fields, trailing newline, inference,
# explicit (strict) dtypes, errors, Csv.render round trip.
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/fmt.bend as F
import ./../src/csv.bend as V

def snd(r: C.Frame & String) -> String:
  (f, s) = r
  s

def show(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      snd(F.Fmt.show(f))

def rend(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      snd(V.Csv.render(f, None{}))

# "<height>x<width> [names]"
def dims.b(+h: U32, r: C.Frame & List<&2, String>) -> String:
  (f, ns) = r
  U32.show(h) ++ " rows, columns " ++ String.join(ns, ",")

def dims.a(r: C.Frame & U32) -> String:
  (f, +h) = r
  dims.b(h, C.Frame.names(f))

def dims(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      dims.a(C.Frame.height(f))

# parse -> render -> parse -> render: the two renders agree
def again(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      rend(V.Csv.parse(snd(V.Csv.render(f, None{})), V.Csv.default()))

def eq(a: String, b: String) -> String:
  Bool.show(String.eq(a, b))

def fields.go(xs: List<&2, V.CsvField>) -> String:
  match xs:
    case Nil{}:
      "."
    case V.CsvField{name, dtype} <> t:
      name ++ ":" ++ D.DType.show(dtype) ++ " " ++ fields.go(t)

def fields(r: E.Res(List<&2, V.CsvField>)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{xs}:
      fields.go(xs)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show(V.Csv.parse("id,name,score,flag\n1,ann,1.5,true\n2,\"b,\"\"ob\",,false\r\n3,,7,True\n", V.Csv.default())))
    IO.print(rend(V.Csv.parse("id,name,score,flag\n1,ann,1.5,true\n2,\"b,\"\"ob\",,false\r\n3,,7,True\n", V.Csv.default())))
    IO.print(eq(rend(V.Csv.parse("id,name,score,flag\n1,ann,1.5,true\n2,\"b,\"\"ob\",,false\r\n3,,7,True\n", V.Csv.default())), again(V.Csv.parse("id,name,score,flag\n1,ann,1.5,true\n2,\"b,\"\"ob\",,false\r\n3,,7,True\n", V.Csv.default()))))
    IO.print(dims(V.Csv.parse("a,b\n1,2\n3,4", V.Csv.default())))
    IO.print(dims(V.Csv.parse("a,b\n", V.Csv.default())))
    IO.print(show(V.Csv.parse("a,b\n", V.Csv.default())))
    IO.print(dims(V.Csv.parse("", V.Csv.default())))
    IO.print(show(V.Csv.parse("1,2\n3,\n", V.CsvOpts{',', False{}, 100})))
    IO.print(show(V.Csv.parse("a;b\n\"x;y\";-5\n;7\n", V.CsvOpts{';', True{}, 0})))
    IO.print(show(V.Csv.parse("i,j,k\n-1,1e3,5000000000\n2,0.5,7\n", V.Csv.default())))
    IO.print(show(V.Csv.parse("m\n\"line1\nline2\"\n", V.Csv.default())))
    IO.print(rend(V.Csv.parse("m\n\"line1\nline2\"\n", V.Csv.default())))
    IO.print(show(V.Csv.parse("a,b\n1,2\n3\n", V.Csv.default())))
    IO.print(show(V.Csv.parse("a,a\n1,2\n", V.Csv.default())))
    IO.print(show(V.Csv.parse("a\n\"bad\"x\n", V.Csv.default())))
    IO.print(show(V.Csv.parse("x\n1\n2\nfoo\n", V.CsvOpts{',', True{}, 2})))
    IO.print(show(V.Csv.parse("x\n1\n2\nfoo\n", V.CsvOpts{',', True{}, 0})))
    IO.print(show(V.Csv.parse_with("a,b,c\n1,x,2.5\n,y,\n", V.Csv.default(), [D.TI32{}, D.TStr{}, D.TF32{}])))
    IO.print(show(V.Csv.parse_with("a,b\n1,2\n2,x\n", V.Csv.default(), [D.TU32{}, D.TU32{}])))
    IO.print(show(V.Csv.parse_with("a,b\n1,2\n", V.Csv.default(), [D.TU32{}])))
    IO.print(show(V.Csv.parse_with("a,b\n1,true\n", V.Csv.default(), [D.TStr{}, D.TBool{}])))
    IO.print(show(V.Csv.parse("a,b\n 1 , x\n2,y\n\n3,z\n", V.Csv.default())))
    IO.print(fields(V.Csv.infer("a,b,c,d,e,f\n1,-2,3.5,true,x,\n2,3,4,False,,\n", V.Csv.default())))
#|shape: (3, 4)
#|+-----+-------+-------+-------+
#|| id  | name  | score | flag  |
#|| --- | ---   | ---   | ---   |
#|| u32 | str   | f32   | bool  |
#|+=====+=======+=======+=======+
#|| 1   | ann   | 1.5   | true  |
#|| 2   | b,"ob |       | false |
#|| 3   |       | 7     | true  |
#|+-----+-------+-------+-------+
#|id,name,score,flag
#|1,ann,1.5,true
#|2,"b,""ob",,false
#|3,,7,true
#|
#|True
#|2 rows, columns a,b
#|0 rows, columns a,b
#|shape: (0, 2)
#|+-----+-----+
#|| a   | b   |
#|| --- | --- |
#|| str | str |
#|+=====+=====+
#|+-----+-----+
#|0 rows, columns
#|shape: (2, 2)
#|+----------+----------+
#|| column_0 | column_1 |
#|| ---      | ---      |
#|| u32      | u32      |
#|+==========+==========+
#|| 1        | 2        |
#|| 3        |          |
#|+----------+----------+
#|shape: (2, 2)
#|+-----+-----+
#|| a   | b   |
#|| --- | --- |
#|| str | i32 |
#|+=====+=====+
#|| x;y | -5  |
#||     | 7   |
#|+-----+-----+
#|shape: (2, 3)
#|+-----+------+------------+
#|| i   | j    | k          |
#|| --- | ---  | ---        |
#|| i32 | f32  | f32        |
#|+=====+======+============+
#|| -1  | 1000 | 5000000000 |
#|| 2   | 0.5  | 7          |
#|+-----+------+------------+
#|shape: (1, 1)
#|+-------------+
#|| m           |
#|| ---         |
#|| str         |
#|+=============+
#|| line1
#|line2 |
#|+-------------+
#|m
#|"line1
#|line2"
#|
#|error: ParseError at line 3: expected 2 fields, got 1
#|error: DuplicateColumn: a
#|error: ParseError at line 0: malformed csv
#|error: ParseError at line 4: column x: cannot parse "foo" as u32
#|shape: (3, 1)
#|+-----+
#|| x   |
#|| --- |
#|| str |
#|+=====+
#|| 1   |
#|| 2   |
#|| foo |
#|+-----+
#|shape: (2, 3)
#|+-----+-----+-----+
#|| a   | b   | c   |
#|| --- | --- | --- |
#|| i32 | str | f32 |
#|+=====+=====+=====+
#|| 1   | x   | 2.5 |
#||     | y   |     |
#|+-----+-----+-----+
#|error: ParseError at line 3: column b: cannot parse "x" as u32
#|error: InvalidOperation: csv schema: 1 dtypes for 2 columns
#|shape: (1, 2)
#|+-----+------+
#|| a   | b    |
#|| --- | ---  |
#|| str | bool |
#|+=====+======+
#|| 1   | true |
#|+-----+------+
#|shape: (3, 2)
#|+-----+-----+
#|| a   | b   |
#|| --- | --- |
#|| u32 | str |
#|+=====+=====+
#|| 1   |  x  |
#|| 2   | y   |
#|| 3   | z   |
#|+-----+-----+
#|a:u32 b:i32 c:f32 d:bool e:str f:str .
