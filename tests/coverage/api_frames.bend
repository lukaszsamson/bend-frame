# T6 coverage: frame construction and inspection: from_columns, named, column, schema, height, clone,
# then, then_io, dump, dump_frame, show, describe, err_show, schema_show. Cases with nulls (null cells
# and SNull rows), zero rows, zero columns, and the refusals (a repeated name, ragged columns, a
# scalar of another dtype, an error value passed through then / show / describe). These operations
# are eager: a result is printed as DF.dump, DF.show, DF.describe text or as the pair they return.
# Expectations: DESIGN.md 15.1, 15.2.1, 15.5.4 (describe), 15.9 (error texts), reasoned first. There is
# no line-by-line Polars twin (show / describe print Bend's own table layout); bench/coverage/api_frames.py
# prints Polars 2.0.0's describe of the same frames and the refusals of ragged / repeated / mistyped
# columns, which agree with the cases here (count, null_count, mean, std, min, nearest-rank quantiles,
# max); departures: f32 statistics for numeric columns (Polars f64), bool columns described as text min /
# max (Polars as 0/1 numbers), the std of [1,2,4] is 1.5275253 (DESIGN 15.5.4's f32 algorithm).
#@ cover from_columns,column success null empty invalid eager
#@ cover named success null empty eager
#@ cover height,clone,dump,dump_frame,show,describe success null empty eager
#@ cover schema success empty eager
#@ cover then,then_io success null empty invalid eager
#@ cover show,describe,dump,schema_show,err_show invalid eager
#@ cover schema_show,err_show success eager
#@ cover schema_show empty eager
#@ na from_columns,named,column,schema,height,clone,then,then_io,dump,dump_frame,show,describe,err_show,schema_show lazy -- an eager frame function: the lazy API starts from DF.source and never builds, inspects or prints a frame (collect_show and collect_schema are covered in api_plans.bend)
#@ na schema,height,clone,dump_frame,named invalid -- the argument is an already valid Frame / Column / name: no input can be refused (a repeated name is from_columns' error, covered)
#@ na schema,schema_show,err_show null -- the answer is a dtype list / a text: a null cell changes none of them
#@ na err_show empty -- the argument is an error value / a name: nothing zero-row to give
#@ na named,err_show zerocol -- a column / an error value has no frame shape
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./../../src/schema.bend as S
import ./../regress/lib/rx.bend as R
import ./lib/fx.bend as FX

# a nullable column of the given dtype from scalars (DF.column), failing into a named error column

# a named column from DF.column (a failed column is named after its error, so the dump shows it)
def nm(+n: String, r: E.ResT(C.Column)) -> C.Named:
  match r:
    case Fail{e}:
      C.Named{DF.err_show(e), C.CU32{0, 0n, C.AllValid{}, [0 : U32*1n]}}
    case Done{c}:
      DF.named(n, c)

def col(+n: String, +t: D.DType, xs: List<&2, D.Scalar>) -> C.Named:
  nm(n, DF.column(t, xs))

def cs(r: E.ResT(C.Column)) -> String:
  match r:
    case Fail{e}:
      "error\t" ++ DF.err_show(e) ++ "\n"
    case Done{c}:
      DF.dump(DF.from_columns([DF.named("c", c)]))

# DF.column over scalars, printed as the one-column frame it builds
def colcase(+tag: String, +t: D.DType, xs: List<&2, D.Scalar>) -> IO(Unit):
  IO.print("-- " ++ tag ++ "\n" ++ cs(DF.column(t, xs)) ++ "\n")

def dframe(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error\t" ++ DF.err_show(e) ++ "\n"
    case Done{f}:
      DF.dump_frame(f)

def pr(+tag: String, r: E.ResT(C.Frame)) -> IO(Unit):
  IO.print("-- " ++ tag ++ "\n" ++ DF.dump(r) ++ "\n")

def sh(+tag: String, r: E.ResT(C.Frame)) -> IO(Unit):
  IO.print("-- " ++ tag ++ "\n" ++ DF.show(r) ++ "\n\n")

def ds() -> E.ResT(C.Frame):
  R.frame([
    R.mk("n", [R.u(1), R.u(2), R.null(), R.u(4)], DF.t_u32()),
    R.mk("f", [R.f(1.5), R.null(), R.f(3.5), R.f(5.0)], DF.t_f32()),
    R.mk("s", [R.s("a"), R.s("b"), R.null(), R.s("d")], DF.t_str()),
    R.mk("b", [R.b(True{}), R.b(False{}), R.b(True{}), R.null()], DF.t_bool())])

def schema_text.k(x: C.Frame & DF.Schema()) -> String:
  (f, s) = x
  DF.schema_show(Done{s})

def schema_text(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ DF.err_show(e)
    case Done{f}:
      schema_text.k(DF.schema(f))

def height_text.k(x: C.Frame & U32) -> String:
  (f, h) = x
  U32.show(h)

def height_text(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ DF.err_show(e)
    case Done{f}:
      height_text.k(DF.height(f))

def cl.k(x: C.Frame & C.Frame) -> E.ResT(C.Frame):
  (a, b) = x
  Done{b}

def cl(r: E.ResT(C.Frame)) -> E.ResT(C.Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      cl.k(DF.clone(f))

def main() -> IO(Unit):
  do IO<Unit>:
    pr("from_columns with nulls", DF.from_columns([nm("a", DF.column(DF.t_u32(), [R.u(1), R.null(), R.u(3)])), nm("s", DF.column(DF.t_str(), [R.s("x"), R.null(), R.s("")]))]))
    pr("from_columns of zero-row columns", DF.from_columns([col("a", DF.t_u32(), []), col("s", DF.t_str(), [])]))
    pr("from_columns of no columns", DF.from_columns([]))
    pr("invalid from_columns repeated name", DF.from_columns([col("a", DF.t_u32(), [R.u(1)]), col("a", DF.t_f32(), [R.f(1.0)])]))
    pr("invalid from_columns ragged columns", DF.from_columns([col("a", DF.t_u32(), [R.u(1), R.u(2)]), col("b", DF.t_f32(), [R.f(1.0)])]))
    colcase("column u32 with a null row", DF.t_u32(), [R.u(1), R.null(), R.u(3)])
    colcase("column i32", DF.t_i32(), [R.i(1), R.ineg(2), R.null()])
    colcase("column f32 NaN inf -0.0", DF.t_f32(), [R.f(R.nan()), R.f(R.inf()), R.f(R.nzero()), R.null()])
    colcase("column bool", DF.t_bool(), [R.b(True{}), R.null(), R.b(False{})])
    colcase("column str with an empty string and a null", DF.t_str(), [R.s(""), R.null(), R.s("é")])
    colcase("column of no scalars", DF.t_u32(), [])
    colcase("column of only nulls", DF.t_str(), [R.null(), R.null()])
    colcase("invalid column scalar of another dtype", DF.t_u32(), [R.u(1), R.s("x")])
    colcase("invalid column f32 scalar in a bool column", DF.t_bool(), [R.f(1.0)])
    pr("dump of a frame with nulls", FX.t())
    pr("dump of zero rows", FX.z())
    pr("dump of zero columns", R.zcols(4))
    IO.print("-- dump_frame of zero columns\n" ++ DF.dump_frame(C.Frame{2, Nil{}}) ++ "\n")
    IO.print("-- dump_frame of a frame with nulls\n" ++ dframe(ds()) ++ "\n")
    IO.print("-- dump_frame of zero rows\n" ++ dframe(FX.z()) ++ "\n")
    IO.print("-- schema and height\n" ++ schema_text(FX.t()) ++ "\n" ++ height_text(FX.t()) ++ "\n" ++ schema_text(FX.z()) ++ "\n" ++ height_text(FX.z()) ++ "\n" ++ schema_text(R.zcols(4)) ++ "\n" ++ height_text(R.zcols(4)) ++ "\n\n")
    pr("clone keeps nulls", cl(ds()))
    pr("clone of zero rows", cl(FX.z()))
    pr("clone of zero columns", cl(R.zcols(2)))
    pr("then runs the function on a frame", DF.then(ds(), f => DF.head(f, 2)))
    pr("then on zero rows", DF.then(FX.z(), f => DF.head(f, 2)))
    pr("then passes an error through", DF.then(DF.from_columns([col("a", DF.t_u32(), [R.u(1), R.u(2)]), col("b", DF.t_f32(), [R.f(1.0)])]), f => DF.head(f, 1)))
    pr("then chains with nulls", DF.then(DF.then(ds(), f => DF.head(f, 3)), f => DF.tail(f, 2)))
    r1 : E.ResT(C.Frame) <- DF.then_io(ds(), f => IO.pure(E.ResT(C.Frame), DF.head(f, 2)))
    pr("then_io runs the IO function on a frame with nulls", r1)
    r2 : E.ResT(C.Frame) <- DF.then_io(FX.z(), f => IO.pure(E.ResT(C.Frame), DF.tail(f, 2)))
    pr("then_io on zero rows", r2)
    r3 : E.ResT(C.Frame) <- DF.then_io(DF.from_columns([col("a", DF.t_u32(), [R.u(1)]), col("a", DF.t_u32(), [R.u(2)])]), f => IO.pure(E.ResT(C.Frame), DF.head(f, 1)))
    pr("then_io passes an error through", r3)
    sh("show of a frame with nulls", ds())
    sh("show of zero rows", FX.z())
    sh("show of zero columns", R.zcols(2))
    sh("show of an error", DF.from_columns([col("a", DF.t_u32(), [R.u(1)]), col("a", DF.t_u32(), [R.u(1)])]))
    sh("describe of a frame with nulls", DF.describe(ds()))
    sh("describe of zero rows", DF.describe(FX.z()))
    sh("describe of the f32 special values", DF.describe(R.frame([R.mk("x", [R.f(1.0), R.f(R.nan()), R.null(), R.f(R.inf()), R.f(R.nzero())], DF.t_f32())])))
    sh("invalid describe passes an error through", DF.describe(DF.from_columns([col("a", DF.t_u32(), [R.u(1)]), col("a", DF.t_u32(), [R.u(1)])])))
    sh("invalid describe of a column named statistic", DF.describe(R.frame([R.mk("statistic", [R.u(1)], DF.t_u32())])))
    IO.print("-- err_show\n" ++ DF.err_show(E.ColumnNotFound{"a"}) ++ "\n" ++ DF.err_show(E.InvalidOperation{"x"}) ++ "\n" ++ DF.err_show(E.IoError{2, "no such file"}) ++ "\n\n")
    IO.print("-- schema_show\n" ++ DF.schema_show(Done{Nil{}}) ++ "\n" ++ DF.schema_show(Fail{E.ColumnNotFound{"z"}}) ++ "\n\n")
#|-- from_columns with nulls
#|frame
#|height	3
#|width	2
#|col	u32	"a"
#|col	str	"s"
#|row	1	"x"
#|row	null	null
#|row	3	""
#|
#|
#|-- from_columns of zero-row columns
#|frame
#|height	0
#|width	2
#|col	u32	"a"
#|col	str	"s"
#|
#|
#|-- from_columns of no columns
#|frame
#|height	0
#|width	0
#|
#|
#|-- invalid from_columns repeated name
#|error	DuplicateColumn: a
#|
#|
#|-- invalid from_columns ragged columns
#|error	ShapeMismatch: expected 2 rows, got 1
#|
#|
#|-- column u32 with a null row
#|frame
#|height	3
#|width	1
#|col	u32	"c"
#|row	1
#|row	null
#|row	3
#|
#|
#|-- column i32
#|frame
#|height	3
#|width	1
#|col	i32	"c"
#|row	1
#|row	-2
#|row	null
#|
#|
#|-- column f32 NaN inf -0.0
#|frame
#|height	4
#|width	1
#|col	f32	"c"
#|row	0x7fc00000
#|row	0x7f800000
#|row	0x80000000
#|row	null
#|
#|
#|-- column bool
#|frame
#|height	3
#|width	1
#|col	bool	"c"
#|row	true
#|row	null
#|row	false
#|
#|
#|-- column str with an empty string and a null
#|frame
#|height	3
#|width	1
#|col	str	"c"
#|row	""
#|row	null
#|row	"é"
#|
#|
#|-- column of no scalars
#|frame
#|height	0
#|width	1
#|col	u32	"c"
#|
#|
#|-- column of only nulls
#|frame
#|height	2
#|width	1
#|col	str	"c"
#|row	null
#|row	null
#|
#|
#|-- invalid column scalar of another dtype
#|error	TypeMismatch in from_scalars: expected u32, got str
#|
#|
#|-- invalid column f32 scalar in a bool column
#|error	TypeMismatch in from_scalars: expected bool, got f32
#|
#|
#|-- dump of a frame with nulls
#|frame
#|height	7
#|width	8
#|col	u32	"a"
#|col	u32	"b"
#|col	i32	"p"
#|col	i32	"q"
#|col	f32	"x"
#|col	f32	"y"
#|col	bool	"k"
#|col	str	"s"
#|row	7	2	7	2	0x3fc00000	0x40000000	true	"a"
#|row	0	3	-7	2	0xc0000000	0x3f000000	false	""
#|row	4294967295	1	7	-2	null	0x3f800000	null	"é"
#|row	null	1	-7	-2	0x7fc00000	0x3f800000	true	null
#|row	5	null	-2147483648	-1	0x7f800000	0x7f800000	false	"abc"
#|row	1	0	null	1	0x00000000	0x00000000	true	"ab"
#|row	2	0	0	0	0x80000000	null	null	"a"
#|
#|
#|-- dump of zero rows
#|frame
#|height	0
#|width	8
#|col	u32	"a"
#|col	u32	"b"
#|col	i32	"p"
#|col	i32	"q"
#|col	f32	"x"
#|col	f32	"y"
#|col	bool	"k"
#|col	str	"s"
#|
#|
#|-- dump of zero columns
#|frame
#|height	4
#|width	0
#|
#|
#|-- dump_frame of zero columns
#|frame
#|height	2
#|width	0
#|
#|
#|-- dump_frame of a frame with nulls
#|frame
#|height	4
#|width	4
#|col	u32	"n"
#|col	f32	"f"
#|col	str	"s"
#|col	bool	"b"
#|row	1	0x3fc00000	"a"	true
#|row	2	null	"b"	false
#|row	null	0x40600000	null	true
#|row	4	0x40a00000	"d"	null
#|
#|
#|-- dump_frame of zero rows
#|frame
#|height	0
#|width	8
#|col	u32	"a"
#|col	u32	"b"
#|col	i32	"p"
#|col	i32	"q"
#|col	f32	"x"
#|col	f32	"y"
#|col	bool	"k"
#|col	str	"s"
#|
#|
#|-- schema and height
#|a:u32, b:u32, p:i32, q:i32, x:f32, y:f32, k:bool, s:str
#|7
#|a:u32, b:u32, p:i32, q:i32, x:f32, y:f32, k:bool, s:str
#|0
#|
#|4
#|
#|
#|-- clone keeps nulls
#|frame
#|height	4
#|width	4
#|col	u32	"n"
#|col	f32	"f"
#|col	str	"s"
#|col	bool	"b"
#|row	1	0x3fc00000	"a"	true
#|row	2	null	"b"	false
#|row	null	0x40600000	null	true
#|row	4	0x40a00000	"d"	null
#|
#|
#|-- clone of zero rows
#|frame
#|height	0
#|width	8
#|col	u32	"a"
#|col	u32	"b"
#|col	i32	"p"
#|col	i32	"q"
#|col	f32	"x"
#|col	f32	"y"
#|col	bool	"k"
#|col	str	"s"
#|
#|
#|-- clone of zero columns
#|frame
#|height	2
#|width	0
#|
#|
#|-- then runs the function on a frame
#|frame
#|height	2
#|width	4
#|col	u32	"n"
#|col	f32	"f"
#|col	str	"s"
#|col	bool	"b"
#|row	1	0x3fc00000	"a"	true
#|row	2	null	"b"	false
#|
#|
#|-- then on zero rows
#|frame
#|height	0
#|width	8
#|col	u32	"a"
#|col	u32	"b"
#|col	i32	"p"
#|col	i32	"q"
#|col	f32	"x"
#|col	f32	"y"
#|col	bool	"k"
#|col	str	"s"
#|
#|
#|-- then passes an error through
#|error	ShapeMismatch: expected 2 rows, got 1
#|
#|
#|-- then chains with nulls
#|frame
#|height	2
#|width	4
#|col	u32	"n"
#|col	f32	"f"
#|col	str	"s"
#|col	bool	"b"
#|row	2	null	"b"	false
#|row	null	0x40600000	null	true
#|
#|
#|-- then_io runs the IO function on a frame with nulls
#|frame
#|height	2
#|width	4
#|col	u32	"n"
#|col	f32	"f"
#|col	str	"s"
#|col	bool	"b"
#|row	1	0x3fc00000	"a"	true
#|row	2	null	"b"	false
#|
#|
#|-- then_io on zero rows
#|frame
#|height	0
#|width	8
#|col	u32	"a"
#|col	u32	"b"
#|col	i32	"p"
#|col	i32	"q"
#|col	f32	"x"
#|col	f32	"y"
#|col	bool	"k"
#|col	str	"s"
#|
#|
#|-- then_io passes an error through
#|error	DuplicateColumn: a
#|
#|
#|-- show of a frame with nulls
#|shape: (4, 4)
#|+-----+-----+-----+-------+
#|| n   | f   | s   | b     |
#|| --- | --- | --- | ---   |
#|| u32 | f32 | str | bool  |
#|+=====+=====+=====+=======+
#|| 1   | 1.5 | a   | true  |
#|| 2   |     | b   | false |
#||     | 3.5 |     | true  |
#|| 4   | 5   | d   |       |
#|+-----+-----+-----+-------+
#|
#|
#|-- show of zero rows
#|shape: (0, 8)
#|+-----+-----+-----+-----+-----+-----+------+-----+
#|| a   | b   | p   | q   | x   | y   | k    | s   |
#|| --- | --- | --- | --- | --- | --- | ---  | --- |
#|| u32 | u32 | i32 | i32 | f32 | f32 | bool | str |
#|+=====+=====+=====+=====+=====+=====+======+=====+
#|+-----+-----+-----+-----+-----+-----+------+-----+
#|
#|
#|-- show of zero columns
#|shape: (2, 0)
#|
#|
#|-- show of an error
#|error: DuplicateColumn: a
#|
#|
#|-- describe of a frame with nulls
#|shape: (9, 5)
#|+------------+-----------+-----------+-----+-------+
#|| statistic  | n         | f         | s   | b     |
#|| ---        | ---       | ---       | --- | ---   |
#|| str        | f32       | f32       | str | str   |
#|+============+===========+===========+=====+=======+
#|| count      | 3         | 3         | 3   | 3     |
#|| null_count | 1         | 1         | 1   | 1     |
#|| mean       | 2.3333333 | 3.3333333 |     |       |
#|| std        | 1.5275253 | 1.7559423 |     |       |
#|| min        | 1         | 1.5       | a   | false |
#|| 25%        | 2         | 3.5       |     |       |
#|| 50%        | 2         | 3.5       |     |       |
#|| 75%        | 4         | 5         |     |       |
#|| max        | 4         | 5         | d   | true  |
#|+------------+-----------+-----------+-----+-------+
#|
#|
#|-- describe of zero rows
#|shape: (9, 9)
#|+------------+-----+-----+-----+-----+-----+-----+-----+-----+
#|| statistic  | a   | b   | p   | q   | x   | y   | k   | s   |
#|| ---        | --- | --- | --- | --- | --- | --- | --- | --- |
#|| str        | f32 | f32 | f32 | f32 | f32 | f32 | str | str |
#|+============+=====+=====+=====+=====+=====+=====+=====+=====+
#|| count      | 0   | 0   | 0   | 0   | 0   | 0   | 0   | 0   |
#|| null_count | 0   | 0   | 0   | 0   | 0   | 0   | 0   | 0   |
#|| mean       |     |     |     |     |     |     |     |     |
#|| std        |     |     |     |     |     |     |     |     |
#|| min        |     |     |     |     |     |     |     |     |
#|| 25%        |     |     |     |     |     |     |     |     |
#|| 50%        |     |     |     |     |     |     |     |     |
#|| 75%        |     |     |     |     |     |     |     |     |
#|| max        |     |     |     |     |     |     |     |     |
#|+------------+-----+-----+-----+-----+-----+-----+-----+-----+
#|
#|
#|-- describe of the f32 special values
#|shape: (9, 2)
#|+------------+-----+
#|| statistic  | x   |
#|| ---        | --- |
#|| str        | f32 |
#|+============+=====+
#|| count      | 4   |
#|| null_count | 1   |
#|| mean       | nan |
#|| std        | nan |
#|| min        | -0  |
#|| 25%        | 1   |
#|| 50%        | inf |
#|| 75%        | inf |
#|| max        | inf |
#|+------------+-----+
#|
#|
#|-- invalid describe passes an error through
#|error: DuplicateColumn: a
#|
#|
#|-- invalid describe of a column named statistic
#|error: DuplicateColumn: statistic
#|
#|
#|-- err_show
#|ColumnNotFound: a
#|InvalidOperation: x
#|IoError 2: no such file
#|
#|
#|-- schema_show
#|
#|error: ColumnNotFound: z
#|
#|
