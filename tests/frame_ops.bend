# Frame ops: from_columns / put errors, take, replace (in place), get_cloned,
# select_names, head, filter_mask, names/height. Every result is shown with Fmt.show.
import Base
import ./../src/dtype.bend as D
import ./../src/err.bend as E
import ./../src/kernels.bend as K
import ./../src/column.bend as C
import ./../src/fmt.bend as F

def mk.k(name: String, r: E.ResT(C.Column)) -> C.Named:
  match r:
    case Fail{e}:
      C.Named{E.Err.show(e), C.CU32{0, 0n, C.AllValid{}, [0 : U32*1n]}}
    case Done{c}:
      C.Named{name, c}

def mk(name: String, xs: List<&2, D.Scalar>, +t: D.DType) -> C.Named:
  mk.k(name, C.Column.from_scalars(xs, t))

def col.k(r: E.ResT(C.Column)) -> C.Column:
  match r:
    case Fail{e}:
      C.CU32{0, 0n, C.AllValid{}, [0 : U32*1n]}
    case Done{c}:
      c

def col(xs: List<&2, D.Scalar>, +t: D.DType) -> C.Column:
  col.k(C.Column.from_scalars(xs, t))

def snd(r: C.Frame & String) -> String:
  (f, s) = r
  s

def show(r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{f}:
      snd(F.Fmt.show(f))

def base() -> E.ResT(C.Frame):
  C.Frame.from_columns([mk("id", [D.SU32{1}, D.SU32{2}, D.SU32{3}, D.SU32{4}], D.TU32{}), mk("s", [D.SStr{"a"}, D.SNull{}, D.SStr{"c"}, D.SStr{"d"}], D.TStr{}), mk("x", [D.SF32{0.5}, D.SF32{1.5}, D.SNull{}, D.SF32{3.5}], D.TF32{})])

def on(f: C.Frame -> String, r: E.ResT(C.Frame)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e)
    case Done{fr}:
      f(fr)

# names and height (the frame comes back)
def nm2(+h: U32, r: C.Frame & List<&2, String>) -> String:
  (f, ns) = r
  "height=" ++ U32.show(h) ++ " names=" ++ List.show(~&2, ~String, ~(s => s), ns)

def nm1(r: C.Frame & U32) -> String:
  (f, +h) = r
  nm2(h, C.Frame.names(f))

def names(f: C.Frame) -> String:
  nm1(C.Frame.height(f))

# take answers (frame, Maybe column)
def tk(r: C.Frame & Maybe<&1, C.Column>) -> String:
  (f, m) = r
  match m:
    case None{}:
      "missing | " ++ names(f)
    case Some{c}:
      "found | " ++ names(f)

# get_cloned answers (frame, result column)
def gc2(+f_names: String, r: E.ResT(C.Column)) -> String:
  match r:
    case Fail{e}:
      "error: " ++ E.Err.show(e) ++ " | " ++ f_names
    case Done{c}:
      "ok | " ++ f_names

def gc1(r: C.Frame & E.ResT(C.Column)) -> String:
  (f, res) = r
  gc2(names(f), res)

def put_res(r: E.ResT(C.Frame)) -> String:
  show(r)

def mask.k(r: U32 & Array<U32>) -> Array<U32>:
  (n, a) = r
  a

def mask(xs: List<&2, U32>) -> Array<U32>:
  mask.k(K.Kernel.from_list(~U32, xs, 0))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(on(names, base()))
    IO.print(on(f => tk(C.Frame.take(f, "s")), base()))
    IO.print(on(f => tk(C.Frame.take(f, "nope")), base()))
    IO.print(on(f => gc1(C.Frame.get_cloned(f, "s")), base()))
    IO.print(on(f => gc1(C.Frame.get_cloned(f, "nope")), base()))
    # put: appended at the end; duplicate name and wrong height are errors
    IO.print(on(f => show(C.Frame.put(f, "y", col([D.SBool{True{}}, D.SBool{False{}}, D.SNull{}, D.SBool{True{}}], D.TBool{}))), base()))
    IO.print(on(f => show(C.Frame.put(f, "id", col([D.SU32{9}, D.SU32{9}, D.SU32{9}, D.SU32{9}], D.TU32{}))), base()))
    IO.print(on(f => show(C.Frame.put(f, "z", col([D.SU32{9}, D.SU32{9}], D.TU32{}))), base()))
    # replace keeps the column's position; a new name appends
    IO.print(on(f => show(C.Frame.replace(f, "s", col([D.SU32{7}, D.SU32{8}, D.SNull{}, D.SU32{6}], D.TU32{}))), base()))
    IO.print(on(f => show(C.Frame.replace(f, "w", col([D.SU32{7}, D.SU32{8}, D.SNull{}, D.SU32{6}], D.TU32{}))), base()))
    IO.print(on(f => show(C.Frame.replace(f, "id", col([D.SU32{7}], D.TU32{}))), base()))
    # select_names: requested order, errors
    IO.print(on(f => show(C.Frame.select_names(f, ["x", "id"])), base()))
    IO.print(on(f => show(C.Frame.select_names(f, ["id", "nope"])), base()))
    IO.print(on(f => show(C.Frame.select_names(f, ["id", "x", "id"])), base()))
    # head, filter_mask
    IO.print(on(f => show(Done{C.Frame.head(f, 2)}), base()))
    IO.print(on(f => show(Done{C.Frame.filter_mask(f, mask([1, 0, 1, 1]), 3)}), base()))
    # from_columns errors
    IO.print(show(C.Frame.from_columns([mk("a", [D.SU32{1}, D.SU32{2}], D.TU32{}), mk("b", [D.SU32{1}], D.TU32{})])))
    IO.print(show(C.Frame.from_columns([mk("a", [D.SU32{1}], D.TU32{}), mk("a", [D.SU32{1}], D.TU32{})])))
#|height=4 names=[id, s, x]
#|found | height=4 names=[id, x]
#|missing | height=4 names=[id, s, x]
#|ok | height=4 names=[id, s, x]
#|error: ColumnNotFound: nope | height=4 names=[id, s, x]
#|shape: (4, 4)
#|+-----+-----+-----+-------+
#|| id  | s   | x   | y     |
#|| --- | --- | --- | ---   |
#|| u32 | str | f32 | bool  |
#|+=====+=====+=====+=======+
#|| 1   | a   | 0.5 | true  |
#|| 2   |     | 1.5 | false |
#|| 3   | c   |     |       |
#|| 4   | d   | 3.5 | true  |
#|+-----+-----+-----+-------+
#|error: DuplicateColumn: id
#|error: ShapeMismatch: expected 4 rows, got 2
#|shape: (4, 3)
#|+-----+-----+-----+
#|| id  | s   | x   |
#|| --- | --- | --- |
#|| u32 | u32 | f32 |
#|+=====+=====+=====+
#|| 1   | 7   | 0.5 |
#|| 2   | 8   | 1.5 |
#|| 3   |     |     |
#|| 4   | 6   | 3.5 |
#|+-----+-----+-----+
#|shape: (4, 4)
#|+-----+-----+-----+-----+
#|| id  | s   | x   | w   |
#|| --- | --- | --- | --- |
#|| u32 | str | f32 | u32 |
#|+=====+=====+=====+=====+
#|| 1   | a   | 0.5 | 7   |
#|| 2   |     | 1.5 | 8   |
#|| 3   | c   |     |     |
#|| 4   | d   | 3.5 | 6   |
#|+-----+-----+-----+-----+
#|error: ShapeMismatch: expected 4 rows, got 1
#|shape: (4, 2)
#|+-----+-----+
#|| x   | id  |
#|| --- | --- |
#|| f32 | u32 |
#|+=====+=====+
#|| 0.5 | 1   |
#|| 1.5 | 2   |
#||     | 3   |
#|| 3.5 | 4   |
#|+-----+-----+
#|error: ColumnNotFound: nope
#|error: DuplicateColumn: id
#|shape: (2, 3)
#|+-----+-----+-----+
#|| id  | s   | x   |
#|| --- | --- | --- |
#|| u32 | str | f32 |
#|+=====+=====+=====+
#|| 1   | a   | 0.5 |
#|| 2   |     | 1.5 |
#|+-----+-----+-----+
#|shape: (3, 3)
#|+-----+-----+-----+
#|| id  | s   | x   |
#|| --- | --- | --- |
#|| u32 | str | f32 |
#|+=====+=====+=====+
#|| 1   | a   | 0.5 |
#|| 3   | c   |     |
#|| 4   | d   | 3.5 |
#|+-----+-----+-----+
#|error: ShapeMismatch: expected 2 rows, got 1
#|error: DuplicateColumn: a
