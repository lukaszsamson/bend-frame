# p09: the column/frame representation. A Column is a Type (it owns Arrays);
# its dtype tag and length ride beside it; a Frame is a list of named
# columns. Probes: Type-kinded records with Array fields, List<&1, Column>,
# Map<&1, Column>, a validity bitmap as Array<U32>, and reading one cell.
# Idiom: a call's pair result is taken apart in a helper's PARAMETER
# (`(a, x) = r`), never by a let on the call itself.
#   ~/.bend/bin/bend probes/p09_column_types.bend
import Base

# validity: bit i of word i/32; a missing bitmap means all valid
type Valid is Type:
  AllValid{}
  Bits{bits: Array<U32>}

type Column is Type:
  CBool{len: U32, valid: Valid, data: Array<U32>}
  CU32{len: U32, valid: Valid, data: Array<U32>}
  CF32{len: U32, valid: Valid, data: Array<F32>}
  CStr{len: U32, valid: Valid, data: Array<String>}

type Named is Type:
  Named{name: String, col: Column}

type Frame is Type:
  Frame{height: U32, cols: List<&1, Named>}

# a scalar cell, Data (printable, copyable)
type Cell is Data:
  Null{}
  VBool{b: Bool}
  VU32{v: U32}
  VF32{v: F32}
  VStr{s: String}

def Cell.show(c: Cell) -> String:
  match c:
    case Null{}:
      "null"
    case VBool{b}:
      Bool.show(b)
    case VU32{v}:
      U32.show(v)
    case VF32{v}:
      F32.show(v)
    case VStr{s}:
      s

def Valid.get.bits(+i: U32, r: Array<U32> & U32) -> Valid & Bool:
  (bits, w) = r
  (Bits{bits}, U32.is_ne(U32.and(U32.shrn(w, U32.to_nat(U32.and(i, 31))), 1), 0))

# is row i valid? hands the bitmap back
def Valid.get(v: Valid, +i: U32) -> Valid & Bool:
  match v:
    case AllValid{}:
      (AllValid{}, True{})
    case Bits{bits}:
      Valid.get.bits(i, Array.get(U32, bits, U32.shrn(i, 5n)))

# continuation helpers: each takes the (array, element) pair apart
def Column.cell.bool.k(len: U32, valid: Valid, r: Array<U32> & U32) -> Column & Cell:
  (d2, x) = r
  (CBool{len, valid, d2}, VBool{U32.is_ne(x, 0)})

def Column.cell.bool(len: U32, +i: U32, vb: Valid & Bool, data: Array<U32>) -> Column & Cell:
  (valid, ok) = vb
  match ok:
    case False{}:
      (CBool{len, valid, data}, Null{})
    case True{}:
      Column.cell.bool.k(len, valid, Array.get(U32, data, i))

def Column.cell.u32.k(len: U32, valid: Valid, r: Array<U32> & U32) -> Column & Cell:
  (d2, x) = r
  (CU32{len, valid, d2}, VU32{x})

def Column.cell.u32(len: U32, +i: U32, vb: Valid & Bool, data: Array<U32>) -> Column & Cell:
  (valid, ok) = vb
  match ok:
    case False{}:
      (CU32{len, valid, data}, Null{})
    case True{}:
      Column.cell.u32.k(len, valid, Array.get(U32, data, i))

def Column.cell.f32.k(len: U32, valid: Valid, r: Array<F32> & F32) -> Column & Cell:
  (d2, x) = r
  (CF32{len, valid, d2}, VF32{x})

def Column.cell.f32(len: U32, +i: U32, vb: Valid & Bool, data: Array<F32>) -> Column & Cell:
  (valid, ok) = vb
  match ok:
    case False{}:
      (CF32{len, valid, data}, Null{})
    case True{}:
      Column.cell.f32.k(len, valid, Array.get(F32, data, i))

def Column.cell.str.k(len: U32, valid: Valid, r: Array<String> & String) -> Column & Cell:
  (d2, x) = r
  (CStr{len, valid, d2}, VStr{x})

def Column.cell.str(len: U32, +i: U32, vb: Valid & Bool, data: Array<String>) -> Column & Cell:
  (valid, ok) = vb
  match ok:
    case False{}:
      (CStr{len, valid, data}, Null{})
    case True{}:
      Column.cell.str.k(len, valid, Array.get(String, data, i))

# read cell i of a column: the column comes back beside the cell
def Column.cell(c: Column, +i: U32) -> Column & Cell:
  match c:
    case CBool{len, valid, data}:
      Column.cell.bool(len, i, Valid.get(valid, i), data)
    case CU32{len, valid, data}:
      Column.cell.u32(len, i, Valid.get(valid, i), data)
    case CF32{len, valid, data}:
      Column.cell.f32(len, i, Valid.get(valid, i), data)
    case CStr{len, valid, data}:
      Column.cell.str(len, i, Valid.get(valid, i), data)

# a frame can also be kept as a Map from name to column
def Frame.to_map(cols: List<&1, Named>, m: Map<&1, Column>) -> Map<&1, Column>:
  match cols:
    case Nil{}:
      m
    case Named{n, c} <> rest:
      Frame.to_map(rest, Map.set(&1, Column, m, n, c))

def show_cell(r: Column & Cell) -> String:
  (c, cell) = r
  Cell.show(cell)

def show_pop(r: Map<&1, Column> & Maybe<&1, Column>) -> String:
  (m, mc) = r
  match mc:
    case None{}:
      "missing"
    case Some{c}:
      show_cell(Column.cell(c, 1))

# a do block takes no destructuring let: open the frame in a helper
def Frame.cols(f: Frame) -> List<&1, Named>:
  match f:
    case Frame{h, cols}:
      cols

def main() -> IO(Unit):
  do IO<Unit>:
    f32s : Column = CF32{3, Bits{[5 : U32*1n]}, [2.5 : F32*4n]}
    strs : Column = CStr{3, AllValid{}, Array.set(String, ["x" : String*4n], 1, "hello")}
    fr : Frame = Frame{3, [Named{"f", f32s}, Named{"s", strs}]}
    m : Map<&1, Column> = Frame.to_map(Frame.cols(fr), Map.new(&1, Column))
    IO.print(show_pop(Map.pop(&1, Column, m, "s")))
    IO.print(show_cell(Column.cell(CF32{3, Bits{[5 : U32*1n]}, [2.5 : F32*4n]}, 1)))
    IO.print(show_cell(Column.cell(CF32{3, Bits{[5 : U32*1n]}, [2.5 : F32*4n]}, 2)))

#|hello
#|null
#|2.5
