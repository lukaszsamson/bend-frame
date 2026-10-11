# src/column.bend -- Valid, Column, Named, Frame and their ops. DESIGN.md 4.4.
#
# Idioms (DESIGN.md section 9):
#  * helpers above callers; the only recursion is structural / Nat fuel;
#  * a call that answers a pair is taken apart in the NEXT helper's parameter
#    (`(a, x) = r`); a `match` on a parameter comes BEFORE any destructuring let;
#  * loops over a list thread their state as a pair PARAMETER and build the
#    next state through non-recursive step helpers called in the recursive
#    call's argument list;
#  * validity-only work goes through `Column.take_valid` / `Column.set_valid`,
#    data-only work through the per-dtype `*.data` helpers, so each op has one
#    five-way dispatch instead of several.
import Base
import ./dtype.bend as D
import ./err.bend as E
import ./kernels.bend as K
import ./strs.bend as ST

# validity as 0/1 words, one per row, so it is also what comparisons yield
type Valid is Type:
  AllValid{}
  Mask{m: Array<U32>}

# len rows live in an array of 2^depth slots (len <= 2^depth); Bool and I32
# share the U32 word buffer (0/1 words; two's complement bits). A Str column's
# data is one of two storages (src/strs.bend, M4): ST.SRaw{Array<String>} or
# ST.SDict{codes, dict} (Dictionary); both decode to the same rows, and every
# operation answers the same values for both (tests/strs_decode.bend).
type Column is Type:
  CBool{len: U32, depth: Nat, valid: Valid, data: Array<U32>}
  CU32{len: U32, depth: Nat, valid: Valid, data: Array<U32>}
  CI32{len: U32, depth: Nat, valid: Valid, data: Array<U32>}
  CF32{len: U32, depth: Nat, valid: Valid, data: Array<F32>}
  CStr{len: U32, depth: Nat, valid: Valid, data: ST.Strs}

type Named is Type:
  Named{name: String, col: Column}

type Frame is Type:
  Frame{height: U32, cols: List<&1, Named>}

# Data summary of a frame: height and column names (for checks without ownership)
type FInfo is Data:
  FInfo{h: U32, names: List<&2, String>}

# ---- Valid ------------------------------------------------------------------

def Valid.get.k(r: Array<U32> & U32) -> Valid & Bool:
  (m, w) = r
  (Mask{m}, U32.is_ne(w, 0))

# is row i valid? hands the mask back
def Valid.get(v: Valid, +i: U32) -> Valid & Bool:
  match v:
    case AllValid{}:
      (AllValid{}, True{})
    case Mask{m}:
      Valid.get.k(Array.get(U32, m, i))

def Valid.clone.k(r: Array<U32> & Array<U32>) -> Valid & Valid:
  (a, b) = r
  (Mask{a}, Mask{b})

def Valid.clone(v: Valid) -> Valid & Valid:
  match v:
    case AllValid{}:
      (AllValid{}, AllValid{})
    case Mask{m}:
      Valid.clone.k(Array.clone(U32, m))

# the number of valid rows among the first n
def Valid.count.k(+n: U32, r: Array<U32> & U32) -> Valid & U32:
  (m, k) = r
  (Mask{m}, k)

def Valid.count(v: Valid, +n: U32) -> Valid & U32:
  match v:
    case AllValid{}:
      (AllValid{}, n)
    case Mask{m}:
      Valid.count.k(n, K.Kernel.popcount(n, m))

# rows perm[0..n) of the validity, into 2^d slots; perm comes back
def Valid.gather.k(r: Array<U32> & Array<U32>) -> Valid & Array<U32>:
  (out, perm) = r
  (Mask{out}, perm)

def Valid.gather(v: Valid, perm: Array<U32>, +n: U32, +d: Nat) -> Valid & Array<U32>:
  match v:
    case AllValid{}:
      (AllValid{}, perm)
    case Mask{m}:
      Valid.gather.k(K.Kernel.gather(~U32, n, d, m, perm, 0))

# rows of the validity where mask = 1, into 2^d slots; mask comes back
def Valid.compact.k(r: Array<U32> & Array<U32>) -> Valid & Array<U32>:
  (out, mask) = r
  (Mask{out}, mask)

def Valid.compact(v: Valid, mask: Array<U32>, +n: U32, +d: Nat) -> Valid & Array<U32>:
  match v:
    case AllValid{}:
      (AllValid{}, mask)
    case Mask{m}:
      Valid.compact.k(K.Kernel.compact_keep(~U32, n, d, m, mask, 0))

# the validity as a mask array of 2^d slots (ones when AllValid)
def Valid.materialize(v: Valid, +d: Nat) -> Array<U32>:
  match v:
    case AllValid{}:
      Array.new(U32, d, 1)
    case Mask{m}:
      m

# ---- Column: structure --------------------------------------------------------

# a Column over a U32 word buffer of the given dtype (Bool, U32 or I32)
def Column.mk_w(t: D.DType, len: U32, depth: Nat, valid: Valid, data: Array<U32>) -> Column:
  match t:
    case D.TBool{}:
      CBool{len, depth, valid, data}
    case D.TI32{}:
      CI32{len, depth, valid, data}
    case _:
      CU32{len, depth, valid, data}

def Column.len(c: Column) -> Column & U32:
  match c:
    case CBool{+len, depth, valid, data}:
      (CBool{len, depth, valid, data}, len)
    case CU32{+len, depth, valid, data}:
      (CU32{len, depth, valid, data}, len)
    case CI32{+len, depth, valid, data}:
      (CI32{len, depth, valid, data}, len)
    case CF32{+len, depth, valid, data}:
      (CF32{len, depth, valid, data}, len)
    case CStr{+len, depth, valid, data}:
      (CStr{len, depth, valid, data}, len)

def Column.depth(c: Column) -> Column & Nat:
  match c:
    case CBool{len, +depth, valid, data}:
      (CBool{len, depth, valid, data}, depth)
    case CU32{len, +depth, valid, data}:
      (CU32{len, depth, valid, data}, depth)
    case CI32{len, +depth, valid, data}:
      (CI32{len, depth, valid, data}, depth)
    case CF32{len, +depth, valid, data}:
      (CF32{len, depth, valid, data}, depth)
    case CStr{len, +depth, valid, data}:
      (CStr{len, depth, valid, data}, depth)

def Column.dtype(c: Column) -> Column & D.DType:
  match c:
    case CBool{len, depth, valid, data}:
      (CBool{len, depth, valid, data}, D.TBool{})
    case CU32{len, depth, valid, data}:
      (CU32{len, depth, valid, data}, D.TU32{})
    case CI32{len, depth, valid, data}:
      (CI32{len, depth, valid, data}, D.TI32{})
    case CF32{len, depth, valid, data}:
      (CF32{len, depth, valid, data}, D.TF32{})
    case CStr{len, depth, valid, data}:
      (CStr{len, depth, valid, data}, D.TStr{})

# the validity out of the column (which keeps AllValid in its place)
def Column.take_valid(c: Column) -> Column & Valid:
  match c:
    case CBool{len, depth, valid, data}:
      (CBool{len, depth, AllValid{}, data}, valid)
    case CU32{len, depth, valid, data}:
      (CU32{len, depth, AllValid{}, data}, valid)
    case CI32{len, depth, valid, data}:
      (CI32{len, depth, AllValid{}, data}, valid)
    case CF32{len, depth, valid, data}:
      (CF32{len, depth, AllValid{}, data}, valid)
    case CStr{len, depth, valid, data}:
      (CStr{len, depth, AllValid{}, data}, valid)

# replace the column's validity (the old one is dropped)
def Column.set_valid(c: Column, v: Valid) -> Column:
  match c:
    case CBool{len, depth, valid, data}:
      CBool{len, depth, v, data}
    case CU32{len, depth, valid, data}:
      CU32{len, depth, v, data}
    case CI32{len, depth, valid, data}:
      CI32{len, depth, v, data}
    case CF32{len, depth, valid, data}:
      CF32{len, depth, v, data}
    case CStr{len, depth, valid, data}:
      CStr{len, depth, v, data}

# len := min(n, len); the arrays are untouched
def Column.head(c: Column, +n: U32) -> Column:
  match c:
    case CBool{len, depth, valid, data}:
      CBool{U32.min(n, len), depth, valid, data}
    case CU32{len, depth, valid, data}:
      CU32{U32.min(n, len), depth, valid, data}
    case CI32{len, depth, valid, data}:
      CI32{U32.min(n, len), depth, valid, data}
    case CF32{len, depth, valid, data}:
      CF32{U32.min(n, len), depth, valid, data}
    case CStr{len, depth, valid, data}:
      CStr{U32.min(n, len), depth, valid, data}

def Column.rename(nc: Named, name: String) -> Named:
  match nc:
    case Named{old, col}:
      Named{name, col}

# ---- Column: cells ------------------------------------------------------------

def Column.cell.word(t: D.DType, x: U32) -> D.Scalar:
  match t:
    case D.TBool{}:
      D.SBool{U32.is_ne(x, 0)}
    case D.TI32{}:
      D.SI32{D.I32{x}}
    case _:
      D.SU32{x}

def Column.cell.w(+t: D.DType, len: U32, depth: Nat, valid: Valid, r: Array<U32> & U32) -> Column & D.Scalar:
  (data, x) = r
  (Column.mk_w(t, len, depth, valid, data), Column.cell.word(t, x))

def Column.cell.f(len: U32, depth: Nat, valid: Valid, r: Array<F32> & F32) -> Column & D.Scalar:
  (data, x) = r
  (CF32{len, depth, valid, data}, D.SF32{x})

def Column.cell.s(len: U32, depth: Nat, valid: Valid, r: ST.Strs & String) -> Column & D.Scalar:
  (data, x) = r
  (CStr{len, depth, valid, data}, D.SStr{x})

# the data slot i as a scalar, ignoring validity
def Column.data_cell(c: Column, +i: U32) -> Column & D.Scalar:
  match c:
    case CBool{len, depth, valid, data}:
      Column.cell.w(D.TBool{}, len, depth, valid, Array.get(U32, data, i))
    case CU32{len, depth, valid, data}:
      Column.cell.w(D.TU32{}, len, depth, valid, Array.get(U32, data, i))
    case CI32{len, depth, valid, data}:
      Column.cell.w(D.TI32{}, len, depth, valid, Array.get(U32, data, i))
    case CF32{len, depth, valid, data}:
      Column.cell.f(len, depth, valid, Array.get(F32, data, i))
    case CStr{len, depth, valid, data}:
      Column.cell.s(len, depth, valid, ST.Strs.get(data, i))

def Column.cell.c(ok: Bool, +i: U32, c: Column) -> Column & D.Scalar:
  match ok:
    case True{}:
      Column.data_cell(c, i)
    case False{}:
      (c, D.SNull{})

def Column.cell.b(+i: U32, c: Column, r: Valid & Bool) -> Column & D.Scalar:
  (v, ok) = r
  Column.cell.c(ok, i, Column.set_valid(c, v))

def Column.cell.a(+i: U32, r: Column & Valid) -> Column & D.Scalar:
  (c, v) = r
  Column.cell.b(i, c, Valid.get(v, i))

# row i as a scalar (SNull when invalid); the column comes back
def Column.cell(c: Column, +i: U32) -> Column & D.Scalar:
  Column.cell.a(i, Column.take_valid(c))

# cells off .. off+n-1 as a list in order; the loop reads from the last row
# down, consing, so the list comes out ascending
def Column.scalars.go(n: Nat, i: U32, acc: List<&2, D.Scalar>, r: Column & D.Scalar) -> Column & List<&2, D.Scalar>:
  match n:
    case 0n:
      (c, s) = r
      (c, acc)
    case 1n+p:
      (c, s) = r
      +j = U32.sub(i, 1)
      Column.scalars.go(p, j, s <> acc, Column.cell(c, j))

def Column.scalars(c: Column, +off: U32, +n: U32) -> Column & List<&2, D.Scalar>:
  +last = U32.sub(U32.add(off, n), 1)
  Column.scalars.go(U32.to_nat(n), last, Nil{}, Column.cell(c, last))

def Column.to_scalars.a(r: Column & U32) -> Column & List<&2, D.Scalar>:
  (c, +n) = r
  Column.scalars(c, 0, n)

def Column.to_scalars(c: Column) -> Column & List<&2, D.Scalar>:
  Column.to_scalars.a(Column.len(c))

# ---- Column: null count -------------------------------------------------------

def Column.null_count.c(+n: U32, c: Column, r: Valid & U32) -> Column & U32:
  (v, k) = r
  (Column.set_valid(c, v), U32.sub(n, k))

def Column.null_count.b(+n: U32, r: Column & Valid) -> Column & U32:
  (c, v) = r
  Column.null_count.c(n, c, Valid.count(v, n))

def Column.null_count.a(r: Column & U32) -> Column & U32:
  (c, +n) = r
  Column.null_count.b(n, Column.take_valid(c))

def Column.null_count(c: Column) -> Column & U32:
  Column.null_count.a(Column.len(c))

# ---- Column: from scalars -----------------------------------------------------

# a null fits every dtype
def Column.fs.fits(+s: D.Scalar, +t: D.DType) -> Bool:
  match s:
    case D.SNull{}:
      True{}
    case D.SBool{b}:
      D.DType.eq(D.TBool{}, t)
    case D.SU32{v}:
      D.DType.eq(D.TU32{}, t)
    case D.SI32{v}:
      D.DType.eq(D.TI32{}, t)
    case D.SF32{v}:
      D.DType.eq(D.TF32{}, t)
    case D.SStr{s2}:
      D.DType.eq(D.TStr{}, t)

def Column.fs.got(s: D.Scalar) -> String:
  match s:
    case D.SNull{}:
      "null"
    case D.SBool{b}:
      "bool"
    case D.SU32{v}:
      "u32"
    case D.SI32{v}:
      "i32"
    case D.SF32{v}:
      "f32"
    case D.SStr{s2}:
      "str"

# the first scalar that does not fit, carried as an accumulator
def Column.fs.pick(found: Maybe<&2, D.Scalar>, ok: Bool, h: D.Scalar) -> Maybe<&2, D.Scalar>:
  match found ok:
    case Some{x} _:
      Some{x}
    case None{} True{}:
      None{}
    case None{} False{}:
      Some{h}

def Column.fs.bad(xs: List<&2, D.Scalar>, +t: D.DType, found: Maybe<&2, D.Scalar>) -> Maybe<&2, D.Scalar>:
  match xs:
    case Nil{}:
      found
    case +h <> rest:
      Column.fs.bad(rest, t, Column.fs.pick(found, Column.fs.fits(h, t), h))

def Column.fs.word(s: D.Scalar) -> U32:
  match s:
    case D.SBool{b}:
      Bool.to_u32(b)
    case D.SU32{v}:
      v
    case D.SI32{v}:
      D.I32.to_u32(v)
    case _:
      0

def Column.fs.f32(s: D.Scalar) -> F32:
  match s:
    case D.SF32{v}:
      v
    case _:
      0.0

def Column.fs.str(s: D.Scalar) -> String:
  match s:
    case D.SStr{v}:
      v
    case _:
      ""

def Column.fs.vword(s: D.Scalar) -> U32:
  match s:
    case D.SNull{}:
      0
    case _:
      1

# the per-row lists are built reversed by a tail call, then reversed: a non-tail recursion
# over a list of ~2^15 or more rows overflows the interpreter's (JS lane) stack (NEW-2)
def Column.fs.words.rev(xs: List<&2, D.Scalar>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      Column.fs.words.rev(t, Column.fs.word(h) <> acc)

def Column.fs.words(xs: List<&2, D.Scalar>) -> List<&2, U32>:
  List.reverse(&2, U32, Column.fs.words.rev(xs, Nil{}))

def Column.fs.f32s.rev(xs: List<&2, D.Scalar>, acc: List<&2, F32>) -> List<&2, F32>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      Column.fs.f32s.rev(t, Column.fs.f32(h) <> acc)

def Column.fs.f32s(xs: List<&2, D.Scalar>) -> List<&2, F32>:
  List.reverse(&2, F32, Column.fs.f32s.rev(xs, Nil{}))

def Column.fs.strs.rev(xs: List<&2, D.Scalar>, acc: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      Column.fs.strs.rev(t, Column.fs.str(h) <> acc)

def Column.fs.strs(xs: List<&2, D.Scalar>) -> List<&2, String>:
  List.reverse(&2, String, Column.fs.strs.rev(xs, Nil{}))

def Column.fs.vwords.rev(xs: List<&2, D.Scalar>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      Column.fs.vwords.rev(t, Column.fs.vword(h) <> acc)

def Column.fs.vwords(xs: List<&2, D.Scalar>) -> List<&2, U32>:
  List.reverse(&2, U32, Column.fs.vwords.rev(xs, Nil{}))

def Column.fs.nulls(xs: List<&2, D.Scalar>, acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      Column.fs.nulls(t, U32.add(acc, U32.sub(1, Column.fs.vword(h))))

def Column.fs.valid.mask(r: U32 & Array<U32>) -> Valid:
  (n, a) = r
  Mask{a}

def Column.fs.valid.if(allv: Bool, +xs: List<&2, D.Scalar>) -> Valid:
  match allv:
    case True{}:
      AllValid{}
    case False{}:
      Column.fs.valid.mask(K.Kernel.from_list(~U32, Column.fs.vwords(xs), 1))

def Column.fs.valid(+xs: List<&2, D.Scalar>) -> Valid:
  Column.fs.valid.if(U32.is_zero(Column.fs.nulls(xs, 0)), xs)

def Column.fs.w(t: D.DType, valid: Valid, r: U32 & Array<U32>) -> Column:
  (+len, data) = r
  Column.mk_w(t, len, K.Kernel.depth_for(len), valid, data)

def Column.fs.f(valid: Valid, r: U32 & Array<F32>) -> Column:
  (+len, data) = r
  CF32{len, K.Kernel.depth_for(len), valid, data}

def Column.fs.s(valid: Valid, r: U32 & Array<String>) -> Column:
  (+len, data) = r
  CStr{len, K.Kernel.depth_for(len), valid, ST.SRaw{data}}

def Column.fs.build(t: D.DType, +xs: List<&2, D.Scalar>) -> Column:
  match t:
    case D.TBool{}:
      Column.fs.w(D.TBool{}, Column.fs.valid(xs), K.Kernel.from_list(~U32, Column.fs.words(xs), 0))
    case D.TU32{}:
      Column.fs.w(D.TU32{}, Column.fs.valid(xs), K.Kernel.from_list(~U32, Column.fs.words(xs), 0))
    case D.TI32{}:
      Column.fs.w(D.TI32{}, Column.fs.valid(xs), K.Kernel.from_list(~U32, Column.fs.words(xs), 0))
    case D.TF32{}:
      Column.fs.f(Column.fs.valid(xs), K.Kernel.from_list(~F32, Column.fs.f32s(xs), 0.0))
    case D.TStr{}:
      Column.fs.s(Column.fs.valid(xs), K.Kernel.from_list(~String, Column.fs.strs(xs), ""))

def Column.fs.go(bad: Maybe<&2, D.Scalar>, +xs: List<&2, D.Scalar>, +t: D.DType) -> E.ResT(Column):
  match bad:
    case Some{s}:
      Fail{E.TypeMismatch{"from_scalars", D.DType.show(t), Column.fs.got(s)}}
    case None{}:
      Done{Column.fs.build(t, xs)}

# the row cap (DESIGN.md 15.8): a list longer than the cap is refused before any array is built
def Column.fs.cap(over: Maybe<&2, E.Err>, +xs: List<&2, D.Scalar>, +t: D.DType) -> E.ResT(Column):
  match over:
    case Some{e}:
      Fail{e}
    case None{}:
      Column.fs.go(Column.fs.bad(xs, t, None{}), xs, t)

# from_scalars with the cap as a parameter (the entry the tests use with a lowered cap)
def Column.from_scalars.cap(+cap: U32, +xs: List<&2, D.Scalar>, +t: D.DType) -> E.ResT(Column):
  Column.fs.cap(K.Kernel.check_rows.cap(cap, K.Kernel.count(~D.Scalar, xs, 0)), xs, t)

# SNull becomes an invalid row (slot = the dtype default); a scalar of another
# dtype is a TypeMismatch; more than K.Kernel.max_rows() scalars are an InvalidOperation
def Column.from_scalars(+xs: List<&2, D.Scalar>, +t: D.DType) -> E.ResT(Column):
  Column.from_scalars.cap(K.Kernel.max_rows(), xs, t)

# ---- Column: clone / gather / compact -------------------------------------------

def Column.clone.w(+t: D.DType, +len: U32, +depth: Nat, vv: Valid & Valid, dd: Array<U32> & Array<U32>) -> Column & Column:
  (v1, v2) = vv
  (d1, d2) = dd
  (Column.mk_w(t, len, depth, v1, d1), Column.mk_w(t, len, depth, v2, d2))

def Column.clone.f(+len: U32, +depth: Nat, vv: Valid & Valid, dd: Array<F32> & Array<F32>) -> Column & Column:
  (v1, v2) = vv
  (d1, d2) = dd
  (CF32{len, depth, v1, d1}, CF32{len, depth, v2, d2})

def Column.clone.s(+len: U32, +depth: Nat, vv: Valid & Valid, dd: ST.Strs & ST.Strs) -> Column & Column:
  (v1, v2) = vv
  (d1, d2) = dd
  (CStr{len, depth, v1, d1}, CStr{len, depth, v2, d2})

# O(n) copy of every buffer
def Column.clone(c: Column) -> Column & Column:
  match c:
    case CBool{len, depth, valid, data}:
      Column.clone.w(D.TBool{}, len, depth, Valid.clone(valid), Array.clone(U32, data))
    case CU32{len, depth, valid, data}:
      Column.clone.w(D.TU32{}, len, depth, Valid.clone(valid), Array.clone(U32, data))
    case CI32{len, depth, valid, data}:
      Column.clone.w(D.TI32{}, len, depth, Valid.clone(valid), Array.clone(U32, data))
    case CF32{len, depth, valid, data}:
      Column.clone.f(len, depth, Valid.clone(valid), Array.clone(F32, data))
    case CStr{len, depth, valid, data}:
      Column.clone.s(len, depth, Valid.clone(valid), ST.Strs.clone(data))

# a result column of n rows in 2^d slots with no validity, plus the index/mask
# array the kernel handed back (shared by gather and compact)
def Column.out.w(t: D.DType, +n: U32, +d: Nat, r: Array<U32> & Array<U32>) -> Column & Array<U32>:
  (out, ix) = r
  (Column.mk_w(t, n, d, AllValid{}, out), ix)

def Column.out.f(+n: U32, +d: Nat, r: Array<F32> & Array<U32>) -> Column & Array<U32>:
  (out, ix) = r
  (CF32{n, d, AllValid{}, out}, ix)

def Column.out.s(+n: U32, +d: Nat, r: ST.Strs & Array<U32>) -> Column & Array<U32>:
  (out, ix) = r
  (CStr{n, d, AllValid{}, out}, ix)

# data only (validity dropped): rows perm[0..n) into 2^d slots
def Column.gather.data(c: Column, perm: Array<U32>, +n: U32, +d: Nat) -> Column & Array<U32>:
  match c:
    case CBool{len, depth, valid, data}:
      Column.out.w(D.TBool{}, n, d, K.Kernel.gather(~U32, n, d, data, perm, 0))
    case CU32{len, depth, valid, data}:
      Column.out.w(D.TU32{}, n, d, K.Kernel.gather(~U32, n, d, data, perm, 0))
    case CI32{len, depth, valid, data}:
      Column.out.w(D.TI32{}, n, d, K.Kernel.gather(~U32, n, d, data, perm, 0))
    case CF32{len, depth, valid, data}:
      Column.out.f(n, d, K.Kernel.gather(~F32, n, d, data, perm, 0.0))
    case CStr{len, depth, valid, data}:
      Column.out.s(n, d, ST.Strs.gather(data, perm, n, d))

def Column.gather.d(v: Valid, r: Column & Array<U32>) -> Column & Array<U32>:
  (c, perm) = r
  (Column.set_valid(c, v), perm)

def Column.gather.c(c: Column, +n: U32, +d: Nat, r: Valid & Array<U32>) -> Column & Array<U32>:
  (v, perm) = r
  Column.gather.d(v, Column.gather.data(c, perm, n, d))

def Column.gather.b(+n: U32, +d: Nat, perm: Array<U32>, r: Column & Valid) -> Column & Array<U32>:
  (c, v) = r
  Column.gather.c(c, n, d, Valid.gather(v, perm, n, d))

# rows perm[0..n) with validity gathered too; the result has depth_for(n);
# perm comes back. Out-of-range indices wrap (indexes wrap around).
def Column.gather(c: Column, perm: Array<U32>, +n: U32) -> Column & Array<U32>:
  Column.gather.b(n, K.Kernel.depth_for(n), perm, Column.take_valid(c))

# data only: the first n rows where mask = 1 into 2^d slots (n = len); mask back
def Column.compact.data(c: Column, mask: Array<U32>, +kept: U32, +d: Nat) -> Column & Array<U32>:
  match c:
    case CBool{+len, depth, valid, data}:
      Column.out.w(D.TBool{}, kept, d, K.Kernel.compact_keep(~U32, len, d, data, mask, 0))
    case CU32{+len, depth, valid, data}:
      Column.out.w(D.TU32{}, kept, d, K.Kernel.compact_keep(~U32, len, d, data, mask, 0))
    case CI32{+len, depth, valid, data}:
      Column.out.w(D.TI32{}, kept, d, K.Kernel.compact_keep(~U32, len, d, data, mask, 0))
    case CF32{+len, depth, valid, data}:
      Column.out.f(kept, d, K.Kernel.compact_keep(~F32, len, d, data, mask, 0.0))
    case CStr{+len, depth, valid, data}:
      Column.out.s(kept, d, ST.Strs.compact(data, mask, len, d))

def Column.compact.c(c: Column, +kept: U32, +d: Nat, r: Valid & Array<U32>) -> Column & Array<U32>:
  (v, mask) = r
  Column.gather.d(v, Column.compact.data(c, mask, kept, d))

def Column.compact.b(+n: U32, +kept: U32, +d: Nat, mask: Array<U32>, r: Column & Valid) -> Column & Array<U32>:
  (c, v) = r
  Column.compact.c(c, kept, d, Valid.compact(v, mask, n, d))

def Column.compact.a(+kept: U32, mask: Array<U32>, r: Column & U32) -> Column & Array<U32>:
  (c, +n) = r
  Column.compact.b(n, kept, K.Kernel.depth_for(U32.add(kept, 1)), mask, Column.take_valid(c))

# the rows where mask = 1 (0/1 words; `kept` = their count) with validity
# compacted too; the result has depth_for(kept + 1): Kernel.compact_keep
# writes every dropped row into slot `kept` (overwritten later or left as
# garbage), so the output needs MORE than `kept` slots, else a dropped row
# after the last kept one wraps around into slot 0 (M2 fix). Mask comes back
# so one mask can filter every column
def Column.compact(c: Column, mask: Array<U32>, +kept: U32) -> Column & Array<U32>:
  Column.compact.a(kept, mask, Column.len(c))

# rows off .. off+n-1 (clamped to the column)
def Column.slice.c(r: Column & Array<U32>) -> Column:
  (c, perm) = r
  c

# rows off .. off+m-1 by one range copy per buffer (Kernel.range, W1f; it was a gather by an
# iota index array: a 4 MB index for 1M rows). The validity: AllValid stays, a Mask is range
# copied too. Str: a Raw slice copies the strings, a Dictionary slice keeps the dictionary and
# range copies the codes.
def Valid.range(v: Valid, +off: U32, +m: U32, +d: Nat) -> Valid:
  match v:
    case AllValid{}:
      AllValid{}
    case Mask{mk}:
      Mask{K.Kernel.range(~U32, m, d, off, mk, 0)}

def Column.slice.s(s: ST.Strs, +off: U32, +m: U32, +d: Nat) -> ST.Strs:
  match s:
    case ST.SRaw{a}:
      ST.SRaw{K.Kernel.range(~String, m, d, off, a, "")}
    case ST.SDict{codes, dict}:
      ST.SDict{K.Kernel.range(~U32, m, d, off, codes, 0), dict}

def Column.slice.r(c: Column, +off: U32, +m: U32, +d: Nat) -> Column:
  match c:
    case CBool{len, depth, valid, data}:
      CBool{m, d, Valid.range(valid, off, m, d), K.Kernel.range(~U32, m, d, off, data, 0)}
    case CU32{len, depth, valid, data}:
      CU32{m, d, Valid.range(valid, off, m, d), K.Kernel.range(~U32, m, d, off, data, 0)}
    case CI32{len, depth, valid, data}:
      CI32{m, d, Valid.range(valid, off, m, d), K.Kernel.range(~U32, m, d, off, data, 0)}
    case CF32{len, depth, valid, data}:
      CF32{m, d, Valid.range(valid, off, m, d), K.Kernel.range(~F32, m, d, off, data, 0.0)}
    case CStr{len, depth, valid, data}:
      CStr{m, d, Valid.range(valid, off, m, d), Column.slice.s(data, off, m, d)}

def Column.slice.b(c: Column, +off: U32, +m: U32) -> Column:
  Column.slice.r(c, off, m, K.Kernel.depth_for(m))

def Column.slice.a(+off: U32, +n: U32, r: Column & U32) -> Column:
  (c, +len) = r
  Column.slice.b(c, off, U32.min(n, Bool.pick(U32, U32.is_lt(off, len), U32.sub(len, off), 0)))

def Column.slice(c: Column, +off: U32, +n: U32) -> Column:
  Column.slice.a(off, n, Column.len(c))

# ---- Str storage (M4: Raw / Dictionary) --------------------------------------------
# The dtype is Str either way; every other dtype passes through unchanged.

# is the column a Dictionary-encoded Str column? (the column comes back)
def Column.is_dict.k(+n: U32, +d: Nat, v: Valid, r: ST.Strs & Bool) -> Column & Bool:
  (x, b) = r
  (CStr{n, d, v, x}, b)

def Column.is_dict(c: Column) -> Column & Bool:
  match c:
    case CStr{+n, +d, v, x}:
      Column.is_dict.k(n, d, v, ST.Strs.is_dict(x))
    case other:
      (other, False{})

# the Dictionary form of a Str column (an already encoded one is kept)
def Column.encode(c: Column) -> Column:
  match c:
    case CStr{+n, +d, v, x}:
      CStr{n, d, v, ST.Strs.encode(n, d, x)}
    case other:
      other

# the Raw form of a Str column (decoded: one gather)
def Column.decode(c: Column) -> Column:
  match c:
    case CStr{+n, +d, v, x}:
      CStr{n, d, v, ST.Strs.raw(n, d, x)}
    case other:
      other

def Column.recode(dict: Bool, c: Column) -> Column:
  match dict:
    case True{}:
      Column.encode(c)
    case False{}:
      Column.decode(c)

def Cols.encode(cols: List<&1, Named>, +dict: Bool) -> List<&1, Named>:
  match cols:
    case Nil{}:
      Nil{}
    case Named{n, c} <> rest:
      Named{n, Column.recode(dict, c)} <> Cols.encode(rest, dict)

# every Str column of the frame in the Dictionary form (dict) or the Raw form (not dict)
def Frame.encode(f: Frame, +dict: Bool) -> Frame:
  match f:
    case Frame{h, cols}:
      Frame{h, Cols.encode(cols, dict)}

# ---- Names (List<&2, String>) ---------------------------------------------------

def Names.has(ns: List<&2, String>, +name: String) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(String.eq(name, h), Names.has(t, name))

def Names.is_empty(ns: List<&2, String>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case h <> t:
      False{}

def Names.dup.pick(found: Maybe<&2, String>, d: Bool, h: String) -> Maybe<&2, String>:
  match found d:
    case Some{x} _:
      Some{x}
    case None{} True{}:
      Some{h}
    case None{} False{}:
      None{}

# the first name that repeats an earlier one; call with seen = [] and found = None
def Names.dup(ns: List<&2, String>, +seen: List<&2, String>, found: Maybe<&2, String>) -> Maybe<&2, String>:
  match ns:
    case Nil{}:
      found
    case +h <> t:
      Names.dup(t, h <> seen, Names.dup.pick(found, Names.has(seen, h), h))

# ---- Frame: structure -------------------------------------------------------------

def Frame.empty() -> Frame:
  Frame{0, Nil{}}

def Frame.height(f: Frame) -> Frame & U32:
  match f:
    case Frame{+h, cols}:
      (Frame{h, cols}, h)

def Cols.names.k(+n: String, c: Column, r: List<&1, Named> & List<&2, String>) -> List<&1, Named> & List<&2, String>:
  (rest, ns) = r
  (Named{n, c} <> rest, n <> ns)

def Cols.names(cols: List<&1, Named>) -> List<&1, Named> & List<&2, String>:
  match cols:
    case Nil{}:
      (Nil{}, Nil{})
    case Named{+n, col} <> rest:
      Cols.names.k(n, col, Cols.names(rest))

def Frame.names.k(+h: U32, r: List<&1, Named> & List<&2, String>) -> Frame & List<&2, String>:
  (cols, ns) = r
  (Frame{h, cols}, ns)

def Frame.names(f: Frame) -> Frame & List<&2, String>:
  match f:
    case Frame{+h, cols}:
      Frame.names.k(h, Cols.names(cols))

def Frame.info.k(+h: U32, r: List<&1, Named> & List<&2, String>) -> Frame & FInfo:
  (cols, ns) = r
  (Frame{h, cols}, FInfo{h, ns})

# height and names without taking the frame apart for good
def Frame.info(f: Frame) -> Frame & FInfo:
  match f:
    case Frame{+h, cols}:
      Frame.info.k(h, Cols.names(cols))

# remove a column by name (everything else keeps its order); the frame keeps its height
def Cols.take.k(eq: Bool, n: String, col: Column, r: List<&1, Named> & Maybe<&1, Column>) -> List<&1, Named> & Maybe<&1, Column>:
  match eq:
    case True{}:
      (rest, m) = r
      (rest, Some{col})
    case False{}:
      (rest, m) = r
      (Named{n, col} <> rest, m)

def Cols.take(cols: List<&1, Named>, +name: String) -> List<&1, Named> & Maybe<&1, Column>:
  match cols:
    case Nil{}:
      (Nil{}, None{})
    case Named{+n, col} <> rest:
      Cols.take.k(String.eq(name, n), n, col, Cols.take(rest, name))

def Frame.take.k(+h: U32, r: List<&1, Named> & Maybe<&1, Column>) -> Frame & Maybe<&1, Column>:
  (cols, m) = r
  (Frame{h, cols}, m)

def Frame.take(f: Frame, +name: String) -> Frame & Maybe<&1, Column>:
  match f:
    case Frame{+h, cols}:
      Frame.take.k(h, Cols.take(cols, name))

# ---- Frame: put / from_columns ------------------------------------------------------

# a Some means the column may not go in: duplicate name, or a height mismatch
# (an empty frame takes any height)
def FInfo.shape.k(ok: Bool, +h: U32, +n: U32) -> Maybe<&2, E.Err>:
  match ok:
    case True{}:
      None{}
    case False{}:
      Some{E.ShapeMismatch{h, n}}

def FInfo.shape(i: FInfo, +n: U32) -> Maybe<&2, E.Err>:
  match i:
    case FInfo{+h, ns}:
      FInfo.shape.k(Bool.or(Names.is_empty(ns), U32.is_eq(h, n)), h, n)

def FInfo.check.k(dup: Bool, i: FInfo, +name: String, +n: U32) -> Maybe<&2, E.Err>:
  match dup:
    case True{}:
      Some{E.DuplicateColumn{name}}
    case False{}:
      FInfo.shape(i, n)

def FInfo.check(i: FInfo, +name: String, +n: U32) -> Maybe<&2, E.Err>:
  match i:
    case FInfo{+h, +ns}:
      FInfo.check.k(Names.has(ns, name), FInfo{h, ns}, name, n)

def Frame.append(f: Frame, name: String, c: Column, +n: U32) -> Frame:
  match f:
    case Frame{h, cols}:
      Frame{n, List.append(&1, Named, cols, Named{name, c} <> Nil{})}

def Frame.put.b(err: Maybe<&2, E.Err>, f: Frame, name: String, c: Column, +n: U32) -> E.ResT(Frame):
  match err:
    case Some{e}:
      Fail{e}
    case None{}:
      Done{Frame.append(f, name, c, n)}

def Frame.put.a(+name: String, r1: Frame & FInfo, r2: Column & U32) -> E.ResT(Frame):
  (f, i) = r1
  (c, +n) = r2
  Frame.put.b(FInfo.check(i, name, n), f, name, c, n)

# append a column; DuplicateColumn if the name exists, ShapeMismatch if the
# length differs from the frame's height (an empty frame adopts the length)
def Frame.put(f: Frame, name: String, c: Column) -> E.ResT(Frame):
  Frame.put.a(name, Frame.info(f), Column.len(c))

def Frame.put.r(r: E.ResT(Frame), name: String, c: Column) -> E.ResT(Frame):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{f}:
      Frame.put(f, name, c)

def Frame.from_columns.go(cols: List<&1, Named>, r: E.ResT(Frame)) -> E.ResT(Frame):
  match cols:
    case Nil{}:
      r
    case Named{name, c} <> rest:
      Frame.from_columns.go(rest, Frame.put.r(r, name, c))

def Frame.from_columns(cols: List<&1, Named>) -> E.ResT(Frame):
  Frame.from_columns.go(cols, Done{Frame{0, Nil{}}})

# ---- Frame: replace (in place) / get_cloned ----------------------------------------------

# loop state: (columns so far, newest first) and the column still to place
def Cols.replace.fin(r: List<&1, Named> & Maybe<&1, Column>) -> List<&1, Named> & Maybe<&1, Column>:
  (acc, slot) = r
  (List.reverse(&1, Named, acc), slot)

def Cols.replace.pick(eq: Bool, n: String, col: Column, acc: List<&1, Named>, slot: Maybe<&1, Column>) -> List<&1, Named> & Maybe<&1, Column>:
  match eq slot:
    case True{} Some{c}:
      (Named{n, c} <> acc, None{})
    case True{} None{}:
      (Named{n, col} <> acc, None{})
    case False{} _:
      (Named{n, col} <> acc, slot)

def Cols.replace.step(eq: Bool, n: String, col: Column, r: List<&1, Named> & Maybe<&1, Column>) -> List<&1, Named> & Maybe<&1, Column>:
  (acc, slot) = r
  Cols.replace.pick(eq, n, col, acc, slot)

def Cols.replace.go(cols: List<&1, Named>, +name: String, r: List<&1, Named> & Maybe<&1, Column>) -> List<&1, Named> & Maybe<&1, Column>:
  match cols:
    case Nil{}:
      Cols.replace.fin(r)
    case Named{+n, col} <> rest:
      Cols.replace.go(rest, name, Cols.replace.step(String.eq(name, n), n, col, r))

def Frame.replace.d(+n: U32, name: String, r: List<&1, Named> & Maybe<&1, Column>) -> Frame:
  (cols, slot) = r
  match slot:
    case None{}:
      Frame{n, cols}
    case Some{c}:
      Frame{n, List.append(&1, Named, cols, Named{name, c} <> Nil{})}

def Frame.replace.c(f: Frame, +name: String, c: Column, +n: U32) -> Frame:
  match f:
    case Frame{h, cols}:
      Frame.replace.d(n, name, Cols.replace.go(cols, name, (Nil{}, Some{c})))

def Frame.replace.b(err: Maybe<&2, E.Err>, f: Frame, name: String, c: Column, +n: U32) -> E.ResT(Frame):
  match err:
    case Some{e}:
      Fail{e}
    case None{}:
      Done{Frame.replace.c(f, name, c, n)}

def Frame.replace.a(+name: String, r1: Frame & FInfo, r2: Column & U32) -> E.ResT(Frame):
  (f, i) = r1
  (c, +n) = r2
  Frame.replace.b(FInfo.shape(i, n), f, name, c, n)

# overwrite the column `name` in place, or append it (with_columns semantics);
# ShapeMismatch if the length differs from the height
def Frame.replace(f: Frame, name: String, c: Column) -> E.ResT(Frame):
  Frame.replace.a(name, Frame.info(f), Column.len(c))

def Cols.cg.cl(n: String, acc: List<&1, Named>, r: Column & Column) -> List<&1, Named> & Maybe<&1, Column>:
  (c1, c2) = r
  (Named{n, c1} <> acc, Some{c2})

def Cols.cg.step(eq: Bool, n: String, col: Column, r: List<&1, Named> & Maybe<&1, Column>) -> List<&1, Named> & Maybe<&1, Column>:
  match eq:
    case True{}:
      (acc, slot) = r
      Cols.cg.cl(n, acc, Column.clone(col))
    case False{}:
      (acc, slot) = r
      (Named{n, col} <> acc, slot)

def Cols.cg.go(cols: List<&1, Named>, +name: String, r: List<&1, Named> & Maybe<&1, Column>) -> List<&1, Named> & Maybe<&1, Column>:
  match cols:
    case Nil{}:
      Cols.replace.fin(r)
    case Named{+n, col} <> rest:
      Cols.cg.go(rest, name, Cols.cg.step(String.eq(name, n), n, col, r))

def Frame.get_cloned.k(+h: U32, name: String, r: List<&1, Named> & Maybe<&1, Column>) -> Frame & E.ResT(Column):
  (cols, slot) = r
  match slot:
    case None{}:
      (Frame{h, cols}, Fail{E.ColumnNotFound{name}})
    case Some{c}:
      (Frame{h, cols}, Done{c})

# a copy of the named column; the frame comes back unchanged (same column order)
def Frame.get_cloned(f: Frame, +name: String) -> Frame & E.ResT(Column):
  match f:
    case Frame{+h, cols}:
      Frame.get_cloned.k(h, name, Cols.cg.go(cols, name, (Nil{}, None{})))

# ---- Frame: lend (the move / borrow of DESIGN.md 16.2 rule 1) ----------------------------------

# (a hollow stand-in, the column): the stand-in has the column's constructor (dtype) and
# length and one empty slot. It holds no rows: it is never read, only replaced
# (Frame.replace) or dropped with its frame
def Column.hollow(c: Column) -> Column & Column:
  match c:
    case CBool{+len, depth, valid, data}:
      (CBool{len, 0n, AllValid{}, Array.new(U32, 0n, 0)}, CBool{len, depth, valid, data})
    case CU32{+len, depth, valid, data}:
      (CU32{len, 0n, AllValid{}, Array.new(U32, 0n, 0)}, CU32{len, depth, valid, data})
    case CI32{+len, depth, valid, data}:
      (CI32{len, 0n, AllValid{}, Array.new(U32, 0n, 0)}, CI32{len, depth, valid, data})
    case CF32{+len, depth, valid, data}:
      (CF32{len, 0n, AllValid{}, Array.new(F32, 0n, 0.0)}, CF32{len, depth, valid, data})
    case CStr{+len, depth, valid, data}:
      (CStr{len, 0n, AllValid{}, ST.SRaw{Array.new(String, 0n, "")}}, CStr{len, depth, valid, data})

def Cols.lend.k(n: String, acc: List<&1, Named>, r: Column & Column) -> List<&1, Named> & Maybe<&1, Column>:
  (hole, c) = r
  (Named{n, hole} <> acc, Some{c})

def Cols.lend.step(eq: Bool, n: String, col: Column, r: List<&1, Named> & Maybe<&1, Column>) -> List<&1, Named> & Maybe<&1, Column>:
  match eq:
    case True{}:
      (acc, slot) = r
      Cols.lend.k(n, acc, Column.hollow(col))
    case False{}:
      (acc, slot) = r
      (Named{n, col} <> acc, slot)

def Cols.lend.go(cols: List<&1, Named>, +name: String, r: List<&1, Named> & Maybe<&1, Column>) -> List<&1, Named> & Maybe<&1, Column>:
  match cols:
    case Nil{}:
      Cols.replace.fin(r)
    case Named{+n, col} <> rest:
      Cols.lend.go(rest, name, Cols.lend.step(String.eq(name, n), n, col, r))

def Frame.lend.k(+h: U32, name: String, r: List<&1, Named> & Maybe<&1, Column>) -> Frame & E.ResT(Column):
  (cols, slot) = r
  match slot:
    case None{}:
      (Frame{h, cols}, Fail{E.ColumnNotFound{name}})
    case Some{c}:
      (Frame{h, cols}, Done{c})

# the named column itself, moved out of the frame with NO copy; a hollow stand-in keeps its
# place, so names, dtypes, order and height are those of the input. The same walk as
# get_cloned with Column.hollow in place of Column.clone: the column answered is the one
# get_cloned would copy, and Frame.replace(f2, name, c) gives the input frame back (LAWS.bend
# lend_observes). Callers use it for a reference that is the column's last use within an
# operator whose output does not keep the input column (a move: select, an overwritten
# with_columns input, group_by), or put the column back with Frame.replace after a kernel
# handed it back (a borrow: unique's keys); DESIGN.md 16.2 rule 1
def Frame.lend(f: Frame, +name: String) -> Frame & E.ResT(Column):
  match f:
    case Frame{+h, cols}:
      Frame.lend.k(h, name, Cols.lend.go(cols, name, (Nil{}, None{})))

def Cols.clone.k(+n: String, cc: Column & Column, r: List<&1, Named> & List<&1, Named>) -> List<&1, Named> & List<&1, Named>:
  (c1, c2) = cc
  (a, b) = r
  (Named{n, c1} <> a, Named{n, c2} <> b)

def Cols.clone(cols: List<&1, Named>) -> List<&1, Named> & List<&1, Named>:
  match cols:
    case Nil{}:
      (Nil{}, Nil{})
    case Named{+n, col} <> rest:
      Cols.clone.k(n, Column.clone(col), Cols.clone(rest))

def Frame.clone.k(+h: U32, r: List<&1, Named> & List<&1, Named>) -> Frame & Frame:
  (a, b) = r
  (Frame{h, a}, Frame{h, b})

# an O(n) deep copy: two frames with the same height, names, order and cells
# (DESIGN.md 15.2.1 DF.clone; Exec clones a Source used more than once, 15.7)
def Frame.clone(f: Frame) -> Frame & Frame:
  match f:
    case Frame{+h, cols}:
      Frame.clone.k(h, Cols.clone(cols))

# ---- Frame: select_names / head / filter_mask ----------------------------------------------

def Frame.select.add(+name: String, acc: List<&1, Named>, r: Frame & Maybe<&1, Column>) -> E.ResT(Frame & List<&1, Named>):
  (f, m) = r
  match m:
    case None{}:
      Fail{E.ColumnNotFound{name}}
    case Some{c}:
      Done{(f, Named{name, c} <> acc)}

def Frame.select.step(+name: String, st: E.ResT(Frame & List<&1, Named>)) -> E.ResT(Frame & List<&1, Named>):
  match st:
    case Fail{e}:
      Fail{e}
    case Done{fa}:
      (f, acc) = fa
      Frame.select.add(name, acc, Frame.take(f, name))

def Frame.select.go(names: List<&2, String>, st: E.ResT(Frame & List<&1, Named>)) -> E.ResT(Frame & List<&1, Named>):
  match names:
    case Nil{}:
      st
    case name <> rest:
      Frame.select.go(rest, Frame.select.step(name, st))

def Frame.select.fin2(acc: List<&1, Named>, r: Frame & U32) -> E.ResT(Frame):
  (f, +h) = r
  Done{Frame{h, List.reverse(&1, Named, acc)}}

def Frame.select.fin(st: E.ResT(Frame & List<&1, Named>)) -> E.ResT(Frame):
  match st:
    case Fail{e}:
      Fail{e}
    case Done{fa}:
      (f, acc) = fa
      Frame.select.fin2(acc, Frame.height(f))

def Frame.select_names.a(d: Maybe<&2, String>, f: Frame, names: List<&2, String>) -> E.ResT(Frame):
  match d:
    case Some{n}:
      Fail{E.DuplicateColumn{n}}
    case None{}:
      Frame.select.fin(Frame.select.go(names, Done{(f, Nil{})}))

# a new frame with the named columns in the requested order (the rest is
# dropped); ColumnNotFound on a miss, DuplicateColumn on a repeated name
def Frame.select_names(f: Frame, +names: List<&2, String>) -> E.ResT(Frame):
  Frame.select_names.a(Names.dup(names, Nil{}, None{}), f, names)

def Cols.head(cols: List<&1, Named>, +n: U32) -> List<&1, Named>:
  match cols:
    case Nil{}:
      Nil{}
    case Named{name, col} <> rest:
      Named{name, Column.head(col, n)} <> Cols.head(rest, n)

# the first n rows (the arrays are untouched)
def Frame.head(f: Frame, +n: U32) -> Frame:
  match f:
    case Frame{h, cols}:
      Frame{U32.min(n, h), Cols.head(cols, n)}

def Cols.compact.add(n: String, acc: List<&1, Named>, r: Column & Array<U32>) -> Array<U32> & List<&1, Named>:
  (c, mask) = r
  (mask, Named{n, c} <> acc)

def Cols.compact.step(n: String, +kept: U32, col: Column, st: Array<U32> & List<&1, Named>) -> Array<U32> & List<&1, Named>:
  (mask, acc) = st
  Cols.compact.add(n, acc, Column.compact(col, mask, kept))

def Cols.compact.go(cols: List<&1, Named>, +kept: U32, st: Array<U32> & List<&1, Named>) -> Array<U32> & List<&1, Named>:
  match cols:
    case Nil{}:
      st
    case Named{n, col} <> rest:
      Cols.compact.go(rest, kept, Cols.compact.step(n, kept, col, st))

def Frame.filter_mask.k(+kept: U32, r: Array<U32> & List<&1, Named>) -> Frame:
  (mask, acc) = r
  Frame{kept, List.reverse(&1, Named, acc)}

# keep the rows where mask = 1 (0/1 words, `kept` of them); mask is consumed
def Frame.filter_mask(f: Frame, mask: Array<U32>, +kept: U32) -> Frame:
  match f:
    case Frame{h, cols}:
      Frame.filter_mask.k(kept, Cols.compact.go(cols, kept, (mask, Nil{})))
