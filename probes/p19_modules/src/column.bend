import Base
import ./dtype.bend as D

type Column is Type:
  CU32{data: Array<U32>}
  CF32{data: Array<F32>}

def Column.dtype(c: Column) -> Column & D.DType:
  match c:
    case CU32{d}:
      (CU32{d}, D.TU32{})
    case CF32{d}:
      (CF32{d}, D.TF32{})
