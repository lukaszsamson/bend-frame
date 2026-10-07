# p19: module layout check -- a src/ module imported by another src/ module
# (relative to the importing file) and by the entry file at the root.
import Base

type DType is Data:
  TU32{}
  TF32{}

def DType.show(t: DType) -> String:
  match t:
    case TU32{}:
      "u32"
    case TF32{}:
      "f32"
