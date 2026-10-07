# p13: how DESIGN.md signatures are checked without bodies. A `law` with a
# `for` list and a result type is an open claim: `bend --check-only` accepts
# it (it is just unproven), so a module skeleton can be type-checked before
# a line of implementation exists. Expected: prints SOME PROOFS FAIL? No --
# expected: checks (laws listed as open). See the run output.
#   ~/.bend/bin/bend probes/p13_signatures_only.bend --check-only
import Base

type DType is Data:
  TBool{}
  TU32{}
  TF32{}
  TStr{}

type Column is Type:
  CU32{len: U32, data: Array<U32>}
  CF32{len: U32, data: Array<F32>}

# signature stubs: a law per def, no body
law Column.len:
  for c: Column
  Column & U32

law Column.dtype:
  for c: Column
  Column & DType

law Column.head:
  for c: Column
  for +n: U32
  Column

# NOTE: live code may NOT call an unfilled law ("an unfilled law is a dead
# claim: live code cannot use it"), so stubs are for checking shapes only.
# The law-above/def-below pattern IS how a def calls one declared later.
