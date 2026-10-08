# Activated in M3 (table verbs: DF.concat_vertical). The lazy chain's cap is tests/table_concat_cap.bend.
# B04-i (DESIGN.md 15.8): Concat sums the input heights before any gather; the sum is checked
# for wrap (a sum past 2^32 - 1 is over the cap by definition and shows as 4294967295, as the
# join's saturating count does) and refused with "too many rows: <n> exceeds 8388608". Zero-column
# frames `Frame{h, []}` carry a height without data, so no test allocates 8M rows.
# The join / CSV / from_scalars / group_by cases are tests/regress/B04_i_row_cap.bend (active).
import Base
import ./../../frame.bend as DF
import ./../../src/dtype.bend as D
import ./../../src/err.bend as E
import ./../../src/column.bend as C
import ./lib/rx.bend as R

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(R.show("B04-i concat-zero-col", "eager", DF.concat_vertical([C.Frame{8388608, Nil{}}, C.Frame{1, Nil{}}])))
    IO.print(R.show("B04-i concat-at-cap", "eager", DF.concat_vertical([C.Frame{8388607, Nil{}}, C.Frame{1, Nil{}}])))
    IO.print(R.show("B04-i concat-wrap", "eager", DF.concat_vertical([C.Frame{2147483648, Nil{}}, C.Frame{2147483648, Nil{}}])))
#|-- B04-i concat-zero-col eager
#|error	InvalidOperation: too many rows: 8388609 exceeds 8388608
#|
#|-- B04-i concat-at-cap eager
#|frame
#|height	8388608
#|width	0
#|
#|-- B04-i concat-wrap eager
#|error	InvalidOperation: too many rows: 4294967295 exceeds 8388608
#|
