# (Since the v0.1 reader's removal, DESIGN.md 14 "Pre-release", every read below is the reader's, at the tiny
# and big piece sizes; the expectations, frozen from the v0.1 reader, are unchanged. The original intent:)
# The v0.1 streaming reader feeds the column builders of a chunk through ONE balanced fork over a tree of
# (builder, cells) pairs (CBs.feed -> FJ.feed, DESIGN.md 16.10: a forking def matches and forks, nothing else
# before the parallel let; the old 1-vs-rest chain down the column list is gone). The tree's shape depends on
# the column count (odd counts leave a lone leaf per level), so this reads files of 1..9, 16, 17 and 33
# columns (U32, Str and F32 columns in turn, a handful of rows, a null in the last row) with the v0.1 reader
# in tiny and big chunks (several batches / one) and with the v0.2 reader (a different fork tree over a
# different code path): every dump must equal the big-chunk v0.1 dump, and the dump's first line pins the
# frame's shape.
import Base
import ./../frame.bend as DF
import ./../src/err.bend as E
import ./../src/column.bend as C
import ./../src/csv.bend as V
import ./../src/strs.bend as ST

# "c0,c1,...,c<n-1>\n"
def ft.hdr(n: Nat, +i: U32, +last: U32) -> String:
  match n:
    case 0n:
      "\n"
    case 1n+p:
      "c" ++ U32.show(i) ++ Bool.pick(String, U32.is_eq(i, last), "", ",") ++ ft.hdr(p, U32.inc(i), last)

# one cell of row r, column i: a number, a word or a float in turn; the last row's column 0 is empty
def ft.cell(+r: U32, +i: U32) -> String:
  Bool.pick(String, Bool.and(U32.is_eq(r, 4), U32.is_eq(i, 0)), "", Bool.pick(String, U32.is_eq(U32.mod(i, 3), 0), U32.show(U32.add(U32.mul(r, 100), i)), Bool.pick(String, U32.is_eq(U32.mod(i, 3), 1), "s" ++ U32.show(U32.add(U32.mul(r, 7), i)), U32.show(r) ++ "." ++ U32.show(i))))

def ft.row(n: Nat, +r: U32, +i: U32, +last: U32) -> String:
  match n:
    case 0n:
      "\n"
    case 1n+p:
      ft.cell(r, i) ++ Bool.pick(String, U32.is_eq(i, last), "", ",") ++ ft.row(p, r, U32.inc(i), last)

def ft.rows(k: Nat, +r: U32, +n: U32) -> String:
  match k:
    case 0n:
      ""
    case 1n+p:
      ft.row(U32.to_nat(n), r, 0, U32.sub(n, 1)) ++ ft.rows(p, U32.inc(r), n)

def ft.text(+n: U32) -> String:
  ft.hdr(U32.to_nat(n), 0, U32.sub(n, 1)) ++ ft.rows(5n, 0, n)

def ft.close(r: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (f, w) = r
  do IO<Unit>:
    File.close(f)
    IO.pure(Unit, Unit{})

def ft.write(+path: String, +text: String) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(path, "w"))
    r : File & Result<&1, &1, U32 & String, Unit> <- File.write(f, text)
    ft.close(r)

def ft.rd1(+path: String, +chunk: U32) -> IO(String):
  do IO<String>:
    r : E.ResT(C.Frame) <- V.Csv.read_v02_full(path, V.Csv.default(), [], ST.EncRaw{}, chunk, 8388608)
    return DF.dump(r)

def ft.rd2(+path: String, +piece: U32) -> IO(String):
  do IO<String>:
    r : E.ResT(C.Frame) <- V.Csv.read_v02_full(path, V.Csv.default(), [], ST.EncRaw{}, piece, 8388608)
    return DF.dump(r)

def ft.first(+s: String) -> String:
  Bool.pick(String, String.starts_with(s, "frame"), "frame", String.trim(s))

def ft.same(+b: String, +x: String) -> String:
  Bool.pick(String, String.eq(b, x), "same", "DIFF")

def ft.go(+path: String, +n: U32) -> IO(Unit):
  do IO<Unit>:
    ft.write(path, ft.text(n))
    +base : String <- ft.rd1(path, 1048576)
    c4 : String <- ft.rd1(path, 4)
    c37 : String <- ft.rd1(path, 37)
    v2 : String <- ft.rd2(path, 16)
    v2b : String <- ft.rd2(path, 1048576)
    IO.print(U32.show(n) ++ " cols: " ++ ft.first(base) ++ " | chunk 4 " ++ ft.same(base, c4) ++ " | chunk 37 " ++ ft.same(base, c37) ++ " | v0.2 piece 16 " ++ ft.same(base, v2) ++ " | v0.2 1 MiB " ++ ft.same(base, v2b))

def ft.one(+n: U32) -> IO(Unit):
  ft.go("/tmp/bend_frame_feedtree_" ++ U32.show(n) ++ ".csv", n)

def main() -> IO(Unit):
  do IO<Unit>:
    ft.one(1)
    ft.one(2)
    ft.one(3)
    ft.one(4)
    ft.one(5)
    ft.one(6)
    ft.one(7)
    ft.one(8)
    ft.one(9)
    ft.one(16)
    ft.one(17)
    ft.one(33)
#|1 cols: frame | chunk 4 same | chunk 37 same | v0.2 piece 16 same | v0.2 1 MiB same
#|2 cols: frame | chunk 4 same | chunk 37 same | v0.2 piece 16 same | v0.2 1 MiB same
#|3 cols: frame | chunk 4 same | chunk 37 same | v0.2 piece 16 same | v0.2 1 MiB same
#|4 cols: frame | chunk 4 same | chunk 37 same | v0.2 piece 16 same | v0.2 1 MiB same
#|5 cols: frame | chunk 4 same | chunk 37 same | v0.2 piece 16 same | v0.2 1 MiB same
#|6 cols: frame | chunk 4 same | chunk 37 same | v0.2 piece 16 same | v0.2 1 MiB same
#|7 cols: frame | chunk 4 same | chunk 37 same | v0.2 piece 16 same | v0.2 1 MiB same
#|8 cols: frame | chunk 4 same | chunk 37 same | v0.2 piece 16 same | v0.2 1 MiB same
#|9 cols: frame | chunk 4 same | chunk 37 same | v0.2 piece 16 same | v0.2 1 MiB same
#|16 cols: frame | chunk 4 same | chunk 37 same | v0.2 piece 16 same | v0.2 1 MiB same
#|17 cols: frame | chunk 4 same | chunk 37 same | v0.2 piece 16 same | v0.2 1 MiB same
#|33 cols: frame | chunk 4 same | chunk 37 same | v0.2 piece 16 same | v0.2 1 MiB same
