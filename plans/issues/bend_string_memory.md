# 16 bytes per character: String and the byte APIs are cons lists, no packed byte/string type

Filed as bendlang/bend#1987. Repro: `strmem.bend` (Base only).

## Summary

A `String` costs **16 bytes per character** on the native heap (one `SCon` cell per character), and so does
every byte API (`File.read_bytes`, `TCP.recv_bytes`, `IO.args_bytes`: `List<U32>`, one cell per byte). The
only compact element storage in Base is `Array<U32>` (4 bytes per slot). There is no packed byte or
string type. Bend 2.0.39, native build, macOS 26 arm64.

Measured with the repro below (2^20 freshly built strings, all alive at once; "peak memory footprint" from
`/usr/bin/time -l`):

| characters per string | peak | per character |
|---:|---:|---:|
| 0 | 17.2 MB | (the list itself) |
| 16 | 273.3 MB | 16.0 B |
| 32 | 529.4 MB | 16.0 B |

## Why it matters

Text-heavy data is 16x its UTF-8 size in memory (Arrow / Polars: ~1 byte per ASCII character plus a 4- or 8-byte
offset per string). In bend-frame, reading a 1M-row CSV of distinct ~15-character keys peaks at ~450 MB; the
keys alone are ~15M characters, ~240 MB as `String`s. Polars holds that column in ~15 MB (the whole
three-column frame in ~31 MB). A library can pack code points into
`Array<U32>` itself (4 B per character), but then loses every `String` function in Base. Would a packed
representation be possible, either for `String` or as a separate `Bytes` / `Array<U8>` type that the byte
APIs return?

## Repro (Base only)

```bend
# The heap cost of a String per character (Base only).
#   bend strmem.bend -o strmem
#   /usr/bin/time -l ./strmem 20 0     # 2^20 empty strings in a list (the list's own cost)
#   /usr/bin/time -l ./strmem 20 16    # 2^20 strings of 16 characters, all alive at once
# (peak(16) - peak(0)) / (2^20 * 16) is the cost of one character. Each string is built fresh
# (its first character depends on its index), so nothing is shared.
import Base

# a fresh string of k characters, the first one 'a' + (i mod 26)
def str.go(+k: Nat, +i: U32, acc: String) -> String:
  match k:
    case 0n:
      acc
    case 1n+p:
      str.go(p, i, SCon{Chr{U32.add(97, U32.mod(U32.add(i, U32.from_nat(p)), 26))}, acc})

def strs(+n: Nat, +k: Nat, acc: List<&1, String>) -> List<&1, String>:
  match n:
    case 0n:
      acc
    case 1n+p:
      strs(p, k, str.go(k, U32.from_nat(p), SNil{}) <> acc)

# every character counted once all strings exist (the list is consumed)
def total(xs: List<&1, String>, +s: Nat) -> Nat:
  match xs:
    case Nil{}:
      s
    case x <> t:
      total(t, Nat.add(s, String.length(x)))

def nat(m: Maybe<&2, Nat>, +d: Nat) -> Nat:
  match m:
    case None{}:
      d
    case Some{v}:
      v

def args2(xs: List<&1, String>) -> Nat & Nat:
  match xs:
    case _ <> d <> k <> t:
      (nat(Nat.read(d), 20n), nat(Nat.read(k), 16n))
    case _:
      (20n, 16n)

def run(r: Nat & Nat) -> IO(Unit):
  (+d, +k) = r
  IO.print(Nat.show(total(strs(U32.to_nat(U32.shln(1, d)), k, Nil{}), 0n)))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    run(args2(args))
```

```bash
bend strmem.bend -o strmem
for k in 0 16 32; do /usr/bin/time -l ./strmem 20 $k 2>&1 | grep -E "^[0-9]+$|peak memory"; done
```
