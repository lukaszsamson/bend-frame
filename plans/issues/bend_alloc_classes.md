# Native heap: freed memory is reused only within its size class (peak = sum of per-class high-water marks)

Filed as bendlang/bend#1986. Repro: `allocclass.bend` (Base only).

## Summary

In native builds (`bend x.bend -o x`), heap memory freed by blocks of one size class is never reused by
blocks of another class, never coalesced or split, and never returned to the OS. A program whose live data
changes shape over time (many small arrays, then one big one; or a big one, then many small ones) peaks at
the **sum** of the per-class high-water marks instead of the largest live set. Bend 2.0.39, macOS 26 arm64
(Apple M2 Pro), `--threads 1` and `--threads 4` alike.

The repro below keeps 4096 arrays of 2^12 U32 (64 MB) alive, frees them, then allocates one array of
2^24 U32 (64 MB). Peak footprint (`/usr/bin/time -l`, "peak memory footprint"):

| mode | what | peak |
|---|---|---:|
| `small` | 4096 x 2^12 words, freed | 65 MB |
| `big` | one 2^24-word array | 65 MB |
| `same` | small, freed, small again | 65 MB (same class: reused) |
| `both` | small, freed, then big | **129 MB** |
| `rev` | big, freed, then small | **129 MB** |

## Where it comes from (generated C)

`heap_free(e, cls, loc)` pushes the block on the per-lane free list of its class `cls` (blocks are 2^cls
words); a full list is handed to the shared bank of the same class. `heap_alloc_miss` takes a block of the
requested class from the lane's cold list or `bank_pop(H, cls)`, and otherwise bumps `H_BUMP`
(`corpus_grow`). Nothing merges two free class-c buddies into a class-(c+1) block, splits a larger free block,
or `madvise`/unmaps freed pages.

## Why it matters

Any pipeline that builds many small pieces and then one big result (a parallel parser whose lanes each build
a part of every column, then a concatenation) pays parts + result, even though the parts are dead before the
result is complete. In bend-frame (a dataframe library), reading an 85 MB CSV peaks at ~300 MB for ~110 MB of
final columns, mostly for this reason, and every later allocation of a new size class grows the heap again.
Coalescing buddies on free (or splitting a larger free block on a miss), or returning long-idle pages with
`madvise(MADV_FREE)`, would let the peak follow the live set.

## Repro (Base only)

```bend
# Freed heap memory is reusable only by blocks of the same size class (Base only).
#   bend allocclass.bend -o allocclass
#   /usr/bin/time -l ./allocclass small   # 4096 arrays of 2^12 U32 alive at once (64 MB), then freed
#   /usr/bin/time -l ./allocclass big     # one array of 2^24 U32 (64 MB)
#   /usr/bin/time -l ./allocclass both    # small, freed, then big: peak ~128 MB, not ~64 MB
#   /usr/bin/time -l ./allocclass same    # small, freed, then small again: peak ~64 MB (same class reused)
#   /usr/bin/time -l ./allocclass rev     # big, freed, then small: peak ~128 MB (a big free block is not split)
# Each phase prints a checksum, so nothing is dead code.
import Base

# sum of a[0..n), a consumed
def sum.go(n: Nat, +i: U32, +s: U32, r: Array<U32> & U32) -> U32:
  match n:
    case 0n:
      (a, x) = r
      s
    case 1n+p:
      (a, +x) = r
      +j = U32.inc(i)
      sum.go(p, j, U32.add(s, x), Array.get(U32, a, j))

def sum(+d: Nat, a: Array<U32>) -> U32:
  sum.go(U32.to_nat(U32.shln(1, d)), 0, 0, Array.get(U32, a, 0))

# k arrays of 2^d words, all alive at once
def many(+k: Nat, +d: Nat, acc: List<&1, Array<U32>>) -> List<&1, Array<U32>>:
  match k:
    case 0n:
      acc
    case 1n+p:
      many(p, d, Array.new(U32, d, U32.from_nat(p)) <> acc)

def sums(+d: Nat, xs: List<&1, Array<U32>>, +s: U32) -> U32:
  match xs:
    case Nil{}:
      s
    case a <> t:
      sums(d, t, U32.add(s, sum(d, a)))

def small() -> U32:
  sums(12n, many(4096n, 12n, Nil{}), 0)

def big() -> U32:
  sum(24n, Array.new(U32, 24n, 1))

def show(+x: U32) -> IO(Unit):
  IO.print(U32.show(x))

def run(+is_small: Bool, +is_big: Bool, +is_same: Bool, +is_rev: Bool) -> IO(Unit):
  match is_small is_big is_same is_rev:
    case True{} False{} False{} False{}:
      show(small())
    case False{} True{} False{} False{}:
      show(big())
    case False{} False{} True{} False{}:
      do IO<Unit>:
        show(small())
        show(small())
    case False{} False{} False{} True{}:
      do IO<Unit>:
        show(big())
        show(small())
    case _ _ _ _:
      do IO<Unit>:
        show(small())
        show(big())

def go(+m: String) -> IO(Unit):
  run(String.eq(m, "small"), String.eq(m, "big"), String.eq(m, "same"), String.eq(m, "rev"))

def arg(xs: List<&1, String>) -> String:
  match xs:
    case Nil{}:
      "both"
    case h <> Nil{}:
      "both"
    case h <> a <> t:
      a

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    go(arg(args))
```

```bash
bend allocclass.bend -o allocclass
for m in small big same both rev; do /usr/bin/time -l ./allocclass $m 2>&1 | grep -E "^[0-9]+$|peak memory"; done
```
