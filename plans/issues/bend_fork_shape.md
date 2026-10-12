# Draft issue for bendlang/bend

**Title:** A non-flat call before a parallel let serialises the whole subtree (fork trees top out at ~2x)

**Bend version:** 2.0.36 (native build, `--threads N`), macOS 26.7 arm64 (Apple M2 Pro, 8 P + 4 E cores)

## Summary

In a def that contains a parallel let, a call to a fork-free but non-flat def (e.g. a non-tail-recursive list split) in the branch arguments makes the scheduler run that whole subtree on one thread. A balanced fork tree built this way gets only its two root halves in parallel, so it stops at about 2x whatever the thread count or the number of leaves. Building the same tree first, in a sequential prelude, and forking by match only scales normally.

This is easy to write by accident. It is the natural way to write a parallel map over a list: split in half, recurse on both halves. As far as I can tell it is not documented in the guide or in the shaders guide.

## Repro

`forkshape.bend` (attached, Base only, ~120 lines) has two modes. Each runs the same 256 leaves, and each leaf runs the same flat tail loop (an LCG, 2^24 steps). Both answer the same checksum.

- **Mode 1 (split in the branch arguments):**
  ```python
  def ps(d: Nat, r: List<&1, U32> & List<&1, U32>) -> U32:
    match d:
      ...
      case 1n++p:
        (l, rr) = r
        a b = ps(p, split(half(p), l)) ps(p, split(half(p), rr))
        U32.add(a, b)
  ```
  where `split` is an ordinary non-tail recursion returning a pair.
- **Mode 2 (prelude tree):** the same splits build a balanced tree `T = L{x} | N{l, r}` first, sequentially. Then:
  ```python
  def pt(t: T) -> U32:
    match t:
      case L{x}:
        wk(x)
      case N{l, r}:
        a b = pt(l) pt(r)
        U32.add(a, b)
  ```

```
bend forkshape.bend -o forkshape
time ./forkshape --threads N 1    # split in the branch arguments
time ./forkshape --threads N 2    # prelude tree, fork by match
```

Wall time, 3 runs each (identical within ~1%), machine load 3-7:

| threads | mode 1 (split before fork) | mode 2 (tree, match + fork) |
|---|---|---|
| 1 | 4.1 s | 4.09 s |
| 4 | 2.08 s (2.0x) | 1.07 s (3.8x) |
| 12 | 2.08 s (2.0x) | 0.44 s (9.2x) |

The splitting work in mode 1 is negligible (256 elements); the leaves are the same. The difference is purely in how the scheduler runs the tree.

## What we think happens

This is from reading the emitted C (`cube_run` / `pool_turn` / `row_grow` / `monk_step` / `work_loop`) and from an instrumented build of the runtime (iterations, turns, ring tasks per thread, grow skips):

- The grow turn runs only tasks whose def can fork. A fork-free def that is not flat is its own segment, and a call to it from a forking def in non-seq mode compiles to `task_node(..); return term_tsk(..)`, which is a task.
- In the grow turn the caller is rewound at that call, so the row stops growing.
- In the drain, the helper runs sequentially, and `FID_EXIT` continues straight into its continuation: the rest of the forking def, including its parallel let, still sequential.
- So the whole subtree runs on one thread. Only the root fork, on the main thread outside a grow turn, splits, so the tree degenerates to two halves.
- Instrumented, in our larger probe (the same two shapes over 1024 leaves): the prelude-tree version drains 256 ring tasks per rep, spread over all threads. The split version drains about 38 tasks per rep, two of which take 5-7 ms each (the halves). There are zero grow skips and zero deferred forks, so it is not a per-level cost.
- A FLAT helper in the same position (inlined as a `spin_N` loop) costs nothing.

A related observation: forks inside a task that is already being drained run sequentially. Nested fork trees, for example a per-column fork under a fork over columns, add no parallelism.

## Request

1. Document the rule in the guide / shaders guide. Suggested wording: "in a def with a parallel let, call nothing non-flat before the fork. Build the work tree in a sequential prelude and fork by match only."
2. If feasible, let the grow pass run fork-free tasks whose continuation can fork (or follow the continuation instead of rewinding), and/or let forks inside a drained task nest in parallel.

We hit this in a real codebase: a dataframe library whose chunked engine stalled at ~2x until every fork was rewritten in the prelude-tree shape. After the rewrite, the same row-wise pipelines went to 3.7-5.6x at 12 threads.
