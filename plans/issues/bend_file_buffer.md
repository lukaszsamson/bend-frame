# Draft issue for bendlang/bend

**Title:** Feature request: read file bytes into an `Array<U32>` (the cons-list File API is a serial floor for parallel parsers)

**Bend version:** 2.0.36 (native build), macOS 26.7 arm64 (Apple M2 Pro)

## Summary

Base's file reads answer cons lists only:
- `File.read(f, max) -> String`
- `File.read_bytes(f, max) -> List<&2, U32>`
- `File.read_at(f, off, max) -> List<&2, U32>`

Each has one cell per byte, and the cells are built on the single IO event-loop thread (`io_list` / `io_str`). There is no way to get a file's bytes into an `Array`, which is what a parallel parser wants to fork over. So every program that parses a file has a sequential stage proportional to the file size that no amount of forking can remove.

## Numbers

`readfloor.bend` (attached, Base only) reads a 41 MB CSV with `File.read_at` in 1 MiB pieces and only counts the bytes of each list. It does one flat walk per piece and builds nothing:

| | 1 thread | 12 threads |
|---|---|---|
| readfloor (standalone program) | 110-141 ms | 112-117 ms |
| the same read inside a larger program where `List` is a `+`-shared ("hot") type | ~273 ms | ~273 ms |
| reference: Python `open(...).read()` of the same file | ~5 ms | |

That is about 2.7 ns per byte in the best case, and about 6.6 ns per byte once `List` is refcounted elsewhere in the program. Neither changes with threads.

In our CSV reader (a sequential producer that walks these lists into packed U32 buffers, then one balanced fork of typed parsers over the regions), the producer is about 280 ms of a ~630 ms single-thread parse. The forked part scales 5.7x at 12 threads, but the parse as a whole stops at about 1.9x. By Amdahl it can't pass ~2.2x while the bytes arrive as a cons list on one thread.

`IO.fork` / `IO.spawn` don't help, since they are green threads on the same loop. Several handles on one file don't help either: list construction serialises.

## Request

A primitive that reads into a flat buffer, for example:

```python
File.read_into(file: File, offset: U32, buf: Array<U32>) -> IO(File & Result<.., Array<U32> & U32>)
# fills buf with packed bytes (4 per word, little-endian) or one byte per word, answers the count
```

or `File.read_array(file, offset, max) -> IO(File & Result<.., Array<U32>>)`. Owned arrays could then be cut into pieces and forked over immediately. Memory-mapping would be even better, but a plain `pread` into an array would already remove the serial cons-list stage.

Side benefit: our whole reader allocates ~1.4 GB cumulatively in ~83 M heap allocations for the 41 MB file, and the per-byte cells alone account for at least 41 M of those allocations. A buffer read would replace them with a handful.
