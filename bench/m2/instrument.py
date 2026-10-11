#!/usr/bin/env python3
"""G6 instrumentation (plans/M_02.txt G6 / W1.h): patch the emitted C of a bend program with allocation and copy
counters, and print them at every IO.now. Counts are exact and deterministic at 1 thread; the timings of an
instrumented binary are NEVER valid (relaxed atomics on every allocation, a fprintf per IO.now).

  python3 -I bench/m2/instrument.py patch IN.c OUT.c        patch the runtime text of a `bend X.bend -o IN.c` file
  python3 -I bench/m2/instrument.py build DRIVER.bend OUT/  emit the C with $BEND, patch, compile with bend's own flags;
                                                            writes OUT/driver.c (original), OUT/driver-g6.c, OUT/driver
  python3 -I bench/m2/instrument.py selftest                patch + compile + run a tiny program (needs $BEND and clang)

What is counted (all u64, relaxed atomics, process wide):

  alloc_bytes / allocs   every heap_alloc (8 << class bytes): array blocks, constructor nodes, task nodes, strings
  free_bytes / frees     every heap_free; live = alloc_bytes - free_bytes, peak_live is its high-water mark
  blk_bytes / blks       the array blocks (BLK_ALLOC: blk_new, blk_copy, blk_node, blk_half) among them
  copy_bytes / copies    blk_copy: Array.clone (8 << class bytes written; a U32 buffer of n elements is 4n bytes)
  node_bytes / nodes     blk_node: ANode{l, r}, i.e. a rebuild of an array out of two halves (copies BOTH halves)
  half_bytes / halves    blk_half: matching an ANode of an array (copies the half it returns)
  minflt / majflt / maxrss   getrusage(RUSAGE_SELF) at the snapshot; bump = the heap arena's high-water in bytes

Copies are also attributed to their CALL SITE: blk_copy / blk_node / blk_half are wrapped by macros that record the
line of the patched C file (`__LINE__`), and the sites that moved bytes since the previous snapshot are printed as
`BF_G6 site k=N kind=copy|node|half line=L bytes=B n=C` lines before the snapshot line N (the window ending at it).
`Resolver` maps a line of the patched C to the enclosing spin loop / Bend function (FID name) by a static scan.

Every IO.now prints one stderr line `BF_G6 now k=N ...`; `BF_G6 end ...` is printed at exit. The patches are located
by regular expressions over the runtime text; each must match EXACTLY once or the build fails loudly (the runtime of a
different bend version, or a hand-edited C file, is refused, never silently half-instrumented).
"""
import os
import re
import subprocess
import sys
from pathlib import Path

VERSION = 1


class PatchError(Exception):
    pass


DECLS = r'''
// ---- bend-frame G6 instrumentation (bench/m2/instrument.py v%(v)d) ------------------------------------
#include <sys/resource.h>
static u64 bf_alloc_bytes, bf_allocs, bf_free_bytes, bf_frees, bf_blk_bytes, bf_blks;
static u64 bf_copy_bytes, bf_copies, bf_node_bytes, bf_nodes, bf_half_bytes, bf_halves;
static long long bf_live, bf_peak;
static u64 bf_snaps;
static __thread u32 bf_line;
#define BF_NSITE 2048
static u64 bf_sk[BF_NSITE], bf_sb[BF_NSITE], bf_sn[BF_NSITE], bf_spb[BF_NSITE], bf_spn[BF_NSITE];
static inline void bf_site(u64 kind, u64 bytes) {
  u64 key = ((kind + 1) << 32) | bf_line;
  bf_line = 0;
  u32 i = (u32)((key * 0x9E3779B97F4A7C15ull) >> 53);
  for (u32 n = 0; n < BF_NSITE; n += 1, i = (i + 1) & (BF_NSITE - 1)) {
    u64 k = __atomic_load_n(&bf_sk[i], __ATOMIC_RELAXED);
    if (k == 0 && __atomic_compare_exchange_n(&bf_sk[i], &k, key, 0, __ATOMIC_RELAXED, __ATOMIC_RELAXED)) { k = key; }
    if (k == key) {
      __atomic_fetch_add(&bf_sb[i], bytes, __ATOMIC_RELAXED);
      __atomic_fetch_add(&bf_sn[i], 1, __ATOMIC_RELAXED);
      return;
    }
  }
}
#define BF_ADD(c, v) __atomic_fetch_add(&(c), (u64)(v), __ATOMIC_RELAXED)
static inline void bf_on_alloc(u32 cls) {
  BF_ADD(bf_alloc_bytes, 8ull << cls);
  BF_ADD(bf_allocs, 1);
  long long l = __atomic_add_fetch(&bf_live, (long long)(8ull << cls), __ATOMIC_RELAXED);
  long long p = __atomic_load_n(&bf_peak, __ATOMIC_RELAXED);
  while (l > p && !__atomic_compare_exchange_n(&bf_peak, &p, l, 1, __ATOMIC_RELAXED, __ATOMIC_RELAXED)) {}
}
static inline void bf_on_free(u32 cls) {
  BF_ADD(bf_free_bytes, 8ull << cls);
  BF_ADD(bf_frees, 1);
  __atomic_sub_fetch(&bf_live, (long long)(8ull << cls), __ATOMIC_RELAXED);
}
#define BF_BLK(w)  (BF_ADD(bf_blk_bytes, 8ull << (w)), BF_ADD(bf_blks, 1))
#define BF_COPY(w) (BF_ADD(bf_copy_bytes, 8ull << (w)), BF_ADD(bf_copies, 1), bf_site(0, 8ull << (w)))
#define BF_NODE(w) (BF_ADD(bf_node_bytes, 8ull << (w)), BF_ADD(bf_nodes, 1), bf_site(1, 8ull << (w)))
#define BF_HALF(w) (BF_ADD(bf_half_bytes, 8ull << (w)), BF_ADD(bf_halves, 1), bf_site(2, 8ull << (w)))
static void bf_g6_print(const char* tag, u64 bump) {
  static const char* kn[3] = {"copy", "node", "half"};
  for (u32 i = 0; i < BF_NSITE; i += 1) {
    u64 key = bf_sk[i], b = bf_sb[i], n = bf_sn[i];
    if (key && (b != bf_spb[i] || n != bf_spn[i])) {
      fprintf(stderr, "BF_G6 site k=%%llu kind=%%s line=%%u bytes=%%llu n=%%llu\n", (unsigned long long)bf_snaps,
        kn[(key >> 32) - 1], (u32)key, (unsigned long long)(b - bf_spb[i]), (unsigned long long)(n - bf_spn[i]));
      bf_spb[i] = b;
      bf_spn[i] = n;
    }
  }
  struct rusage ru;
  getrusage(RUSAGE_SELF, &ru);
  fprintf(stderr,
    "BF_G6 %%s k=%%llu alloc_bytes=%%llu allocs=%%llu free_bytes=%%llu frees=%%llu live=%%lld peak_live=%%lld "
    "blk_bytes=%%llu blks=%%llu copy_bytes=%%llu copies=%%llu node_bytes=%%llu nodes=%%llu half_bytes=%%llu halves=%%llu "
    "minflt=%%ld majflt=%%ld maxrss=%%ld bump=%%llu v=%(v)d\n",
    tag, (unsigned long long)bf_snaps++,
    (unsigned long long)bf_alloc_bytes, (unsigned long long)bf_allocs, (unsigned long long)bf_free_bytes,
    (unsigned long long)bf_frees, (long long)bf_live, (long long)bf_peak,
    (unsigned long long)bf_blk_bytes, (unsigned long long)bf_blks, (unsigned long long)bf_copy_bytes,
    (unsigned long long)bf_copies, (unsigned long long)bf_node_bytes, (unsigned long long)bf_nodes,
    (unsigned long long)bf_half_bytes, (unsigned long long)bf_halves,
    (long)ru.ru_minflt, (long)ru.ru_majflt, (long)ru.ru_maxrss, (unsigned long long)bump);
}
static void bf_g6_end(void) { bf_g6_print("end", 0); }
static void __attribute__((constructor)) bf_g6_init(void) { atexit(bf_g6_end); }
// ---- end of G6 declarations ---------------------------------------------------------------------------

''' % {"v": VERSION}

# (name, regex, kind, text): kind "before" inserts the text before the match, "after" after it.
# Every regex must match exactly once.
PATCHES = [
    ("decls", r"^#define ALC_AT\(e, i\)[^\n]*\n", "before", DECLS),
    ("heap_alloc", r"INLINE\s+u64\s+heap_alloc\(Env e, u32 cls\)\s*\{\n", "after",
     "  bf_on_alloc(cls);\n"),
    ("heap_free", r"INLINE\s+void\s+heap_free\(Env e, u32 cls, u64 loc\)\s*\{\n\s*if \(err_peek\(e\.mem\)\) \{\n\s*return;\n\s*\}\n",
     "after", "  bf_on_free(cls);\n"),
    ("BLK_ALLOC", r"#define BLK_ALLOC\(n, w\) \\\n", "after", "  BF_BLK(w); \\\n"),
    ("blk_copy", r"OUTLINE\s+Term\s+blk_copy\(Env e, Term a\)\s*\{\n\s*bool arr = term_tag\(a\) == TAG_ARR;\n\s*u32 cls = blk_span\(a\);\n",
     "after", "  BF_COPY(cls);\n"),
    ("blk_node", r"^  BLK_ALLOC\(n, arr \? c \+ 1 : c\)\n", "after", "  BF_NODE(arr ? c + 1 : c);\n"),
    ("blk_half", r"^  BLK_ALLOC\(n, cw\)\n", "after", "  BF_HALF(cw);\n"),
    # call-site attribution: after blk_copy and blk_node are defined, wrap their calls (and blk_half's after its definition)
    ("site_copy_node", r"^INLINE Term blk_half\(Env e, Term a, u32 hi\) \{\n", "before",
     "#define blk_copy(e, a)    (bf_line = __LINE__, blk_copy(e, a))\n#define blk_node(e, l, r) (bf_line = __LINE__, blk_node(e, l, r))\n"),
    ("site_half", r"^INLINE Term blk_new\(Env e, bool arr, u64 d, u32 lgs, u32 n, THR Term\* v\) \{\n", "before",
     "#define blk_half(e, a, hi) (bf_line = __LINE__, blk_half(e, a, hi))\n"),
    ("io_now", r"Term\s+io_now_run\(Env e, Term\* f, IoWork\* w\)\s*\{\n", "after",
     "  bf_g6_print(\"now\", (u64)a32_load(a32_at(e.mem, H_BUMP)) << (PAGE_BITS + 3));\n"),
]

HINTS = {"decls": "ALC_AT", "heap_alloc": "heap_alloc", "heap_free": "heap_free", "BLK_ALLOC": "BLK_ALLOC",
         "blk_copy": "blk_copy", "blk_node": "blk_node", "blk_half": "blk_half", "io_now": "io_now_run",
         "site_copy_node": "blk_half", "site_half": "blk_new"}


def patch_c(text: str) -> str:
    """-> the patched C text; raises PatchError naming the first anchor that does not match exactly once."""
    if "bf_g6_print" in text:
        raise PatchError("the C text is already instrumented (patching twice would double-count)")
    for name, pat, kind, rep in PATCHES:
        ms = list(re.finditer(pat, text, re.M))
        if len(ms) != 1:
            hint = HINTS[name]
            at = [m.start() for m in re.finditer(re.escape(hint), text)][:1]
            ctx = ""
            if at:
                ctx = "\n  first occurrence of %r:\n    " % hint + text[at[0]:at[0] + 240].replace("\n", "\n    ")
            raise PatchError(f"G6 patch '{name}': expected exactly 1 match of /{pat}/, found {len(ms)}: the runtime text "
                             f"changed (a different bend version?); update bench/m2/instrument.py{ctx}")
        m = ms[0]
        i = m.start() if kind == "before" else m.end()
        text = text[:i] + rep + text[i:]
    for must in ("bf_on_alloc(cls);", "bf_on_free(cls);", "BF_BLK(w);", "BF_COPY(cls);", "BF_NODE(arr ? c + 1 : c);", "BF_HALF(cw);",
                 'bf_g6_print("now"', "#define blk_copy(e, a)", "#define blk_half(e, a, hi)"):
        if text.count(must) != 1:
            raise PatchError(f"G6 self-check: '{must}' occurs {text.count(must)} times after patching, expected 1")
    return text


class Resolver:
    """Map a line of the PATCHED C file (the `line=` of a BF_G6 site record) to the Bend-level function it belongs to.
    The emitted C has two kinds of functions: `WL_CASE(FID_<module path>_<Bend name>)` bodies (one per Bend def, plus
    generated continuations `_K<n>` / `_J<n>`) and `spin_<n>` flat loops, which are INLINE helpers called from them. A line is
    attributed to its enclosing function; a spin is traced up the static call graph to the nearest FID functions."""
    DEF = re.compile(r"^(?:INLINE|OUTLINE|FAR|static)\s[^;()]*?\b(spin_\d+)\(")
    CASE = re.compile(r"WL_CASE\((FID_\w+)\)")
    CALL = re.compile(r"\b(spin_\d+)\(")

    def __init__(self, path):
        lines = Path(path).read_text().split("\n")
        starts = []                      # (line, name) of every function definition that matters, in file order
        for i, l in enumerate(lines, 1):
            m = self.DEF.match(l)
            if m:
                starts.append((i, m.group(1)))
                continue
            m = self.CASE.search(l)
            if m and "define" not in l:
                starts.append((i, m.group(1)))
        self.starts = starts
        self.first = [s[0] for s in starts]
        self.callers = {}
        import bisect
        self.bisect = bisect
        for i, l in enumerate(lines, 1):
            for m in self.CALL.finditer(l):
                callee = m.group(1)
                here = self.fn_at(i)
                if here and here != callee:
                    self.callers.setdefault(callee, set()).add(here)

    def fn_at(self, line):
        k = self.bisect.bisect_right(self.first, line) - 1
        return self.starts[k][1] if k >= 0 else None

    def where(self, line, limit=3):
        """-> a short description: the FID name, or `spin_N <- FID, FID` (nearest FID callers, breadth first)."""
        f = self.fn_at(line)
        if f is None:
            return "?"
        if f.startswith("FID_"):
            return f[4:].lstrip("_")
        seen, front, fids = {f}, [f], []
        for _ in range(10):
            nxt = []
            for g in front:
                for c in sorted(self.callers.get(g, ())):
                    if c in seen:
                        continue
                    seen.add(c)
                    (fids if c.startswith("FID_") else nxt).append(c)
            if fids or not nxt:
                break
            front = nxt
        fids = [x[4:].lstrip("_") for x in fids[:limit]]
        return f + (" <- " + ", ".join(fids) if fids else "")


def cc() -> str:
    return os.environ.get("CC", "clang")


def compile_c(c_path: Path, exe: Path, original: Path = None):
    """bend's own native build (bend2/main.ts cli_build) is `clang -std=c11 -O3 FILE -lpthread -lm -o BIN` for a
    program with `#define BANGS 0` and no #import (no GPU lane, no framework): the same command here."""
    src = (original or c_path).read_text()
    if not re.search(r"^#define BANGS\s+0$", src, re.M) or re.search(r"^#import ", src, re.M):
        raise PatchError("the emitted C is a GPU / framework build (BANGS != 0 or #import): bend would compile it with "
                         "other flags than this script uses; not supported")
    cmd = [cc(), "-std=c11", "-O3", str(c_path), "-lpthread", "-lm", "-o", str(exe)]
    if subprocess.run(cmd).returncode != 0:
        raise PatchError("compile failed: " + " ".join(cmd))
    return cmd


def build(src: Path, outdir: Path):
    bend = os.path.expanduser(os.environ.get("BEND", "~/.bend/bin/bend"))
    outdir.mkdir(parents=True, exist_ok=True)
    orig, pat, exe = outdir / "driver.c", outdir / "driver-g6.c", outdir / "driver"
    if subprocess.run([bend, str(src), "-o", str(orig)]).returncode != 0:
        raise PatchError("bend failed to emit the C of " + str(src))
    pat.write_text(patch_c(orig.read_text()))
    return compile_c(pat, exe, orig)


SELFTEST = '''import Base

def main() -> IO(Unit):
  do IO<Unit>:
    +a : Nat <- IO.now()
    IO.print("one")
    +b : Nat <- IO.now()
    IO.print(Nat.show(Nat.sub(b, b)))
'''


def selftest():
    import tempfile
    d = Path(tempfile.mkdtemp(prefix="g6selftest"))
    (d / "t.bend").write_text(SELFTEST)
    build(d / "t.bend", d / "o")
    p = subprocess.run([str(d / "o" / "driver")], capture_output=True, text=True)
    lines = [l for l in p.stderr.splitlines() if l.startswith("BF_G6 ")]
    print(p.stdout.strip().replace("\n", " "), len(lines), "snapshots")
    for l in lines:
        print(l)
    ok = len(lines) == 3 and "live=0 " in lines[-1]
    # the loud failures: a changed runtime text, a double patch
    orig = (d / "o" / "driver.c").read_text()
    for what, text in (("changed blk_copy", orig.replace("blk_copy(Env e, Term a)", "blk_copy(Env e, Term b)", 1)),
                       ("double patch", patch_c(orig))):
        try:
            patch_c(text)
            print("selftest FAILED: no error for", what)
            ok = False
        except PatchError as e:
            print("selftest: refused as expected:", what, "->", str(e).splitlines()[0][:100])
    return 0 if ok else 1


def main(argv):
    if len(argv) >= 4 and argv[1] == "patch":
        Path(argv[3]).write_text(patch_c(Path(argv[2]).read_text()))
        return 0
    if len(argv) >= 4 and argv[1] == "build":
        build(Path(argv[2]), Path(argv[3]))
        return 0
    if len(argv) >= 2 and argv[1] == "selftest":
        return selftest()
    print(__doc__)
    return 2


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv))
    except PatchError as e:
        print("instrument.py: " + str(e), file=sys.stderr)
        sys.exit(3)
