"""Typed comparator for bend-frame results (plan M_01 B05).

Two modes; both exit 0 = match, 1 = mismatch (a diff report on stdout), 2 = unusable input
(missing or malformed file).

1. CSV mode (Bend's rendered result vs a Polars golden CSV, floats printed at 4 decimals):

     python check.py <bend.csv> <golden.csv> [--ulp N] [--rtol R] [--signed-zero strict|ignore]

   Cells are compared by type, read from the golden column: a column whose non-empty cells
   are all integers is an int column (exact), true/false a bool column (exact), integers /
   decimals / nan / inf with at least one non-integer a float column, anything else a string
   column (exact). The actual cell must parse as the golden column's type: `nan` never
   matches an int column, `100000` never matches `100001`. The header (names, order) and
   the row count must agree. An empty cell matches only an empty cell.
   Float cells: NaN equals NaN and nothing else; an infinity equals the same infinity;
   finite values must be exactly equal unless a tolerance is given: --ulp N allows N units
   in the last place of the f32 (ordered-integer distance), --rtol R a relative error R
   (either passing is enough). With --signed-zero strict (default) -0.0 != 0.0.

2. Dump mode (two DF.dump texts, DESIGN.md 15.1):

     python check.py --dump <a.txt> <b.txt> [--ulp N] [--signed-zero strict|ignore]

   Exact line-by-line equality of the parsed dumps (height, width, dtypes, names, validity,
   every cell, error text) with the contract's one relaxation: any two NaN f32 cells are
   equal whatever their payload (15.1 rule 3). f32 cells are the stored bits; --ulp N
   allows a distance of N in the ordered bit representation; -0.0 vs 0.0 differ unless
   --signed-zero ignore. Trailing blank lines are ignored (IO.print adds one). `-` as a
   path reads stdin. Each dump must be canonical (decimal u32/i32 without padding or sign
   tricks and in range, known dtypes, `\\xHH` only where 15.1 requires it, no raw control
   characters), so two different texts never parse to equal frames; anything else exits 2.
   An integer CSV cell must match its golden text exactly, and no cell is whitespace-stripped.

The comparison functions (compare_csv_rows, compare_dumps, ...) are importable; the tests
are in tests/test_check.py.
"""
import argparse
import csv
import math
import re
import struct
import sys

# ASCII digits only, matched with fullmatch: `\d` takes other scripts' digits and `$` matches
# before a trailing newline, so "5\n" (a quoted CSV cell) would have passed as the integer 5
INT_RE = re.compile(r"[+-]?[0-9]+")
BOOL = ("true", "false")
SPECIAL = {"nan": math.nan, "+nan": math.nan, "-nan": math.nan,
           "inf": math.inf, "+inf": math.inf, "-inf": -math.inf,
           "infinity": math.inf, "+infinity": math.inf, "-infinity": -math.inf}
FLOAT_RE = re.compile(r"[+-]?([0-9]+\.?[0-9]*|\.[0-9]+)([eE][+-]?[0-9]+)?")
# canonical dump integers (15.1: U32.show / I32.show: no sign on u32, no "+", no padding, no "-0")
U32_RE = re.compile(r"0|[1-9][0-9]*")
I32_RE = re.compile(r"0|-?[1-9][0-9]*")
DTYPE_NAMES = ("bool", "u32", "i32", "f32", "str")
MAX_DIFFS = 20


# ---- floats -------------------------------------------------------------------------------

def parse_float(tok):
    """A float token (decimal, exponent, nan, inf) as a Python float, or None. Surrounding
    whitespace is not stripped: " 1.5" is not a number."""
    t = tok.lower()
    if t in SPECIAL:
        return SPECIAL[t]
    if FLOAT_RE.fullmatch(t):
        return float(t)
    return None


def f32_bits(x):
    """The IEEE-754 binary32 bits of x (rounded to f32)."""
    try:
        return struct.unpack(">I", struct.pack(">f", x))[0]
    except OverflowError:  # finite double too big for f32
        return 0x7F800000 if x > 0 else 0xFF800000


def ulp_key(bits):
    """Monotone integer key of an f32 bit pattern; -0.0 and 0.0 share the key 0."""
    mag = bits & 0x7FFFFFFF
    return -mag if bits & 0x80000000 else mag


def is_nan_bits(bits):
    return (bits & 0x7F800000) == 0x7F800000 and (bits & 0x007FFFFF) != 0


def is_inf_bits(bits):
    return (bits & 0x7FFFFFFF) == 0x7F800000


def bits_equal(a, b, ulp=0, signed_zero="strict"):
    """Compare two f32 bit patterns. NaN == NaN (any payload) and nothing else."""
    na, nb = is_nan_bits(a), is_nan_bits(b)
    if na or nb:
        return na and nb
    if is_inf_bits(a) or is_inf_bits(b):  # FLT_MAX is 1 ulp from inf: no tolerance here
        return a == b
    if (a & 0x7FFFFFFF) == 0 and (b & 0x7FFFFFFF) == 0:
        return a == b or signed_zero == "ignore"
    return abs(ulp_key(a) - ulp_key(b)) <= ulp


def floats_equal(x, y, ulp=0, rtol=None, signed_zero="strict"):
    """Compare two Python floats read from text: NaN only with NaN, inf only with the same inf,
    finite values exactly unless `ulp` (f32 units) or `rtol` (relative) allows a difference."""
    nx, ny = math.isnan(x), math.isnan(y)
    if nx or ny:
        return nx and ny
    if math.isinf(x) or math.isinf(y):
        return x == y
    if x == 0.0 and y == 0.0:
        return signed_zero == "ignore" or math.copysign(1.0, x) == math.copysign(1.0, y)
    if x == y:
        return True
    if ulp and abs(ulp_key(f32_bits(x)) - ulp_key(f32_bits(y))) <= ulp:
        return True
    if rtol is not None:
        return abs(x - y) <= rtol * max(abs(x), abs(y))
    return False


# ---- CSV mode -----------------------------------------------------------------------------

def read_csv(path):
    with open(path, newline="", encoding="utf-8") as f:
        return list(csv.reader(f))


def column_kind(cells):
    """int | bool | float | str | empty, from the non-empty cells of a reference column."""
    vals = [c for c in cells if c != ""]
    if not vals:
        return "empty"
    if all(INT_RE.fullmatch(v) for v in vals):
        return "int"
    if all(v in BOOL for v in vals):
        return "bool"
    if all(INT_RE.fullmatch(v) or parse_float(v) is not None for v in vals):
        return "float"
    return "str"


def cell_diff(kind, got, want, ulp=0, rtol=None, signed_zero="strict"):
    """None if the cells agree, else a short reason. `want` is the reference cell."""
    if got == "" or want == "":
        return None if got == want else "null vs value"
    if kind == "int":
        if not INT_RE.fullmatch(got):
            return "not an integer"
        return None if got == want else "ints differ"   # exact text: "007" is not "7"
    if kind == "bool":
        return None if got == want else "bools differ"
    if kind == "float":
        g, w = parse_float(got), parse_float(want)
        if g is None:
            return "not a number"
        if floats_equal(g, w, ulp, rtol, signed_zero):
            return None
        if math.isnan(g) != math.isnan(w):
            return "NaN vs number"
        if math.isinf(g) or math.isinf(w):
            return "infinity differs"
        if g == 0.0 and w == 0.0:
            return "signed zeros differ"
        rel = abs(g - w) / max(abs(g), abs(w))
        return f"floats differ (rel {rel:.2e})"
    return None if got == want else "strings differ"


def compare_csv_rows(got, want, ulp=0, rtol=None, signed_zero="strict", max_diffs=MAX_DIFFS):
    """Compare two parsed CSVs (lists of rows, header first). Returns (diffs, n_inexact):
    a list of human lines (empty = match) and the number of float cells that differed within
    tolerance. Structural problems (header, row count, field count) are reported first."""
    diffs = []
    if not got and not want:
        return diffs, 0
    if not got or not want:
        return [f"one side is empty ({len(got)} lines vs {len(want)})"], 0
    if got[0] != want[0]:
        return [f"header: {got[0]!r} vs {want[0]!r}"], 0
    if len(got) != len(want):
        diffs.append(f"row count: {len(got) - 1} vs {len(want) - 1}")
    names = want[0]
    kinds = [column_kind([r[i] for r in want[1:] if i < len(r)]) for i in range(len(names))]
    inexact = 0
    for ln, (r1, r2) in enumerate(zip(got[1:], want[1:]), start=2):
        if len(r1) != len(names) or len(r2) != len(names):
            diffs.append(f"line {ln}: {len(r1)} fields vs {len(r2)} (header has {len(names)})")
            continue
        for i, (c1, c2) in enumerate(zip(r1, r2)):
            why = cell_diff(kinds[i], c1, c2, ulp, rtol, signed_zero)
            if why:
                diffs.append(f"line {ln}, column {names[i]!r} ({kinds[i]}): {c1!r} vs {c2!r}: {why}")
            elif c1 != c2:
                inexact += 1
    return diffs[:max_diffs] + ([f"... {len(diffs) - max_diffs} more"] if len(diffs) > max_diffs else []), inexact


# ---- dump mode ----------------------------------------------------------------------------

class DumpError(ValueError):
    pass


ESC = {'"': '"', "\\": "\\", "n": "\n", "r": "\r", "t": "\t"}


def unquote(tok):
    """The text of a quoted dump string, escapes resolved."""
    if len(tok) < 2 or tok[0] != '"' or tok[-1] != '"':
        raise DumpError(f"not a quoted string: {tok!r}")
    s, out, i = tok[1:-1], [], 0
    while i < len(s):
        c = s[i]
        if c == '"':
            raise DumpError(f"unescaped quote in {tok!r}")
        if ord(c) < 0x20 or ord(c) == 0x7F:
            raise DumpError(f"unescaped control character in {tok!r}")
        if c != "\\":
            out.append(c)
            i += 1
            continue
        i += 1
        if i >= len(s):
            raise DumpError(f"dangling backslash in {tok!r}")
        if s[i] in ESC:
            out.append(ESC[s[i]])
            i += 1
        elif s[i] == "x" and i + 2 < len(s) and re.fullmatch(r"[0-9a-f]{2}", s[i + 1:i + 3]):
            # only for the C0 controls and U+007F without a short escape: one text per string
            ch = chr(int(s[i + 1:i + 3], 16))
            if not (ord(ch) < 0x20 or ord(ch) == 0x7F) or ch in "\n\r\t":
                raise DumpError(f"non-canonical escape \\x{s[i + 1:i + 3]} in {tok!r}")
            out.append(ch)
            i += 3
        else:
            raise DumpError(f"bad escape \\{s[i]} in {tok!r}")
    return "".join(out)


def parse_cell(dtype, tok):
    if tok == "null":
        return None
    if dtype == "bool":
        if tok not in BOOL:
            raise DumpError(f"bad bool cell {tok!r}")
        return tok == "true"
    if dtype in ("u32", "i32"):
        lo, hi = (0, 2**32 - 1) if dtype == "u32" else (-2**31, 2**31 - 1)
        if not (U32_RE if dtype == "u32" else I32_RE).fullmatch(tok) or not lo <= int(tok) <= hi:
            raise DumpError(f"bad {dtype} cell {tok!r}")
        return int(tok)
    if dtype == "f32":
        if not re.fullmatch(r"0x[0-9a-f]{8}", tok):
            raise DumpError(f"bad f32 cell {tok!r}")
        return int(tok[2:], 16)
    if dtype == "str":
        return unquote(tok)
    raise DumpError(f"unknown dtype {dtype!r}")


def parse_dump(text):
    """A DF.dump text as ("error", text) or ("frame", {height, width, cols, rows}), where cols
    is [(dtype, name)] and rows a list of cell lists (None = null; f32 cells are bit ints)."""
    if not text.endswith("\n"):
        raise DumpError("dump does not end in a newline")
    # IO.print adds a newline after the dump's own: trailing blank lines are not part of it
    lines = text.rstrip("\n").split("\n")
    if lines[0].startswith("error\t"):
        if len(lines) != 1:
            raise DumpError("error dump has more than one line")
        return ("error", lines[0][len("error\t"):])
    if lines[0] != "frame":
        raise DumpError(f"first line is {lines[0]!r}, want 'frame' or 'error<TAB>..'")
    try:
        h = lines[1].split("\t")
        w = lines[2].split("\t")
    except IndexError:
        raise DumpError("truncated header")
    if h[0] != "height" or len(h) != 2 or w[0] != "width" or len(w) != 2 \
            or not U32_RE.fullmatch(h[1]) or not U32_RE.fullmatch(w[1]):
        raise DumpError("bad height/width lines")
    height, width = int(h[1]), int(w[1])
    cols, rows = [], []
    for ln in lines[3:]:
        f = ln.split("\t")
        if f[0] == "col" and not rows:
            if len(f) != 3 or f[1] not in DTYPE_NAMES:
                raise DumpError(f"bad col line {ln!r}")
            cols.append((f[1], unquote(f[2])))
        elif f[0] == "row":
            if len(cols) != width:
                raise DumpError(f"{len(cols)} col lines before the first row, width is {width}")
            if len(f) != width + 1:
                raise DumpError(f"row has {len(f) - 1} cells, width is {width}: {ln!r}")
            rows.append([parse_cell(cols[i][0], t) for i, t in enumerate(f[1:])])
        else:
            raise DumpError(f"unexpected line {ln!r}")
    if len(cols) != width:
        raise DumpError(f"{len(cols)} col lines, width is {width}")
    if width > 0 and len(rows) != height:
        raise DumpError(f"{len(rows)} row lines, height is {height}")
    if width == 0 and rows:
        raise DumpError("a zero-column frame has no row lines")
    return ("frame", {"height": height, "width": width, "cols": cols, "rows": rows})


def show_cell(dtype, v):
    if v is None:
        return "null"
    if dtype == "f32":
        return f"0x{v:08x}"
    if dtype == "str":
        return repr(v)
    return str(v).lower() if dtype == "bool" else str(v)


def compare_dumps(a, b, ulp=0, signed_zero="strict", max_diffs=MAX_DIFFS):
    """Compare two DF.dump texts; returns a list of difference lines (empty = equal)."""
    ka, da = parse_dump(a)
    kb, db = parse_dump(b)
    if ka != kb:
        return [f"{ka} dump vs {kb} dump"]
    if ka == "error":
        return [] if da == db else [f"error text: {da!r} vs {db!r}"]
    diffs = []
    for key in ("height", "width"):
        if da[key] != db[key]:
            diffs.append(f"{key}: {da[key]} vs {db[key]}")
    if da["cols"] != db["cols"]:
        diffs.append(f"columns (dtype, name): {da['cols']} vs {db['cols']}")
    if diffs or len(da["rows"]) != len(db["rows"]):
        if not diffs:
            diffs.append(f"rows: {len(da['rows'])} vs {len(db['rows'])}")
        return diffs
    for r, (x, y) in enumerate(zip(da["rows"], db["rows"])):
        for c, (u, v) in enumerate(zip(x, y)):
            dt = da["cols"][c][0]
            if u is None or v is None:
                same = u is None and v is None
            elif dt == "f32":
                same = bits_equal(u, v, ulp, signed_zero)
            else:
                same = u == v
            if not same:
                diffs.append(f"row {r}, column {da['cols'][c][1]!r} ({dt}): {show_cell(dt, u)} vs {show_cell(dt, v)}")
    return diffs[:max_diffs] + ([f"... {len(diffs) - max_diffs} more"] if len(diffs) > max_diffs else [])


# ---- command line -------------------------------------------------------------------------

def read_text(path):
    if path == "-":
        return sys.stdin.read()
    with open(path, newline="", encoding="utf-8") as f:
        return f.read()


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("actual", help="Bend output (CSV, or a dump with --dump)")
    ap.add_argument("expected", help="reference (Polars golden CSV, or a dump with --dump)")
    ap.add_argument("--dump", action="store_true", help="compare two DF.dump texts")
    ap.add_argument("--ulp", type=int, default=0, help="allowed f32 distance in units in the last place (default 0: exact)")
    ap.add_argument("--rtol", type=float, default=None, help="CSV mode: allowed relative error on floats (default: exact)")
    ap.add_argument("--signed-zero", choices=("strict", "ignore"), default="strict",
                    help="strict: -0.0 != 0.0 (default); ignore: equal")
    a = ap.parse_args(argv)
    if a.dump and a.rtol is not None:
        ap.error("--rtol applies to CSV mode only")
    try:
        if a.dump:
            diffs = compare_dumps(read_text(a.actual), read_text(a.expected), a.ulp, a.signed_zero)
            inexact = 0
        else:
            diffs, inexact = compare_csv_rows(read_csv(a.actual), read_csv(a.expected), a.ulp, a.rtol, a.signed_zero)
    except (OSError, DumpError, csv.Error, UnicodeDecodeError, ValueError) as e:
        print(f"ERROR: {e}")
        return 2
    if diffs:
        print(f"MISMATCH ({a.actual} vs {a.expected}):")
        for d in diffs:
            print("  " + d)
        return 1
    print("identical" if not inexact else f"ok ({inexact} float cells differ within tolerance)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
