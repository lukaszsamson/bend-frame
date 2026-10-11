#!/usr/bin/env python3
"""Public-API coverage matrix and def-call coverage report (plans/M_01.txt T6).

    scripts/coverage_matrix.py             write docs/COVERAGE.md, exit 1 on a gap (make coverage)
    scripts/coverage_matrix.py --check     the gate only, write nothing
    scripts/coverage_matrix.py --stdout    print the report instead of writing the file

THE MATRIX.  Rows are the released operations: every public `def` of frame.bend (a name
without a `.`, not a type alias), grouped only where defs are trivial aliases of one another
(ROWS below: `lit_*`, `t_*`, `s_*`, `closed_*`, `str_*`, `cast_*`, `lit_i32`, `i32`). Columns
are the six kinds every row needs:

    success  a case with a normal, valid input
    null     a case whose input holds nulls (a null row, a null cell, a nullable column)
    empty    a zero-row input (and, shown apart as `0col`, a zero-column frame where meaningful)
    invalid  an input the operation must refuse, with the error it answers (an error path)
    eager    the operation is exercised through the eager API
    lazy     the lazy twin is exercised and raw / optimised / fully optimised collects agree
             with the eager result (tests/regress/lib/rx.bend `four`)

Classification is by explicit annotation, in the test that holds the case (comment lines,
ignored by the test runner):

    #@ cover select,with_columns success null eager lazy
    #@ na    sqrt invalid -- no argument can be refused beyond the type error covered elsewhere

`cover` names one or more operations (a row name, or one member of a grouped row) and the
kinds the case in this file demonstrates; `na` marks kinds that have no meaningful case, and
the reason after `--` is mandatory. The script VALIDATES each annotation: the file exists
under tests/, the operation is real, and the file calls it: `DF.<op>(` directly, or
`<Alias>.<op>(` / `<Alias>.e_<op>(` through a tests/**/lib/ helper module it imports. A
grouped row needs every member named in some annotation. The gate (exit status 1) fails when
any row lacks any of the six kinds (neither covered nor n/a with a reason), when an annotation
is invalid, or when a public facade def is in no row. Cases that pin a known defect
(`#! xfail`) count as covered and are marked in the matrix. Heuristic, report only: the
"other files" column counts every other test file that calls the operation.

THE DEF-CALL REPORT (not gated). Bend has no coverage tool, so this is a static
approximation: a call graph over src/*.bend and frame.bend (a def's body mentions another
def, qualified through the file's import aliases or bare inside its own module), entered at
every facade def a test calls (directly or through a tests/**/lib helper it imports) and every
src def a test or helper calls directly. A def is "reached" when some path leads to it. It is
an over-approximation of what runs (a branch never taken still counts) and a def reached only
through a function passed as a value is found only if its name appears in the body; it says
which defs NO test can reach, not which lines run.
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
KINDS = ["success", "null", "empty", "invalid", "eager", "lazy"]
EXTRA_KINDS = ["zerocol"]  # reported as the `0col` mark, not required

# (section, row, members). A row with one member is that op. Order is the matrix order.
SECTIONS = [
    ("Columns, literals and builders", [
        ("col", ["col"]),
        ("lit_*", ["lit_u32", "lit_f32", "lit_str", "lit_bool"]),
        ("lit_i32*", ["lit_i32", "lit_i32_neg"]),
        ("lit_null", ["lit_null"]),
        ("alias", ["alias"]),
        ("cast", ["cast"]),
        ("cast_*", ["cast_f32", "cast_u32"]),
        ("try_cast", ["try_cast"]),
        ("t_*", ["t_bool", "t_u32", "t_i32", "t_f32", "t_str"]),
        ("s_*", ["s_null", "s_bool", "s_u32", "s_i32", "s_f32", "s_str"]),
        ("i32*", ["i32", "i32_neg"]),
        ("named", ["named"]),
        ("column", ["column"]),
        ("from_columns", ["from_columns"]),
        ("closed_*", ["closed_both", "closed_left", "closed_right", "closed_neither"]),
        ("sort_key", ["sort_key"]),
        ("asc", ["asc"]),
        ("desc", ["desc"]),
    ]),
    ("Expression operators", [(n, [n]) for n in [
        "add", "sub", "mul", "div", "floor_div", "mod", "neg", "abs", "sqrt",
        "eq", "ne", "lt", "le", "gt", "ge", "and", "or", "not",
        "is_null", "is_not_null", "fill_null", "when", "is_in", "clip",
        "is_between", "is_between_closed",
        "len_chars", "contains_literal", "starts_with", "ends_with"]]),
    ("Aggregations", [(n, [n]) for n in [
        "sum", "mean", "min", "max", "count", "len", "first", "last", "n_unique",
        "std", "var", "median"]]),
    ("Eager table verbs", [(n, [n]) for n in [
        "select", "with_columns", "filter", "sort", "group_by", "head", "inner_join",
        "left_join", "semi_join", "anti_join", "drop", "rename", "slice", "tail", "unique",
        "concat_vertical"]]),
    ("Lazy plan builders", [(n, [n]) for n in [
        "lazy_select", "lazy_with_columns", "lazy_filter", "lazy_sort", "lazy_group_by",
        "lazy_head", "lazy_inner_join", "lazy_left_join", "lazy_semi_join", "lazy_anti_join",
        "lazy_drop", "lazy_rename", "lazy_slice", "lazy_tail", "lazy_unique",
        "lazy_concat_vertical"]]),
    ("Sources, environments and running a plan", [(n, [n]) for n in [
        "empty_env", "source", "add_source", "validate_bindings", "collect_raw", "collect",
        "collect_full", "collect_show"]]),
    ("Introspection", [(n, [n]) for n in [
        "schema", "height", "collect_schema", "schema_show", "err_show", "explain",
        "optimize", "optimize_full", "show", "dump", "dump_frame", "describe", "clone",
        "then", "then_io"]]),
    ("IO and string storage", [
        ("csv_opts", ["csv_opts"]),
        ("read_csv", ["read_csv"]),
        ("read_csv_opts", ["read_csv_opts"]),
        ("read_csv_schema", ["read_csv_schema"]),
        ("read_csv_enc", ["read_csv_enc"]),
        ("csv_engine_*", ["csv_engine_v01", "csv_engine_v02"]),
        ("read_csv_engine", ["read_csv_engine"]),
        ("read_csv_v02", ["read_csv_v02"]),
        ("collect_engine", ["collect_engine"]),
        ("str_*", ["str_raw", "str_dict", "str_auto"]),
        ("encode_strings", ["encode_strings"]),
        ("dict_columns", ["dict_columns"]),
        ("scan_csv", ["scan_csv"]),
        ("scan_csv_opts", ["scan_csv_opts"]),
        ("scan_csv_schema", ["scan_csv_schema"]),
        ("write_opts", ["write_opts"]),
        ("write_csv", ["write_csv"]),
        ("write_csv_opts", ["write_csv_opts"]),
    ]),
]
# facade defs that are not operations: type aliases (their result kind is Type / Data)
NON_OPS = {"Frame", "Column", "Expr", "SortKey", "Plan", "Env", "ResT", "Res", "Err",
           "Schema", "CsvOpts", "CsvWriteOpts", "StrEnc", "RenamePair"}

ROWS = [(sec, row, members) for sec, rows in SECTIONS for row, members in rows]
MEMBER_ROW = {}
for _sec, _row, _members in ROWS:
    for _m in _members:
        MEMBER_ROW[_m] = _row
ROW_NAMES = {row for _s, row, _m in ROWS}
ROW_MEMBERS = {row: members for _s, row, members in ROWS}

COMMENT = re.compile(r"^\s*#")
DEF = re.compile(r"^def\s+([A-Za-z_][\w.]*)\s*\(")
IMPORT = re.compile(r"^import\s+(\S+)\s+as\s+(\w+)\s*$")
TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z0-9_]+)*")
ANNOT = re.compile(r"^#@\s+(cover|na)\s+(\S+)\s+(.*?)\s*$")


def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


def rel(path):
    return os.path.relpath(path, ROOT)


def code_lines(text):
    return [ln for ln in text.splitlines() if not COMMENT.match(ln)]


def strip_strings(line):
    return re.sub(r'"(?:\\.|[^"\\])*"', '""', line)


def tests_files():
    out = []
    for d, _dirs, files in os.walk(os.path.join(ROOT, "tests")):
        for f in files:
            if f.endswith(".bend"):
                out.append(os.path.join(d, f))
    return sorted(out)


def is_lib(path):
    return os.sep + "lib" + os.sep in path


def imports_of(path, text):
    """alias -> absolute path of the imported file."""
    out = {}
    for ln in text.splitlines():
        m = IMPORT.match(ln)
        if m:
            out[m.group(2)] = os.path.normpath(os.path.join(os.path.dirname(path), m.group(1)))
    return out


def facade_ops():
    ops = []
    for ln in read(os.path.join(ROOT, "frame.bend")).splitlines():
        m = DEF.match(ln)
        if m and "." not in m.group(1) and m.group(1) not in NON_OPS:
            ops.append(m.group(1))
    return ops


class Test:
    def __init__(self, path):
        self.path = path
        self.text = read(path)
        self.imports = imports_of(path, self.text)
        self.xfail = None
        for ln in self.text.splitlines():
            m = re.match(r"^#!\s*xfail\s+(\S+)", ln)
            if m:
                self.xfail = m.group(1)
        self.code = [strip_strings(ln) for ln in code_lines(self.text)]
        self.calls = self._calls()

    def _calls(self):
        """Facade ops this file calls: DF.<op>( or <Alias>.<op>( / .e_<op>( into a lib helper."""
        names = set()
        body = "\n".join(self.code)
        for alias, p in self.imports.items():
            if os.path.basename(p) == "frame.bend":
                for m in re.finditer(r"\b" + re.escape(alias) + r"\.(\w+)\(", body):
                    names.add(m.group(1))
        for alias, p in self.imports.items():
            if is_lib(p) and p.startswith(os.path.join(ROOT, "tests")):
                try:
                    defs = {m.group(1) for m in (DEF.match(l) for l in read(p).splitlines()) if m}
                except OSError:
                    continue
                for m in re.finditer(r"\b" + re.escape(alias) + r"\.(\w+)\(", body):
                    n = m.group(1)
                    if n in defs and n.startswith("e_"):
                        names.add(n[2:])
        return names


def parse_annotations(tests, errors):
    """-> {(op, kind): [(kind_of_mark, Test, reason)]} with kind_of_mark cover | na."""
    marks = {}
    per_file = {}
    n_annot = 0
    for t in tests:
        if is_lib(t.path):
            continue
        for lineno, ln in enumerate(t.text.splitlines(), 1):
            if not ln.startswith("#@"):
                continue
            m = ANNOT.match(ln)
            where = "%s:%d" % (rel(t.path), lineno)
            if not m:
                errors.append("%s: malformed annotation: %s" % (where, ln))
                continue
            n_annot += 1
            verb, ops, rest = m.group(1), m.group(2).split(","), m.group(3)
            reason = ""
            if verb == "na":
                if "--" not in rest:
                    errors.append("%s: `#@ na` needs `-- <reason>`" % where)
                    continue
                rest, reason = rest.split("--", 1)
                reason = reason.strip()
                if len(reason) < 12:
                    errors.append("%s: `#@ na` reason too short (say why there is no case)" % where)
                    continue
            kinds = rest.split()
            if not kinds:
                errors.append("%s: no kinds" % where)
            for k in kinds:
                if k not in KINDS + EXTRA_KINDS:
                    errors.append("%s: unknown kind %r (want one of %s)" % (where, k, " ".join(KINDS + EXTRA_KINDS)))
            for op in ops:
                if op not in MEMBER_ROW and op not in ROW_NAMES:
                    errors.append("%s: unknown operation %r" % (where, op))
                    continue
                members = ROW_MEMBERS.get(op, [op])
                if op in ROW_NAMES and len(members) > 1:
                    errors.append("%s: name a member of the grouped row %r, not the row" % (where, op))
                    continue
                if op not in t.calls:
                    errors.append("%s: the file does not call DF.%s (or an e_%s wrapper): an annotation names an operation the test exercises" % (where, op, op))
                    continue
                for k in kinds:
                    seen = per_file.setdefault((t.path, op, k), set())
                    if seen and verb not in seen:
                        errors.append("%s: %s %s is both covered and n/a in this file" % (where, op, k))
                    seen.add(verb)
                    marks.setdefault((MEMBER_ROW[op], k), []).append((verb, t, reason, op))
    return marks, n_annot


def matrix(marks, errors):
    """-> {row: {kind: ('ok', [tests]) | ('na', reason) | ('missing',)}}"""
    res = {}
    for _sec, row, members in ROWS:
        cells = {}
        for k in KINDS + EXTRA_KINDS:
            ms = marks.get((row, k), [])
            covers = [t for (v, t, _r, _op) in ms if v == "cover"]
            nas = [r for (v, _t, r, _op) in ms if v == "na"]
            if covers:
                seen, uniq = set(), []
                for t in covers:
                    if t.path not in seen:
                        seen.add(t.path)
                        uniq.append(t)
                cells[k] = ("ok", uniq)
            elif nas:
                cells[k] = ("na", nas[0])
            else:
                cells[k] = ("missing",)
        res[row] = cells
        if len(members) > 1:
            named = {op for k in KINDS for (_v, _t, _r, op) in marks.get((row, k), [])}
            for m in members:
                if m not in named:
                    errors.append("grouped row %s: member %s is named in no annotation" % (row, m))
    return res


# ---- the report ---------------------------------------------------------------------------

def md_cell(cell, na_ids, others_xfail=True):
    if cell[0] == "missing":
        return "**MISSING**"
    if cell[0] == "na":
        return "n/a [%d]" % na_ids.setdefault(cell[1], len(na_ids) + 1)
    tests = cell[1]
    parts = []
    for t in tests[:2]:
        stem = os.path.splitext(os.path.basename(t.path))[0]
        s = "[%s](../%s)" % (stem, rel(t.path))
        if t.xfail:
            s += " (xfail %s)" % t.xfail
        parts.append(s)
    if len(tests) > 2:
        parts.append("+%d" % (len(tests) - 2))
    return ", ".join(parts)


def counts(res):
    out = {}
    for k in KINDS:
        ok = sum(1 for r in res.values() if r[k][0] == "ok")
        na = sum(1 for r in res.values() if r[k][0] == "na")
        miss = sum(1 for r in res.values() if r[k][0] == "missing")
        out[k] = (ok, na, miss)
    return out


def others_count(tests, row, members, annotated):
    n = 0
    for t in tests:
        if is_lib(t.path) or t.path in annotated:
            continue
        if any(m in t.calls for m in members):
            n += 1
    return n


def render_matrix(res, tests, marks):
    na_ids = {}
    lines = []
    annotated = {t.path for ms in marks.values() for (_v, t, _r, _o) in ms}
    c = counts(res)
    n_ops = len(res)
    lines.append("| kind | covered | n/a (reason given) | missing |")
    lines.append("|---|---|---|---|")
    for k in KINDS:
        lines.append("| %s | %d | %d | %d |" % (k, c[k][0], c[k][1], c[k][2]))
    lines.append("")
    lines.append("%d rows (%d facade defs); %d row x kind cells; covered by a case %d, n/a with a reason %d, missing %d." % (
        n_ops, sum(len(m) for _s, _r, m in ROWS), n_ops * len(KINDS),
        sum(c[k][0] for k in KINDS), sum(c[k][1] for k in KINDS), sum(c[k][2] for k in KINDS)))
    lines.append("")
    for sec, rows in SECTIONS:
        lines.append("### " + sec)
        lines.append("")
        lines.append("| operation | " + " | ".join(KINDS) + " | 0col | other test files |")
        lines.append("|---|" + "---|" * (len(KINDS) + 2))
        for row, members in rows:
            cells = res[row]
            z = cells["zerocol"]
            zc = "yes" if z[0] == "ok" else ("n/a" if z[0] == "na" else "")
            name = "`%s`" % row
            if len(members) > 1:
                name += " (%s)" % ", ".join(members)
            lines.append("| %s | %s | %s | %d |" % (
                name, " | ".join(md_cell(cells[k], na_ids) for k in KINDS), zc,
                others_count(tests, row, members, annotated)))
        lines.append("")
    lines.append("### n/a reasons")
    lines.append("")
    for reason, i in sorted(na_ids.items(), key=lambda kv: kv[1]):
        lines.append("%d. %s" % (i, reason))
    lines.append("")
    return "\n".join(lines), c


# ---- def-call coverage over src/ ------------------------------------------------------------

class Module:
    def __init__(self, path):
        self.path = path
        self.name = os.path.splitext(os.path.basename(path))[0]
        self.text = read(path)
        self.imports = imports_of(path, self.text)
        self.defs = {}  # name -> body text (comments and strings stripped)
        cur, buf = None, []
        for ln in self.text.splitlines():
            m = DEF.match(ln)
            top = ln and not ln[0].isspace() and not ln.startswith("#")
            if m:
                if cur:
                    self.defs[cur] = "\n".join(buf)
                cur, buf = m.group(1), [strip_strings(ln)]
            elif top:
                if cur:
                    self.defs[cur] = "\n".join(buf)
                cur, buf = None, []
            elif cur and not COMMENT.match(ln):
                buf.append(strip_strings(ln))
        if cur:
            self.defs[cur] = "\n".join(buf)


def refs_in(mod, body, modules, self_name=None):
    """The (module path, def) pairs a body mentions."""
    out = set()
    for tok in TOKEN.findall(body):
        cands = [(mod.path, tok)]
        if "." in tok:
            alias, rest = tok.split(".", 1)
            if alias in mod.imports:
                cands.append((mod.imports[alias], rest))
        for p, d in cands:
            m = modules.get(p)
            if m is not None and d in m.defs and not (p == mod.path and d == self_name):
                out.add((p, d))
    return out


def defcall_report(tests):
    srcdir = os.path.join(ROOT, "src")
    paths = [os.path.join(ROOT, "frame.bend")] + sorted(
        os.path.join(srcdir, f) for f in os.listdir(srcdir) if f.endswith(".bend"))
    modules = {p: Module(p) for p in paths}
    frame = modules[paths[0]]
    graph = {}
    for p, m in modules.items():
        for d, body in m.defs.items():
            graph[(p, d)] = refs_in(m, body, modules, d)
    entries = set()
    used_libs = set()
    for t in tests:
        if is_lib(t.path):
            continue
        for alias, p in t.imports.items():
            if is_lib(p):
                used_libs.add(p)
    for t in [x for x in tests if not is_lib(x.path)] + [Test(p) for p in sorted(used_libs) if os.path.exists(p)]:
        for alias, p in t.imports.items():
            if p not in modules:
                continue
            body = "\n".join(t.code)
            for m in re.finditer(r"\b" + re.escape(alias) + r"\.([A-Za-z_][A-Za-z0-9_.]*)", body):
                name = m.group(1)
                # the longest prefix of the dotted token that is a def of the module
                parts = name.split(".")
                for i in range(len(parts), 0, -1):
                    d = ".".join(parts[:i])
                    if d in modules[p].defs:
                        entries.add((p, d))
                        break
    def closure(start):
        seen = set(start)
        work = list(start)
        while work:
            n = work.pop()
            for r in graph.get(n, ()):
                if r not in seen:
                    seen.add(r)
                    work.append(r)
        return seen

    facade_path = paths[0]
    via_facade = closure({e for e in entries if e[0] == facade_path})
    seen = closure(entries)
    rows = []
    unreached = {}
    for p in paths:
        m = modules[p]
        total = len(m.defs)
        hit = sum(1 for d in m.defs if (p, d) in seen)
        hit_f = sum(1 for d in m.defs if (p, d) in via_facade)
        direct = sum(1 for d in m.defs if (p, d) in entries)
        rows.append((rel(p), total, direct, hit_f, hit))
        unreached[rel(p)] = sorted(d for d in m.defs if (p, d) not in seen)
    return rows, unreached, len(entries)


def render_defcalls(tests):
    rows, unreached, n_entries = defcall_report(tests)
    tot = sum(r[1] for r in rows)
    hit = sum(r[4] for r in rows)
    hit_f = sum(r[3] for r in rows)
    L = []
    L.append("Method: a static call graph (see the header of `scripts/coverage_matrix.py`). A def *mentions* another def")
    L.append("when its body names it (qualified through the file's import aliases, or bare inside its own module).")
    L.append("Entry points are the %d defs that a test (or a `tests/**/lib` helper a test imports) calls directly," % n_entries)
    L.append("`frame.bend` defs and `src/` defs alike. A def is *reached* when a path of mentions leads to it. Two")
    L.append("reach columns: **via facade** follows only the entries that are `frame.bend` defs (what the public API")
    L.append("alone can reach); **reached** adds the `src/` defs the tests call directly (the proof-style and unit tests).")
    L.append("This over-approximates what runs (a branch no test takes still counts, an error path is reached when its")
    L.append("function is) and misses a def used only as a value without its name in a body: read it as \"no test can")
    L.append("reach these\", not as line coverage. Reported, not gated.")
    L.append("")
    L.append("| file | defs | called directly | reached via facade | reached | unreached |")
    L.append("|---|---|---|---|---|---|")
    for f, total, direct, h_f, h in rows:
        L.append("| `%s` | %d | %d | %d | %d | %d |" % (f, total, direct, h_f, h, total - h))
    L.append("| **total** | **%d** | **%d** | **%d** | **%d** | **%d** |" % (tot, sum(r[2] for r in rows), hit_f, hit, tot - hit))
    L.append("")
    L.append("%.1f %% of the %d defs are reachable from the tests (%.1f %% through the facade alone)." % (
        100.0 * hit / max(tot, 1), tot, 100.0 * hit_f / max(tot, 1)))
    L.append("")
    any_un = {f: u for f, u in unreached.items() if u}
    if any_un:
        L.append("Unreached defs:")
        L.append("")
        for f, u in any_un.items():
            L.append("- `%s`: %s" % (f, ", ".join("`%s`" % d for d in u)))
        L.append("")
    return "\n".join(L), (tot, hit)


def files_md(files):
    """One row per annotated test file: its Polars twin (bench/coverage/<name>.py) or how its values were checked."""
    out = ["| test | cases | Polars 2.0.0 twin |", "|---|---|---|"]
    for p in files:
        stem = os.path.splitext(os.path.basename(p))[0]
        text = read(p)
        n = sum(1 for ln in text.splitlines() if ln.startswith("#|") and ln.startswith("#|-- "))
        twin = os.path.join(ROOT, "bench", "coverage", stem + ".py")
        if os.path.exists(twin):
            how = "[bench/coverage/%s.py](../bench/coverage/%s.py)" % (stem, stem)
            if "no line-by-line" in text or "no Polars twin" in text:
                how += " (reference values only; see the test header)"
            else:
                how += " (`bench/coverage/check.sh %s`: byte-for-byte after the documented departures applied in the twin)" % stem
        else:
            how = "none: expectation reasoned from the contract (see the test header)"
        out.append("| [%s](../%s) | %d | %s |" % (stem, rel(p), n, how))
    out.append("")
    return "\n".join(out)


def main(argv):
    check_only = "--check" in argv
    to_stdout = "--stdout" in argv
    errors = []
    ops = facade_ops()
    for op in ops:
        if op not in MEMBER_ROW:
            errors.append("facade def %s is in no matrix row (add it to ROWS, or NON_OPS if it is not an operation)" % op)
    for m in MEMBER_ROW:
        if m not in ops:
            errors.append("matrix names %s, which frame.bend does not define" % m)
    tests = [Test(p) for p in tests_files()]
    marks, n_annot = parse_annotations([t for t in tests], errors)
    res = matrix(marks, errors)
    missing = [(row, k) for row, cells in res.items() for k in KINDS if cells[k][0] == "missing"]
    by_row = {}
    for row, k in missing:
        by_row.setdefault(row, []).append(k)
    for row, ks in by_row.items():
        errors.append("MISSING %s: %s" % (row, " ".join(ks)))
    body, c = render_matrix(res, tests, marks)
    if not check_only:
        defs_md, (tot, hit) = render_defcalls(tests)
        files = sorted({t.path for ms in marks.values() for (_v, t, _r, _o) in ms})
        xf = sorted({"%s (%s)" % (rel(t.path), t.xfail) for ms in marks.values() for (_v, t, _r, _o) in ms if t.xfail})
        head = [
            "# Public-API coverage (plans/M_01.txt T6)",
            "",
            "Generated by `scripts/coverage_matrix.py` (`make coverage`); do not edit by hand. The script is the",
            "gate: it exits 1 when an operation lacks a kind, an annotation is invalid, or a facade def is in no row.",
            "",
            "Every released operation (every public def of `frame.bend`) has a row; a row has the six kinds:",
            "**success**, **null** (input with nulls), **empty** (zero rows; **0col** marks a zero-column frame case),",
            "**invalid** (an error path), **eager** and **lazy** (the lazy twin, with `collect_raw` / `collect` /",
            "`collect_full` agreeing with the eager dump, `tests/regress/lib/rx.bend` `four`). A cell is a test file",
            "holding such a case (`#@ cover` annotation, checked: the file must call the operation) or `n/a [k]` with",
            "the reason k listed below (`#@ na`, reason required). `other test files` counts the tests that call the",
            "operation without an annotation (a heuristic, report only). Cases are DF.dump-based with the expectation",
            "reasoned first and confirmed against Polars 2.0.0 where the semantics match (`bench/coverage/`), the",
            "documented departures (DESIGN.md 14, 15) applied by hand.",
            "",
            "%d annotated test files, %d annotation lines." % (len(files), n_annot),
        ]
        if xf:
            head += ["", "Cases pinning a known defect (`#! xfail`, shown `(xfail ID)` in the matrix): " + ", ".join(xf) + "."]
        head += ["", "What the gate proves and what it does not. It proves that every row has every kind accounted for by a",
                 "case named in an annotation, that each annotation names an operation its file really calls, and that no",
                 "facade def is outside the matrix. It cannot prove that a named case is a good one: whether the case in the",
                 "file really holds nulls / zero rows / a refusal is the author's assertion, checked by review. The cases",
                 "themselves are real tests (`make test` runs them and compares every dump with its expectation).",
                 "", "## Test files", "", files_md(files), "## Matrix", "", body, "## Def-call coverage over src/", "", defs_md]
        text = "\n".join(head)
        if to_stdout:
            print(text)
        else:
            os.makedirs(os.path.join(ROOT, "docs"), exist_ok=True)
            with open(os.path.join(ROOT, "docs", "COVERAGE.md"), "w", encoding="utf-8") as f:
                f.write(text)
    tot_cells = len(res) * len(KINDS)
    ok = sum(c[k][0] for k in KINDS)
    na = sum(c[k][1] for k in KINDS)
    print("coverage: %d rows x %d kinds = %d cells: %d covered, %d n/a, %d missing; %d problems" % (
        len(res), len(KINDS), tot_cells, ok, na, len(missing), len(errors)))
    if errors:
        for e in errors[:80]:
            print("  " + e)
        if len(errors) > 80:
            print("  ... %d more" % (len(errors) - 80))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
