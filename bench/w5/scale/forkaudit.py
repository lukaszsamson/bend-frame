#!/usr/bin/env python3
"""bench/w5/scale/forkaudit.py -- find the fork-tree stall shape in an emitted Bend C file.

  ~/.bend/bin/bend x.bend -o x.c && python3 -I bench/w5/scale/forkaudit.py x.c [NAME_SUBSTRING ...]
  python3 -I bench/w5/scale/forkaudit.py --forks x.c [x2.c ...]            the forking defs, with their call tasks
  python3 -I bench/w5/scale/forkaudit.py --check bench/w5/scale/forkaudit.allow x.c [x2.c ...]   the gate

The runtime (2.0.36) grows a fork tree breadth-first (the grow pass) by running the tasks whose def can fork; a
task whose def is fork-free (FID_T flag 2) is never run by the grow pass. A forking def that CALLS a non-flat
fork-free def before its parallel let compiles that call to `task_node(.., 0); return term_tsk(..)` in
non-sequential mode: the call becomes a task of its own, the grow pass pushes it back and stops growing the row,
and the drain then runs it in sequential mode together with its continuation, the parallel let included, so the
whole subtree below runs on one thread (DESIGN.md 16.10). The default mode lists every `return term_tsk(FID_Y ..)`
inside a segment of a def that can fork (a `WL_CASE` whose FID is not fork-free), i.e. every call that can stall a
fork tree, as `def -> called def`; that includes the sequential program's own defs that merely CALL a forking def
(their calls run on the main thread, which is never in a grow turn: harmless), so it is noisy.

--forks and --check restrict the listing to the FORKING DEFS: a def that contains a parallel let (the segment
family `D`, `D_K<n>` ... has a join `D_J<n>` paired with a continuation `D_K<n>`). Of those only the call tasks inside
the def's own segments are listed (not the join continuation `D_J<n>`, which runs after the fork, in place). Names
are normalised (leading FID_ and underscores dropped, the `_K/_C/_J<n>` segment suffix dropped, a template-instance
suffix `_<n>` of an instantiated def kept out of the comparison by the allowlist's regular expressions).

--src FILE.bend [...] is the SOURCE lint, the part of the gate that needs no compile and sees the forking defs no
audited program reaches (the generated src/ckernels.bend wrappers, every def of a module the programs do not use):
for every parallel let (`a b = f(x) g(y)`) it requires (1) that no argument of a branch calls anything but the
inlined primitives (U32.* Bool.* Nat.* I32.* F32.* Char.*: the cuts, the splits and the clones that stalled the walks
were calls in branch arguments), and (2) that no statement before the fork in its block (the `case` arm, or the def
body) calls anything but those primitives. Any finding exits 1; there is no allowlist (move the work into a prelude).

--check ALLOW compares that listing, over all the given C files, with the allowlist: one entry per line,
`caller_regex -> callee_regex | reason` (fullmatch on the normalised names; `#` comments). It exits 1 on
  - a call task in a forking def that no entry allows (a NEW violation, or a leaf / join call to be reviewed), and
  - an entry that matched nothing in any of the files (a stale entry: the code changed, the reason may not hold).
Every entry carries the reason the call is not a stall: it is in LEAF position (the unit of work of the fork: a task
of its own by design), it is the root of a fork called from the sequential program (the main thread is never in a
grow turn: a helper before the fork costs one task, not the tree), or it sits in a sequential prelude that builds the
tree. The gate cannot tell a leaf call from a call in a branch argument, so a new call to an ALREADY allowed callee
from an allowed caller is not seen: read the diff of a forking def.
"""
import re
import sys


def load(path):
    src = open(path).read()
    fids = {int(m.group(2)): m.group(1) for m in re.finditer(r"#define (FID_\w+) (\d+)\n", src)}
    # the task table: Bend 2.0.36 emitted `CONSTV u8 FID_T[][3] = {{ar, resw, flags}, ..}` (fork-free = flags bit 1);
    # 2.0.38+ emits `typedef struct { u8 ar, resw, bangs, nofk; } Fid; CONSTV Fid FID_T[] = {..}` (fork-free = nofk)
    m = re.search(r"CONSTV Fid FID_T\[\] = \{(.*?)\};", src, re.S)
    if m:
        rows = re.findall(r"\{ (\d+), (\d+), (\d+), (\d+) \}", m.group(1))
        nofk = {fids[i]: int(nf) for i, (ar, rw, bg, nf) in enumerate(rows) if i in fids}
    else:
        m = re.search(r"CONSTV u8 FID_T\[\]\[3\] = \{(.*?)\};", src, re.S)
        if not m:
            sys.exit("forkaudit: no FID_T task table in %s (unknown Bend C layout: update load())" % path)
        rows = re.findall(r"\{ (\d+), (\d+), (\d+) \}", m.group(1))
        nofk = {fids[i]: (int(fl) & 2) >> 1 for i, (ar, rw, fl) in enumerate(rows) if i in fids}
    parts = re.split(r"\n  WL_CASE\((FID_\w+)\)\n", src)
    bodies = {parts[i]: parts[i + 1] for i in range(1, len(parts), 2)}
    return fids, nofk, bodies


# 2.0.36 spelled segments _K12 / _J12 / _C12; 2.0.38+ spells them _k12 / _j12 / _c12
SEG = re.compile(r"_[KCJkcj]\d+$")


def base(name):
    """a segment's def: FID_x_K12 / FID_x_J12 / FID_x_C12 -> FID_x (possibly nested: a segment of a segment)"""
    while SEG.search(name):
        name = SEG.sub("", name)
    return name


def pretty(name):
    return re.sub(r"^FID_+", "", base(name)).lower()


def forking_defs(fids, bodies):
    """defs with a parallel let: the join J<n> is paired with the continuation K<n> of the same family"""
    out = set()
    names = set(fids.values())
    for n in names:
        m = re.match(r"(.*)_([Jj])(\d+)$", n)
        k = "_K" if m and m.group(2) == "J" else "_k"
        if m and (m.group(1) + k + m.group(3)) in names:
            out.add(m.group(1))
    return out


def sites(path, only_forking):
    fids, nofk, bodies = load(path)
    fk = forking_defs(fids, bodies)
    found = []
    for name, body in bodies.items():
        if nofk.get(name, 1):
            continue
        b = base(name)
        if only_forking and b not in fk:
            continue
        if re.search(r"_[Jj]\d+$", name):
            continue  # the join continuation: runs after the fork, in place
        for m in re.finditer(r"return term_tsk\((FID_\w+),", body):
            callee = m.group(1)
            if not nofk.get(callee, 0):
                continue  # a forking callee is entered directly (WL_JMP); the guard is fid_nofk(callee)
            if re.match(re.escape(b) + r"_[Jj]\d+$", callee):
                continue  # this def's own join task
            found.append((name, callee))
    return found, fk


def parse_allow(path):
    ents = []
    for n, line in enumerate(open(path), 1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        m = re.match(r"^(\S+)\s*->\s*(\S+)\s*\|\s*(.+)$", line)
        if not m:
            sys.exit(f"{path}:{n}: expected `caller_regex -> callee_regex | reason`")
        ents.append((re.compile(m.group(1)), re.compile(m.group(2)), m.group(3), n, [0]))
    return ents


def norm(s):
    # the program's own path prefix (src_ vs ____src_ in tests/) is irrelevant
    return re.sub(r"^_*(src_)?", "", s)


NFORKS = [0]
PRIM = ("U32.", "Bool.", "Nat.", "I32.", "F32.", "Char.")
CALL = re.compile(r"(?<![\w.])([A-Za-z_][\w.']*)\(")


def top_level_parts(rhs):
    d, parts, cur = 0, [], ""
    for ch in rhs:
        if ch in "([{":
            d += 1
        if ch in ")]}":
            d -= 1
        if ch == " " and d == 0:
            if cur:
                parts.append(cur)
                cur = ""
        else:
            cur += ch
    if cur:
        parts.append(cur)
    return parts


def bad_calls(expr, skip_head=False):
    """the non-primitive names called inside an expression (constructor applications `C{..}` are not calls)"""
    names = [m.group(1) for m in CALL.finditer(expr)]
    if skip_head and names:
        names = names[1:]
    return [n for n in names if not n.startswith(PRIM)]


def lint_src(path):
    """the parallel lets of a .bend file whose branch arguments or preceding statements call non-primitives"""
    out = []
    lines = open(path).read().split("\n")
    cur_def = "?"
    for i, raw in enumerate(lines):
        if raw.startswith("def "):
            cur_def = re.match(r"def ([^\s(]+)", raw).group(1)
        s = raw.strip()
        if not s or s.startswith("#"):
            continue
        m = re.match(r"^((?:\(?[A-Za-z_][\w']*\)?[ ,]+)+)=\s(?!=)(.*)$", s)
        if not m or not raw.startswith(" "):
            continue
        parts = top_level_parts(m.group(2))
        calls = [p for p in parts if re.match(r"^[A-Za-z_][\w.']*\(", p)]
        if not (len(calls) >= 2 and len(parts) == len(calls) and "," not in m.group(1).replace(" ", "")):
            continue
        NFORKS[0] += 1
        where = f"{path}:{i + 1}: {cur_def}"
        for c in calls:
            for n in bad_calls(c, skip_head=True):
                out.append(f"{where}: a branch argument calls {n} (a non-flat helper becomes a task that stops the grow pass)")
        ind = len(raw) - len(raw.lstrip(" "))
        j = i - 1
        while j >= 0:
            r2 = lines[j]
            t2 = r2.strip()
            if not t2 or t2.startswith("#"):
                j -= 1
                continue
            ind2 = len(r2) - len(r2.lstrip(" "))
            if ind2 < ind:
                break  # the `case` arm head / the def line
            if ind2 == ind:
                for n in bad_calls(t2):
                    out.append(f"{where}: before the fork, `{t2[:60]}` calls {n} (work before the parallel let)")
            j -= 1
    return out


def main():
    args = sys.argv[1:]
    mode = "list"
    allow = None
    if args and args[0] == "--forks":
        mode, args = "forks", args[1:]
    elif args and args[0] == "--src":
        bad = []
        for f in args[1:]:
            bad += lint_src(f)
        for b in bad:
            print(b)
        print(f"fork-audit --src: {len(args) - 1} file(s), {NFORKS[0]} parallel let(s), {len(bad)} finding(s)")
        return 1 if bad else 0
    elif args and args[0] == "--check":
        mode, allow, args = "check", args[1], args[2:]
    if mode == "list":
        path, want = args[0], args[1:]
        found, _ = sites(path, False)
        n = 0
        for name, callee in found:
            if want and not any(w in name or w in callee for w in want):
                continue
            print(f"{name} -> {callee}")
            n += 1
        print(f"{n} call task(s) inside forking segments")
        return 0
    files = [a for a in args if a.endswith(".c")]
    if not files:
        sys.exit("usage: forkaudit.py [--forks | --check ALLOW] x.c [x2.c ...]")
    seen = {}
    allfk = set()
    for f in files:
        found, fk = sites(f, True)
        allfk |= {pretty(x) for x in fk}
        for name, callee in found:
            seen.setdefault((pretty(name), pretty(callee)), set()).add(f)
    if mode == "forks":
        for fk in sorted(allfk):
            print(fk)
            for (a, b), fs in sorted(seen.items()):
                if a == fk:
                    print(f"    -> {b}")
        print(f"{len(allfk)} forking def(s), {len(seen)} call task(s)")
        return 0
    ents = parse_allow(allow)
    bad = []
    for (a, b), fs in sorted(seen.items()):
        ok = False
        for ca, cb, reason, n, hit in ents:
            if ca.fullmatch(norm(a)) and cb.fullmatch(norm(b)):
                hit[0] += 1
                ok = True
        if not ok:
            bad.append((a, b, sorted(fs)))
    stale = [(n, ca.pattern, cb.pattern) for ca, cb, reason, n, hit in ents if hit[0] == 0]
    for a, b, fs in bad:
        print(f"NEW call task in a forking def: {a} -> {b}   ({', '.join(fs)})")
    for n, ca, cb in stale:
        print(f"{allow}:{n}: stale allowlist entry (matched nothing): {ca} -> {cb}")
    print(f"fork-audit: {len(allfk)} forking def(s), {len(seen)} call task(s), {len(ents)} allowlist entr(ies), "
          f"{len(bad)} new, {len(stale)} stale")
    if bad:
        print("A forking def must do nothing but match (and call FLAT helpers) before its parallel let: build the work "
              "tree in a sequential prelude and fork by match only (DESIGN.md 16.10). If the call is a leaf, a "
              "join or a root-level prelude, add an entry with the reason to " + allow + ".")
    return 1 if (bad or stale) else 0


if __name__ == "__main__":
    sys.exit(main())
