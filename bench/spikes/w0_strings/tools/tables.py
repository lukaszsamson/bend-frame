"""Markdown tables (medians of the fresh-process samples, load range) from results/*.jsonl.
    python3 tools/tables.py            # prints every table DESIGN.md 17.9 uses
"""
import collections
import json
import os
import statistics

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RES = os.path.join(HERE, "results")


def load(name):
    p = os.path.join(RES, name)
    rows = collections.OrderedDict()
    if not os.path.exists(p):
        return rows
    for line in open(p):
        r = json.loads(line)
        rows.setdefault(r["cmd"], []).append(r)
    return rows


def med(rs, f):
    xs = []
    for r in rs:
        if f in ("max_rss_mb", "user_s", "real_s"):
            v = r.get(f)
        else:
            v = r["out"][-1].get(f) if r["out"] else None
        if isinstance(v, (int, float)):
            xs.append(v)
    return statistics.median(xs) if xs else None


def loads(rs):
    xs = [r["load_before"][0] for r in rs]
    return f"{min(xs):.0f}-{max(xs):.0f}"


def chk(rs):
    return sorted({str(r["out"][-1].get("chk")) for r in rs if r["out"]})


def find(rows, *words):
    for cmd, rs in rows.items():
        parts = cmd.split()
        if all(w in parts for w in words):
            return rs
    return None


def fmt(x, d=0):
    return "-" if x is None else (f"{x:.{d}f}" if d else f"{x:.0f}")


def t1():
    rows = load("t1_coder.jsonl")
    print("\nT1 coder (1 thread): ms = coding only (rows alive past the clock); ns/row and ns/char of the new coder")
    print("| shape | n | k | chars/row | new ms | old ms | speedup | new ns/row | new ns/char | load | codes equal |")
    print("|---|---|---|---|---|---|---|---|---|---|---|")
    for s in ["distinct", "prefix", "skew", "equal", "low", "uni"]:
        for n in ["100000", "300000", "1000000"]:
            a = find(rows, s, n, "new")
            b = find(rows, s, n, "old")
            if not a:
                continue
            na, nb = med(a, "ms"), med(b, "ms") if b else None
            k, ch = med(a, "k"), med(a, "chars")
            ok = "yes" if b and chk(a) == chk(b) else ("-" if not b else "NO")
            print(f"| {s} | {n} | {fmt(k)} | {ch / int(n):.1f} | {fmt(na)} | {fmt(nb)} | {('%.0fx' % (nb / max(na, 1))) if nb else '-'} | {na * 1e6 / int(n):.0f} | {na * 1e6 / ch:.1f} | {loads(a + (b or []))} | {ok} |")


def t2():
    rows = load("t2_ranks.jsonl")
    print("\nT2 lexical ranks (1 thread), ms: total (coder + stage) and the stage's parts")
    print("| shape | n | k | rrad total (code/pack/sort/rank) | rounds | rnew total (flat/sort) | rmap total (map) | rold | load | words equal |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    for s in ["distinct", "prefix", "skew", "low", "uni"]:
        for n in ["100000", "300000", "1000000"]:
            a = find(rows, s, n, "rrad")
            b = find(rows, s, n, "rnew")
            c = find(rows, s, n, "rmap")
            d = find(rows, s, n, "rold")
            if not a:
                continue
            same = len({tuple(chk(x)) for x in (a, b, c, d) if x}) == 1
            print(f"| {s} | {n} | {fmt(med(a, 'k'))} | {fmt(med(a, 'ms'))} ({fmt(med(a, 'code_ms'))}/{fmt(med(a, 'pack_ms'))}/{fmt(med(a, 'sort_ms'))}/{fmt(med(a, 'rank_ms'))}) | {fmt(med(a, 'rounds'))} | "
                  f"{fmt(med(b, 'ms')) if b else '-'} ({fmt(med(b, 'flat_ms')) if b else '-'}/{fmt(med(b, 'sort_ms')) if b else '-'}) | {fmt(med(c, 'ms')) if c else '-'} ({fmt(med(c, 'mapsort_ms')) if c else '-'}) | {fmt(med(d, 'ms')) if d else '-'} | {loads(a)} | {'yes' if same else 'NO'} |")


def t3():
    rows = load("t3_probe.jsonl")
    print("\nT3 parallel coding, owned hash partitions vs sequential borrowed (1M rows), ms")
    print("| shape | seq (1 thr) | part L, threads | total | hash | partition+move | lanes | remap+assemble | load | codes equal |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    for s in ["distinct", "prefix", "skew", "equal"]:
        seq = find(rows, s, "seq")
        for l, t in (("0", "1"), ("4", "1"), ("4", "4"), ("4", "12"), ("6", "12")):
            for cmd, rs in rows.items():
                p = cmd.split()
                if s in p and "part" in p and p[-1] == l and p[p.index("--threads") + 1] == t:
                    ok = "yes" if seq and chk(rs) == chk(seq) else "NO"
                    print(f"| {s} | {fmt(med(seq, 'ms')) if seq else '-'} | L={l}, {t} thr | {fmt(med(rs, 'ms'))} | {fmt(med(rs, 'hash_ms'))} | {fmt(med(rs, 'part_ms'))} | {fmt(med(rs, 'lanes_ms'))} | {fmt(med(rs, 'assemble_ms'))} | {loads(rs)} | {ok} |")


def t4():
    rows = load("t4_hot.jsonl")
    print("\nT4 hot-type tax in situ (41 MB), ms")
    print("| probe | ms | read | parse | max RSS MB | load |")
    print("|---|---|---|---|---|---|")
    for cmd, rs in rows.items():
        short = cmd.replace("bench/spikes/w0_strings/build/", "").replace("bench/data/", "")
        print(f"| {short} | {fmt(med(rs, 'ms'))} | {fmt(med(rs, 'read_ms'))} | {fmt(med(rs, 'parse_ms'))} | {fmt(med(rs, 'max_rss_mb'))} | {loads(rs)} |")


def t5():
    for name, title in (("t5_scale.jsonl", "T5 reader scaling (41 MB, 1M rows), ms"), ("t5_phases.jsonl", "T5 reader phase decomposition (1 thread), ms")):
        rows = load(name)
        print(f"\n{title}")
        print("| command | total | producer (read) | fork (lanes) | merge | max RSS MB | user s | load | chk |")
        print("|---|---|---|---|---|---|---|---|---|")
        for cmd, rs in rows.items():
            short = cmd.replace("bench/spikes/w0_strings/build/", "").replace("bench/data/sales_1000000.csv", "F")
            print(f"| {short} | {fmt(med(rs, 'ms'))} | {fmt(med(rs, 'read_ms'))} | {fmt(med(rs, 'fork_ms'))} | {fmt(med(rs, 'merge_ms'))} | {fmt(med(rs, 'max_rss_mb'))} | {fmt(med(rs, 'user_s'), 2)} | {loads(rs)} | {','.join(chk(rs))} |")


def t6():
    rows = load("t6_flat.jsonl")
    print("\nT6 hashing every row: cons String vs flat UTF-8 buffer (1 thread), ms")
    print("| shape | n | chars | flat words | cons hash | flat hash | flat build (untimed in use) | cons ns/char | flat ns/byte | load |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    for cmd, rs in rows.items():
        p = cmd.split()
        ch = med(rs, "chars")
        cons, flat = med(rs, "cons_hash_ms"), med(rs, "flat_hash_ms")
        print(f"| {p[3]} | {p[4]} | {fmt(ch)} | {fmt(med(rs, 'flat_words'))} | {fmt(cons)} | {fmt(flat)} | {fmt(med(rs, 'flat_build_ms'))} | {cons * 1e6 / ch:.1f} | {flat * 1e6 / ch:.2f} | {loads(rs)} |")


for f in (t1, t2, t3, t4, t5, t6):
    f()
