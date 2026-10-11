"""Operation counts per flat loop (spin_N function with a WL_SPIN) of an emitted Bend C file
(`bend x.bend -o x.c`), transitively through the spin_N functions a loop calls.

    python3 bench/w6/cops.py build/w6/probe.c                 # every loop with a hot-path op or an array op
    python3 bench/w6/cops.py build/w6/probe.c spin_310 ...    # these loops: counts and the Bend locals they carry
    python3 bench/w6/cops.py build/w6/probe.c --names         # the known lane / producer loops by their locals

The C keeps each Bend variable as `_name_N`, which is how a spin is matched to its def (the name
lists below). A flat loop shows only blk_read / blk_write (array access) and WL_AGAIN (the native
tail loop); term_keep / ctr_take / rfc_seal are reference counts, blk_copy / blk_half / blk_node
array copies, heap_alloc / term_ctr allocations; term_peek is a borrow.
"""
import re
import sys

src = open(sys.argv[1]).read()
funcs = {}
for m in re.finditer(r"^(?:INLINE|FAR|OUTLINE|static)[^\n]*?\b(spin_\d+)\(([^\n]*)\{\n(.*?)^\}\n", src, re.M | re.S):
    funcs[m.group(1)] = m.group(3)

OPS = ["term_keep", "ctr_take", "rfc_seal", "blk_copy", "blk_half", "blk_node", "heap_alloc", "term_ctr",
       "blk_read", "blk_write", "task_node", "WL_AGAIN"]


def counts(name, seen=None):
    seen = seen if seen is not None else set()
    if name in seen or name not in funcs:
        return {}
    seen.add(name)
    body = funcs[name]
    c = {o: len(re.findall(r"\b" + o + r"\b", body)) for o in OPS}
    for callee in set(re.findall(r"\b(spin_\d+)\(e", body)):
        for k, v in counts(callee, seen).items():
            c[k] = c.get(k, 0) + v
    return c


def locals_of(name):
    return sorted(set(re.findall(r"\b_([a-z][a-z0-9]*)_\d+ = r", funcs[name])))


def show(n):
    c = counts(n)
    return f"{n:9s} lines={funcs[n].count(chr(10)):5d} " + " ".join(f"{k}={v}" for k, v in c.items() if v)


args = [a for a in sys.argv[2:] if not a.startswith("--")]
if "--find" in sys.argv:
    want = [t for t in args[0].split(",")]
    for n in sorted(funcs, key=lambda n: int(n[5:])):
        if all(t in locals_of(n) for t in want):
            print(show(n), "WL_SPIN" in funcs[n])
elif args:
    for n in args:
        print(show(n))
        print("          locals:", " ".join(locals_of(n)))
elif "--names" in sys.argv:
    KNOWN = {
        "Pk.go producer (pack + scan a piece)": ["cut", "lfc", "acc", "sh"],
        "Tk.go2 tokenizer": ["fs0", "esc", "rgn", "rag"],
        "Tk.skipb / Tk.skipq text runs": ["sk", "sep"],
        "Lw.go u32 / i32 / bool column": ["bad", "fr", "nulls", "out", "t", "v"],
        "Lf.go f32 column (a spin_N per step)": ["bad", "fe", "fq", "fs", "nulls", "out", "pv"],
        "Rw.go raw string column (decodes)": ["fe", "fq", "fs", "nulls", "ok", "out", "rs"],
        "Sc.go Dictionary coder rows": ["hs", "rp", "ids"],
    }
    for title, toks in KNOWN.items():
        hits = [n for n, b in funcs.items() if "WL_SPIN" in b and all(t in locals_of(n) for t in toks)]
        for n in sorted(hits, key=lambda n: len(funcs[n]))[:3]:
            print(f"{title:38s} {show(n)}")
else:
    for n in sorted(funcs, key=lambda n: int(n[5:])):
        if "WL_SPIN" in funcs[n]:
            print(show(n))
