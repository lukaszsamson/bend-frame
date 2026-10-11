"""Summary tables of a bench/w2/campaign.sh run (JSONL from bench/w2/run.py).

    python3 bench/w2/tables.py bench/w2/results/w2_provisional.jsonl

Per (mode, shape, n): the median of the program's own `ms` over the fresh processes, the raw
samples, the load (1-minute, before each process) range, and whether the checksums agree between
the v0.1 mode and the new one (equal chk = the same codes / words). Per-row growth: new ns per row
at n over new ns per row at 100000 (the 17.8 threshold: <= 2x from 100k to 1M).
"""
import json
import statistics
import sys
from collections import defaultdict

recs = defaultdict(list)
for line in open(sys.argv[1]):
    r = json.loads(line)
    if r.get("exit") != 0 or not r.get("out"):
        continue
    o = r["out"][-1]
    if "w2" not in o:
        continue
    recs[(o["w2"], o["shape"], o["n"])].append((o, r))


def med(mode, shape, n, key="ms"):
    xs = [o[key] for o, r in recs.get((mode, shape, n), []) if key in o]
    return statistics.median(xs) if xs else None


def raw(mode, shape, n, key="ms"):
    return [o[key] for o, r in recs.get((mode, shape, n), []) if key in o]


def chk(mode, shape, n):
    return sorted({o["chk"] for o, r in recs.get((mode, shape, n), [])})


def load(mode, shape, n):
    ls = [r["load_before"][0] for o, r in recs.get((mode, shape, n), [])]
    return f"{min(ls):.0f}-{max(ls):.0f}" if ls else "-"


def f(x, w=7):
    return f"{x:{w}.0f}" if x is not None else f"{'-':>{w}}"


shapes = ["distinct", "prefix", "skew", "equal", "low", "uni"]
sizes = [100000, 300000, 1000000]


def table(title, old, new, extra=()):
    print(f"\n{title}  (ms = median of the program's own timer; raw samples in brackets; 1 thread)")
    print(f"{'shape':9s} {'n':>8s} {'k':>8s} {'old':>8s} {'new':>7s} {'speedup':>8s} {'new ns/row':>10s} {'growth':>7s} "
          f"{'equal':>6s} {'load':>9s}  " + " ".join(f"{e:>8s}" for e in extra) + "   raw old | new")
    for sh in shapes:
        base = None
        for n in sizes:
            o, w = med(old, sh, n), med(new, sh, n)
            if o is None and w is None:
                continue
            ks = [x[0].get("k") for x in recs.get((new, sh, n), [])]
            k = ks[0] if ks else None
            nsr = w * 1e6 / n if w is not None else None
            if n == 100000:
                base = nsr
            growth = (nsr / base) if (nsr and base) else None
            co, cn = chk(old, sh, n), chk(new, sh, n)
            eq = "yes" if (co and cn and co == cn) else ("-" if not co else "NO")
            ex = " ".join(f"{f(med(e, sh, n)):>8s}" for e in extra)
            print(f"{sh:9s} {n:8d} {k if k is not None else '-':>8} {f(o, 8)} {f(w)} {(o / w if o and w else float('nan')):7.1f}x "
                  f"{(nsr if nsr else float('nan')):10.0f} {(growth if growth else float('nan')):6.2f}x {eq:>6s} "
                  f"{load(new, sh, n):>9s}  {ex}   {raw(old, sh, n)} | {raw(new, sh, n)}")


table("COMPUTE CODES: Sort.str_codes_par (old) vs Hc.code (new: FNV-1a + byte lengths); newh = ST.Str.hash only",
      "old", "new", extra=("newh",))
table("SORT WORDS: Sort.str_words (old; frees its rows inside the call) vs Rk.words (new; rows handed back)",
      "rold", "rnew")

print("\nrank stage split (rstage, ms medians): code / rank stage (pack + rounds + scatter) / gather")
print(f"{'shape':9s} {'n':>8s} {'code':>7s} {'rank':>7s} {'gather':>7s} {'total':>7s}")
for sh in shapes:
    for n in sizes:
        t = med("rstage", sh, n)
        if t is None:
            continue
        print(f"{sh:9s} {n:8d} {f(med('rstage', sh, n, 'code_ms'))} {f(med('rstage', sh, n, 'rank_ms'))} "
              f"{f(med('rstage', sh, n, 'gather_ms'))} {f(t)}")

print("\nDictionary ranks of the distinct rows (dold = ST.Dict.ranks, dnew = Rk.dict)")
print(f"{'n':>8s} {'dold':>8s} {'dnew':>7s} {'speedup':>8s} {'equal':>6s}   raw old | new")
for n in sizes:
    o, w = med("dold", "distinct", n), med("dnew", "distinct", n)
    if o is None and w is None:
        continue
    co, cn = chk("dold", "distinct", n), chk("dnew", "distinct", n)
    print(f"{n:8d} {f(o, 8)} {f(w)} {(o / w if o and w else float('nan')):7.1f}x {('yes' if co and co == cn else 'NO'):>6s}   "
          f"{raw('dold', 'distinct', n)} | {raw('dnew', 'distinct', n)}")

# per-row growth of the stage (new words), all shapes
print("\nWords per-row growth 100k -> 1M (rnew ns/row at n over at 100k)")
for sh in shapes:
    a, b = med("rnew", sh, 100000), med("rnew", sh, 1000000)
    if a and b:
        print(f"  {sh:9s} {a * 1e6 / 100000:6.0f} -> {b * 1e6 / 1000000:6.0f} ns/row = {b * 1e6 / 1000000 / (a * 1e6 / 100000):.2f}x")
