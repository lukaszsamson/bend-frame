"""W6.3 mutation controls: each mutant of the v0.2 reader (src/csv.bend Csv.v2.*, src/csvlane.bend Lc.*) is
applied in place, the W6.3 tests run, the file is restored. Every mutant must be KILLED except the documented
equivalent one ("odd parity ignored": the last lane rejects in mode ME anyway; DESIGN.md 14 W6.3 item 6).

    python3 bench/w6/mut63.py [extra test files]      # from the repository root; ~5 min
"""
import subprocess, sys, shutil, os
os.chdir(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
os.makedirs('build/w6', exist_ok=True)
BEND = os.path.expanduser('~/.bend/bin/bend')
muts = [
 ('src/csv.bend', 'Bool.or(U32.is_eq(x, 0), U32.is_gt(x, lim))', 'Bool.or(U32.is_eq(x, 0), U32.is_ge(x, lim))', 'ci.ok off by one'),
 ('src/csv.bend', 'off2, Bool.and(U32.is_lt(off2, lim), U32.is_eq(rej, 0))}', 'off2, False{}}', 'head classifies one region only'),
 ('src/csv.bend', 'Csv.dict_over(enc, U32.inc(code), U32.inc(row))', 'Csv.dict_over(enc, U32.inc(code), U32.add(row, 2))', 'EncAuto row off by one'),
 ('src/csv.bend', 'Csv.dict_over(enc, U32.inc(code), U32.inc(row))', 'Csv.dict_over(enc, code, U32.inc(row))', 'EncAuto code off by one'),
 ('src/csv.bend', '+first = Bool.and(U32.is_ne(rag, 0), U32.is_eq(rg, 0))\n      QSM', '+first = U32.is_ne(rag, 0)\n      QSM', 'last ragged region wins'),
 ('src/csv.bend', 'Csv.v2.hrec(hdr, sep, U32.inc(p), U32.add(ln, U32.inc(nlf)), rec)', 'Csv.v2.hrec(hdr, sep, U32.inc(p), U32.add(ln, nlf), rec)', 'header line0 off by one'),
 ('src/csv.bend', 'QH{QMR{}, U32.inc(p), ln, Bool.to_u32(U32.is_eq(b, 34)), 0, b <> (13 <> rec)}', 'QH{QMR{}, U32.inc(p), ln, Bool.to_u32(U32.is_eq(b, 34)), 0, b <> rec}', 'header drops the CR'),
 ('src/csv.bend', 'Csv.v2.ci.f(+g: U32, +l: U32, +off: U32) -> U32:\n  Csv.v2.sel(Bool.and(U32.is_eq(g, 0), U32.is_ne(l, 0)), U32.add(off, l), g)', 'Csv.v2.ci.f(+g: U32, +l: U32, +off: U32) -> U32:\n  Csv.v2.sel(Bool.and(U32.is_eq(g, 0), U32.is_ne(l, 0)), l, g)', 'class ignores the row offset'),
 ('src/csv.bend', 'Csv.v2.comb.cap(K.Kernel.check_rows.cap(cap, n), n,', 'Csv.v2.comb.cap(None{}, n,', 'no row cap'),
 ('src/csv.bend', 'case P.PrOk{nr, odd, regs}:\n      Csv.v2.odd(U32.is_ne(odd, 0)', 'case P.PrOk{nr, odd, regs}:\n      Csv.v2.odd(False{}', 'odd parity ignored'),
 ('src/csv.bend', '      Bool.pick(QD, U32.is_eq(size, 0), QDNone{}, QDOk{Csv.gen_names(1n, 0n), 1, 0, 1})', '      QDNone{}', 'headerless blank file is empty'),
 ('src/csv.bend', 'case _ QG{ents, fr, dict, map, True{}}:\n      QG{ents, fr, dict, map, True{}}', 'case _ QG{ents, fr, dict, map, True{}}:\n      QG{ents, fr, dict, map, False{}}', 'merge never stops'),
 ('src/csv.bend', 'Csv.v2.x.raw(m, off, nulls, ST.Dict.decode(off, d, oc, dict), ov, c, v, ents)', 'Csv.v2.x.raw(m, off, nulls, ST.Dict.decode(0, d, oc, dict), ov, c, v, ents)', 'fall back forgets the prefix'),
 ('src/csv.bend', 'Fail{E.ParseError{line, "expected "', 'Fail{E.ParseError{U32.inc(line), "expected "', 'ragged line'),
 ('src/csv.bend', '    case Some{e}:\n      Csv.v2.whole(Some{e}, Csv.v2.tyn(U32.to_nat(w)), ts', '    case Some{e}:\n      Csv.v2.whole(None{}, Csv.v2.tyn(U32.to_nat(w)), ts', 'count error dropped'),
 ('src/csv.bend', 'Csv.v2.x.zero(Bool.and(U32.is_eq(n, 0), Csv.dict_over(enc, 1, 0))', 'Csv.v2.x.zero(False{}', 'no zero-row storage rule'),
 ('src/csvlane.bend', 'Lc.first(U32.is_eq(sf, 2), r, ff)', 'ff', 'f32 class never fails'),
 ('src/csvlane.bend', 'Lc.first(U32.is_ne(su, 0), r, fv)', 'Lc.first(U32.is_eq(su, 1), r, fv)', 'has_value only on u32'),
]
tests = ['tests/csv_v02_adv.bend', 'tests/csv_v02_infer.bend', 'tests/csv_v02_texts.bend'] + sys.argv[1:]
for f, a, b, name in muts:
    src = open(f).read()
    if src.count(a) != 1:
        print('SKIP (pattern count %d): %s' % (src.count(a), name)); continue
    shutil.copy(f, 'build/w6/mut63_backup.bend')
    try:
        open(f, 'w').write(src.replace(a, b))
        killed = []
        for t in tests:
            r = subprocess.run([BEND, t], capture_output=True, text=True, timeout=600)
            out = r.stdout + r.stderr
            bad = [l for l in out.splitlines() if ': ok' not in l and l.strip()]
            if r.returncode != 0 or bad:
                killed.append((t, (bad or [out[-200:]])[0][:150]))
        print(('KILLED' if killed else 'SURVIVED') + ': ' + name + ('  <- ' + killed[0][0] + ': ' + killed[0][1] if killed else ''))
    finally:
        shutil.copy('build/w6/mut63_backup.bend', f)
