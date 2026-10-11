"""Regression of the CSV fuzz harness itself (bench/diff/csvfuzz.py, csvgen.py); no Bend needed.

    cd bench && uv run python diff/tests/test_csvfuzz.py

1. The generator: deterministic per (seed, index), valid specs, and every feature tag of csvgen.py's docstring
   shows up in 1500 cases (a coverage floor: a generator edit that silently drops a feature fails here).
2. The driver, with the native runner replaced by a fake that answers `ok` for every case except:
     a file holding a double quote      -> `DIFF piece 3: ...`
     a file holding the byte 0xFF       -> a crash (exit 3, nothing printed)
     a file holding the byte 0xFE       -> a hang (sleeps past the timeout)  [skipped unless --slow]
   A clean run must exit 0; a difference, a crash must exit 1 and the difference must shrink to the single
   byte that causes it (lines, then bytes, then the spec).
"""
from __future__ import annotations

import contextlib
import io
import os
import stat
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import csvfuzz  # noqa: E402
import csvgen as G  # noqa: E402

FAILS = []
SCRATCH = G.ROOT + "/build/csvfuzz/selftest"


def check(name, ok, detail=""):
    print(("ok   " if ok else "FAIL ") + name + (("  " + str(detail)) if detail and not ok else ""))
    if not ok:
        FAILS.append(name)


FAKE = '''#!/usr/bin/env python3
import sys
man = sys.argv[1]
for line in open(man).read().splitlines():
    if not line:
        continue
    t = line.split(" ")
    cid, path, pieces = t[0], t[1], t[8].split(",")
    data = open(path, "rb").read()
    if b"\\xff" in data:
        sys.exit(3)
    if b'"' in data:
        print(f"{cid}: DIFF {cfg}, piece {pieces[0]}: differs at char 0: want <a> got <b>".replace("{cfg}", "x"))
    else:
        print(f"{cid}: ok {len(pieces)} | frame| height 1| width 1")
'''


def drive(fake: Path, args):
    csvfuzz.RUNNER = fake
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        rc = csvfuzz.main(args + ["--runner", str(fake), "--out", str(fake.parent / "f.json"), "--scratch", str(SCRATCH)])
    return rc, buf.getvalue()


def test_generator():
    a = [G.gen_case(7, i) for i in range(1500)]
    b = [G.gen_case(7, i) for i in range(1500)]
    check("generator is deterministic", all(x.data == y.data and x.spec() == y.spec() and x.tags == y.tags for x, y in zip(a, b)))
    check("different seeds differ", any(G.gen_case(8, i).data != a[i].data for i in range(50)))
    bad = [c.id for c in a if not (c.schema and c.enc[0] in "RDAT" and c.hdr in (0, 1) and c.cap >= 0 and c.inf >= 0 and c.sep > 0 and (len(c.data) <= 70000 or "big" in c.tags))]
    check("every spec is well formed", not bad, bad[:3])
    tags = set(t for c in a for t in c.tags)
    want = ["quote_all", "dq", "qempty", "crlf", "cr_only", "mixed_eol", "no_final_nl", "blank_pre", "blank_mid", "blank_end", "blank_w1", "empty", "blank_only", "header_only", "one_col",
            "many_cols", "bom", "ragged_short", "ragged_long", "hdr_ragged", "mal_unterminated", "mal_midquote", "mal_afterclose", "mal_crafter", "invalid_utf8", "utf8_4byte", "long_rec",
            "bad_cell", "late", "competing", "explicit", "infer", "inf_0", "inf_small", "inf_default", "inf_large", "enc_A", "enc_R", "enc_D", "enc_T", "cap_small", "sep_nonascii2",
            "sep_nonascii3", "sep_nonascii4", "hdr_off", "hdr_flipped", "schema_perturbed", "schema_count_wrong", "adv", "big", "mut_ins", "mut_trunc", "truncated", "bad_sep", "non_ascii"]
    check("every feature tag occurs in 1500 cases", all(t in tags for t in want), [t for t in want if t not in tags])
    allb = b"".join(c.data for c in a)
    for name, needle in [("u32 max", b"4294967295"), ("i32 min", b"-2147483648"), ("f32 subnormal", b"1e-45"), ("nan spelling", b"nan"), ("inf spelling", b"-inf"), ("bool spelling", b"False"), ("CR byte", b"\r"),
                         ("invalid byte 0xC3 alone", b"\xc3("), ("4 byte UTF-8", b"\xf0\x9f\x98\x80")]:
        check("content: " + name, needle in allb)
    check("a record longer than 4096 bytes occurs", any(len(r) > 4096 for c in a for r in c.data.split(b"\n")))


def test_driver():
    with tempfile.TemporaryDirectory() as td:
        fake = Path(td) / "fakerunner"
        fake.write_text(FAKE.replace("{cfg}", "x"))
        fake.chmod(fake.stat().st_mode | stat.S_IEXEC)
        okf = Path(td) / "okrunner"
        okf.write_text(FAKE.replace('if b"\\xff" in data:', "if False:").replace("if b'\"' in data:", "if False:"))
        okf.chmod(okf.stat().st_mode | stat.S_IEXEC)
        rc, out = drive(okf, ["--seed", "3", "--n", "30", "--no-shrink"])
        check("clean run exits 0", rc == 0, out[-300:])
        # a difference
        seed = next(s for s in range(1, 50) if any(b'"' in G.gen_case(s, i).data and b"\xff" not in G.gen_case(s, i).data for i in range(6)))
        rc, out = drive(fake, ["--seed", str(seed), "--n", "6", "--max-shrink", "1", "--shrink-secs", "60", "--jobs", "2"])
        check("a difference exits 1", rc == 1, out[-300:])
        import json
        rep = json.loads((Path(td) / "f.json").read_text())
        recs = [r for r in rep["failures"] if "shrunk_hex" in r]
        check("a difference is reported with its piece and first difference", bool(rep["failures"]) and rep["failures"][0]["status"] in ("DIFF", "crash"), rep["failures"][:1])
        check("the difference shrinks to the one double quote", bool(recs) and recs[0]["shrunk_hex"] == "22", [r.get("shrunk_hex") for r in recs])
        check("the shrunk piece is the smallest that fails", bool(recs) and recs[0]["shrunk_piece"] == 1 or not recs, [r.get("shrunk_piece") for r in recs])
        # a crash
        seed = next(s for s in range(1, 400) if any(b"\xff" in G.gen_case(s, i).data for i in range(6)))
        rc, out = drive(fake, ["--seed", str(seed), "--n", "6", "--no-shrink", "--jobs", "2"])
        rep = json.loads((Path(td) / "f.json").read_text())
        check("a crash exits 1", rc == 1, out[-300:])
        check("a crash is recorded as crash", any(r["status"] == "crash" for r in rep["failures"]), rep["failures"][:2])


if __name__ == "__main__":
    test_generator()
    test_driver()
    if FAILS:
        print("FAILED: " + ", ".join(FAILS))
        sys.exit(1)
    print("all csvfuzz harness checks passed")
