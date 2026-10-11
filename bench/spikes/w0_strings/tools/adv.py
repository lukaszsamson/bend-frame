"""W0 spike T5b: adversarial differential test of the piece reader (rd.bend) against today's
reader (Csv.read_with, explicit schema), over many piece sizes.

    python3 tools/adv.py [BIN]          # BIN default build/rd_adv (rd_frame.bend built)

Each case is a CSV (bytes) and a schema string (U u32, S str, F f32, B bool). The reference is
`BIN <file> 0 ref <schema>`; the candidate `BIN <file> <P> spike <schema>` for every piece size
P in PIECES. Compared: the canonical error (malformed / ragged <line> <width> / bad <column>
<line> / ok) and, when ok, the row count and the checksum of every cell (values, validity,
dictionary codes and size). Records every run to results/t5_adv.jsonl; exits 1 on a mismatch
that is not listed in KNOWN.
"""
import json
import os
import random
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIN = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "build", "rd_adv")
OUT = os.path.join(HERE, "build", "adv")
PIECES = [1, 2, 3, 4, 5, 7, 8, 13, 16, 31, 64, 97, 256, 4096, 1 << 20]
os.makedirs(OUT, exist_ok=True)

# a case whose header comes after leading blank lines can lose its header when the first region
# holds only blank lines (the spike propagates "header pending" to the next region only when a
# region is empty); the design parses the header sequentially before the regions (DESIGN 17.6)
KNOWN = {"lead_blank", "empty"}


def rnd_str(r, n):
    alpha = "abcxyz ,\"\r\né日\U0001F600"
    return "".join(r.choice(alpha) for _ in range(n))


def q(s):
    return '"' + s.replace('"', '""') + '"'


def cases():
    r = random.Random(7)
    c = {}
    # quoted newlines in every record, doubled quotes everywhere, CRLF, multibyte
    rows = ["a,b,c"]
    for i in range(300):
        rows.append(",".join([q(rnd_str(r, r.randint(0, 12))), q('x""y' * (i % 3)), q(f"line{i}\nnext\r\nend")]))
    c["quoted_nl"] = ("\n".join(rows) + "\n", "SSS")
    c["quoted_nl_crlf"] = ("\r\n".join(rows) + "\r\n", "SSS")
    # bare fields with CR content, lone CR, CR before LF, final CR without LF
    c["cr_soup"] = ("a,b\nx\r,y\n\r,z\nq\r\r,w\r\r\nlast,one\r", "SS")
    # UTF-8: 2/3/4-byte sequences in every field, typed columns with spaces
    rows = ["s,u,f,b"]
    for i in range(400):
        rows.append(f"{rnd_str(r, 5).replace(',', '').replace(chr(34), '').replace(chr(10), '').replace(chr(13), '')},  {i} , {i}.25 ,{' true ' if i % 2 else 'False'}")
    c["utf8_typed"] = ("\n".join(rows) + "\n", "SUFB")
    # records longer than many pieces
    rows = ["k,v"]
    for i in range(20):
        rows.append(q(("long field " * 30 + "\n") * 3) + "," + str(i))
    c["long_records"] = ("\n".join(rows), "SU")
    # blank lines between records (w > 1: skipped), at the end, single-column nulls
    c["blanks_w2"] = ("a,b\n1,x\n\n\r\n2,y\n\n", "US")
    c["blanks_w1"] = ("a\n1\n\n2\n\r\n3\n", "U")
    c["lead_blank"] = ("\n\n\r\na,b\n1,2\n", "UU")
    c["empty"] = ("", "UU")
    c["header_only"] = ("a,b\n", "US")
    c["no_final_nl"] = ("a,b\n1,2\n3,4", "UU")
    # invalid UTF-8 bytes: distinct byte keys decoding to the same string (U+FFFD)
    c["bad_utf8"] = (b"s,u\n\xff,1\n\xfe,2\n\xc3,3\n\xe2\x82,4\n\xff,5\n\xef\xbf\xbd,6\n".decode("latin-1"), "SU")
    # malformed quoting at various places (malformed wins over everything)
    c["mal_bare_quote_late"] = ("a,b\n" + "1,x\n" * 200 + 'x"y,2\n' + "3,z\n" * 50, "SS")
    c["mal_after_close"] = ("a,b\n" + "1,x\n" * 100 + '"ab"c,2\n', "SS")
    c["mal_unclosed"] = ("a,b\n" + "1,x\n" * 100 + '"never closed,2\n3,4\n', "SS")
    c["mal_cr_quote"] = ("a,b\n1,\r\"x\"\n", "SS")
    c["mal_and_ragged"] = ("a,b\n1\n" + "1,x\n" * 100 + 'q"q,2\n', "SS")
    # ragged: the first one wins (short and long), with a bad cell earlier
    c["ragged_short"] = ("a,b,c\n" + "1,2,3\n" * 120 + "1,2\n" + "1,2,3,4\n", "UUU")
    c["ragged_after_bad"] = ("a,b\n" + "x,2\n" + "1,2\n" * 150 + "1,2,3\n", "UU")
    # bad cells: the first COLUMN in column order wins, at its first row
    c["bad_cols"] = ("a,b,c\n" + "1,2.5,true\n" * 80 + "1,zz,true\n" + "1,2.5,true\n" * 80 + "q,2.5,true\n" + "1,2.5,maybe\n", "UFB")
    # numeric edge cases (fast path vs F32.read slow path vs U32.read)
    fl = ["1e3", ".5", "5.", "+5", "-0", "nan", "inf", "-inf", " 1.5 ", "0.1000000000001", "16777217",
          "16777216", "3.4028235e38", "1e-45", "394.47", "0.06", "-12.75", "1.0000000001", '"7.5"', '""', "  "]
    c["f32_edges"] = ("x\n" + "\n".join(fl) + "\n", "F")
    us = ["4294967295", "007", " 12 ", '"42"', '""', "0", "123456789"]
    vals = []
    for i in range(20000):
        m = r.randint(0, 16777216 if i % 2 else 99999)
        fd = r.randint(0, 10)
        s = str(m).rjust(fd + 1, "0")
        vals.append((r.choice(["", "-", "+"]) + s[:len(s) - fd] + "." + s[len(s) - fd:]) if fd else str(m))
    c["f32_random_fast"] = ("x\n" + "\n".join(vals) + "\n", "F")
    c["u32_edges"] = ("x\n" + "\n".join(us) + "\n", "U")
    c["u32_overflow"] = ("x\n1\n4294967296\n", "U")
    c["u32_plus"] = ("x\n1\n+5\n", "U")
    bs = ["true", "True", "false", "False", " true ", '"false"', ""]
    c["bool_edges"] = ("x\n" + "\n".join(bs) + "\n", "B")
    c["bool_bad"] = ("x\ntrue\nTRUE\n", "B")
    c["escaped_numeric"] = ('x,y\n"1""2",1\n', "SU")
    c["escaped_f32_bad"] = ('x,y\na,"1""2"\n', "SF")
    # quote characters at every offset of a piece: "" pairs straddling piece edges
    rows = ["a,b"]
    for i in range(200):
        rows.append(q('"' * (i % 7) + "v" + '"' * (i % 5)) + "," + q('"' * (i % 3)))
    c["quote_edges"] = ("\n".join(rows) + "\n", "SS")
    return c


def canon_ref(o, header):
    if "error" not in o:
        return ("ok", o.get("n"), o.get("chk"))
    t = o["error"]
    m = re.match(r"ParseError at line (\d+): (.*)", t)
    if m and "malformed csv" in m.group(2):
        return ("malformed",)
    if m and m.group(2).startswith("expected"):
        g = re.search(r"got (\d+)", m.group(2)).group(1)
        return (f"ragged {m.group(1)} {g}",)
    if m and m.group(2).startswith("column "):
        name = m.group(2)[len("column "):].split(":")[0]
        return (f"bad {header.index(name)} {m.group(1)}",)
    return ("other: " + t,)


def canon_spike(o):
    if o.get("err") != "ok":
        return (o.get("err"),)
    return ("ok", o.get("n"), o.get("chk"))


def run(args):
    p = subprocess.run([BIN] + args, capture_output=True, text=True)
    lines = [l for l in p.stdout.splitlines() if l.startswith("{")]
    if not lines:
        return {"crash": p.stderr[-300:], "exit": p.returncode}
    try:
        return json.loads(lines[-1])
    except ValueError:  # the reference prints error texts unescaped
        m = re.search(r'"error":"(.*)"\}$', lines[-1])
        return {"error": m.group(1) if m else lines[-1]}


def main():
    bad = 0
    log = open(os.path.join(HERE, "results", "t5_adv.jsonl"), "a")
    for name, (text, schema) in cases().items():
        path = os.path.join(OUT, name + ".csv")
        with open(path, "wb") as f:
            f.write(text.encode("latin-1") if name == "bad_utf8" else text.encode("utf-8"))
        header = text.split("\n")[0].strip("\r").split(",") if text else []
        hl = [h for h in header]
        ref = canon_ref(run([path, "0", "ref", schema]), hl)
        fails = []
        for p in PIECES:
            o = run([path, str(p), "spike", schema])
            got = canon_spike(o) if "crash" not in o else ("crash", o)
            log.write(json.dumps({"case": name, "piece": p, "ref": ref, "spike": got}) + "\n")
            if got != ref:
                fails.append((p, got))
        status = "ok" if not fails else ("KNOWN" if name in KNOWN else "FAIL")
        if fails and name not in KNOWN:
            bad += 1
        print(f"{status:5s} {name:22s} ref={ref} " + (f"mismatch at pieces {[f[0] for f in fails]}: {fails[0][1]}" if fails else f"all {len(PIECES)} piece sizes equal"))
    print("FAILURES:", bad)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
