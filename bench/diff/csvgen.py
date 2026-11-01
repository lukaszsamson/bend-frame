"""W6.4: the random CSV generator of the reader fuzz harness (bench/diff/csvfuzz.py).

A case is a file (bytes) plus an engine-independent read spec (explicit dtype letters or inference,
header flag, separator, infer_rows, Str storage rule, row cap). The generator never says what the
answer is: the oracle was the v0.1 reader (now: the reader at 1 MiB pieces plus golden hashes frozen from
the v0.1 reader, csvfuzz.py --golden), the candidate the reader at several piece sizes
(DESIGN.md 15.6.6, 17.6), so it is free to produce files the contract rejects. Seed and index fix a
case (`random.Random(f"csv:{seed}:{index}")`).

Coverage (each item is also a tag counted in the report):
  quoting     quoted fields holding separators, quotes, LF, CRLF, CR; doubled quotes at random positions
              (`dq`), quoting of every field (`quote_all`), quoted empty vs empty (`qempty`), CR inside a
              bare field (`bare_cr`)
  endings     LF, CRLF, CR-only data, mixed endings (`mixed_eol`); no final terminator (`no_final_nl`)
  blank       blank lines before the header, between records, at the end (`blank_pre`, `blank_mid`,
              `blank_end`), a one-column file with blank lines (null rows, `blank_w1`)
  shape       empty file, blank-only file, header only, one column, many columns (up to 300), BOM, ragged
              records (short / long, also the header), unterminated quote, quote in mid-field, text after a
              closing quote, a stray last quote (`mal_*`), multibyte UTF-8 incl. 4-byte, invalid UTF-8
              bytes of every kind (lone continuation, truncated sequences, overlong, surrogate, > U+10FFFF),
              records longer than a piece (`long_rec`), NUL / U+FFFF / U+10FFFF
  numeric     u32 max and overflow, i32 min / max and overflow, leading + / -, padding with spaces and
              tabs, F32 subnormal / huge / overflow / NaN / inf spellings, many-digit mantissas, exponents,
              bool spellings, numbers as strings; a late value that changes the inferred dtype (`late`)
  errors      bad cells in several columns and regions, ragged and bad cells in different regions,
              malformed quoting after a ragged record, a bad cell before / after it (`competing`)
  options     explicit schema (right / perturbed / wrong count) or inference with infer_rows in
              {0, 1..10, 100, 70000}; Raw / Dictionary / Auto / AutoAt storage; separators , ; tab | space
              and non-ASCII (2, 3 and 4 byte); header on / off (independent of the file's first line); row
              cap (small values, around the row count)
  mutation    byte level mutations (insert / delete / duplicate / swap / truncate structural bytes) of
              generated files and of the 102 adversarial files of tests/csvadv (bench/w6/gen_adv.py)
"""
from __future__ import annotations

import os
import random
import struct
from dataclasses import dataclass, field

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
ADV_DIR = os.path.join(ROOT, "tests", "csvadv")
PIECES = [1, 2, 3, 7, 64, 4096, 245760]  # 245760 = Pr.piece(), the default
DEFAULT_CAP = 8388608
G_DEFAULT_PIECE = 245760


@dataclass
class Case:
    id: str
    data: bytes
    schema: str  # dtype letters U I F B S, or "-" to infer
    hdr: int
    sep: int  # code point
    inf: int
    enc: str  # R | D | A | T<floor>.<den>
    cap: int
    tags: list = field(default_factory=list)
    pieces: list = None  # None: PIECES; the big files (several regions at the default piece) use a short list

    def spec(self) -> dict:
        return {"schema": self.schema, "hdr": self.hdr, "sep": self.sep, "inf": self.inf, "enc": self.enc, "cap": self.cap}


def manifest_line(cid: str, path: str, spec: dict, pieces) -> str:
    return " ".join([cid, path, spec["schema"] or "-", str(spec["hdr"]), str(spec["sep"]), str(spec["inf"]), spec["enc"], str(spec["cap"]), ",".join(str(p) for p in pieces)])


def esc(b: int) -> str:
    """a raw byte >= 0x80 as a lone surrogate: str.encode(..., 'surrogateescape') writes the byte back"""
    return chr(0xDC00 + b)


def enc_text(s: str) -> bytes:
    return s.encode("utf-8", "surrogateescape")


INVALID = ["\udcff", "\udcc3", "\udce2\udc82", "\udcc0\udc80", "\udced\udca0\udc80", "\udcf4\udc90\udc80\udc80", "\udc80", "\udcf0\udc9f\udc98", "\udcfe", "\udcc3(", "\udce2(\udca1", "\udce0\udc80\udc80", "\udce0\udc9f\udcbf", "\udcf0\udc80\udc80\udc80", "\udcf0\udc8f\udcbf\udcbf", "\udced\udc9f\udcbf", "\udcf4\udc8f\udcbf\udcbf", "\udcf5\udc80\udc80\udc80", "\udcc1\udcbf", "\udce0\udca0\udc80"]
MULTI = ["é", "ñ", "日", "本", "語", "\U0001F600", "€", " ", " ", "�", "\U0010ffff", "￿", "\u0000", "\u0080", "߿", "ࠀ", "\U00010000", "ß", "Ω"]
U_EDGE = ["0", "1", "4294967295", "4294967294", "4294967296", "4294967300", "00012", "+7", "+0", " 5 ", "5 ", "  ", "-0", "-1", "1_000", "0x1F", "1e3", "1.0", "٣", "99999999999",
          "0000000000000000000000001", "+", "++1", "1 2", "\t7", "7\x0b", "\x0c7", "4294967295 ", " 4294967295", "+4294967295", "+4294967296", "429496729", "42949672950", "00000000000"]
I_EDGE = ["-2147483648", "2147483647", "-2147483649", "2147483648", "-2147483647", "+5", "-0", "+0", "- 5", "--5", "-", "+", "  -3 ", "-2147483648 ", "-00001", "4294967295", "-4294967296", "+2147483647",
          "+2147483648", "-0000002147483648", "214748364", "-214748364", "-214748364 8"]
F_EDGE = ["0", "-0", "-0.0", "+0.0", "1e38", "3.4028235e38", "3.4028236e38", "3.5e38", "1e39", "-3.4028235e38", "-1e39", "1e-45", "1.4e-45", "1e-46", "7e-46", "1.17549435e-38", "1.1754942e-38", "nan", "NaN", "NAN",
          "-nan", "inf", "-inf", "+inf", "Inf", "infinity", "Infinity", "-Infinity", "INF", "1.", ".5", "+.5", "-.5", "1e", "e5", "1e+5", "1E5", "1e-5", "1d5", "0x1p3", "16777216", "16777217", "16777219", "0.1", "0.3",
          "0.30000001192092896", "123456789012345678901234567890", "1_0", " 1.5 ", "1,5", "0.00000000001", "0.0000000001", "0.00000000012345", "1.00000000000000000001", "-1.5e-10", "5e-324", "1e-400", "16777217.5",
          "8388608.5", "3.14159265358979", ".", "-", "+.", "1.2.3", "1e5e5", "١", "1 5", "0e0", "1e0", "00.5", "0.5e", "NaN ", "-inf ", "nan1", "in", "i", "2.5E+3", "9e9999"]
B_EDGE = ["TRUE", "FALSE", "t", "f", "1", "0", "yes", "no", "true ", " false", " True ", "tru", "truee", "T", "F", "TrUe", "false\x0b", "\x0ctrue", "True\t", "y", "n", "NA", "null", "None"]
WORDS = ["a", "b", "c", "alpha", "beta", "gamma", "delta", "x y", "foo,bar", "q\"q", "multi\nline", "tab\there", "é", "日本語", "\U0001F600", "", " ", "  s  ", "NULL", "null", "NaN", "true", "007", "1.0", " 1 ", "-", "0"]
SEPS = [(44, 70), (59, 5), (9, 6), (124, 5), (32, 2), (58, 1), (233, 4), (26085, 2), (128512, 1), (97, 1), (8364, 1)]  # , ; TAB | space : é 日 😀 a €
BAD_SEPS = [34, 10, 13]  # refused with the same error by both readers
ALPHA = list("abcxyzXYZ019 _-.:") + ["é", "日", "\U0001F600"]


def wchoice(rng, pairs):
    tot = sum(w for _, w in pairs)
    x = rng.random() * tot
    for v, w in pairs:
        x -= w
        if x < 0:
            return v
    return pairs[-1][0]


class Col:
    """One column's value source: a dtype kind, null rate and style, edge rate, a late change"""

    def __init__(self, rng, kind, sepch, nrows, rich):
        self.kind = kind
        self.rng = rng
        self.sepch = sepch
        self.nullp = rng.choice([0, 0, 0, 0.05, 0.2, 0.5, 0.9, 1.0])
        self.nullstyle = rng.choice(["bare", "bare", "bare", "quoted", "spaces", "mixed"])
        self.edgep = rng.choice([0, 0, 0, 0.02, 0.1, 0.3, 0.9]) if rich else 0
        self.scale = rng.choice([9, 99, 999, 100000, 2 ** 32 - 1])
        self.pool = rng.sample(WORDS + [sepch, sepch + "x", "a" + sepch + "b"], rng.randint(1, 12))
        self.mode = rng.choice(["low", "uniq", "text", "wild", "numlike", "prefix"])
        self.late = None
        self.dq = rng.random() < 0.3
        self.nl = rng.random() < 0.3
        self.mbp = rng.choice([0, 0.1, 0.5])
        self.fm = rng.choice(["dec", "dec", "int", "sci", "bits", "short", "long", "tiny"])
        self.uniq = 0

    def text(self, rng):
        n = rng.randint(0, 12)
        out = []
        for _ in range(n):
            x = rng.random()
            if x < self.mbp:
                out.append(rng.choice(MULTI))
            elif x < self.mbp + 0.04:
                out.append(rng.choice(['"', self.sepch, "\n", "\r\n", "\r"]) if self.mode == "wild" else rng.choice(ALPHA))
            else:
                out.append(rng.choice(ALPHA))
        s = "".join(out)
        if self.dq and s and rng.random() < 0.5:
            i = rng.randint(0, len(s))
            s = s[:i] + '"' * rng.choice([1, 2, 3]) + s[i:]
        if self.nl and rng.random() < 0.3:
            i = rng.randint(0, len(s))
            s = s[:i] + rng.choice(["\n", "\r\n", "\r", "\n\n"]) + s[i:]
        return s

    def gen_kind(self, rng, kind, r):
        if kind == "U":
            if rng.random() < self.edgep:
                return rng.choice(U_EDGE)
            return str(rng.randint(0, self.scale))
        if kind == "I":
            if rng.random() < self.edgep:
                return rng.choice(I_EDGE)
            v = rng.randint(-self.scale // 2, self.scale // 2)
            return ("+" if v > 0 and rng.random() < 0.05 else "") + str(v)
        if kind == "F":
            if rng.random() < self.edgep:
                return rng.choice(F_EDGE)
            fm = self.fm
            if fm == "int":
                return str(rng.randint(-1000, 100000))
            if fm == "short":
                return "%d.%d" % (rng.randint(-99, 99), rng.randint(0, 99))
            if fm == "sci":
                return "%.*e" % (rng.randint(0, 8), rng.uniform(-1, 1) * 10 ** rng.randint(-45, 38))
            if fm == "tiny":
                # a small mantissa behind many fraction digits (the fast path ends at 10: 10^11 is not exact in f32)
                m = rng.choice([1, 3, 7, 123, 9999, 16777215, 16777216, 16777217, rng.randint(1, 2 ** 24)])
                fd = rng.randint(8, 14)
                digits = str(m).zfill(fd)[-fd:] if len(str(m)) <= fd else str(m)
                return "%s0.%s" % ("-" if rng.random() < 0.3 else "", digits)
            if fm == "long":
                return "%d.%s" % (rng.randint(0, 99999), "".join(rng.choice("0123456789") for _ in range(rng.randint(5, 14))))
            if fm == "bits":
                b = rng.getrandbits(32)
                f = struct.unpack("<f", struct.pack("<I", b))[0]
                return "nan" if f != f else ("inf" if f == float("inf") else ("-inf" if f == float("-inf") else repr(f)))
            return "%d.%03d" % (rng.randint(-1000, 1000), rng.randint(0, 999))
        if kind == "B":
            if rng.random() < self.edgep:
                return rng.choice(B_EDGE)
            return rng.choice(["true", "false", "True", "False"])
        # S
        m = self.mode
        if m == "low":
            return rng.choice(self.pool)
        if m == "uniq":
            self.uniq += 1
            return "id%d_%d" % (r, rng.randint(0, 99))
        if m == "numlike":
            return rng.choice(["007", "1.0", " 1 ", "-5", "1e3", "true", "0", "12", "+3", "nan", "", " "] + [str(rng.randint(0, 99))])
        if m == "prefix":
            return "common_prefix_value_" + str(rng.randint(0, 30 if r % 3 else 5000))
        return self.text(rng)

    def cell(self, rng, r):
        """(logical text, force quote)"""
        if self.nullp and rng.random() < self.nullp:
            st = self.nullstyle
            if st == "mixed":
                st = rng.choice(["bare", "quoted", "spaces"])
            return {"bare": ("", False), "quoted": ("", True), "spaces": ("  ", False)}[st]
        kind = self.kind
        if self.late is not None and r >= self.late[0]:
            kind = self.late[1]
        t = self.gen_kind(rng, kind, r)
        return t, (rng.random() < 0.05)


def render_field(rng, text, sep, force, qall, bare_cr_ok):
    needs = ('"' in text) or ("\n" in text) or (sep in text) or ("\r" in text)
    if needs and bare_cr_ok and "\r" in text and '"' not in text and "\n" not in text and sep not in text and rng.random() < 0.5:
        needs = False  # a CR inside a bare field
    if text == "" and not force:
        return b""
    if needs or force or qall:
        return enc_text('"' + text.replace('"', '""') + '"')
    return enc_text(text)


def junk_for(rng, kind):
    return rng.choice({
        "U": ["abc", "-1", "1.5", "4294967296", "x1", "1x", " ", "٣", "true", "0x10", "1e3", "++1", "1_000"],
        "I": ["abc", "2147483648", "-2147483649", "1.5", "- 1", "--1", "x", "true", "1e3"],
        "F": ["abc", "1.2.3", "1e", "x", "true", "--1", "0x1p3", "1,5", "1_0", "e5"],
        "B": ["yes", "1", "tru", "TRUE", "t", "x", "0", "2", "falsee"],
        "S": ["x"],
    }[kind])


def mut_bytes(rng, b: bytes, sepb: bytes, tags: list) -> bytes:
    for _ in range(rng.choice([1, 1, 2, 3])):
        if not b:
            b = rng.choice([b'"', b"\n", b"a", b","])
        i = rng.randint(0, len(b))
        op = rng.choice(["ins", "ins", "ins", "del", "dup", "swap", "trunc", "rep", "delrange"])
        tags.append("mut_" + op)
        if op == "ins":
            b = b[:i] + rng.choice([b'"', b'"', b"\n", b"\r", b"\r\n", sepb, sepb, b",", b" ", b'""', b"\xff", b"\xc3", b"\xe2\x82", b"0", b"-", b".", b"e", b"\x00", b"\xf0\x9f\x98\x80", b"\xf0\x9f\x98", b"\n\n"]) + b[i:]
        elif op == "del":
            b = b[:i] + b[i + 1:]
        elif op == "delrange":
            b = b[:i] + b[i + rng.randint(1, 20):]
        elif op == "dup":
            j = min(len(b), i + rng.randint(1, 40))
            b = b[:j] + b[i:j] + b[j:]
        elif op == "swap" and i + 1 < len(b):
            b = b[:i] + b[i + 1:i + 2] + b[i:i + 1] + b[i + 2:]
        elif op == "trunc":
            b = b[:i]
        elif op == "rep":
            b = b[:i] + rng.choice([b'"', b"\n", b"\r", sepb, b"\xff", b" "]) + b[i + 1:]
    return b


def pick_options(rng, kinds, nrows, tags, base_schema=None, explicit=False):
    """schema, infer_rows, enc, cap (engine-independent read options); kinds = intended letters"""
    x = rng.random()
    if base_schema is not None:
        letters = base_schema
        x = 0.0 if x < 0.7 else 0.9  # explicit mostly, inference sometimes
        if x == 0.9:
            letters = None
    else:
        letters = "".join(kinds)
    if explicit and letters is not None:
        x = 0.0
    if x < 0.5 and letters is not None:
        schema = letters
        r = rng.random()
        if r < 0.15 and schema:
            s = list(schema)
            for _ in range(rng.randint(1, 2)):
                s[rng.randrange(len(s))] = rng.choice("UIFBS")
            schema = "".join(s)
            tags.append("schema_perturbed")
        elif r < 0.2:
            schema = schema + rng.choice("UIFBS") * rng.randint(1, 2) if rng.random() < 0.5 else schema[:-rng.randint(1, 2)]
            if not schema:
                schema = "S"
            tags.append("schema_count_wrong")
        tags.append("explicit")
    elif x < 0.5:
        schema = "-"
        tags.append("infer")
    else:
        schema = "-"
        tags.append("infer")
    inf = wchoice(rng, [(100, 40), (0, 20), (rng.choice([1, 2, 3, 5, 10]), 25), (70000, 15)])
    tags.append("inf_" + ("0" if inf == 0 else "small" if inf < 100 else "default" if inf == 100 else "large"))
    e = wchoice(rng, [("A", 50), ("R", 14), ("D", 14), ("T", 22)])
    enc = e if e != "T" else "T%d.%d" % (rng.choice([0, 1, 2, 4, 8]), rng.choice([1, 2, 3, 4, 16]))
    tags.append("enc_" + enc[0])
    if rng.random() < 0.05:
        cap = rng.choice([0, 1, 2, 3, 5, 10, 100, max(0, nrows - 1), nrows, nrows + 1])
        tags.append("cap_small")
    else:
        cap = DEFAULT_CAP
    return schema, inf, enc, cap


_ADV = None


def adv_corpus():
    # built whole, then published: csvfuzz.py generates cases on several threads, and a list published empty and
    # filled in place let a thread draw from a partial corpus (a case then depended on thread timing)
    global _ADV
    if _ADV is None:
        corpus = []
        mp = os.path.join(ADV_DIR, "MANIFEST")
        if os.path.exists(mp):
            for line in open(mp).read().splitlines():
                p = line.split()
                if len(p) == 4:
                    with open(os.path.join(ADV_DIR, p[0] + ".csv"), "rb") as f:
                        corpus.append((p[0], f.read(), p[1], int(p[2]), int(p[3])))
        _ADV = corpus
    return _ADV


def gen_adv(rng, idx) -> Case:
    """an adversarial file of tests/csvadv, its own spec or random options, optionally byte mutated"""
    name, data, letters, hdr, sep = rng.choice(adv_corpus())
    tags = ["adv", "adv:" + name]
    kinds = list(letters)
    schema, inf, enc, cap = pick_options(rng, kinds, 50, tags, base_schema=letters)
    if rng.random() < 0.3:
        hdr = 1 - hdr
        tags.append("hdr_flipped")
    if rng.random() < 0.5:
        data = mut_bytes(rng, data, chr(sep).encode("utf-8"), tags)
    return Case("", data, schema, hdr, sep, inf, enc, cap, tags)


def gen_case(seed: int, idx: int) -> Case:
    rng = random.Random(f"csv:{seed}:{idx}")
    if rng.random() < 0.12 and adv_corpus():
        c = gen_adv(rng, idx)
        c.id = f"c{idx:06d}"
        return c
    tags: list = []
    # ---- separator
    sep = wchoice(rng, SEPS)
    if rng.random() < 0.004:
        sep = rng.choice(BAD_SEPS)
        tags.append("bad_sep")
    sepch = chr(sep)
    sepb = sepch.encode("utf-8")
    if sep > 127:
        tags.append("sep_nonascii%d" % len(sepb))
    sepq = sepch if sep not in BAD_SEPS else ","  # the separator the generator writes
    # ---- shape
    shape = wchoice(rng, [("normal", 80), ("empty", 2), ("blank_only", 1), ("header_only", 3), ("one_col", 8), ("many", 3), ("long", 5), ("big", 0.3)])
    k = {"one_col": 1, "many": rng.randint(40, 300), "big": rng.randint(3, 6)}.get(shape) or wchoice(rng, [(2, 15), (3, 20), (4, 15), (5, 10), (6, 8), (8, 6), (12, 5), (20, 2), (1, 2)])
    rr = rng.random()
    nrows = rng.randint(22000, 36000) if shape == "big" else 0 if shape == "header_only" else (rng.randint(0, 3) if shape == "many" else (0 if rr < 0.04 else 1 if rr < 0.12 else rng.randint(2, 5) if rr < 0.32 else rng.randint(6, 40) if rr < 0.72 else rng.randint(41, 130) if rr < 0.9 else rng.randint(131, 400) if rr < 0.97 else rng.randint(401, 1200)))
    while nrows * k > 5000 and nrows > 4 and shape != "big":
        nrows //= 2
    rich = rng.random() < 0.7
    kinds = [wchoice(rng, [("U", 20), ("I", 15), ("F", 20), ("B", 12), ("S", 33)]) for _ in range(k)]
    cols = [Col(rng, kd, sepq, nrows, rich) for kd in kinds]
    # late dtype change
    if rng.random() < 0.18 and nrows > 3:
        j = rng.randrange(k)
        L = rng.choice([1, 2, 3, 4, nrows // 2, max(1, nrows - 2), 101, 105]) if nrows > 1 else 1
        L = min(L, nrows - 1) if rng.random() < 0.85 else L
        if L < nrows:
            cols[j].late = (L, rng.choice([x for x in "UIFBS" if x != kinds[j]]))
            if cols[j].late[1] == kinds[j]:
                cols[j].late = None
            cols[j].nullp = min(cols[j].nullp, 0.2)
            tags.append("late")
    # ---- header
    names = []
    for j in range(k):
        x = rng.random()
        if x < 0.55:
            names.append("c%d" % j if rng.random() < 0.5 else "col_%s" % chr(97 + j % 26))
        elif x < 0.7:
            names.append(rng.choice(["a", "b", "x", "id", "é", "日本", "", " ", "a b", "q\"q", "s,p", "m\nl", sepq, "\U0001F600", "A" * 40]))
        elif x < 0.8:
            names.append(Col(rng, "S", sepq, 1, True).text(rng))
        else:
            names.append("n%d" % j)
    if rng.random() < 0.02 and k > 1:
        names[rng.randrange(k)] = names[rng.randrange(k)]
        tags.append("dup_names")
    # ---- records as lists of rendered fields
    qmode = rng.choice([0, 0, 0, 0.05, 0.5, 1.0])
    if qmode == 1.0:
        tags.append("quote_all")
    bare_cr_ok = rng.random() < 0.5
    recs = []  # (rendered fields, is_header)
    hdr_rec = [render_field(rng, n, sepq, False, rng.random() < qmode, False) for n in names]
    rows = []
    for r in range(nrows):
        row = []
        for j, c in enumerate(cols):
            t, fq = c.cell(rng, r)
            if fq and t == "":
                tags.append("qempty")
            row.append(render_field(rng, t, sepq, fq, rng.random() < qmode, bare_cr_ok))
        rows.append(row)
    hdr_on = rng.random() < 0.85
    has_hdr_line = (hdr_on and rng.random() < 0.95) or ((not hdr_on) and rng.random() < 0.3)
    spec_hdr = 1 if hdr_on else 0
    if not hdr_on:
        tags.append("hdr_off")
    # ---- long record
    if shape == "long" and rows:
        r = rng.randrange(len(rows))
        j = rng.randrange(k)
        n = rng.choice([40, 300, 5000, 9000])
        unit = rng.choice(["long field text ", "x\n", "a\"\"b,", "é日\U0001F600 ", "line\r\n"])
        txt = (unit * (n // len(unit) + 1))[:n]
        rows[r][j] = render_field(rng, txt, sepq, True, False, False)
        tags.append("long_rec")
    # ---- errors and structure on rendered fields
    competing = rng.random() < 0.08 and nrows >= 2
    events = []
    if competing:
        tags.append("competing")
        for _ in range(rng.randint(2, 4)):
            events.append(rng.choice(["bad", "bad", "ragged", "malformed"]))
    else:
        if rng.random() < 0.04:
            events.append("ragged")
        if rng.random() < 0.03:
            events.append("malformed")
        if rng.random() < 0.08:
            events.append("bad")
    for ev in events:
        if not rows:
            break
        r = rng.randrange(len(rows))
        if ev == "bad":
            if not rows[r]:
                continue
            j = rng.randrange(min(k, len(rows[r])))
            rows[r][j] = render_field(rng, junk_for(rng, kinds[j]), sepq, False, False, False)
            tags.append("bad_cell")
        elif ev == "ragged":
            if rng.random() < 0.5 and len(rows[r]) > 1:
                rows[r] = rows[r][: -rng.randint(1, max(1, min(2, len(rows[r]) - 1)))]
                tags.append("ragged_short")
            else:
                rows[r] = rows[r] + [b"x"] * rng.randint(1, 2)
                tags.append("ragged_long")
        else:
            j = rng.randrange(len(rows[r])) if rows[r] else 0
            m = rng.choice(["unterminated", "midquote", "afterclose", "crafter", "unterminated"])
            if rows[r]:
                rows[r][j] = {"unterminated": b'"abc', "midquote": b'ab"c', "afterclose": b'"abc"d', "crafter": b'"abc"\rx'}[m]
            tags.append("mal_" + m)
    if hdr_on and rng.random() < 0.04:
        tags.append("hdr_ragged")
        hdr_rec = hdr_rec + [b"extra"] if rng.random() < 0.5 else hdr_rec[:-1]
    # ---- invalid UTF-8 bytes into some field
    if rng.random() < 0.07 and rows:
        for _ in range(rng.choice([1, 1, 2, 5])):
            r = rng.randrange(len(rows))
            j = rng.randrange(len(rows[r])) if rows[r] else 0
            if rows[r]:
                bad = enc_text(rng.choice(INVALID))
                f = rows[r][j]
                p = rng.randint(0, len(f)) if f else 0
                rows[r][j] = f[:p] + bad + f[p:]
        tags.append("invalid_utf8")
    # ---- lay out lines
    eolmode = wchoice(rng, [("LF", 56), ("CRLF", 20), ("CR", 2), ("mixed", 22)])
    if eolmode == "CRLF":
        tags.append("crlf")
    elif eolmode == "CR":
        tags.append("cr_only")
    elif eolmode == "mixed":
        tags.append("mixed_eol")

    mix = [b"\n"] * 6 + [b"\r\n"] * 3 + ([b"\r"] if rng.random() < 0.15 else [])

    def eol():
        return {"LF": b"\n", "CRLF": b"\r\n", "CR": b"\r"}.get(eolmode) or rng.choice(mix)

    lines = []  # list of bytes without terminator; blank = b""
    if has_hdr_line:
        lines.append(sepb.join(hdr_rec))
    blank_p = 0.3 if k == 1 else 0.06
    for row in rows:
        if rng.random() < blank_p and (k == 1 or rng.random() < 0.5):
            lines.append(rng.choice([b"", b"", b"", b"\r"] if eolmode != "CR" else [b""]))
            tags.append("blank_mid") if k > 1 else tags.append("blank_w1")
        lines.append(sepb.join(row))
    if rng.random() < 0.15:
        n = rng.randint(1, 3)
        lines = [b""] * n + lines
        tags.append("blank_pre")
    if rng.random() < 0.1:
        lines = lines + [b""] * rng.randint(1, 3)
        tags.append("blank_end")
    data = b""
    for i, ln in enumerate(lines):
        data += ln
        if i < len(lines) - 1:
            data += eol()
    final_nl = rng.random() < 0.8
    if lines and final_nl:
        data += eol()
    elif lines:
        tags.append("no_final_nl")
    # ---- special files
    if shape == "empty":
        data = b""
        tags.append("empty")
    elif shape == "blank_only":
        data = rng.choice([b"\n", b"\n\n", b"\r\n\n", b"\r", b"\n\r\n\n"])
        tags.append("blank_only")
    elif shape == "header_only":
        tags.append("header_only")
    if shape == "one_col":
        tags.append("one_col")
    if shape == "many":
        tags.append("many_cols")
    if rng.random() < 0.01:
        data = b"\xef\xbb\xbf" + data
        tags.append("bom")
    if rng.random() < 0.005 and data:
        data = data + rng.choice([b'"', b'""', b'"x', b"\xff", b"\r", b"\r\r", b'"\r'])
        tags.append("tail_junk")
    # a stray final quote or truncation at a random byte
    if rng.random() < 0.05 and len(data) > 2:
        data = data[: rng.randint(1, len(data) - 1)]
        tags.append("truncated")
    if rng.random() < 0.10:
        data = mut_bytes(rng, data, sepb, tags)
    if len(data) > 60000 and shape != "big":
        data = data[:60000]
    # ---- options
    schema, inf, enc, cap = pick_options(rng, kinds, nrows, tags, explicit=competing and rng.random() < 0.8)
    # tags of the content classes
    if b'""' in data:
        tags.append("dq")
    if not data.isascii():
        tags.append("non_ascii")
    if b"\xf0" in data:
        tags.append("utf8_4byte")
    tags.append("k%s" % ("1" if k == 1 else "2-6" if k <= 6 else "7-39" if k < 40 else "40+"))
    tags.append("rows%s" % ("0" if nrows == 0 else "1" if nrows == 1 else "2-40" if nrows <= 40 else "41-400" if nrows <= 400 else "400+"))
    pieces = None
    if shape == "big":
        tags.append("big")
        pieces = [4096, rng.choice([30011, 65536, 100003]), G_DEFAULT_PIECE]
    return Case(f"c{idx:06d}", data, schema, spec_hdr, sep, inf, enc, cap, sorted(set(tags)), pieces)


if __name__ == "__main__":
    import argparse

    ap = argparse.ArgumentParser(description="show generated cases")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--n", type=int, default=5)
    ap.add_argument("--start", type=int, default=0)
    a = ap.parse_args()
    for i in range(a.start, a.start + a.n):
        c = gen_case(a.seed, i)
        print(c.id, c.spec(), c.tags)
        print(repr(c.data[:300]))
