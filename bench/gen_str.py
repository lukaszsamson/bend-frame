"""M4 string-experiment data (plans/M_01.txt section 5). Usage:
    uv run --project bench python bench/gen_str.py            # every file below -> bench/data/str/
Deterministic. Each file `<shape>_<card>_<n>.csv` has columns
    id: u32 row number   s: str (the measured column)   v: u32 0..999   x: f32 (2 decimals)
`s` draws from `card` distinct values (card = "N": every row its own value, shuffled), with 5 %
nulls (empty unquoted field) and 2 % empty strings ("" quoted). Shapes:
    short    3..8 lowercase letters
    long     60..80 characters of words
    prefix   a 31-character shared prefix + 6 digits
    unicode  multi-byte text (CJK, Polish letters, emoji) + a number
`dim_<shape>_<card>_<n>.csv` lists every distinct value of `s` once (shuffled again: the codes a
reader gives equal values differ between the two files) with a u32 `w`: the join's right side.
"""
import random
import sys
from pathlib import Path

HERE = Path(__file__).parent
OUT = HERE / "data" / "str"
LETTERS = "abcdefghijklmnopqrstuvwxyz"
WORDS = ["alpha", "bravo", "charlie", "delta", "echo", "foxtrot", "golf", "hotel", "india", "juliet",
         "kilo", "lima", "mike", "november", "oscar", "papa", "quebec", "romeo", "sierra", "tango"]
UNI = ["日本語", "żółć", "ąęłńś", "Ελληνικά", "русский", "😀🎉", "中文字", "ümlaut"]


def value(shape: str, i: int, rng: random.Random) -> str:
    if shape == "short":
        k = 3 + i % 6
        r = random.Random(i * 7919 + 13)
        return "".join(r.choice(LETTERS) for _ in range(k)) + str(i)
    if shape == "long":
        r = random.Random(i * 104729 + 7)
        out = []
        while sum(len(w) + 1 for w in out) < 60 + i % 20:
            out.append(r.choice(WORDS))
        return " ".join(out) + f" #{i}"
    if shape == "prefix":
        return f"customer_segment_internal_code_{i:06d}"
    if shape == "unicode":
        return f"{UNI[i % len(UNI)]}_{UNI[(i // 8) % len(UNI)]}_{i}"
    raise ValueError(shape)


def csv_field(s: str) -> str:
    if s == "" or any(c in s for c in ',"\r\n'):
        return '"' + s.replace('"', '""') + '"'
    return s


def gen(shape: str, card: str, n: int) -> None:
    rng = random.Random(f"{shape}:{card}:{n}")
    k = n if card == "N" else int(card)
    pool = [value(shape, i, rng) for i in range(k)]
    order = list(range(n))
    rng.shuffle(order)
    rows = ["id,s,v,x"]
    used = set()
    for i in range(n):
        u = rng.random()
        if u < 0.05:
            s = None
        elif u < 0.07:
            s = ""
        else:
            s = pool[order[i] % k] if card == "N" else pool[rng.randrange(k)]
        if s is not None:
            used.add(s)
        f = "" if s is None else csv_field(s)
        rows.append(f"{i},{f},{rng.randrange(1000)},{rng.randrange(100000) / 100:.2f}")
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / f"{shape}_{card}_{n}.csv").write_text("\n".join(rows) + "\n", encoding="utf-8")
    dim = sorted(used)
    rng.shuffle(dim)
    drows = ["s,w"] + [f"{csv_field(s)},{j}" for j, s in enumerate(dim)]
    (OUT / f"dim_{shape}_{card}_{n}.csv").write_text("\n".join(drows) + "\n", encoding="utf-8")
    print(f"{shape}_{card}_{n}: {n} rows, {len(used)} distinct")


PLAN = (
    [("short", c, n) for n in (1000, 100_000, 1_000_000) for c in ("8", "64", "1000", "N")]
    + [(sh, c, 100_000) for sh in ("long", "prefix", "unicode") for c in ("8", "64", "1000", "N")]
    + [("short", c, 1_000_000) for c in ("10000", "100000", "500000")]
    + [("prefix", "1000", 1_000_000)]
)

if __name__ == "__main__":
    only = set(sys.argv[1:])
    for shape, card, n in PLAN:
        if not only or f"{shape}_{card}_{n}" in only:
            gen(shape, card, n)
