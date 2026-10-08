"""T2.3 reference: exact f32 reductions, the contract's step model, and calibrated error bounds.

Everything here is independent of Bend. Inputs are f32 BIT PATTERNS (ints); sums are exact integer
arithmetic in units of 2^-149 (every f32 is an integer multiple of that), so the "truth" is exact.

Three layers per quantity (DESIGN.md 15.5.3 / 15.5.4):

  exact   the mathematically exact value, rounded ONCE to f32 (round-to-nearest-even): `rn_*`;
  model   the contract's algorithm re-implemented step for step with numpy float32 scalars
          (Neumaier + non-finite guard, ascending row order, two-pass std/var, median definition):
          `model_*`. Bend must equal it bit for bit (reduction order is part of the contract);
  bound   a RIGOROUS absolute error bound of the model against the exact value, derived below:
          `bound_*`. A result outside it is a numerical defect whatever the model says.

Error bound (u = 2^-24, gamma_k = k u / (1 - k u), n valid cells, S the exact sum, A = sum |x_i|):

  Neumaier with the guard, while no partial sum overflows, is the compensated "Sum2" of Ogita,
  Rump & Oishi (SIAM J. Sci. Comput. 26, 2005, Prop. 4.4): each step's (s - t) + x (or
  (x - t) + s, the branch of Neumaier) is an error-free transformation (Fast2Sum; exact in f32,
  subnormals included), c accumulates the n-1 exact error terms with f32 rounding, and
        |(s + c) - S|  <=  u |S|  +  gamma_{n-1}^2 * A.                                 (1)
  The first term is the final rounding, the second is the second-order cost of summing the
  errors in f32. For n = 10^4 gamma^2 ~ 3.6e-7 = 6u, so a well-conditioned sum (A ~ |S|) is within
  ~1 ulp of S, while a cancelling sum with A/|S| = 1e8 may be off by ~36 |S|... measured against
  A, never against |S|; the classic [1e8, 1, -1e8] gives exactly 1 because its errors are
  exact (n = 3: gamma^2 ~ 1e-14). A naive f32 sum violates (1) on those inputs by 12 orders.
  We add 2 units (2^-148) of slack for the subnormal range, where relative rounding models stop
  holding (additions there are exact; only a final division/multiplication loses < 2^-150).

  mean = fl(s_hat / n), n <= 2^24 exact:
        |mean_hat - S/n|  <=  (B1 + u (|S| + B1)) / n + slack,   B1 = bound (1).         (2)

  var / std (ddof 1), m_hat the f32 mean the algorithm used, d_i = fl(x_i - m_hat),
  tau_i = fl(d_i^2): tau_i = (x_i - m_hat)^2 (1 + e)^{3-ish}, |tau_i - t_i| <= rho t_i, rho =
  (1+u)^3 - 1, plus 2^-150 per term when the square underflows; the terms are non-negative, so
  (1) applies with A = S: |s_hat - T| <= rho T + n 2^-150 + (u + gamma_{n-1}^2) (1 + rho) T'.
  T = sum (x_i - m_hat)^2 (exact) = T0 + n (mu - m_hat)^2 where T0 is the exact centred sum; the
  division by n-1 rounds once more:
        |v_hat - T0/(n-1)|  <=  [ B_T + u (T + B_T) + n delta^2 ] / (n-1) + slack,       (3)
  delta = mu - m_hat. For std, |sqrt a - sqrt b| <= min(|a-b| / sqrt b, sqrt |a-b|), plus the
  sqrt rounding u * std_hat.                                                              (4)
  If a partial sum or a square overflows (finite data), the contract's guard answers inf/NaN: the
  `model` is then the expectation ("overflow" cases, counted apart).

Non-finite inputs are tested apart ("special"): IEEE gives the answer independent of the order
(any NaN -> NaN; +inf with -inf -> NaN; +inf -> +inf; -inf -> -inf), checked against that rule and
against the model.
"""
from __future__ import annotations

import math
import struct
from decimal import Decimal, getcontext
from fractions import Fraction

import numpy as np

U = Fraction(1, 2 ** 24)
NAN_BITS = 0x7FC00000
INF_BITS = 0x7F800000
NINF_BITS = 0xFF800000
UNIT = 149                       # exact sums are integers in units of 2^-149

np.seterr(all="ignore")
F = np.float32


# ---- bit helpers --------------------------------------------------------------------------

def b2f(b: int) -> "np.float32":
    return np.frombuffer(struct.pack("<I", b & 0xFFFFFFFF), dtype="<f4")[0]


def f2b(x) -> int:
    return struct.unpack("<I", struct.pack("<f", float(x)) if not isinstance(x, np.float32) else x.tobytes())[0]


def is_nan(b: int) -> bool:
    return (b & 0x7FFFFFFF) > 0x7F800000


def is_inf(b: int) -> bool:
    return (b & 0x7FFFFFFF) == 0x7F800000


def is_finite(b: int) -> bool:
    return (b & 0x7FFFFFFF) < 0x7F800000


def canon(b: int) -> int:
    """The dump's NaN canonicalisation (DESIGN.md 15.1 rule 3)."""
    return NAN_BITS if is_nan(b) else b


def ordinal(b: int) -> int:
    """Monotone integer for finite or infinite f32 (-0.0 and 0.0 share 0)."""
    return -(b & 0x7FFFFFFF) if b >> 31 else b


def ulp_dist(a: int, b: int) -> int:
    return abs(ordinal(a) - ordinal(b))


def to_units(b: int) -> int:
    """A finite f32 as a signed integer multiple of 2^-149."""
    e = (b >> 23) & 0xFF
    m = b & 0x7FFFFF
    v = m if e == 0 else (m | 0x800000) << (e - 1)
    return -v if b >> 31 else v


def round_f32(q: Fraction) -> int:
    """Round-to-nearest-even of an exact rational (real units) to f32 bits; overflow -> inf."""
    if q == 0:
        return 0
    sign = 0x80000000 if q < 0 else 0
    num, den = abs(q.numerator), q.denominator
    e = num.bit_length() - den.bit_length()

    def ge(k):                                  # q >= 2^k
        return num >= (den << k) if k >= 0 else (num << -k) >= den

    while not ge(e):
        e -= 1
    while ge(e + 1):
        e += 1
    qexp = max(e, -126) - 23
    n2, d2 = (num, den << qexp) if qexp >= 0 else (num << -qexp, den)
    m, r = divmod(n2, d2)
    if 2 * r > d2 or (2 * r == d2 and m & 1):
        m += 1
    if m == 0:
        return sign
    if m >= 1 << 24:
        m >>= 1
        qexp += 1
    if m < 1 << 23:
        return sign | m                       # subnormal
    E = qexp + 150
    if E >= 255:
        return sign | INF_BITS
    return sign | (E << 23) | (m - (1 << 23))


def units_to_f32(v: int) -> int:
    return round_f32(Fraction(v, 1 << UNIT))


def fword_key(b: int) -> int:
    """15.5.2 total order key: -inf < .. < -0.0 = 0.0 < .. < +inf < NaN."""
    if is_nan(b):
        return 1 << 40
    return -(b & 0x7FFFFFFF) if b >> 31 else (b & 0x7FFFFFFF)


# ---- the contract's algorithms with numpy float32 -----------------------------------------

def model_fsum(xs) -> int:
    """15.5.3 over f32 bit patterns in the given order; returns bits."""
    s = F(0.0)
    c = F(0.0)
    for b in xs:
        x = b2f(b)
        t = s + x
        if np.isfinite(t):
            if abs(s) >= abs(x):
                c = c + ((s - t) + x)
            else:
                c = c + ((x - t) + s)
        s = t
    r = s + c if np.isfinite(s) else s
    return f2b(r)


def model_sum(xs) -> int:
    return model_fsum(xs)


def model_mean(xs):
    if not xs:
        return None
    return f2b(b2f(model_fsum(xs)) / F(len(xs)))


def model_var(xs):
    """ddof 1 two-pass (15.5.4): the f32 var; None when n < 2."""
    n = len(xs)
    if n < 2:
        return None
    m = b2f(model_mean(xs))
    sq = []
    for b in xs:
        d = b2f(b) - m
        sq.append(f2b(d * d))
    return f2b(b2f(model_fsum(sq)) / F(n - 1))


def model_std(xs):
    v = model_var(xs)
    return None if v is None else f2b(np.sqrt(b2f(v)))


def sort_valid(xs):
    return sorted(xs, key=fword_key)           # stable: ties keep input order


def model_median(xs):
    n = len(xs)
    if n == 0:
        return None
    s = sort_valid(xs)
    if n % 2:
        return s[(n - 1) // 2]
    lo, hi = b2f(s[n // 2 - 1]), b2f(s[n // 2])
    return f2b(lo * F(0.5) + hi * F(0.5))


def quantile_idx(n: int):
    """describe's nearest-rank rows (round half away from zero) of min, 25%, 50%, 75%, max."""
    m = n - 1
    return [0] + [int(Fraction(p) * m + Fraction(1, 2)) for p in ("1/4", "1/2", "3/4")] + [m]


def model_quantiles(xs):
    if not xs:
        return None
    s = sort_valid(xs)
    return [s[i] for i in quantile_idx(len(xs))]


def model_minmax(xs):
    """(min, max) bits per 15.5.2: NaN skipped (all NaN -> NaN), on a -0.0 / 0.0 tie min answers -0.0 and max 0.0."""
    fin = [b for b in xs if not is_nan(b)]
    if not fin:
        return NAN_BITS, NAN_BITS
    return (min(fin, key=lambda b: (fword_key(b), b >> 31 == 0)),
            max(fin, key=lambda b: (fword_key(b), b >> 31 == 0)))


# ---- IEEE-order-independent expectations for non-finite data ------------------------------

def special_sum(xs):
    """Expected sum/mean bits when the data holds a NaN or an inf; None when all finite."""
    if any(is_nan(b) for b in xs):
        return NAN_BITS
    pos = any(b == INF_BITS for b in xs)
    neg = any(b == NINF_BITS for b in xs)
    if pos and neg:
        return NAN_BITS
    if pos:
        return INF_BITS
    if neg:
        return NINF_BITS
    return None


# ---- exact values and bounds (finite data) ------------------------------------------------

class Exact:
    """Exact quantities of a finite sample, in real units (Fractions)."""

    def __init__(self, xs):
        self.n = len(xs)
        self.X = [to_units(b) for b in xs]
        self.S = sum(self.X)                          # units 2^-149
        self.A = sum(abs(v) for v in self.X)
        n = self.n
        self.sum = Fraction(self.S, 1 << UNIT)
        self.abs_sum = Fraction(self.A, 1 << UNIT)
        self.mean = self.sum / n if n else None
        self._var = None

    # -- sums and means
    def kappa(self):
        return None if self.S == 0 else Fraction(self.A, abs(self.S))

    def gamma2(self, k):
        g = Fraction(k) * U / (1 - Fraction(k) * U) if k > 0 else Fraction(0)
        return g * g

    def sum_bound(self):
        n = self.n
        return U * abs(self.sum) + self.gamma2(max(n - 1, 0)) * self.abs_sum + Fraction(2, 1 << UNIT)

    def mean_bound(self):
        B1 = self.sum_bound()
        return (B1 + U * (abs(self.sum) + B1)) / self.n + Fraction(2, 1 << UNIT)

    # -- variance around the f32 mean m_hat the algorithm used
    def var_parts(self, mhat_bits):
        """(T0, T, delta) exactly: centred sum, sum about m_hat, mu - m_hat (real units)."""
        M = to_units(mhat_bits)
        n = self.n
        T = Fraction(sum((x - M) ** 2 for x in self.X), 1 << (2 * UNIT))
        mu = self.mean
        delta = mu - Fraction(M, 1 << UNIT)
        T0 = T - n * delta * delta
        return T0, T, delta

    def var_exact(self, mhat_bits):
        T0, _, _ = self.var_parts(mhat_bits)
        return T0 / (self.n - 1)

    def var_bound(self, mhat_bits):
        n = self.n
        T0, T, delta = self.var_parts(mhat_bits)
        rho = (1 + U) ** 3 - 1
        slack_sq = Fraction(n, 1 << 150)                     # underflowing squares
        Ts = (1 + rho) * T + slack_sq
        BT = rho * T + slack_sq + (U + self.gamma2(n - 1)) * Ts
        return (BT + U * (T + BT) + n * delta * delta) / (n - 1) + Fraction(1, 1 << 148)


def frac_sqrt_bits(q: Fraction) -> int:
    """sqrt of a non-negative rational rounded to f32 (60-digit Decimal; ties impossible)."""
    if q == 0:
        return 0
    getcontext().prec = 80
    d = Decimal(q.numerator) / Decimal(q.denominator)
    r = d.sqrt()
    # Decimal -> Fraction exactly
    return round_f32(Fraction(r))


def std_bound(var_exact: Fraction, var_bound: Fraction, std_hat: float) -> Fraction:
    """(4): |std_hat - sqrt(v)| <= min(Bv / sqrt v, sqrt Bv) + u std_hat (floats, 1e-9 safety)."""
    bv = float(var_bound)
    cand = math.sqrt(bv)
    if var_exact > 0:
        cand = min(cand, bv / math.sqrt(float(var_exact)))
    tot = cand * (1 + 1e-9) + float(U) * abs(std_hat) * (1 + 1e-9) + 2.0 ** -148
    return Fraction(tot)


def val(b: int) -> Fraction:
    """Real value of a finite f32 (bits)."""
    return Fraction(to_units(b), 1 << UNIT)
