"""Exhaustive search for counterexamples to can_float_sum_overflow on tiny IEEE formats.

A format has precision p (MANTISSA_BITS = p - 1) and emax (= EXPONENT_BIAS), emin = 1 - emax.
Arithmetic is exact (Fractions) with round-to-nearest; overflow per IEEE 754 (the result rounded
with unbounded exponent exceeds MAX). Ties are either "even" (IEEE default) or "any" (both ways).

For each format and each bound magnitude, finds the largest size the check accepts and
explores every reachable partial sum of datasets of up to that size. Expected output: no
counterexample with ties to even; counterexamples for the sequential sum when ties may round
up (see FINDINGS.md, D2). Takes about three minutes.

    python3 verification/scripts/float_sum_overflow_search.py
"""
from fractions import Fraction as F
import math, sys
from functools import lru_cache

def make_format(p, emax):
    emin = 1 - emax
    q0 = emin - p + 1
    vals = set()
    for m in range(0, 2**p):
        vals.add(F(m) * F(2) ** q0)
    for e in range(emin, emax + 1):
        for m in range(2 ** (p - 1), 2**p):
            vals.add(F(m) * F(2) ** (e - p + 1))
    pos = sorted(vals)
    MAX = pos[-1]
    allv = sorted(set(pos) | {-v for v in pos})
    return dict(p=p, emax=emax, emin=emin, MAX=MAX, pos=pos, all=allv)

def floor_log2(x):
    # x > 0 Fraction
    e = x.numerator.bit_length() - x.denominator.bit_length()
    while F(2) ** e > x: e -= 1
    while F(2) ** (e + 1) <= x: e += 1
    return e

def rnd(fmt, x, ties):
    """Set of nearest values (unbounded exponent); None means overflow."""
    if x == 0: return [F(0)]
    s = 1 if x > 0 else -1
    a = abs(x)
    e = max(floor_log2(a), fmt['emin'])
    q = F(2) ** (e - fmt['p'] + 1)
    m = a / q
    fl = math.floor(m)
    frac = m - fl
    if frac < F(1, 2): ms = [fl]
    elif frac > F(1, 2): ms = [fl + 1]
    else:
        ms = [fl if fl % 2 == 0 else fl + 1] if ties == 'even' else [fl, fl + 1]
    out = []
    for mm in ms:
        v = s * mm * q
        out.append(None if abs(v) > fmt['MAX'] else v)
    return out

def ru(fmt, x):
    """Round up to the format (None = +inf)."""
    for v in fmt['all']:
        if v >= x: return v
    return None

def rd(fmt, x):
    best = None
    for v in fmt['all']:
        if v <= x: best = v
    return best

def round_up_pow2(fmt, x):
    # smallest power of two >= x, at least 2^(-bias) as in the Rust code for x = 0
    if x == 0: return F(2) ** (-fmt['emax'])
    if x < F(2) ** fmt['emin']: return F(2) ** fmt['emin']
    e = floor_log2(x)
    return F(2) ** e if F(2) ** e == x else F(2) ** (e + 1)

def can_overflow(fmt, alg, n, mag):
    """Mirror of can_float_sum_overflow (worst case for the directed-rounding primitives is exact)."""
    size_ = ru(fmt, F(n))
    if size_ is None: return 'err'
    p, emax = fmt['p'], fmt['emax']
    if alg == 'seq':
        lim = F(2) ** (emax - (p - 1) - 1)
        if mag < lim: return False
    else:
        max_ulp = F(2) ** (emax - (p - 1))
        lim = rd(fmt, max_ulp / size_)
        if mag < lim: return False
    M = round_up_pow2(fmt, mag)
    if M > fmt['MAX']: return 'err'
    prod = ru(fmt, M * size_)
    return prod is None

def seq_overflows(fmt, n, elems, ties):
    reach = {F(0)}
    for k in range(n):
        nxt = set()
        for s in reach:
            for x in elems:
                for r in rnd(fmt, s + x, ties):
                    if r is None: return k + 1
                    nxt.add(r)
        reach = nxt
    return 0

def pw_overflows(fmt, n, elems, ties):
    memo = {0: {F(0)}, 1: set(elems)}
    def P(k):
        if k in memo: return memo[k]
        m = k // 2
        a, b = P(m), P(k - m)
        if a is None or b is None: memo[k] = None; return None
        out = set()
        for x in a:
            for y in b:
                for r in rnd(fmt, x + y, ties):
                    if r is None: memo[k] = None; return None
                    out.add(r)
        memo[k] = out
        return out
    for k in range(n + 1):
        if P(k) is None: return k
    return 0

def main():
    for ties in ['even', 'any']:
        for p in [2, 3, 4]:
            for emax in [2, 3, 4]:
                fmt = make_format(p, emax)
                for alg in ['seq', 'pw']:
                    for mag in fmt['pos']:
                        # largest n for which the check passes (monotone in n)
                        n = 0
                        while n < 400 and can_overflow(fmt, alg, n + 1, mag) is False:
                            n += 1
                        if n == 0: continue
                        elems = [v for v in fmt['all'] if -mag <= v <= mag]
                        f = (seq_overflows if alg == 'seq' else pw_overflows)(fmt, n, elems, ties)
                        if f:
                            print(f"COUNTEREXAMPLE ties={ties} p={p} emax={emax} alg={alg} mag={mag} n={n} overflow at length {f}")
                print(f"done ties={ties} p={p} emax={emax}", flush=True)

main()
