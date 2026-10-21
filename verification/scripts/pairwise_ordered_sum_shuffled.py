"""The pairwise ordered (saturating) float sums after a uniform shuffle (FINDINGS.md, F2).

Under `SymmetricDistance`, `make_sum` runs `make_ordered_random >> make_*_float_ordered_sum::<Pairwise>`.
The output is then random, so stability means a coupling of the outputs on neighbouring datasets
within the map: the infinity-Wasserstein distance `W_inf` of the two output laws is at most the map.
That suffices for noise calibrated to the map (Laplace gives eps-DP). This script computes, exactly,
`W_inf / map` and the privacy loss of `Laplace(map / eps)` divided by `eps`, for the F2 examples and
then for every multiset on small grids.

Values are integer multiples of `k` (scaled by 1000), with saturation at `MAX = C` and real
arithmetic (no rounding). The output law of `pairwise(shuffle(x))` follows by recursion on counts:
a uniform shuffle puts a uniformly random sub-multiset of size `n // 2` on the left (multivariate
hypergeometric), and the two halves are then independent uniform shuffles.

    python3 verification/scripts/pairwise_ordered_sum_shuffled.py            # examples + check
    python3 verification/scripts/pairwise_ordered_sum_shuffled.py search unsized -1 1 48
    python3 verification/scripts/pairwise_ordered_sum_shuffled.py search sized -1 2 20 [C]
"""
import itertools
import random
import sys
from collections import Counter, defaultdict
from functools import lru_cache
from math import comb, exp, log

S = 1000
vals, C = (), 0


def setup(vals_, C_):
    global vals, C
    vals, C = vals_, C_
    law.cache_clear()


@lru_cache(None)
def law(counts):
    """The output law of pairwise(shuffle(x)), for x with `counts[i]` copies of `vals[i]`."""
    n = sum(counts)
    if n == 0:
        return ((0, 1.0),)
    if n == 1:
        return ((vals[counts.index(1)], 1.0),)
    m = n // 2
    total = comb(n, m)
    out = defaultdict(float)
    for left in itertools.product(*[range(c + 1) for c in counts]):
        if sum(left) != m:
            continue
        p = 1.0
        for c, l in zip(counts, left):
            p *= comb(c, l)
        p /= total
        right = tuple(c - l for c, l in zip(counts, left))
        for a, wa in law(left):
            for b, wb in law(right):
                out[max(-C, min(C, a + b))] += p * wa * wb
    return tuple(sorted(out.items()))


def w_inf(P, Q, tol=1e-12):
    """sup_t |F_P^-1(t) - F_Q^-1(t)|: the quantile coupling is optimal on the real line."""
    sp, sq = [], []
    for L, s in ((P, sp), (Q, sq)):
        acc = 0.0
        for a, w in L:
            acc += w
            s.append((acc, a))
    i = j = 0
    best = 0
    while i < len(sp) and j < len(sq):
        best = max(best, abs(sp[i][1] - sq[j][1]))
        if sp[i][0] < sq[j][0] - tol:
            i += 1
        elif sp[i][0] > sq[j][0] + tol:
            j += 1
        else:
            i += 1
            j += 1
    return best


def lse(xs):
    m = max(xs)
    return m + log(sum(exp(x - m) for x in xs))


def laplace_loss(P, Q, b):
    """sup_z |log p(z) / q(z)| for P, Q plus Laplace(b) noise.

    Between atoms, the log ratio has the form log((A e^u + B e^-u) / (C e^u + D e^-u)), which is
    monotone in u, so its sup is at an atom or a tail limit."""
    P = [(a, w) for a, w in P if w > 0]
    Q = [(a, w) for a, w in Q if w > 0]

    def ld(L, z):
        return lse([log(w) - abs(z - a) / b for a, w in L])

    cands = [abs(ld(P, z) - ld(Q, z)) for z in {a for a, _ in P} | {a for a, _ in Q}]
    for s in (1, -1):
        cands.append(abs(lse([log(w) + s * a / b for a, w in P])
                         - lse([log(w) + s * a / b for a, w in Q])))
    return max(cands)


def brute_law(ms):
    def pw(xs):
        n = len(xs)
        if n == 0:
            return 0
        if n == 1:
            return xs[0]
        m = n // 2
        return max(-C, min(C, pw(xs[:m]) + pw(xs[m:])))

    out = Counter(pw(p) for p in itertools.permutations(ms))
    t = sum(out.values())
    return {a: w / t for a, w in out.items()}


def check_recursion(trials=30):
    rng = random.Random(1)
    for _ in range(trials):
        setup((-S, 0, S, 2 * S), rng.choice([2001, 3001, 4001]))
        ms = [rng.choice(vals) for _ in range(rng.randint(2, 8))]
        a = dict(law(tuple(ms.count(v) for v in vals)))
        b = brute_law(ms)
        assert set(a) == set(b) and all(abs(a[x] - b[x]) < 1e-12 for x in a), (ms, C)
    print(f"recursion matches brute-force enumeration on {trials} random multisets")


def report(name, cx, cy, sens):
    Px, Py = law(cx), law(cy)
    print(f"{name}: W_inf / map = {w_inf(Px, Py) / sens:.4f}; Laplace loss / eps: "
          + ", ".join(f"eps={e}: {laplace_loss(Px, Py, sens / e) / e:.4f}" for e in (0.1, 1, 5)))


def examples():
    # unsized, 11 elements: bounds [-1, 2], MAX = 4.001, y = x minus a 2, map = 3
    setup((-S, 0, S, 2 * S), 4001)
    x = Counter([2, -1, -1, 2, 2, 2, 0, -1, -1, -1, -1])
    cx = tuple(x[v] for v in (-1, 0, 1, 2))
    report("unsized (11), minus 2", cx, (6, 1, 0, 3), 3 * S)
    # unsized, 32 elements: bounds [-1, 1], MAX = 4.001, y = x minus a -1, map = 2
    setup((-S, 0, S), 4001)
    x = Counter([-1, -1, -1, 0, -1, -1, 0, 1, 1, -1, -1, 1, 0, 1, 1, -1,
                 1, 1, 0, 1, 1, 1, 1, 1, 0, -1, -1, 1, -1, 0, -1, -1])
    cx = tuple(x[v] for v in (-1, 0, 1))
    report("unsized (32), minus -1", cx, (cx[0] - 1, cx[1], cx[2]), 2 * S)
    # sized, 10 elements: bounds [-1, 1], MAX = 2.001, replace a -1 by a 1, map = (2 / 2) * 2
    setup((-S, 0, S), 2001)
    report("sized (10), -1 -> 1", (6, 0, 4), (5, 0, 5), 2 * S)


def compositions(n, k):
    if k == 1:
        yield (n,)
        return
    for i in range(n + 1):
        for r in compositions(n - i, k - 1):
            yield (i,) + r


def search(mode, lo, hi, N, C_=None):
    """Every multiset over [lo, hi] of at most N values, against every neighbour: unsized deletes
    one value (d_in = 1), sized replaces one (d_in = 2). The map is U - L in both cases.
    C defaults to the smallest MAX that `make_sum` accepts: max(U - L, 2 max(|L|, U))."""
    sens = (hi - lo) * S
    mag = max(-lo, hi) * S
    setup(tuple(v * S for v in range(lo, hi + 1)), C_ or max(sens, 2 * mag) + 1)
    k = len(vals)
    best_w = (0, None)
    best_l = {e: (0, None) for e in (0.1, 1.0, 5.0)}
    for n in range(2, N + 1):
        for cx in compositions(n, k):
            Px = law(cx)
            ys = []
            for i in range(k):
                if cx[i] == 0:
                    continue
                d = list(cx)
                d[i] -= 1
                if mode == "unsized":
                    ys.append(tuple(d))
                else:
                    for j in range(k):
                        if j != i:
                            e = d[:]
                            e[j] += 1
                            ys.append(tuple(e))
            for cy in ys:
                Py = law(cy)
                w = w_inf(Px, Py) / sens
                if w > best_w[0] + 1e-9:
                    best_w = (w, (cx, cy))
                for e in best_l:
                    loss = laplace_loss(Px, Py, sens / e) / e
                    if loss > best_l[e][0] + 1e-9:
                        best_l[e] = (loss, (cx, cy))
    print(f"{mode} [{lo}, {hi}] MAX={C / S} n<={N}: worst W_inf / map {best_w[0]:.4f} {best_w[1]}; "
          "worst Laplace loss / eps "
          + ", ".join(f"eps={e}: {v[0]:.4f} {v[1]}" for e, v in best_l.items()))


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "search":
        mode, lo, hi, N = sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
        search(mode, lo, hi, N, int(float(sys.argv[6]) * S) if len(sys.argv) > 6 else None)
    else:
        check_recursion()
        examples()
