"""Counterexamples to the stability of OpenDP's pairwise ordered (saturating) float sums.

`make_(sized_)bounded_float_ordered_sum::<Pairwise<f64>>` sums with saturating addition,
`clamp(a + b, -MAX, MAX)`, over the pairwise split `n // 2`. Deleting or inserting one element
changes every later split, which regroups the elements, and clamping depends on the grouping.
See FINDINGS.md, F2. Python floats are IEEE binary64, like Rust's `f64`.

    python3 verification/scripts/pairwise_ordered_sum_counterexample.py
"""
import sys

MAX = sys.float_info.max


def sat_add(a, b):
    return max(-MAX, min(MAX, a + b))


def pairwise(xs):
    n = len(xs)
    if n == 0:
        return 0.0
    if n == 1:
        return xs[0]
    m = n // 2
    return sat_add(pairwise(xs[:m]), pairwise(xs[m:]))


def report(name, x, y, d_out):
    fx, fy = pairwise(x), pairwise(y)
    # compare halves, as the difference itself can exceed MAX
    diff_half = abs(fx / 2 - fy / 2)
    print(f"{name}: f(x) = {fx:.4e}, f(y) = {fy:.4e}, "
          f"|f(x) - f(y)| / 2 = {diff_half:.4e} > d_out / 2 ~ {d_out / 2:.4e} "
          f"(ratio {diff_half / (d_out / 2):.3f})")
    assert diff_half > d_out / 2


# Unsized (make_sum on InsertDeleteDistance): bounds [-k, k], y = x without its last element (d_in = 1).
# The stability map is d_in * max(U - L, |L|, U) + relaxation = 2k + (a relative 1e-8 or less).
k = MAX / 4.001
x = [v * k for v in [-1, -1, -1, 0, -1, -1, 0, 1, 1, -1, -1, 1, 0, 1, 1, -1,
                     1, 1, 0, 1, 1, 1, 1, 1, 0, -1, -1, 1, -1, 0, -1, -1]]
report("unsized", x, x[:-1], 2 * k * (1 + 1e-6))

# Sized (size 6): bounds [-k, 2k], y = x with its first element deleted and 2k inserted (d_in = 2).
# The stability map is (d_in / 2) * (U - L) + relaxation = 3k + (a relative 1e-14 or less).
k = MAX / 3.001
x = [v * k for v in [-1, 2, 2, -1, -1, -1]]
y = [v * k for v in [2, 2, -1, 2, -1, -1]]
report("sized", x, y, 3 * k * (1 + 1e-6))
