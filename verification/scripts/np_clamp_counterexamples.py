"""Counterexamples to the contract of `make_np_clamp`, run through the real library.

F9-F14 are proved in `verification/lean/OpenDPVerification/NpClamp.lean` against a model of the
numpy operations; this script checks that each one reproduces with numpy and opendp. F15 and F16
are confirmed only by running them. See FINDINGS.md.

    uv run --with opendp --with numpy python -I verification/scripts/np_clamp_counterexamples.py

Takes about 30 seconds (the two non-terminating calls are stopped after 10 seconds each).
"""
import multiprocessing as mp
import sys
import warnings

import numpy as np
import opendp.prelude as dp

dp.enable_features("contrib")
TINY = 2.0**-1074  # smallest subnormal
MAX = sys.float_info.max


def clamp(norm, p, origin, data, cols, dtype=np.float64):
    origin = None if origin is None else np.array(origin, dtype=float)
    domain = dp.numpy.array2_domain(T="f32" if dtype == np.float32 else "f64", num_columns=cols)
    t = dp.numpy.make_np_clamp(domain, dp.symmetric_distance(), norm=norm, p=p, origin=origin)
    return t, t(np.array(data, dtype=dtype))


def member(t, out):
    try:
        return t.output_domain.member(out)
    except Exception:
        return False


def run(args, q):
    q.put(clamp(*args)[1].tolist())


def main():
    # F9: `arg + origin` rounds the clamped row out of the ball
    t, out = clamp(12.0, 2, [2.0**56], [[2.0**56 + 48]], 1)
    print("F9  origin rounding: out - origin =", out[0, 0] - 2.0**56, "> 12; output is a member:", member(t, out))

    # F10: squares underflow in the L2 norm
    t, out = clamp(2.0**-600, 2, None, [[2.0**-565, 0.0]], 2)
    print("F10 underflow: output row unchanged:", out[0, 0] == 2.0**-565,
          "; its norm 2^-565 > 2^-600; output is a member:", member(t, out))

    # F11: the loop does not terminate
    cases = [
        ("subnormal norm, p=1", (3 * TINY, 1, None, [[TINY] * 4], 4)),
        ("norm 2^-1022, p=1", (2.0**-1022, 1, None, [[(2**51 - 1) * TINY, (2**51 - 1) * TINY, 3 * TINY]], 3)),
    ]
    for name, args in cases:
        q = mp.Queue()
        proc = mp.Process(target=run, args=(args, q))
        proc.start()
        proc.join(10)
        if proc.is_alive():
            proc.terminate()
            print(f"F11 non-termination ({name}): no result after 10 s")
        else:
            print(f"F11 non-termination ({name}): returned", q.get())

    # F12: the norm overflows to inf, which nan_to_num turns into MAX = norm
    t, out = clamp(MAX, 1, None, [[MAX, MAX]], 2)
    print("F12 overflow at norm = MAX: output row unchanged:", out.tolist() == [[MAX, MAX]],
          "; output is a member:", member(t, out))

    # F13: an empty dataset raises, its neighbour with one row does not
    t, _ = clamp(1.0, 2, None, [[0.0]], 1)
    try:
        t(np.zeros((0, 1)))
        print("F13 empty dataset: returned")
    except Exception:
        print("F13 empty dataset: raises (zero-size array to reduction operation maximum)")

    # F14: the output domain keeps the input's cardinalities
    domain = dp.numpy.array2_domain(T=float, num_columns=2, cardinalities=[1, 2])
    t = dp.numpy.make_np_clamp(domain, dp.symmetric_distance(), norm=1.0, p=1)
    x = np.array([[2.0, 0.0], [2.0, 2.0]])
    out = t(x)
    print("F14 cardinalities: input is a member:", domain.member(x), "; output", out.tolist(),
          "is a member:", member(t, out))

    # F15: the row norms depend on the memory layout of the array
    t = dp.numpy.make_np_clamp(dp.numpy.array2_domain(T=float, num_columns=16), dp.symmetric_distance(), norm=1.0, p=2)
    x = np.random.default_rng(1).normal(size=(4, 16))
    a, b = t(np.ascontiguousarray(x)), t(np.asfortranarray(x))
    rows = [i for i in range(len(x)) if not np.array_equal(a[i], b[i])]
    print("F15 layout: rows clamped differently in C and Fortran order:", rows,
          "(max difference", np.abs(a - b).max(), ")")

    # F16: float32 data is clamped to float32(norm), which can exceed norm
    t, out = clamp(0.1, 2, None, [[1.0, 0.0], [0.3, 0.4]], 2, dtype=np.float32)
    norms = np.linalg.norm(out.astype(np.float64), axis=1)
    print("F16 float32: exact row norms", norms.tolist(), "> 0.1:", bool((norms > 0.1).any()),
          "; output is a member:", member(t, out))


if __name__ == "__main__":
    warnings.simplefilter("ignore")
    main()
