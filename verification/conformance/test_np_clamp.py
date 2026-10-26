"""Tie the Lean model of `make_np_clamp` to the code it models.

`verification/lean/OpenDPVerification/NpClamp.lean` proves theorems about a hand transcription of
`make_np_clamp`, over a model of numpy. `NpClampExec.lean` is an executable copy of that model,
proved equal to it (`ClampQ.clamp_toRes`), with numpy's summation order (`numpyPlan`). These tests
run the executable model (`NpClampOracle.lean`) and the code on the same inputs and require the same
results, bit for bit (signed zeros aside, which the model does not track):

* `test_norm`: the model's `rowNorm` is `np.linalg.norm(x, ord=p, axis=1)`. This checks the numpy
  model: IEEE operations, the norm formulas, and the pairwise summation tree.
* `test_outside`: the model's `outside` is the output domain's norm check
  (`array2_domain(...).member`), on rows at the boundary.
* `test_clamp`: the model's `clamp` is `make_np_clamp`'s function, including the bound and origin
  that the constructor computes. This checks the transcription.

Run from the repository root, after building the library (`cargo build --features untrusted,ffi --lib`
in `rust/`):

    PYTHONPATH=python/src uv run --no-project --with numpy --with pytest --with deprecated \
        python -m pytest verification/conformance
"""

import json
import os
import shutil
import subprocess
from fractions import Fraction
from pathlib import Path

import pytest

np = pytest.importorskip("numpy")
import opendp.prelude as dp  # noqa: E402

dp.enable_features("contrib")

LEAN = Path(__file__).resolve().parents[1] / "lean"
DTYPES = {"f64": np.float64, "f32": np.float32}
MIN_NORM = {"f64": 2.0**-458, "f32": 2.0**-39}


class Oracle:
    def __init__(self):
        env = dict(os.environ)
        env["PATH"] = f"{Path.home() / '.elan' / 'bin'}{os.pathsep}{env['PATH']}"
        if shutil.which("lake", path=env["PATH"]) is None:
            pytest.skip("lake (Lean) is not installed")
        subprocess.run(
            ["lake", "build", "OpenDPVerification.NpClampExec"],
            cwd=LEAN,
            env=env,
            check=True,
            capture_output=True,
        )
        self.proc = subprocess.Popen(
            ["lake", "env", "lean", "--run", "NpClampOracle.lean"],
            cwd=LEAN,
            env=env,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            text=True,
        )

    def __call__(self, **request):
        self.proc.stdin.write(json.dumps(request) + "\n")
        self.proc.stdin.flush()
        response = json.loads(self.proc.stdout.readline())
        assert "error" not in response, response["error"]
        return response

    def close(self):
        self.proc.stdin.close()
        self.proc.wait()


@pytest.fixture(scope="module")
def oracle():
    o = Oracle()
    yield o
    o.close()


def enc(x) -> str:
    x = float(x)
    if np.isnan(x):
        return "nan"
    if np.isinf(x):
        return "inf" if x > 0 else "-inf"
    n, d = x.as_integer_ratio()
    return f"{n}/{d}"


def enc_rows(x):
    return [[enc(v) for v in row] for row in x]


def same(actual, expected: str) -> bool:
    """`actual` (a numpy float) is the model's float `expected`."""
    if expected == "nan":
        return bool(np.isnan(actual))
    if expected in ("inf", "-inf"):
        return float(actual) == float(expected)
    n, d = map(int, expected.split("/"))
    return bool(np.isfinite(actual)) and Fraction(float(actual)) == Fraction(n, d)


def random_values(rng, shape, dtype, scale_exp=(-30, 30), special=0.05):
    """Values over a wide range of magnitudes, with zeros, infinities and NaN, so that rounding and
    the summation order matter."""
    info = np.finfo(dtype)
    x = rng.standard_normal(shape) * 2.0 ** rng.integers(*scale_exp, shape)
    u = rng.random(shape)
    x[u < special] = 0.0
    x[(u >= special) & (u < 1.5 * special)] = np.inf
    x[(u >= 1.5 * special) & (u < 2 * special)] = -np.inf
    x[(u >= 2 * special) & (u < 2.5 * special)] = np.nan
    big = (u >= 2.5 * special) & (u < 3 * special)
    x[big] = rng.choice([1, -1], big.sum()) * float(info.max) * rng.random(big.sum())
    tiny = (u >= 3 * special) & (u < 3.5 * special)
    x[tiny] = (
        rng.choice([1, -1], tiny.sum())
        * float(info.smallest_subnormal)
        * rng.integers(1, 100, tiny.sum())
    )
    with np.errstate(over="ignore"):
        return x.astype(dtype)


# row lengths that reach each branch of numpy's pairwise_sum: < 8, 8..128, and split recursively
LENGTHS = list(range(0, 20)) + [
    31,
    64,
    100,
    127,
    128,
    129,
    130,
    136,
    200,
    255,
    256,
    257,
    300,
    1000,
    1500,
]


@pytest.mark.parametrize("fmt", DTYPES)
@pytest.mark.parametrize("p", [1, 2])
def test_norm(oracle, fmt, p):
    rng = np.random.default_rng([1, p, len(fmt)])
    dtype = DTYPES[fmt]
    for n in LENGTHS:
        for scale_exp in [(-30, 30), (-200, 200) if fmt == "f64" else (-60, 60)]:
            x = random_values(
                rng, (6, n), dtype, scale_exp, special=0.02 if n > 20 else 0.05
            )
            with np.errstate(over="ignore", under="ignore", invalid="ignore"):
                actual = np.linalg.norm(x, ord=p, axis=1)
            expected = oracle(op="norm", fmt=fmt, p=p, rows=enc_rows(x))["out"]
            for i, (a, e) in enumerate(zip(actual, expected, strict=True)):
                assert same(a, e), (fmt, p, n, x[i].tolist(), float(a), e)


@pytest.mark.parametrize("fmt", DTYPES)
@pytest.mark.parametrize("p", [1, 2])
@pytest.mark.filterwarnings("ignore:.*does not belong to carrier type")
def test_outside(oracle, fmt, p):
    rng = np.random.default_rng([2, p, len(fmt)])
    dtype = DTYPES[fmt]
    for trial in range(60):
        cols = int(rng.integers(1, 40))
        norm = float(dtype(2.0 ** rng.uniform(-20, 20)))
        origin = (rng.standard_normal(cols) * 2.0 ** rng.integers(-10, 30)).astype(
            dtype
        )
        # rows whose norm is within a few ulps of `norm`
        direction = rng.standard_normal((8, cols))
        direction /= np.linalg.norm(direction, ord=p, axis=1, keepdims=True)
        scale = 1.0 + rng.integers(-4, 5, (8, 1)) * float(np.finfo(dtype).eps)
        x = (direction * norm * scale).astype(dtype) + origin
        domain = dp.numpy.array2_domain(norm=norm, p=p, origin=origin, T=fmt)

        expected = oracle(
            op="outside",
            fmt=fmt,
            p=p,
            bound=enc(norm),
            origin=[enc(o) for o in origin],
            rows=enc_rows(x),
        )["out"]
        for i, e in enumerate(expected):
            try:
                accepted = domain.member(x[i : i + 1])
            except Exception as err:
                assert "row norm" in str(err), err
                accepted = False
            assert accepted == (not e), (fmt, p, norm, origin.tolist(), x[i].tolist())


# inputs from the findings (verification/FINDINGS.md), run on the fixed code
FINDINGS = [
    # F9: adding origin back rounds the row out of the ball
    dict(fmt="f64", p=2, norm=12.0, origin=[2.0**56], x=[[2.0**56 + 48]]),
    # F10: squares underflow (now rejected by the constructor for norms this small)
    dict(
        fmt="f64",
        p=2,
        norm=MIN_NORM["f64"],
        origin=None,
        x=[[2.0**-400, 0.0], [2.0**-500, 2.0**-500]],
    ),
    # F12: the norm of the largest floats overflows
    dict(
        fmt="f64",
        p=1,
        norm=float(np.finfo(np.float64).max),
        origin=None,
        x=[[float(np.finfo(np.float64).max)] * 2, [1.0, 2.0]],
    ),
    # F14: equal values in a column differ after clamping
    dict(fmt="f64", p=2, norm=1.0, origin=None, x=[[2.0, 0.0], [2.0, 2.0]]),
    # F16: norm is not a float32
    dict(fmt="f32", p=2, norm=0.1, origin=None, x=[[1.0, 1.0], [0.05, 0.05]]),
    dict(fmt="f32", p=1, norm=1 / 3, origin=[0.1, 0.2], x=[[3.0, -4.0]]),
]


def run_case(oracle, fmt, p, norm, origin, x, fortran=False):
    dtype = DTYPES[fmt]
    x = np.array(x, dtype=dtype, order="F" if fortran else "C")
    cols = x.shape[1]
    trans = dp.numpy.array2_domain(T=fmt, num_columns=cols), dp.symmetric_distance()
    trans = trans >> dp.numpy.then_np_clamp(
        norm=norm, p=p, origin=None if origin is None else np.array(origin)
    )
    out = trans(x)

    model_origin = [0.0] * cols if origin is None else origin
    res = oracle(
        op="clamp",
        fmt=fmt,
        p=p,
        norm=enc(norm),
        origin=[enc(o) for o in model_origin],
        rows=enc_rows(x),
        fuel=10_000,
    )
    context = (fmt, p, norm, origin, x.tolist())
    assert res["res"] == "ok", context
    assert out.dtype == dtype and out.shape == x.shape, context
    for row, expected in zip(out, res["out"], strict=True):
        for a, e in zip(row, expected, strict=True):
            assert same(a, e), (*context, row.tolist(), expected)
    assert trans.output_domain.member(out), context


@pytest.mark.parametrize("case", FINDINGS)
def test_clamp_findings(oracle, case):
    run_case(oracle, **case)


@pytest.mark.parametrize("fmt", DTYPES)
@pytest.mark.parametrize("p", [1, 2])
def test_clamp(oracle, fmt, p):
    rng = np.random.default_rng([3, p, len(fmt)])
    dtype = DTYPES[fmt]
    info = np.finfo(dtype)
    for trial in range(150):
        rows = int(rng.integers(0, 6))
        cols = int(rng.choice([1, 2, 3, 7, 8, 9, 16, 50, 129, 300]))
        kind = rng.integers(0, 5)
        if kind == 0:
            norm = 1.0
        elif kind == 1:  # any magnitude above the minimum, often not a float32
            norm = 2.0 ** rng.uniform(np.log2(MIN_NORM[fmt]), np.log2(float(info.max)))
        elif kind == 2:  # near the minimum
            norm = MIN_NORM[fmt] * (1 + rng.random())
        elif kind == 3:
            # large, but at most half the largest float: closer to it, a row whose norm overflows
            # takes up to ~2^52 passes of the loop to clamp (F18). For f32 data, a float64 norm
            # above the largest float32 makes the bound the largest float32 exactly.
            if fmt == "f32" and rng.random() < 0.5:
                norm = float(info.max) * rng.uniform(1.0, 1.5)
            else:
                norm = float(info.max) * rng.uniform(0.25, 0.5)
        else:
            norm = float(rng.uniform(0, 10)) + MIN_NORM[fmt]
        origin = None
        if rng.random() < 0.5:
            origin = (
                rng.standard_normal(cols)
                * 2.0 ** rng.integers(-20, 60 if fmt == "f64" else 20)
            ).tolist()
        # data around the scale of norm, and anywhere
        scale_exp = int(
            np.clip(
                np.log2(norm),
                -900 if fmt == "f64" else -100,
                900 if fmt == "f64" else 100,
            )
        )
        lo, hi = (scale_exp - 10, scale_exp + 10) if rng.random() < 0.7 else (-60, 60)
        x = random_values(rng, (rows, cols), dtype, (lo, hi), special=0.03).astype(
            np.float64
        )
        run_case(oracle, fmt, p, norm, origin, x, fortran=bool(rng.random() < 0.2))
