"""Property-based tests for ``make_np_clamp``.

``make_np_clamp`` scales each row of a 2-D array so that its L``p`` norm about ``origin``
is at most ``norm``, and declares that bound in its output domain.
Downstream constructors (``make_np_sum``, ``make_np_mean``, PCA) set their sensitivity from the
declared bound, so an output row that is really outside it breaks their privacy guarantees.

Rows and arrays are compared exactly (floats by their bits), and norms are checked exactly
in rationals as well as with the library's own floating-point membership check.

Properties (labels match the comments below):

* A: the constructor accepts exactly the valid parameters, and builds the expected output space
* B: rows are scaled independently, towards the origin, only when outside the bound, without NaN
* C: outputs satisfy the declared bound, exactly up to rounding, and the identity map is stable
* D: clamping terminates
* E: large datasets, wide rows, extreme values and huge sizes

Known issues in the library are listed in ``KNOWN_ISSUES``. Each has minimal tests of the correct
behavior, marked with ``known_issue`` (strict xfail), and the properties skip the inputs it
affects while it's listed. When an issue is fixed, its tests pass and fail the run:
remove the issue from ``KNOWN_ISSUES``, with its markers.
"""

from __future__ import annotations

import math
import warnings
from dataclasses import dataclass
from fractions import Fraction
from typing import Any

import pytest

np = pytest.importorskip("numpy")

from hypothesis import event, given, strategies as st  # noqa: E402

import opendp.prelude as dp  # noqa: E402
from opendp.extras.numpy import make_np_clamp  # noqa: E402

from test._props_common import (  # noqa: E402
    array_key,
    array_row_key,
    edge_floats,
    exact_lp_norm_cmp,
    float_arrays,
    known_issue,
    member_reason,
    rejection,
    symmetric_distance,
    time_limit,
)

dp.enable_features("contrib")

SYM = dp.symmetric_distance()
DTYPES = {"f64": np.float64, "f32": np.float32, "i64": np.int64}

#: Known issues in ``make_np_clamp`` (and ``array2_domain``), which undermine the declared bound
#: or the domain. See the module docstring.
KNOWN_ISSUES = {
    "exact-norm": "the loop stops once the rounded norm is at most the bound, "
    "so clamped rows can be just above it in exact arithmetic",
    "nonzero-origin": "adding a nonzero origin back doesn't round-trip, "
    "so rows land outside the bound",
    "f32-domain": "f32 data is checked against a float64 origin, or turned into float64",
    "integer-data": "integer data is clamped to float64, while the domain declares T=i64",
    "underflow": "L2 squares underflow, so rows far outside a tiny bound aren't clamped",
    "subnormal-hang": "with a subnormal norm, the clamping loop can run forever",
    "overflow-saturated": "norms that overflow are saturated at MAX, "
    "so rows far outside a bound near MAX aren't clamped",
    "cardinalities": "the output domain keeps the input's cardinalities",
    "length-one-origin": "a length-1 origin broadcasts, but the domain declares one column",
    "unfit-norm-warns": "a norm that doesn't fit the data's type warns when clamping",
    "l2-membership-overflow": "array2_domain's L2 check squares values, which overflows",
    "empty-data": "clamping an empty dataset raises",
    "infinite-norm": "an infinite norm is accepted",
    "p-true": "p=True is accepted as p=1",
}


# ---------------------------------------------------------------------------------------------
# Generators
# ---------------------------------------------------------------------------------------------


@dataclass
class Config:
    """Parameters for one construction: an input domain, ``norm``, ``p`` and ``origin``."""

    T: str
    cols: int
    rows: int
    p: Any
    norm: float
    #: as passed to the constructor
    origin: Any
    #: a label for the kind of origin
    origin_kind: str
    #: whether the input domain declares the number of columns
    num_columns: bool
    #: whether the input domain declares the number of rows
    sized: bool
    #: whether the input domain declares (satisfiable) cardinalities
    cardinalities: bool
    #: whether the input domain already has a norm bound, which is replaced
    bounded_input: bool

    @property
    def dtype(self):
        return DTYPES[self.T]

    def input_domain(self):
        kwargs: dict[str, Any] = {"T": self.T}
        if self.num_columns:
            kwargs["num_columns"] = self.cols
        if self.sized:
            kwargs["size"] = self.rows
        if self.cardinalities:
            # every column has at most `rows` distinct values, so the data always satisfies this
            kwargs["cardinalities"] = [max(self.rows, 1)] * self.cols
        if self.bounded_input:
            kwargs |= {"norm": math.inf, "p": 1}
        return dp.numpy.array2_domain(**kwargs)

    def origin_array(self):
        """The origin as the function subtracts it."""
        return 0.0 if self.origin is None else self.origin


def accepts(cfg: Config) -> bool:
    """The reference for when construction succeeds."""
    if not cfg.norm > 0:  # also rejects NaN
        return False
    if math.isinf(cfg.norm) and "infinite-norm" not in KNOWN_ISSUES:
        return False
    if cfg.p not in {1, 2}:
        return False
    origin = cfg.origin
    if origin is None:
        return True
    if not np.all(np.isfinite(origin)):
        return False
    if isinstance(origin, (int, float)):
        return origin == 0  # array2_domain only accepts a zero scalar
    if not isinstance(origin, np.ndarray) or origin.ndim != 1:
        return False
    # declared cardinalities also declare the number of columns
    declared = cfg.num_columns or cfg.cardinalities
    return not declared or origin.size == cfg.cols


def norms() -> st.SearchStrategy[float]:
    moderate = st.floats(1e-3, 1e6)
    extreme = st.sampled_from(
        [
            5e-324,
            3 * 5e-324,
            2.0**-1070,
            1e-300,
            1e-150,
            1e-30,
            1e300,
            1.7976931348623157e308,
            math.inf,
        ]
    )
    invalid = st.sampled_from([0.0, -0.0, -1.0, math.nan, -math.inf])
    return st.one_of(*[moderate] * 6, extreme, extreme, invalid)


@st.composite
def origins(draw, cols: int) -> tuple[str, Any]:
    kind = draw(
        st.sampled_from(
            ["none"] * 8
            + [
                "zero scalar",
                "zeros",
                "moderate",
                "moderate",
                "1e3",
                "1e15",
                "f32 array",
            ]
            + ["length 1", "nonzero scalar", "list", "non-finite"]
        )
    )
    values = lambda lo, hi: draw(  # noqa: E731
        st.lists(st.floats(lo, hi), min_size=cols, max_size=cols)
    )
    origin = {
        "none": lambda: None,
        "zero scalar": lambda: 0.0,
        "zeros": lambda: np.zeros(cols),
        "moderate": lambda: np.array(values(-10, 10)),
        "1e3": lambda: np.array(values(-1e3, 1e3)),
        "1e15": lambda: np.array(values(1e15, 2e15)),
        "f32 array": lambda: np.array(values(-10, 10), dtype=np.float32),
        "length 1": lambda: np.array([draw(st.floats(-10, 10))]),
        "nonzero scalar": lambda: draw(st.floats(0.5, 10)),
        "list": lambda: values(-10, 10),
        "non-finite": lambda: np.array([math.inf] * cols),
    }[kind]()
    return kind, origin


@st.composite
def configs(draw) -> Config:
    T = draw(st.sampled_from(["f64"] * 4 + ["f32"] * 2 + ["i64"]))
    cols = draw(st.integers(1, 6))
    origin_kind, origin = draw(origins(cols))
    return Config(
        T=T,
        cols=cols,
        rows=draw(st.integers(1 if "empty-data" in KNOWN_ISSUES else 0, 40)),
        p=draw(st.sampled_from([1, 2] * 12 + [0, 3, 1.5, None])),
        norm=draw(norms()),
        origin=origin,
        origin_kind=origin_kind,
        num_columns=draw(st.booleans()),
        sized=draw(st.booleans()),
        cardinalities=draw(st.integers(0, 4)) == 0,
        bounded_input=draw(st.integers(0, 4)) == 0,
    )


def int_elements() -> st.SearchStrategy:
    i64 = np.iinfo(np.int64)
    return st.one_of(
        st.integers(-1000, 1000),
        st.integers(int(i64.min), int(i64.max)),
        st.sampled_from([0, 1, -1, int(i64.max), int(i64.min)]),
    )


def arrays(draw, cfg: Config, rows: int):
    """An array of ``rows`` rows in ``cfg``'s dtype and column count."""
    if cfg.dtype == np.int64:
        return draw(float_arrays(np.int64, rows, cfg.cols, int_elements()))
    return draw(float_arrays(cfg.dtype, rows, cfg.cols))


# ---------------------------------------------------------------------------------------------
# Reference computations
# ---------------------------------------------------------------------------------------------


def centered(x, origin):
    """``x - origin`` with NaN as 0 and ±inf as ±MAX, as the function computes it."""
    with np.errstate(over="ignore", invalid="ignore"):
        return np.nan_to_num(x - origin)


def computed_norms(c, p):
    """Row norms, as the function computes them."""
    with np.errstate(over="ignore", under="ignore"):
        return np.nan_to_num(np.linalg.norm(c, ord=p, axis=1))


def exact_norm_cmp(row, origin, bound, p) -> int:
    """Compares the exact L``p`` norm of ``row - origin`` with ``bound``."""
    diff = [Fraction(float(v)) - Fraction(float(o)) for v, o in zip(row, origin)]
    return exact_lp_norm_cmp(diff, bound, p)


def eps(dtype) -> Fraction:
    return Fraction(float(np.finfo(dtype).eps))


def membership_issues(cfg: Config) -> set[str]:
    """The known issues that can put this configuration's output outside the output domain."""
    issues = set()
    if cfg.T == "f32":
        issues.add("f32-domain")
    if cfg.T == "i64":
        issues.add("integer-data")
    if cfg.origin_kind in {"moderate", "1e3", "1e15", "f32 array"}:
        issues.add("nonzero-origin")
    if cfg.origin_kind == "length 1":
        issues.add("length-one-origin")
    if cfg.norm == math.inf:
        issues.add("infinite-norm")
    if cfg.p == 2 and cfg.norm > 1e154:
        issues.add("l2-membership-overflow")
    return issues & KNOWN_ISSUES.keys()


def hang_allowed(cfg: Config, out_dtype) -> bool:
    """Whether clamping may hang: only with tiny norms, while that issue is known."""
    return (
        "subnormal-hang" in KNOWN_ISSUES
        and cfg.norm < float(np.finfo(out_dtype).smallest_normal) * 2.0**30
    )


# ---------------------------------------------------------------------------------------------
# Properties
# ---------------------------------------------------------------------------------------------


@given(configs(), st.data())
def test_np_clamp_properties(cfg: Config, data):
    # data, occasionally large
    if data.draw(st.integers(0, 30)) == 0 and cfg.T != "i64":
        rng = np.random.default_rng(data.draw(st.integers(0, 2**32 - 1)))
        n = data.draw(st.integers(10_000, 100_000))
        scales = 10.0 ** rng.integers(-3, 4, size=(n, 1))
        x = (rng.normal(size=(n, cfg.cols)) * scales).astype(cfg.dtype)
        for special in [np.nan, np.inf]:
            x[rng.integers(0, n, size=10), rng.integers(0, cfg.cols, size=10)] = special
        cfg.rows = n
        event("large dataset")
    else:
        x = arrays(data.draw, cfg, cfg.rows)

    input_domain = cfg.input_domain()
    event(f"T={cfg.T} p={cfg.p!r} origin={cfg.origin_kind}")

    # A: construction succeeds exactly when the parameters are valid, and fails with ValueError
    if not accepts(cfg):
        event("rejected")
        with pytest.raises(ValueError):
            make_np_clamp(input_domain, SYM, cfg.norm, cfg.p, cfg.origin)
        return
    t = make_np_clamp(input_domain, SYM, cfg.norm, cfg.p, cfg.origin)

    # A: the output space replaces the norm, p, origin and nan, and keeps everything else
    din, dout = input_domain.descriptor, t.output_domain.descriptor
    assert t.input_domain == input_domain
    assert t.input_metric == SYM and t.output_metric == SYM
    assert (dout.norm, dout.p, dout.nan) == (float(cfg.norm), cfg.p, False)
    assert (dout.size, dout.T) == (din.size, din.T)
    # (the output's cardinalities aren't checked: see the "cardinalities" known issue)
    expected_cols = din.num_columns
    if isinstance(cfg.origin, np.ndarray) and cfg.origin.ndim == 1:
        expected_cols = cfg.origin.size
    assert dout.num_columns == expected_cols
    expected_origin = (
        np.zeros(()) if cfg.origin is None else np.asarray(cfg.origin, float)
    )
    if expected_origin.ndim == 0 and expected_cols is not None:
        expected_origin = np.zeros(expected_cols)
    assert np.array_equal(dout.origin, expected_origin)
    for d in [0, 1, 2**31, data.draw(st.integers(0, 2**32 - 1))]:
        assert t.map(d) == d

    def clamp(x):
        before = array_key(x)
        out_dtype = np.result_type(x, cfg.origin_array())
        try:
            with warnings.catch_warnings(record=True) as caught, time_limit(10):
                warnings.simplefilter("always")
                out = t(x)
        except TimeoutError:
            # D: only tiny norms may hang
            assert hang_allowed(cfg, out_dtype), "clamping hung"
            event("hang (tiny norm)")
            return None
        # only a norm that doesn't fit the data's type may warn, while that issue is known
        info = np.finfo(out_dtype)
        unfit = not float(info.smallest_subnormal) / 2 < cfg.norm <= float(info.max)
        for w in caught:
            assert unfit and "unfit-norm-warns" in KNOWN_ISSUES, (
                f"unexpected warning: {w.message}"
            )
            event(f"warning: {w.message}")
        # B: same shape, and the input isn't mutated
        assert array_key(x) == before, "the input array was mutated"
        assert out.shape == x.shape
        # B: NaN is gone
        assert not np.isnan(out).any()
        return out

    out = clamp(x)
    if out is None:
        return

    origin = cfg.origin_array()
    c = centered(x, origin)
    c_norms = computed_norms(c, cfg.p)
    with np.errstate(over="ignore"):  # the norm may not fit the data's type
        inside = c_norms <= cfg.norm
    event(
        f"rows inside: {'all' if inside.all() else 'none' if not inside.any() else 'some'}"
    )

    # B: rows already inside the bound are only shifted to the origin and back, bit for bit
    with np.errstate(over="ignore"):
        expected_inside = (c + origin)[inside]
    assert array_key(out[inside]) == array_key(expected_inside.astype(out.dtype))

    sample = (
        range(len(x)) if len(x) <= 40 else np.random.default_rng(0).choice(len(x), 20)
    )

    # B: with a zero origin, a scaled row is a shrunken positive multiple of the centered row
    if cfg.origin_kind in {"none", "zero scalar", "zeros"}:
        tol = 64 * float(np.finfo(out.dtype).eps)
        for i in (i for i in sample if not inside[i]):
            ci, oi = c[i].astype(out.dtype), out[i]
            assert np.all(np.abs(oi) <= np.abs(ci)), f"row {i} grew"
            assert np.all((oi == 0) | (np.sign(oi) == np.sign(ci))), (
                f"row {i} changed sign"
            )
            normal = (np.abs(oi) >= np.finfo(out.dtype).smallest_normal) & (ci != 0)
            ratios = [
                Fraction(float(o)) / Fraction(float(v))
                for o, v in zip(oi[normal], ci[normal])
            ]
            if ratios:
                assert max(ratios) <= min(ratios) * Fraction(1 + tol), (
                    f"row {i} changed direction"
                )

    # B: each row is clamped on its own, and the order of rows doesn't matter
    for i in sample:
        assert array_row_key(clamp(x[i : i + 1])[0]) == array_row_key(out[i]), (
            f"row {i} isn't row-local"
        )
    perm = np.random.default_rng(data.draw(st.integers(0, 2**32 - 1))).permutation(
        len(x)
    )
    assert array_key(clamp(x[perm])) == array_key(out[perm])

    # C: the output is in the output domain, except where a known issue applies
    if not membership_issues(cfg):
        reason = member_reason(t.output_domain, out)
        assert reason is None, reason

    # C: the exact norm about the origin is at most the bound. While the rounding issues are
    # known, it may exceed the bound by rounding: relative error from the norm computation,
    # plus the rounding of adding the origin back; and extreme norms are skipped
    small = cfg.norm < (1e-150 if out.dtype == np.float64 else 1e-15)
    huge = cfg.norm >= float(np.finfo(out.dtype).max) / 2
    if (small and "underflow" in KNOWN_ISSUES) or (
        huge and "overflow-saturated" in KNOWN_ISSUES
    ):
        event("C skipped: extreme norm")
    elif cfg.norm < math.inf:
        o = np.broadcast_to(np.asarray(origin, dtype=out.dtype), (cfg.cols,))
        bound = Fraction(cfg.norm)
        if {"exact-norm", "nonzero-origin"} & KNOWN_ISSUES.keys():
            # adding the origin back moves each coordinate by at most one spacing of floats
            shift = np.spacing(out.dtype.type(np.abs(o).max() + cfg.norm))
            bound *= 1 + 4 * (cfg.cols + 2) * eps(out.dtype)
            bound += Fraction(float(shift)) * cfg.cols
        for i in sample:
            assert exact_norm_cmp(out[i], o, bound, cfg.p) <= 0, (
                f"row {i} is beyond the bound"
            )

    # C: neighbors (rows inserted, deleted and permuted) are no further apart after clamping
    k = data.draw(st.integers(0, 4))
    other = list(x[perm])
    for _ in range(k):
        if other and data.draw(st.booleans()):
            other.pop(data.draw(st.integers(0, len(other) - 1)))
        else:
            other.insert(
                data.draw(st.integers(0, len(other))), arrays(data.draw, cfg, 1)[0]
            )
    other = np.array(other, dtype=x.dtype).reshape(-1, cfg.cols)
    if (cfg.sized and len(other) != len(x)) or len(other) == 0:
        return
    out_other = clamp(other)
    if out_other is None:
        return
    d_in = symmetric_distance(x, other, key=array_row_key)
    d_out = symmetric_distance(out, out_other, key=array_row_key)
    assert d_out <= t.map(d_in)


# ---------------------------------------------------------------------------------------------
# E. Large datasets, wide rows, extreme values and huge sizes
# ---------------------------------------------------------------------------------------------


def f64_clamp(norm, p, origin=None, **domain):
    return make_np_clamp(
        dp.numpy.array2_domain(T=float, **domain), SYM, norm, p, origin
    )


@pytest.mark.parametrize("p", [1, 2])
def test_np_clamp_large_dataset(p):
    # E: a million rows clamp within the bound, row by row, in reasonable time
    import time

    rng = np.random.default_rng(p)
    x = rng.normal(size=(1_000_000, 5)) * 10
    t = f64_clamp(1.0, p)
    start = time.monotonic()
    out = t(x)
    assert time.monotonic() - start < 60
    assert computed_norms(out, p).max() <= 1.0
    assert t.output_domain.member(out)
    for i in rng.choice(len(x), 50):
        assert array_key(t(x[i : i + 1])[0]) == array_key(out[i])


@pytest.mark.parametrize("p", [1, 2])
def test_np_clamp_wide_rows(p):
    # E: rows with 10^5 columns, whose squares overflow under L2, still clamp within the bound
    rng = np.random.default_rng(p)
    x = rng.normal(size=(3, 100_000)) * 1e160
    t = f64_clamp(1.0, p)
    with time_limit(60):
        out = t(x)
    assert t.output_domain.member(out)
    for row in out:
        assert exact_lp_norm_cmp(row, 1.0 * (1 + 1e-12), p) <= 0


@pytest.mark.parametrize("p", [1, 2])
@pytest.mark.parametrize(
    "value", [np.inf, -np.inf, np.finfo(np.float64).max, -np.finfo(np.float64).max]
)
def test_np_clamp_extreme_rows(p, value):
    # E: rows of ±inf or ±MAX in every column clamp within the bound, without hanging
    x = np.full((2, 6), value)
    t = f64_clamp(1.0, p)
    with time_limit(10):
        out = t(x)
    assert t.output_domain.member(out)
    for row in out:
        assert exact_lp_norm_cmp(row, 1.0 * (1 + 1e-12), p) <= 0
        assert np.all(np.sign(row) == np.sign(value))


@pytest.mark.parametrize("size", [2**31, 2**62, 10**20])
def test_np_clamp_huge_sizes(size):
    # E: a huge declared size is kept in the output domain
    t = f64_clamp(1.0, 2, size=size)
    assert t.output_domain.descriptor.size == size
    assert t.map(3) == 3


# ---------------------------------------------------------------------------------------------
# Known issues
# ---------------------------------------------------------------------------------------------


def exact_violations(out, norm, p, origin=0.0) -> list[int]:
    """The rows whose exact L``p`` norm about ``origin`` is above ``norm``."""
    o = np.broadcast_to(np.asarray(origin, dtype=np.float64), (out.shape[1],))
    return [i for i, row in enumerate(out) if exact_norm_cmp(row, o, norm, p) > 0]


def issue(key: str, raises=AssertionError):
    return known_issue(KNOWN_ISSUES, key, raises)


@issue("exact-norm")
@pytest.mark.parametrize("p", [1, 2])
def test_np_clamp_rows_within_exact_bound(p):
    # C: clamped rows are within the bound in exact arithmetic, as the domain declares.
    # Known issue: the loop stops once the *rounded* norm is at most the bound,
    # so many rows end up just above it (by rounding only)
    t = f64_clamp(1.0, p)
    out = t(np.random.default_rng(0).normal(size=(1_000, 5)) * 10)
    assert member_reason(t.output_domain, out) is None
    assert not exact_violations(out, 1.0, p)


@issue("nonzero-origin")
def test_np_clamp_nonzero_origin_in_domain():
    # C: with a nonzero origin, rows are in the output domain, and within the bound.
    # Known issue: adding the origin back after clamping doesn't round-trip, so rows land
    # outside the bound, by up to the spacing of floats near the origin: more than 1% near 1e15
    rng = np.random.default_rng(1)
    origin = rng.normal(size=5) * 1e3
    t = f64_clamp(1.0, 2, origin)
    out = t(rng.normal(size=(1_000, 5)) * 1e3 + origin)
    assert member_reason(t.output_domain, out) is None
    origin = np.full(5, 1e15)
    t = f64_clamp(1.0, 2, origin)
    out = t(rng.normal(size=(1_000, 5)) * 10 + origin)
    assert not exact_violations(out, 1.0, 2, origin)


@issue("f32-domain")
def test_np_clamp_f32_in_domain():
    # C: clamped f32 data is in the output domain.
    # Known issue: the output domain's origin is a float64 array, so membership measures
    # f32 rows in float64, where a row clamped to norm 1 in f32 is over 1
    t = make_np_clamp(dp.numpy.array2_domain(T=dp.f32), SYM, 1.0, 2)
    out = t(np.array([[3.0, 4.0]], dtype=np.float32))
    assert member_reason(t.output_domain, out) is None


@issue("f32-domain")
def test_np_clamp_f32_keeps_type():
    # C: with a float64 origin array, f32 data stays f32, as the domain declares.
    # Known issue: the float64 origin turns f32 data into f64, which isn't of type T
    t = make_np_clamp(dp.numpy.array2_domain(T=dp.f32), SYM, 1.0, 2, np.zeros(2))
    out = t(np.array([[3.0, 4.0]], dtype=np.float32))
    assert member_reason(t.output_domain, out) is None


@issue("integer-data")
def test_np_clamp_integer_data_in_domain():
    # C: integer data is rejected, or its output is in the output domain.
    # Known issue: it's accepted, but the output is float64 while the domain declares T=i64
    try:
        t = make_np_clamp(dp.numpy.array2_domain(T=dp.i64), SYM, 1.0, 2)
    except ValueError:
        return
    out = t(np.array([[3, 4]], dtype=np.int64))
    assert member_reason(t.output_domain, out) is None


@issue("underflow")
def test_np_clamp_tiny_bound():
    # C: a row far outside a tiny bound is clamped.
    # Known issue: L2 norms are computed as sqrt(sum(x**2)), and the squares underflow to zero,
    # so the row isn't clamped, and the output domain accepts it
    t = f64_clamp(1e-300, 2)
    out = t(np.array([[1e-200, 1e-200]]))
    assert not exact_violations(out, 1e-300 * (1 + 1e-9), 2)


@issue("subnormal-hang")
def test_np_clamp_subnormal_norm_terminates():
    # D: clamping terminates with a subnormal norm.
    # Known issue: dividing by a factor near 1 can round back to the same value,
    # so the loop never ends
    t = f64_clamp(3 * 5e-324, 1)
    try:
        with time_limit(5):
            t(np.array([[1e-323, 1e-323]]))
    except TimeoutError:
        raise AssertionError("clamping didn't finish in 5 seconds") from None


@issue("overflow-saturated")
def test_np_clamp_bound_near_max():
    # C: with a bound near MAX, a row whose exact norm is far above it is clamped.
    # Known issue: a norm that overflows is replaced with MAX, so the row is left unchanged
    # (its exact L1 norm is 4·MAX)
    max_ = np.finfo(np.float64).max
    t = f64_clamp(max_, 1)
    out = t(np.full((1, 4), max_))
    assert not exact_violations(
        out, Fraction(float(max_)) * (1 + Fraction(1, 2**40)), 1
    )


@issue("cardinalities")
def test_np_clamp_cardinalities():
    # C: with declared cardinalities, the output is in the output domain.
    # Known issue: the output domain keeps the input's cardinalities,
    # but scaling rows creates new values
    t = make_np_clamp(
        dp.numpy.array2_domain(T=float, cardinalities=[1, 2]), SYM, 1.0, 2
    )
    x = np.array([[1.0, 0.0], [1.0, 5.0]])
    assert member_reason(t.input_domain, x) is None
    assert member_reason(t.output_domain, t(x)) is None


@issue("length-one-origin")
def test_np_clamp_length_one_origin():
    # C: an origin of length 1 over wider data is rejected, or the output is in the output domain.
    # Known issue: it broadcasts, but the output domain then declares a single column
    try:
        t = f64_clamp(1.0, 2, np.array([1.0]))
    except ValueError:
        return
    out = t(np.array([[3.0, 4.0, 5.0]]))
    assert member_reason(t.output_domain, out) is None


@issue("unfit-norm-warns")
@pytest.mark.parametrize(
    "norm", [5e-324, 1e300], ids=["rounds to zero", "above f32 MAX"]
)
def test_np_clamp_unfit_norm_doesnt_warn(norm):
    # A: a norm that doesn't fit the data's type is rejected, or clamps without warnings
    # (which this project's configuration turns into errors).
    # Known issue: one that rounds to zero divides by zero, and one above the type's MAX
    # overflows a cast. The function suppresses some overflow and underflow warnings,
    # but not these. The results themselves are within the bound.
    x = np.array([[1.0]], dtype=np.float32)
    try:
        t = make_np_clamp(dp.numpy.array2_domain(T=dp.f32), SYM, norm, 1)
    except ValueError:
        return
    with warnings.catch_warnings(record=True) as caught:
        warnings.simplefilter("always")
        t(x)
    assert not caught, [str(w.message) for w in caught]


@issue("l2-membership-overflow")
def test_np_clamp_l2_membership_huge_norm():
    # C: array2_domain accepts rows well within a huge declared L2 norm.
    # Known issue: it checks L2 norms as sqrt(sum(x**2)), and the squares overflow,
    # so with a declared norm above about 1.3e154, such rows are rejected
    # (and, under warnings-as-errors, the check raises)
    domain = dp.numpy.array2_domain(T=float, norm=1e300, p=2)
    with warnings.catch_warnings():
        warnings.simplefilter("ignore", RuntimeWarning)
        assert member_reason(domain, np.array([[1e150, 0.0]])) is None
        assert member_reason(domain, np.array([[1e200, 0.0]])) is None


@issue("empty-data")
def test_np_clamp_empty_data():
    # B: clamping an empty dataset returns it. It's a member of the input domain,
    # and its neighbors are single rows.
    # Known issue: it raises, since the loop takes the max of no row norms
    t = f64_clamp(1.0, 2)
    x = np.empty((0, 3))
    assert member_reason(t.input_domain, x) is None
    try:
        out = t(x)
    except Exception as e:
        raise AssertionError(f"clamping empty data raised {e!r}") from e
    assert out.shape == (0, 3)


@issue("infinite-norm", raises=pytest.fail.Exception)
def test_np_clamp_rejects_infinite_norm():
    # A: an infinite norm is rejected.
    # Known issue: it's accepted, so nothing is clamped and the declared bound is infinite
    with pytest.raises(ValueError):
        f64_clamp(math.inf, 2)


@issue("p-true", raises=pytest.fail.Exception)
def test_np_clamp_rejects_p_true():
    # A: p=True is rejected, like any p other than 1 or 2.
    # Known issue: it's accepted as p=1
    with pytest.raises(ValueError):
        f64_clamp(1.0, True)


def test_np_clamp_rejects_unusual_origins():
    # A: a nonzero scalar or a list origin is rejected (by array2_domain)
    with pytest.raises(ValueError, match="scalar origin must be zero"):
        f64_clamp(1.0, 2, 5.0)
    with pytest.raises(ValueError, match="origin must be a scalar, ndarray or None"):
        f64_clamp(1.0, 2, [1.0, 2.0])


# ---------------------------------------------------------------------------------------------
# Regression cases
# ---------------------------------------------------------------------------------------------


def test_np_clamp_nan_and_inf():
    t = f64_clamp(1.0, 2)
    out = t(np.array([[np.nan, 0.0], [np.inf, 0.0], [-np.inf, np.nan], [0.5, -0.0]]))
    # NaN becomes the origin, inf is clamped like MAX, and -0.0 becomes 0.0 (-0.0 - 0.0 + 0.0)
    expected = np.array([[0.0, 0.0], [1.0, 0.0], [-1.0, 0.0], [0.5, 0.0]])
    assert array_key(out) == array_key(expected)


def test_np_clamp_invalid_parameters():
    for norm, p, origin in [
        (0.0, 2, None),
        (-1.0, 2, None),
        (math.nan, 2, None),
        (1.0, 3, None),
        (1.0, None, None),
        (1.0, 2, np.array([np.inf, 0.0])),
    ]:
        with pytest.raises(ValueError):
            f64_clamp(norm, p, origin)


def test_edge_floats_cover_extremes():
    # the shared generator produces the values that matter here
    seen = set()

    @given(edge_floats(np.float64))
    def collect(v):
        seen.add(
            "nan"
            if np.isnan(v)
            else "inf"
            if np.isinf(v)
            else "subnormal"
            if 0 < abs(v) < 2.2e-308
            else "other"
        )

    collect()
    assert {"nan", "inf", "other"} <= seen
