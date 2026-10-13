"""Shared helpers for property-based tests of Polars plans in OpenDP.

Test suites (for example ``test_polars_filter_props.py``) build their strategies
and checks out of these pieces:

* a fixed schema, its OpenDP domain, and a strategy for frames over it
* a strategy for predicate expressions, labeled with whether OpenDP should accept them
* neighboring frames, with exact symmetric distances between row multisets
* zero-noise private releases, for comparison against plain Polars

Rows are compared exactly: floats by their bits (so ``-0.0`` and ``0.0`` differ),
and nulls distinctly from every value.
"""

from __future__ import annotations

import math
import os
import struct
from collections import Counter
from dataclasses import dataclass
from typing import Any, Sequence

import pytest

pl = pytest.importorskip("polars")

from hypothesis import HealthCheck, settings  # noqa: E402
from hypothesis import strategies as st  # noqa: E402

import opendp.prelude as dp  # noqa: E402

dp.enable_features("contrib")

for _name, _examples in [("opendp", 100), ("stress", 2000)]:
    settings.register_profile(
        _name,
        deadline=None,  # FFI calls and Polars collection have unpredictable latency
        max_examples=_examples,
        suppress_health_check=[HealthCheck.too_slow, HealthCheck.data_too_large],
    )
settings.load_profile(os.environ.get("HYPOTHESIS_PROFILE", "opendp"))


# ---------------------------------------------------------------------------------------------
# Frames
# ---------------------------------------------------------------------------------------------

SCHEMA = {
    "i": pl.Int64,  # nullable, small values so that comparisons go both ways
    "f": pl.Float64,  # nullable, never NaN, may be infinite or signed zero
    "s": pl.String,  # nullable, few categories
    "k": pl.Int64,  # non-null grouping key
    "flag": pl.Boolean,  # nullable
}

Row = tuple


def frame_domain(margins: Sequence[Any] = ()):
    """The OpenDP domain of frames over :data:`SCHEMA`, with the given margins."""
    domain = dp.lazyframe_domain(
        [
            dp.series_domain("i", dp.option_domain(dp.atom_domain(T="i64"))),
            dp.series_domain("f", dp.option_domain(dp.atom_domain(T="f64", nan=False))),
            dp.series_domain("s", dp.option_domain(dp.atom_domain(T="String"))),
            dp.series_domain("k", dp.atom_domain(T="i64")),
            dp.series_domain("flag", dp.option_domain(dp.atom_domain(T=bool))),
        ]
    )
    for margin in margins:
        domain = dp.with_margin(domain, margin)
    return domain


def rows() -> st.SearchStrategy[Row]:
    """Single rows over :data:`SCHEMA`, biased towards edge values."""
    floats = st.one_of(
        st.sampled_from([0.0, -0.0, 1.0, -1.0, math.inf, -math.inf]),
        st.floats(-10, 10, allow_nan=False),
    )
    return st.tuples(
        st.none() | st.integers(-5, 5),
        st.none() | floats,
        st.none() | st.sampled_from(["a", "b", "c"]),
        st.integers(0, 2),
        st.none() | st.booleans(),
    )


def datasets(max_size: int = 30) -> st.SearchStrategy[list[Row]]:
    """Lists of rows, including the empty list."""
    return st.lists(rows(), max_size=max_size)


def to_lazyframe(data: Sequence[Row]):
    return pl.DataFrame(list(data), schema=SCHEMA, orient="row").lazy()


@st.composite
def neighbors(draw, data: list[Row], max_distance: int = 4) -> tuple[list[Row], int]:
    """A dataset formed by deleting and inserting rows of ``data``,
    and its exact symmetric distance from ``data``."""
    other = list(data)
    for _ in range(draw(st.integers(0, max_distance))):
        if other and draw(st.booleans()):
            other.pop(draw(st.integers(0, len(other) - 1)))
        else:
            other.insert(draw(st.integers(0, len(other))), draw(rows()))
    return other, symmetric_distance(data, other)


# ---------------------------------------------------------------------------------------------
# Exact comparison of rows
# ---------------------------------------------------------------------------------------------


def value_key(v: Any) -> tuple:
    """An exact identity for a value: floats by bits, and types kept distinct."""
    if v is None:
        return ("null",)
    if isinstance(v, float):
        return ("float", struct.pack(">d", v))
    return (type(v).__name__, v)


def row_multiset(rows_: Sequence[Row]) -> Counter:
    return Counter(tuple(value_key(v) for v in row) for row in rows_)


def frame_rows(frame) -> list[Row]:
    """The rows of a DataFrame or LazyFrame, in the column order of :data:`SCHEMA` where present."""
    df = frame.collect() if isinstance(frame, pl.LazyFrame) else frame
    return df.rows()


def symmetric_distance(a: Sequence[Row], b: Sequence[Row]) -> int:
    """The exact symmetric distance between two datasets, viewed as multisets of rows."""
    ma, mb = row_multiset(a), row_multiset(b)
    return sum(((ma - mb) + (mb - ma)).values())


# ---------------------------------------------------------------------------------------------
# Predicates
# ---------------------------------------------------------------------------------------------

#: OpenDP should accept the predicate.
OK = "ok"
#: The predicate is row-wise, but uses an operation OpenDP doesn't support.
UNSUPPORTED = "unsupported"
#: The predicate doesn't evaluate to a boolean.
NON_BOOLEAN = "non_boolean"
#: Whether a row is kept depends on other rows.
NON_ROW_WISE = "non_row_wise"

#: More severe kinds take precedence when predicates are combined.
_SEVERITY = [OK, UNSUPPORTED, NON_ROW_WISE]


@dataclass(frozen=True)
class Pred:
    """A predicate expression, labeled with how OpenDP should treat it."""

    expr: Any
    kind: str

    @property
    def accepted(self) -> bool:
        return self.kind == OK

    def __repr__(self) -> str:
        return f"Pred({self.expr}, {self.kind})"


def _combine(a: Pred, b: Pred, op) -> Pred:
    kind = max(a.kind, b.kind, key=_SEVERITY.index)
    return Pred(op(a.expr, b.expr), kind)


def _numeric_operands() -> st.SearchStrategy:
    col_i, col_f, col_k = pl.col("i"), pl.col("f"), pl.col("k")
    lits = st.integers(-5, 5).map(pl.lit)
    return st.one_of(
        st.sampled_from([col_i, col_f, col_k]),
        lits.map(lambda v: col_i + v),
        lits.map(lambda v: col_i * v),
        lits.map(lambda v: col_i // v),  # floor division by zero is null
        lits.map(lambda v: col_i % v),
        lits.map(lambda v: col_f / v),  # true division by zero is infinite or NaN
        st.just(col_i.fill_null(0)),
        st.just(col_i.cast(pl.Float64)),
    )


def _comparisons() -> st.SearchStrategy[Pred]:
    ops = st.sampled_from(
        [
            lambda a, b: a == b,
            lambda a, b: a != b,
            lambda a, b: a < b,
            lambda a, b: a <= b,
            lambda a, b: a > b,
            lambda a, b: a >= b,
            lambda a, b: a.eq_missing(b),
            lambda a, b: a.ne_missing(b),
        ]
    )
    rhs = st.one_of(
        st.integers(-5, 5).map(pl.lit),
        st.sampled_from([pl.lit(0.5), pl.lit(-0.0), pl.lit(math.inf)]),
        _numeric_operands(),
    )
    numeric = st.builds(
        lambda op, a, b: Pred(op(a, b), OK), ops, _numeric_operands(), rhs
    )
    string = st.builds(
        lambda op, v: Pred(op(pl.col("s"), pl.lit(v)), OK),
        ops,
        st.sampled_from(["a", "b", "z"]),
    )
    return numeric | string


def _atoms(accepted_only: bool = False) -> st.SearchStrategy[Pred]:
    any_col = st.sampled_from([pl.col(c) for c in SCHEMA])
    col_f = pl.col("f")
    ok = st.one_of(
        _comparisons(),
        any_col.map(lambda c: Pred(c.is_null(), OK)),
        any_col.map(lambda c: Pred(c.is_not_null(), OK)),
        st.sampled_from(
            [
                Pred(col_f.is_nan(), OK),
                Pred(col_f.is_not_nan(), OK),
                Pred(col_f.is_finite(), OK),
                Pred(col_f.is_infinite(), OK),
                Pred(pl.col("flag"), OK),
                Pred(pl.lit(True), OK),
                Pred(pl.lit(False), OK),
            ]
        ),
    )
    if accepted_only:
        return ok
    col_i = pl.col("i")
    unsupported = st.sampled_from(
        [
            Pred(col_i.is_between(-1, 2), UNSUPPORTED),
            Pred(pl.col("s").is_in(["a", "b"]), UNSUPPORTED),
            Pred(col_f.abs() > 1, UNSUPPORTED),
            # null literals aren't supported
            Pred(pl.lit(None, dtype=pl.Boolean), UNSUPPORTED),
        ]
    )
    non_row_wise = st.sampled_from(
        [
            Pred(col_i > col_i.mean(), NON_ROW_WISE),
            Pred(col_i.shift(1) > 0, NON_ROW_WISE),
            Pred(col_i.rank() < 3, NON_ROW_WISE),
            Pred(col_i > col_i.min().over("k"), NON_ROW_WISE),
            Pred(pl.len() > 3, NON_ROW_WISE),
            Pred(col_i.is_duplicated(), NON_ROW_WISE),
            Pred(col_i.cum_sum() > 0, NON_ROW_WISE),
            # these compile in an aggregation context, but not row-by-row
            Pred(pl.col("flag").filter(pl.col("k") > 0), NON_ROW_WISE),
            Pred(col_i.count() > 2, NON_ROW_WISE),
            Pred(col_i.len() > 2, NON_ROW_WISE),
            Pred(col_i.fill_null(0).sum() > 0, NON_ROW_WISE),
        ]
    )
    return st.one_of(ok, ok, ok, unsupported, non_row_wise)


def boolean_predicates(accepted_only: bool = False) -> st.SearchStrategy[Pred]:
    """Boolean predicates: atoms combined with ``& | ^ ~``.
    With ``accepted_only``, only predicates OpenDP should accept."""
    return st.recursive(
        _atoms(accepted_only),
        lambda inner: st.one_of(
            inner.map(lambda p: Pred(~p.expr, p.kind)),
            st.builds(lambda a, b: _combine(a, b, lambda x, y: x & y), inner, inner),
            st.builds(lambda a, b: _combine(a, b, lambda x, y: x | y), inner, inner),
            st.builds(lambda a, b: _combine(a, b, lambda x, y: x ^ y), inner, inner),
        ),
        max_leaves=4,
    )


def accepted_predicates() -> st.SearchStrategy[Pred]:
    """Supported, boolean, row-wise predicates, which OpenDP should accept."""
    return boolean_predicates(accepted_only=True)


def predicates() -> st.SearchStrategy[Pred]:
    """Predicates of every kind, mostly boolean, sometimes evaluating to a non-boolean."""
    non_boolean = st.sampled_from(
        [
            Pred(pl.col("i"), NON_BOOLEAN),
            Pred(pl.col("i") + 1, NON_BOOLEAN),
            Pred(pl.col("s"), NON_BOOLEAN),
            Pred(pl.col("f").fill_null(0.0), NON_BOOLEAN),
        ]
    )
    return st.one_of(
        boolean_predicates(), boolean_predicates(), boolean_predicates(), non_boolean
    )


# ---------------------------------------------------------------------------------------------
# OpenDP plumbing
# ---------------------------------------------------------------------------------------------


def zero_noise(domain, plan, measure=None, threshold=None):
    """A private measurement of ``plan`` with no noise, to compare releases against plain Polars."""
    return dp.m.make_private_lazyframe(
        domain,
        dp.symmetric_distance(),
        measure or dp.max_divergence(),
        plan,
        global_scale=0.0,
        threshold=threshold,
    )
