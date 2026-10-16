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
from dataclasses import dataclass
from typing import Any, Sequence

import pytest

pl = pytest.importorskip("polars")

from hypothesis import strategies as st  # noqa: E402

import opendp.prelude as dp  # noqa: E402

# exact row comparison, and the known-issue marker
from test._props_common import (  # noqa: E402, F401
    Row,
    known_issue,
    row_key,
    row_multiset,
    symmetric_distance,
    value_key,
)

dp.enable_features("contrib")


# ---------------------------------------------------------------------------------------------
# Frames
# ---------------------------------------------------------------------------------------------

SCHEMA = {
    "i": pl.Int64,  # nullable, small values so that comparisons go both ways
    "f": pl.Float64,  # nullable, never NaN, may be infinite or signed zero
    "s": pl.String,  # nullable, few categories
    "k": pl.Int64,  # non-null grouping key
    "flag": pl.Boolean,  # nullable
    "g": pl.Float64,  # nullable, may be NaN
}


def frame_domain(margins: Sequence[Any] = ()):
    """The OpenDP domain of frames over :data:`SCHEMA`, with the given margins."""
    domain = dp.lazyframe_domain(
        [
            dp.series_domain("i", dp.option_domain(dp.atom_domain(T="i64"))),
            dp.series_domain("f", dp.option_domain(dp.atom_domain(T="f64", nan=False))),
            dp.series_domain("s", dp.option_domain(dp.atom_domain(T="String"))),
            dp.series_domain("k", dp.atom_domain(T="i64")),
            dp.series_domain("flag", dp.option_domain(dp.atom_domain(T=bool))),
            dp.series_domain("g", dp.option_domain(dp.atom_domain(T="f64", nan=True))),
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
        st.none() | floats | st.just(math.nan),
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


def frame_rows(frame) -> list[Row]:
    """The rows of a DataFrame or LazyFrame, in the column order of :data:`SCHEMA` where present."""
    df = frame.collect() if isinstance(frame, pl.LazyFrame) else frame
    return df.rows()


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


# ---------------------------------------------------------------------------------------------
# Shared suite plumbing
# ---------------------------------------------------------------------------------------------


def build(make):
    """Calls ``make``, returning ``None`` if OpenDP rejects it."""
    try:
        return make()
    except dp.OpenDPException:
        return None


def margin_lists():
    """Margins over groupings of the frame, with random descriptors."""
    by = st.sampled_from([(), ("k",), ("s",), ("k", "s")])
    margin = st.builds(
        lambda by, max_length, max_groups, invariant: dp.polars.Margin(
            by=[pl.col(c) for c in by],
            max_length=max_length,
            max_groups=max_groups,
            invariant=invariant,
        ),
        by,
        st.none() | st.integers(1, 50),
        st.none() | st.integers(1, 5),
        st.sampled_from([None, "keys", "lengths"]),
    )
    return st.lists(margin, max_size=3, unique_by=lambda m: tuple(map(str, m.by)))


# ---------------------------------------------------------------------------------------------
# Imputation: expressions to fill, and fill values
# ---------------------------------------------------------------------------------------------

#: The fill is null, or may be.
NULLABLE = "nullable"
#: The filled data is categorical.
CATEGORICAL = "categorical"


@dataclass(frozen=True)
class Target:
    """A row-wise expression whose nulls are filled, named after its column ``name``.

    ``nan`` is whether its values may be NaN, and ``kind`` whether OpenDP should accept filling it.
    """

    expr: Any
    name: str
    nan: bool = False
    kind: str = OK

    def __repr__(self) -> str:
        return f"Target({self.expr})"


@dataclass(frozen=True)
class Fill:
    """A fill value or expression, labeled with how OpenDP should treat it,
    and with whether its values may be NaN."""

    expr: Any
    kind: str = OK
    nan: bool = False
    #: OpenDP wrongly declares this nullable fill non-null, and accepts it (a pinned finding).
    undeclared_nulls: bool = False

    @property
    def accepted(self) -> bool:
        return self.kind == OK

    def __repr__(self) -> str:
        return f"Fill({self.expr}, {self.kind})"


I64_MIN, I64_MAX = -(2**63), 2**63 - 1

_i, _f, _s, _k = pl.col("i"), pl.col("f"), pl.col("s"), pl.col("k")

#: Expressions to fill: every column, and row-wise expressions that add nulls, bounds or NaN.
TARGETS = [
    Target(_i, "i"),
    Target(_f, "f"),
    Target(pl.col("g"), "g", nan=True),
    Target(_s, "s"),
    Target(_k, "k"),
    Target(pl.col("flag"), "flag"),
    Target(_i + 1, "i"),
    # failed casts are null
    Target(_s.cast(pl.Int64, strict=False), "s"),
    # bounded
    Target(_i.clip(0, 4), "i"),
    # division by zero is NaN or infinite
    Target(_f / 0, "f", nan=True),
    Target(_s.cast(pl.Categorical), "s", kind=CATEGORICAL),
]

#: Scalar literals of every type, including edge values and NaN.
LITERAL_FILLS = [
    Fill(v)
    for v in [
        0,
        -1,
        7,
        I64_MIN,
        I64_MAX,
        0.5,
        -0.0,
        math.inf,
        -math.inf,
        1e308,
        "z",
        True,
    ]
] + [
    Fill(math.nan, nan=True),
    Fill(pl.lit(3, dtype=pl.Int32)),
    Fill(pl.lit(2.5, dtype=pl.Float32)),
]

#: Non-null row-wise expressions.
COLUMN_FILLS = [
    Fill(_k),
    Fill(_k + 1),
    Fill(_k.cast(pl.Float64)),
    Fill(_i.fill_null(0)),
    Fill(_f.fill_null(0.0)),
    Fill(pl.col("g").fill_null(0.0), nan=True),
    Fill(_s.fill_null("z")),
    Fill(pl.col("flag").fill_null(False)),
]

#: Fills OpenDP should reject.
REJECTED_FILLS = [Fill(pl.col(c), NULLABLE) for c in ["i", "f", "g", "s", "flag"]] + [
    Fill(pl.lit(None), NULLABLE),
    Fill(pl.lit(None, dtype=pl.Int64), NULLABLE),
    # failed casts are null
    Fill(
        _s.fill_null("z").cast(pl.Int64, strict=False), NULLABLE, undeclared_nulls=True
    ),
    # a series literal doesn't broadcast
    Fill(pl.lit(pl.Series([1, 2])), UNSUPPORTED),
    Fill(_k.sum(), NON_ROW_WISE),
    Fill(_k.mean(), NON_ROW_WISE),
    Fill(pl.len(), NON_ROW_WISE),
    Fill(_k.shift(1), NON_ROW_WISE),
    Fill(_k.filter(_k > 0), NON_ROW_WISE),
    Fill(_k.cum_sum(), NON_ROW_WISE),
]


def fill_targets() -> st.SearchStrategy[Target]:
    """Targets, with the grouping columns of :func:`margin_lists`,
    and the float column declared as not NaN, drawn more often."""
    common = [t for t in TARGETS[:5] if t.name in ("k", "s", "f")]
    return st.sampled_from(TARGETS) | st.sampled_from(common)


def fills(accepted_only: bool = False) -> st.SearchStrategy[Fill]:
    """Fill values and expressions. With ``accepted_only``, only fills OpenDP should accept."""
    # fills that may be NaN are rare in the lists, but matter, so they're drawn more often
    nan = st.sampled_from([f for f in LITERAL_FILLS + COLUMN_FILLS if f.nan])
    ok = st.one_of(st.sampled_from(LITERAL_FILLS), st.sampled_from(COLUMN_FILLS), nan)
    if accepted_only:
        return ok
    return st.one_of(ok, ok, st.sampled_from(REJECTED_FILLS))


#: Fill strategies, which Polars applies with ``fill_null(strategy=...)``. OpenDP rejects them all.
FILL_STRATEGIES = ["forward", "backward", "min", "max", "mean", "zero", "one"]
