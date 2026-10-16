"""Property-based tests for Polars ``fill_null`` in OpenDP.

``expr.fill_null(fill)`` compiles to ``make_expr_fill_null``, wherever it appears in a plan:
in ``with_columns``/``select``, in a predicate, or in an aggregation.
The fill must be a non-null scalar literal or a non-null row-wise expression,
the output column is declared non-null with no bounds, and the stability map is the identity.

Properties (labels match the comments below):

* A: accepted exactly for supported targets and fills; the declared output column
  is non-null and unbounded, with Polars' dtype, and admits NaN if the fill does;
  other columns and margins are unchanged unless a grouping column is filled
* B: the transformation computes exactly what Polars computes, leaves no nulls,
  changes no non-null value, and its output is a member of its domain
* C: the stability map is the identity, and holds empirically on neighbors
* D: private releases after a fill are exact at zero noise and move within the sensitivity
  on neighbors; invariants and noise scales are as without a fill
* E: queries built through the Context API respect the privacy budget and carry no data
* F: large frames and extreme margins

Known issues in the library are listed in ``KNOWN_ISSUES``. Each has minimal tests of the correct
behavior, marked with ``known_issue`` (strict xfail), and the properties skip the cases it
affects while it's listed. When an issue is fixed, its tests pass and fail the run:
remove the issue from ``KNOWN_ISSUES``, with its markers. Two are privacy violations:
a NaN fill, and sums of filtered columns when lengths are public.
"""

from __future__ import annotations

import math
import re
import time
import warnings

import pytest

pl = pytest.importorskip("polars")

from hypothesis import assume, event, given, settings, strategies as st  # noqa: E402

import opendp.prelude as dp  # noqa: E402

from test.polars._props import (  # noqa: E402
    COLUMN_FILLS,
    FILL_STRATEGIES,
    I64_MAX,
    I64_MIN,
    LITERAL_FILLS,
    OK,
    SCHEMA,
    TARGETS,
    Fill,
    Target,
    build,
    datasets,
    fill_targets,
    fills,
    frame_domain,
    frame_rows,
    known_issue,
    margin_lists,
    neighbors,
    row_key,
    row_multiset,
    rows,
    symmetric_distance,
    to_lazyframe,
    value_key,
    zero_noise,
)

Margin = dp.polars.Margin

#: Known issues in the library. See the module docstring.
KNOWN_ISSUES = {
    "nan-fill": "a NaN fill (a literal, or a column that may be NaN) is declared as not NaN, "
    "so one null row can turn a noisy sum into noise around 0: a privacy violation",
    "dtype-coercion": "when Polars coerces the column to the fill's type, "
    "OpenDP still declares the original dtype",
    "nullable-cast": "a cast that can fail is declared non-null, so it's accepted as a fill, "
    "and nulls remain in a column declared non-null",
    "filtered-sum": "with known lengths, a fill after an expression filter (explicit, or "
    "dp.sum's own) forgets the filter, so the sum is under-charged: a privacy violation",
    "filtered-mean": "with known lengths, dp.mean after filter-then-fill is charged "
    "infinite loss",
    "bool-numeric-fill": "a boolean column filled with a number is accepted, "
    "though Polars can't run it",
    "member-frame-margin": "LazyFrameDomain.member fails on every frame when the domain has "
    "a margin with no grouping columns",
}


def issue(key: str, raises=AssertionError):
    return known_issue(KNOWN_ISSUES, key, raises)


#: Queries through the Context API search for a noise scale, which is slow,
#: so they run a fifth as many examples as the active profile.
context_settings = settings(max_examples=max(10, settings().max_examples // 5))

_CARRIERS = {
    "i32": pl.Int32,
    "i64": pl.Int64,
    "f32": pl.Float32,
    "f64": pl.Float64,
    "String": pl.String,
    "bool": pl.Boolean,
}


def _plan(lf, target: Target, fill: Fill):
    return lf.with_columns(target.expr.fill_null(fill.expr).alias(target.name))


def _stable(domain, plan):
    return build(
        lambda: dp.t.make_stable_lazyframe(domain, dp.symmetric_distance(), plan)
    )


def _expr(fill: Fill):
    return fill.expr if isinstance(fill.expr, pl.Expr) else pl.lit(fill.expr)


def _is_literal(fill: Fill) -> bool:
    return not isinstance(fill.expr, pl.Expr) or "col(" not in str(fill.expr)


def _expect_accepted(target: Target, fill: Fill, polars_dtype) -> bool:
    """Whether OpenDP should accept the fill: a supported target and fill, which Polars can plan."""
    return target.kind == OK and fill.accepted and polars_dtype is not None


def _dtype(plan, name: str):
    """The dtype Polars gives column ``name`` of ``plan``, or ``None`` if Polars can't plan it."""
    try:
        return plan.collect_schema()[name]
    except pl.exceptions.PolarsError:
        return None


def _declared(domain, name: str):
    """The declared series domain of ``name``, and the Polars dtype of its carrier."""
    series = domain.get_series_domain(name)
    carrier = re.search(r"T=(\w+)", str(series.element_domain)).group(1)
    return series, _CARRIERS[carrier]


def _has_bounds(element_domain) -> bool:
    # read from the description: the bounds accessor isn't available for every type in
    # debug builds
    return "bounds=" in str(element_domain)


def _member(domain, value) -> bool:
    """Membership, where a carrier type mismatch (which OpenDP warns about) counts as non-member."""
    with warnings.catch_warnings():
        warnings.simplefilter("ignore", UserWarning)
        return domain.member(value)


def _coerced(lf, target: Target, fill: Fill) -> bool:
    """Whether Polars changes the target's dtype to fit the fill."""
    before = _dtype(lf.with_columns(target.expr.alias(target.name)), target.name)
    return _dtype(_plan(lf, target, fill), target.name) != before


def _nan_fill(target: Target, fill: Fill, dtype) -> bool:
    """Whether the fill may add NaN to a column that may not otherwise be NaN."""
    return dtype is not None and dtype.is_float() and fill.nan and not target.nan


# ---------------------------------------------------------------------------------------------
# A. Construction and output space
# ---------------------------------------------------------------------------------------------


@given(target=fill_targets(), fill=fills(), margins=margin_lists())
def test_polars_fill_null_construction(target: Target, fill: Fill, margins):
    event(f"fill kind: {fill.kind}")
    domain = frame_domain(margins)
    lf = to_lazyframe([])
    plan = _plan(lf, target, fill)

    # A: accepted exactly for supported, non-categorical targets and non-null, row-wise fills
    # that Polars can plan
    t = _stable(domain, plan)
    actual = _dtype(plan, target.name)
    if t is not None and fill.undeclared_nulls and "nullable-cast" in KNOWN_ISSUES:
        event("known issue: nullable-cast")
        return
    if t is not None and actual is None and "bool-numeric-fill" in KNOWN_ISSUES:
        event("known issue: bool-numeric-fill")
        return
    expected = _expect_accepted(target, fill, actual)
    assert (t is not None) == expected, (
        f"{target}.fill_null({fill}) should be {'accepted' if expected else 'rejected'}"
    )
    if t is None:
        return

    # A: the output column is declared non-null and unbounded; other columns are unchanged
    series, declared = _declared(t.output_domain, target.name)
    assert not series.nullable
    assert not _has_bounds(series.element_domain)
    for name in SCHEMA:
        if name != target.name:
            assert str(t.output_domain.get_series_domain(name)) == str(
                domain.get_series_domain(name)
            )

    # A: the declared dtype is Polars' dtype
    if _coerced(lf, target, fill) and "dtype-coercion" in KNOWN_ISSUES:
        event("known issue: dtype-coercion")
    else:
        assert declared == actual

        # A: the declared column admits NaN if the target or fill may be NaN
        if actual.is_float() and target.nan:
            assert series.element_domain.nan
        if _nan_fill(target, fill, actual):
            if "nan-fill" in KNOWN_ISSUES:
                event("known issue: nan-fill")
            else:
                assert series.element_domain.nan

    # A: margins are unchanged, except those grouping by the filled column, which can merge
    # groups: they're dropped, and what remains is only what the other margins imply
    def describe(d, by):
        m = d.get_margin(by)
        return (m.invariant, m.max_length, m.max_groups)

    target_col = str(pl.col(target.name))
    kept = [m for m in margins if target_col not in {str(e) for e in m.by}]
    if len(kept) < len(margins):
        event("grouping column filled")
    expected_domain = frame_domain(kept)
    for margin in margins:
        assert describe(t.output_domain, margin.by) == describe(
            expected_domain, margin.by
        ), margin


# ---------------------------------------------------------------------------------------------
# B. Function
# ---------------------------------------------------------------------------------------------


@given(data=datasets(), target=fill_targets(), fill=fills(accepted_only=True))
def test_polars_fill_null_matches_polars(data, target: Target, fill: Fill):
    domain, lf = frame_domain(), to_lazyframe(data)
    plan = _plan(lf, target, fill)
    t = _stable(domain, plan)
    assume(t is not None)

    actual = _dtype(plan, target.name)
    if actual is None:
        # the fill should have been rejected
        assert "bool-numeric-fill" in KNOWN_ISSUES, "accepted a fill Polars can't plan"
        event("known issue: bool-numeric-fill")
        return

    # B: exactly the frame Polars computes, row by row
    out = t(lf)
    assert [row_key(r) for r in frame_rows(out)] == [
        row_key(r) for r in frame_rows(plan)
    ]

    # B: no nulls remain, nulls become the fill, and other values are unchanged
    # (after Polars' coercion to the common type)
    filled = out.collect()[target.name]
    assert filled.null_count() == 0
    reference = lf.select(
        target.expr.cast(actual).alias("target"),
        _expr(fill).cast(actual).alias("fill"),
    ).collect()
    for got, before, value in zip(filled, reference["target"], reference["fill"]):
        assert value_key(got) == value_key(value if before is None else before)
    event(
        "nothing to fill"
        if reference["target"].null_count() == 0
        else "everything filled"
        if reference["target"].null_count() == len(data)
        else "some filled"
    )

    # B: the output is a member of the output domain, except where a known issue applies
    issues = set()
    if _coerced(lf, target, fill):
        issues.add("dtype-coercion")
    if _nan_fill(target, fill, actual) and filled.is_nan().any():
        issues.add("nan-fill")
    if issues & KNOWN_ISSUES.keys():
        for key in sorted(issues & KNOWN_ISSUES.keys()):
            event(f"known issue: {key}")
    else:
        assert _member(t.output_domain, out)


#: Fills that keep an integer column integral.
_INT_FILLS = [
    f
    for f in LITERAL_FILLS + COLUMN_FILLS
    if f.expr is not True
    and _dtype(
        to_lazyframe([]).select(pl.lit(0, dtype=pl.Int64).fill_null(f.expr).alias("x")),
        "x",
    )
    == pl.Int64
]

#: Literal fills that keep an integer column integral. A column fill is rejected
#: after an expression filter, or where its column may be null (as in the Context API).
_INT_LITERAL_FILLS = [f for f in _INT_FILLS if _is_literal(f)]


@given(data=datasets(), fill=st.sampled_from(_INT_FILLS))
def test_polars_fill_null_private_release_matches_polars(data, fill: Fill):
    domain = frame_domain([Margin(by=[], max_length=100)])
    lf = to_lazyframe(data)
    i = pl.col("i").fill_null(fill.expr)

    # B: aggregates of filled columns, released with no noise, equal plain Polars
    plan = lf.select(
        i.dp.sum((-5, 5)).alias("sum"),
        pl.col("s").fill_null("z").dp.count(signed=True).alias("count"),
        i.dp.null_count(signed=True).alias("nulls"),
        pl.col("f").fill_null(0.0).dp.sum((-1.0, 1.0)).alias("fsum"),
    )
    released = zero_noise(domain, plan)(lf).collect().row(0)
    expected = (
        lf.select(
            i.clip(-5, 5).sum().alias("sum"),
            pl.col("s").fill_null("z").count().alias("count"),
            i.null_count().alias("nulls"),
            pl.col("f").fill_null(0.0).clip(-1.0, 1.0).sum().alias("fsum"),
        )
        .collect()
        .row(0)
    )
    assert [int(v) for v in released[:3]] == [int(v) for v in expected[:3]]
    assert released[1] == len(data) and released[2] == 0
    assert released[3] == pytest.approx(expected[3], abs=1e-9)

    # ...and in grouped aggregations over public keys, before and after an expression filter
    keyed = frame_domain([Margin(by=[pl.col("k")], invariant="keys", max_length=50)])
    pred = pl.col("flag").fill_null(False)
    for agg, reference in [
        (i.dp.sum((-5, 5)), i.clip(-5, 5).sum()),
        (i.filter(pred).dp.sum((-5, 5)), i.filter(pred).clip(-5, 5).sum()),
    ] + [
        (
            pl.col("i").filter(pred).fill_null(fill.expr).dp.sum((-5, 5)),
            pl.col("i").filter(pred).fill_null(fill.expr).clip(-5, 5).sum(),
        )
    ] * _is_literal(fill):
        grouped = zero_noise(keyed, lf.group_by("k").agg(agg))(lf).collect()
        assert dict(grouped.rows()) == dict(
            lf.group_by("k").agg(reference).collect().rows()
        )


@given(data=datasets(), fill=fills(accepted_only=True))
def test_polars_fill_null_in_predicates_and_selects(data, fill: Fill):
    domain, lf = frame_domain(), to_lazyframe(data)
    target = pl.col("i").fill_null(fill.expr)

    # B: fills compose with filters and selects, and compute exactly what Polars computes
    for plan in [
        lf.filter(target.cast(pl.Float64, strict=False).fill_null(0.0) > 0),
        lf.select(target.alias("x"), pl.col("k")),
        lf.with_columns(target.alias("x")).filter(pl.col("k") != 1).select("x", "k"),
    ]:
        t = _stable(domain, plan)
        if t is None or _dtype(plan, plan.collect_schema().names()[0]) is None:
            continue
        assert row_multiset(frame_rows(t(lf))) == row_multiset(frame_rows(plan))


# ---------------------------------------------------------------------------------------------
# C. Stability
# ---------------------------------------------------------------------------------------------


@given(
    data=datasets(),
    target=fill_targets(),
    fill=fills(),
    d=st.sampled_from([0, 1, 2, 7]),
    seed=st.data(),
)
def test_polars_fill_null_stability(data, target: Target, fill: Fill, d, seed):
    domain, lf = frame_domain(), to_lazyframe(data)
    plan = _plan(lf, target, fill)
    t = _stable(domain, plan)
    if t is None or _dtype(plan, target.name) is None:
        return

    # C: filling doesn't change the stability map
    t_identity = dp.t.make_stable_lazyframe(domain, dp.symmetric_distance(), lf)
    assert t.map(d) == t_identity.map(d)

    # C: filled neighbors are no further apart than the neighbors themselves
    other, k = seed.draw(neighbors(data))
    event(f"neighbor distance {k}")
    out = frame_rows(t(lf))
    out_other = frame_rows(t(to_lazyframe(other)))
    assert symmetric_distance(out, out_other) <= k
    (bound,) = t.map(k)
    assert bound.per_group == k


# ---------------------------------------------------------------------------------------------
# D. Private queries
# ---------------------------------------------------------------------------------------------

#: Targets and fills for noisy sums: numeric targets that OpenDP doesn't declare as NaN.
_SUM_TARGETS = [
    t for t in TARGETS if t.kind == OK and not t.nan and t.name in ("i", "f", "k", "s")
]
_NUMERIC_FILLS = [
    f
    for f in LITERAL_FILLS + COLUMN_FILLS
    if (
        _dtype(to_lazyframe([]).select(pl.lit(0.0).fill_null(f.expr).alias("x")), "x")
        == pl.Float64
    )
    and f.expr is not True
]


_NAN_FILLS = [f for f in _NUMERIC_FILLS if f.nan]


def _noisy_sum(target: Target, fill: Fill):
    return target.expr.fill_null(fill.expr).clip(-5, 5).sum().dp.noise()


def _null_row():
    return (None, None, None, 0, None, None)


@given(
    data=datasets(),
    target=st.sampled_from(_SUM_TARGETS),
    fill=st.sampled_from(_NUMERIC_FILLS) | st.sampled_from(_NAN_FILLS),
    complete=st.booleans(),
)
def test_polars_fill_null_sum_sensitivity(data, target: Target, fill: Fill, complete):
    domain = frame_domain([Margin(by=[], max_length=100)])
    plan = to_lazyframe([]).select(_noisy_sum(target, fill))
    m = build(lambda: zero_noise(domain, plan))
    if m is None:
        event("query rejected")
        return
    if complete:
        # with no nulls to fill in ``data``, only the added row is filled
        column = list(SCHEMA).index(target.name)
        data = [row for row in data if row[column] is not None]

    # D: adding a row whose target is null moves the sum by at most the clipping bound, 5
    def release(rows):
        return m(to_lazyframe(rows)).collect().item()

    def plain(rows):
        filled = target.expr.fill_null(fill.expr).cast(pl.Float64)
        return to_lazyframe(rows).select(filled.clip(-5, 5).sum()).collect().item()

    neighbor = data + [_null_row()]
    a, b = release(data), release(neighbor)
    if (
        math.isnan(plain(neighbor))
        and not math.isnan(plain(data))
        and "nan-fill" in KNOWN_ISSUES
    ):
        # the filled NaN poisons the sum, which is released as 0, however large it was
        event("known issue: nan-fill")
        return
    event("sensitivity checked")
    assert abs(a - b) <= 5 + 1e-9, f"{a} vs {b}"


@given(fill=fills(accepted_only=True))
def test_polars_fill_null_keeps_invariants(fill: Fill):
    lf = to_lazyframe([])

    # D: filling a non-grouping column keeps the frame length public
    lengths = frame_domain([Margin(by=[], invariant="lengths", max_length=100)])
    plan = _plan(lf, Target(pl.col("i"), "i"), fill).select(dp.len(signed=True))
    assert zero_noise(lengths, plan).map(1) == 0.0

    # ...and keys of a grouping column public, unless the grouping column is filled
    keys = frame_domain([Margin(by=[pl.col("k")], invariant="keys", max_length=50)])

    def private(plan, threshold=None):
        return dp.m.make_private_lazyframe(
            keys,
            dp.symmetric_distance(),
            dp.approximate(dp.max_divergence()) if threshold else dp.max_divergence(),
            plan,
            global_scale=1.0,
            threshold=threshold,
        )

    private(
        _plan(lf, Target(pl.col("i"), "i"), fill).group_by("k").agg(dp.len(signed=True))
    )
    filled_key = _plan(lf, Target(pl.col("k"), "k"), fill)
    if _dtype(filled_key, "k") is None:
        return
    plan = filled_key.group_by("k").agg(dp.len(signed=True))
    with pytest.raises(dp.OpenDPException, match="key-set"):
        private(plan)
    _, delta = private(plan, threshold=10).map(1)
    assert delta > 0.0


#: Filters in a grouped aggregation: on the grouping key, which changing a row within its
#: group can't flip, and on values, which it can.
_KEY_PREDICATES = [pl.col("k") > 0]
_VALUE_PREDICATES = [
    pl.col("i") > 1,
    pl.col("i").is_null(),
    pl.col("f") > 0,
    pl.col("flag").fill_null(False),
]
_PREDICATES = _KEY_PREDICATES + _VALUE_PREDICATES
_SUMMED_PREDICATES = [pl.col("i") > 1, pl.col("i") < 0, pl.col("i").is_null()]

#: Clipping bounds, including some that exclude 0, where a row that's filtered out
#: (and contributes nothing) differs from every row that's kept.
_SUM_BOUNDS = [(-5, 5), (0, 4), (2, 3)]


def _grouped_domain(invariant: str):
    return frame_domain(
        [Margin(by=[pl.col("k")], invariant=invariant, max_length=50, max_groups=3)]
    )


@given(
    fill=st.sampled_from(_INT_LITERAL_FILLS),
    pred=st.sampled_from(_PREDICATES),
    bounds=st.sampled_from(_SUM_BOUNDS),
    invariant=st.sampled_from(["keys", "lengths"]),
)
def test_polars_fill_null_grouped_losses(fill: Fill, pred, bounds, invariant):
    domain = _grouped_domain(invariant)
    lf = to_lazyframe([])
    i = pl.col("i")

    def loss(agg):
        try:
            return dp.m.make_private_lazyframe(
                domain,
                dp.symmetric_distance(),
                dp.max_divergence(),
                lf.group_by("k").agg(agg),
            ).map(2)
        except dp.OpenDPException:
            return math.inf

    # D: filling before or after an expression filter costs the same
    for name, make in [
        ("sum", lambda c: c.clip(*bounds).sum().dp.noise(scale=1.0)),
        ("dp.sum", lambda c: c.dp.sum(bounds, scale=1.0)),
        ("dp.mean", lambda c: c.dp.mean(bounds, scale=1.0)),
    ]:
        unfiltered = loss(make(i.fill_null(fill.expr)))
        fill_then_filter = loss(make(i.fill_null(fill.expr).filter(pred)))
        filter_then_fill = loss(make(i.filter(pred).fill_null(fill.expr)))
        assert unfiltered < math.inf
        # with known lengths, a fill after the filter forgets the filter: the mean is
        # charged infinite loss, and the sum (or dp.sum, which fills itself) too little
        key = "filtered-mean" if name == "dp.mean" else "filtered-sum"
        if invariant == "lengths" and key in KNOWN_ISSUES:
            event(f"known issue: {key}")
            continue
        assert filter_then_fill == fill_then_filter < math.inf


#: Ways to release the sum of a filtered column with noise of a given scale: an explicit
#: fill before or after the filter, then clip, sum and add noise; or dp.sum, which fills
#: nulls itself, after the filter.
_FILTERED_SUMS = {
    "fill, filter, sum": lambda i, fill, pred, b, scale: (
        i.fill_null(fill).filter(pred).clip(*b).sum().dp.noise(scale)
    ),
    "filter, fill, sum": lambda i, fill, pred, b, scale: (
        i.filter(pred).fill_null(fill).clip(*b).sum().dp.noise(scale)
    ),
    "fill, filter, dp.sum": lambda i, fill, pred, b, scale: (
        i.fill_null(fill).filter(pred).dp.sum(b, scale=scale)
    ),
    "filter, dp.sum": lambda i, fill, pred, b, scale: i.filter(pred).dp.sum(
        b, scale=scale
    ),
}
#: Only this way accounts for the filter.
_SOUND_SUMS = {"fill, filter, sum"}


@given(
    data=datasets(),
    fill=st.sampled_from(_INT_LITERAL_FILLS),
    # mostly filters on the summed column, so that changing its value can flip them
    pred=st.sampled_from(_SUMMED_PREDICATES) | st.sampled_from(_PREDICATES),
    # bounds that exclude 0 are where a filtered row differs most from a kept one
    bounds=st.sampled_from([(2, 3), (1, 4)]) | st.sampled_from(_SUM_BOUNDS),
    how=st.sampled_from(list(_FILTERED_SUMS)),
    seed=st.data(),
)
def test_polars_fill_null_filtered_sum_sensitivity(
    data, fill: Fill, pred, bounds, how, seed
):
    assume(data)
    domain = _grouped_domain("lengths")

    # neighbors under known lengths: change one row, keeping its group;
    # often only the summed value, which the filters mostly depend on
    j = seed.draw(st.integers(0, len(data) - 1))
    other = list(data)
    if seed.draw(st.booleans()):
        other[j] = (seed.draw(st.none() | st.integers(-5, 5)),) + data[j][1:]
    else:
        new = seed.draw(rows())
        other[j] = new[:3] + (data[j][3],) + new[4:]

    # D: the sums move by at most the sensitivity, which is the loss at noise scale 1
    def private(scale, **kwargs):
        plan = (
            to_lazyframe([])
            .group_by("k")
            .agg(
                _FILTERED_SUMS[how](pl.col("i"), fill.expr, pred, bounds, scale).alias(
                    "sum"
                )
            )
        )
        return dp.m.make_private_lazyframe(
            domain, dp.symmetric_distance(), dp.max_divergence(), plan, **kwargs
        )

    sensitivity = private(1.0).map(2)
    release = private(None, global_scale=0.0)
    a = dict(release(to_lazyframe(data)).collect().rows())
    b = dict(release(to_lazyframe(other)).collect().rows())
    assert a.keys() == b.keys()
    shift = sum(abs(a[g] - b[g]) for g in a)
    if how not in _SOUND_SUMS and "filtered-sum" in KNOWN_ISSUES:
        # a fill after the filter (explicit, or dp.sum's own) forgets the filter, so the sum
        # is charged as if every row contributed a value within the bounds, though a filtered
        # row contributes nothing
        if shift > sensitivity:
            event(f"known issue: filtered-sum ({how})")
        return
    event("sensitivity checked")
    assert shift <= sensitivity, (
        f"{a} vs {b}: moved by {shift}, sensitivity {sensitivity}"
    )


@context_settings
@given(fill=st.sampled_from(_INT_LITERAL_FILLS), contributions=st.integers(1, 3))
def test_polars_fill_null_noise_scales(fill: Fill, contributions):
    context = dp.Context.compositor(
        data=to_lazyframe([]),
        privacy_unit=dp.unit_of(contributions=contributions),
        privacy_loss=dp.loss_of(epsilon=1.0),
        split_evenly_over=2,
        margins=[Margin(by=(), max_length=100)],
    )

    def scales(query):
        return query.summarize()["scale"].to_list()

    # D: an explicit fill costs the same as dp.sum's own imputation
    explicit = context.query().with_columns(pl.col("i").fill_null(fill.expr))
    assert scales(explicit.select(pl.col("i").dp.sum((-5, 5)))) == scales(
        context.query().select(pl.col("i").dp.sum((-5, 5)))
    )


# ---------------------------------------------------------------------------------------------
# E. Context API
# ---------------------------------------------------------------------------------------------


@context_settings
@given(
    data=datasets(),
    fill=st.sampled_from(_INT_LITERAL_FILLS),
    epsilon=st.floats(0.1, 10.0),
    contributions=st.integers(1, 3),
)
def test_polars_fill_null_context(data, fill: Fill, epsilon, contributions):
    context = dp.Context.compositor(
        data=to_lazyframe(data),
        privacy_unit=dp.unit_of(contributions=contributions),
        privacy_loss=dp.loss_of(epsilon=epsilon),
        split_evenly_over=2,
        margins=[Margin(by=(), max_length=100)],
    )
    filled = context.query().with_columns(pl.col("i").fill_null(fill.expr))

    # E: the plan built by the context never carries the data
    assert object.__getattribute__(filled, "polars_plan").collect().height == 0

    query = filled.select(dp.len(signed=True), pl.col("i").clip(-5, 5).sum().dp.noise())

    # E: the resolved measurement fits within this query's share of the budget,
    # and releasing it spends exactly that share
    assert query.resolve().map(contributions) <= epsilon / 2
    released = query.release().collect()
    assert released.columns == ["len", "i"]
    assert context.remaining_privacy_loss() == [pytest.approx(epsilon / 2)]


# ---------------------------------------------------------------------------------------------
# F. Large sizes and extremes
# ---------------------------------------------------------------------------------------------


def test_polars_fill_null_large_frame():
    n = 100_000
    data = [
        (None if r % 2 else r % 7 - 3, None, None, r % 3, None, None) for r in range(n)
    ]
    lf = to_lazyframe(data)
    domain = frame_domain([Margin(by=[], max_length=n)])
    plan = lf.with_columns(pl.col("i").fill_null(pl.col("k")))

    start = time.monotonic()
    t = dp.t.make_stable_lazyframe(domain, dp.symmetric_distance(), plan)
    out = t(lf).collect()
    assert time.monotonic() - start < 30
    assert out["i"].null_count() == 0
    assert out.equals(plan.collect())
    # while membership fails with a margin with no grouping columns, check it without margins
    if "member-frame-margin" in KNOWN_ISSUES:
        t = dp.t.make_stable_lazyframe(frame_domain(), dp.symmetric_distance(), plan)
    assert _member(t.output_domain, t(lf))

    released = zero_noise(domain, plan.select(pl.col("i").dp.sum((-5, 5))))(lf)
    assert released.collect().item() == plan.select(pl.col("i").sum()).collect().item()


@pytest.mark.parametrize("value", [I64_MIN, I64_MAX, -1, 0])
def test_polars_fill_null_extreme_int_fills(value):
    data = [(None, None, None, 0, None, None), (3, None, None, 0, None, None)]
    lf = to_lazyframe(data)
    domain = frame_domain([Margin(by=[], max_length=100)])
    plan = lf.select(pl.col("i").fill_null(value).dp.sum((-5, 5)))
    released = zero_noise(domain, plan)(lf).collect().item()
    assert released == max(-5, min(5, value)) + 3


@pytest.mark.parametrize("value", [math.inf, -math.inf, 1e308, -0.0])
def test_polars_fill_null_extreme_float_fills(value):
    data = [(None, None, None, 0, None, None), (None, 1.5, None, 0, None, None)]
    lf = to_lazyframe(data)
    domain = frame_domain([Margin(by=[], max_length=100)])
    plan = lf.select(pl.col("f").fill_null(value).dp.sum((-5.0, 5.0)))
    m = dp.m.make_private_lazyframe(
        domain, dp.symmetric_distance(), dp.max_divergence(), plan, global_scale=1.0
    )
    assert math.isfinite(m.map(1))
    assert zero_noise(domain, plan)(lf).collect().item() == pytest.approx(
        max(-5.0, min(5.0, value)) + 1.5
    )


def test_polars_fill_null_huge_max_length():
    domain = frame_domain([Margin(by=[], max_length=2**32 - 1)])
    plan = to_lazyframe([]).select(pl.col("i").fill_null(0).dp.sum((-5, 5)))
    m = dp.m.make_private_lazyframe(
        domain, dp.symmetric_distance(), dp.max_divergence(), plan, global_scale=1.0
    )
    assert math.isfinite(m.map(1))


# ---------------------------------------------------------------------------------------------
# Deterministic cases and pinned findings
# ---------------------------------------------------------------------------------------------


def test_polars_fill_null_rejects_strategies():
    lf = to_lazyframe([])
    for strategy in FILL_STRATEGIES:
        plan = lf.with_columns(pl.col("i").fill_null(strategy=strategy))
        with pytest.raises(dp.OpenDPException):
            dp.t.make_stable_lazyframe(frame_domain(), dp.symmetric_distance(), plan)


def test_polars_fill_null_rejects_invalid_fills():
    lf = to_lazyframe([])
    for fill in [
        pl.col("i"),  # nullable
        pl.lit(None),
        pl.lit(pl.Series([1, 2])),  # doesn't broadcast
        pl.col("k").sum(),
        pl.col("k").filter(pl.col("k") > 0),
    ]:
        with pytest.raises(dp.OpenDPException):
            dp.t.make_stable_lazyframe(
                frame_domain(),
                dp.symmetric_distance(),
                lf.with_columns(pl.col("i").fill_null(fill)),
            )
    with pytest.raises(dp.OpenDPException):
        dp.t.make_stable_lazyframe(
            frame_domain(),
            dp.symmetric_distance(),
            lf.with_columns(pl.col("s").cast(pl.Categorical).fill_null("z")),
        )

    # in an aggregation, a column fill must still be row-by-row, so that it aligns with the data
    keyed = frame_domain([Margin(by=[pl.col("k")], invariant="keys", max_length=50)])
    for agg in [
        pl.col("i").fill_null(pl.col("k").filter(pl.col("k") > 0)),
        pl.col("i").fill_null(pl.col("k").sort()),
    ]:
        with pytest.raises(dp.OpenDPException):
            dp.m.make_private_lazyframe(
                keyed,
                dp.symmetric_distance(),
                dp.max_divergence(),
                lf.group_by("k").agg(agg.dp.sum((-5, 5))),
                global_scale=1.0,
            )


@pytest.mark.parametrize("fill", [-100, 2, pl.col("k")])
def test_polars_fill_null_drops_bounds(fill):
    """Bounds from a clip are dropped by the fill, even when the fill is within them,
    so a sum must be clipped again: otherwise the fill could exceed the bounds."""
    domain = frame_domain([Margin(by=[], max_length=100)])
    lf = to_lazyframe([])
    bounded = pl.col("i").clip(0, 4)
    dp.m.make_private_lazyframe(
        domain,
        dp.symmetric_distance(),
        dp.max_divergence(),
        lf.select(bounded.fill_null(0).clip(0, 4).sum().dp.noise()),
        global_scale=1.0,
    )
    with pytest.raises(dp.OpenDPException, match="bounded"):
        dp.m.make_private_lazyframe(
            domain,
            dp.symmetric_distance(),
            dp.max_divergence(),
            lf.select(bounded.fill_null(fill).sum().dp.noise()),
            global_scale=1.0,
        )


#: A NaN literal, and a column that may be NaN, as fills for ``f`` (declared as not NaN).
_NAN_FILL_CASES = pytest.mark.parametrize(
    "fill, null_row",
    [
        (math.nan, (None, None, None, 0, None, None)),
        (pl.col("g").fill_null(0.0), (None, None, None, 0, None, math.nan)),
    ],
    ids=["NaN literal", "NaN-able column"],
)


@issue("nan-fill")
@_NAN_FILL_CASES
def test_polars_fill_null_declares_nan(fill, null_row):
    """A: a fill that may be NaN makes the declared column admit NaN."""
    t = dp.t.make_stable_lazyframe(
        frame_domain(),
        dp.symmetric_distance(),
        to_lazyframe([]).with_columns(pl.col("f").fill_null(fill)),
    )
    assert t.output_domain.get_series_domain("f").element_domain.nan


@issue("nan-fill")
@_NAN_FILL_CASES
def test_polars_fill_null_nan_sum_sensitivity(fill, null_row):
    """D: a clipped noisy sum after a NaN fill is rejected, or moves by at most the clipping
    bound (5) when one row is added. Known issue: the NaN isn't declared, so the query is
    accepted at ε = 1, and one null row turns the sum into NaN, released as 0: with 99 rows
    of 5.0, the releases are 495 and 0."""
    domain = frame_domain([Margin(by=[], max_length=100)])
    data = [(0, 5.0, "a", 0, True, None)] * 99
    plan = to_lazyframe([]).select(
        pl.col("f").fill_null(fill).clip(-5.0, 5.0).sum().dp.noise()
    )
    release = build(lambda: zero_noise(domain, plan))
    if release is None:
        return
    a = release(to_lazyframe(data)).collect().item()
    b = release(to_lazyframe(data + [null_row])).collect().item()
    assert abs(a - b) <= 5, f"releases {a} and {b}"


@issue("dtype-coercion")
@pytest.mark.parametrize(
    "fill",
    [0.5, "z", pl.col("f").fill_null(0.0)],
    ids=["float", "string", "float column"],
)
def test_polars_fill_null_declares_coerced_dtype(fill):
    """A: when Polars casts the column to the fill's type, the fill is rejected, or the
    declared dtype is Polars' dtype, and the output is a member of the output domain."""
    lf = to_lazyframe([(None, None, None, 0, None, None), (3, 1.5, "a", 1, True, 0.0)])
    plan = lf.with_columns(pl.col("i").fill_null(fill))
    t = _stable(frame_domain(), plan)
    if t is None:
        return
    assert _declared(t.output_domain, "i")[1] == t(lf).collect()["i"].dtype
    assert _member(t.output_domain, t(lf))


@issue("dtype-coercion")
def test_polars_fill_null_coerced_sum_summary():
    """D: a sum over an integer column filled with a float is summarized as float noise,
    which is what it adds. Known issue: it's summarized as Integer Laplace."""
    lf = to_lazyframe([(None, None, None, 0, None, None), (3, 1.5, "a", 1, True, 0.0)])
    context = dp.Context.compositor(
        data=lf,
        privacy_unit=dp.unit_of(contributions=1),
        privacy_loss=dp.loss_of(epsilon=1.0),
        split_evenly_over=1,
        margins=[Margin(by=(), max_length=100)],
    )
    query = context.query().select(pl.col("i").fill_null(0.5).dp.sum((-5, 5)))
    assert query.release().collect()["i"].dtype == pl.Float64
    assert query.summarize()["distribution"].to_list() == ["Float Laplace"]


def _cast_lf():
    return to_lazyframe(
        [(None, None, "a", 0, None, None), (None, None, "7", 1, None, None)]
    )


@issue("nullable-cast")
def test_polars_cast_declares_nullable():
    """A: a cast that can fail is declared nullable, since failures become null.
    Known issue: ``make_expr_cast`` keeps its input's nullability, so casting a non-null
    column is declared non-null, though "a" becomes null."""
    lf = _cast_lf()
    cast = pl.col("s").fill_null("z").cast(pl.Int64)
    t = dp.t.make_stable_lazyframe(
        frame_domain(), dp.symmetric_distance(), lf.with_columns(cast.alias("x"))
    )
    assert t(lf).collect()["x"].to_list() == [None, 7]
    assert t.output_domain.get_series_domain("x").nullable


@issue("nullable-cast")
def test_polars_fill_null_rejects_nullable_cast():
    """A: a fill that can be null, such as a cast that can fail, is rejected.
    Known issue: the cast is declared non-null, so it's accepted, and nulls remain
    in a column declared non-null."""
    cast = pl.col("s").fill_null("z").cast(pl.Int64)
    plan = _cast_lf().with_columns(pl.col("i").fill_null(cast))
    assert _stable(frame_domain(), plan) is None


def _filtered_sum_frames(column):
    """Neighbors with the same group lengths: the first row changes, and passes ``> 1``."""
    index = list(SCHEMA).index(column)

    def frame(values):
        rows_ = []
        for v in values:
            row = [None] * len(SCHEMA)
            row[3], row[index] = 0, v
            rows_.append(tuple(row))
        return to_lazyframe(rows_)

    one, three = (1.0, 3.0) if column == "g" else (1, 3)
    return frame([one, three, three]), frame([three] * 3)


@issue("filtered-sum")
@pytest.mark.parametrize(
    "fill_then_filter, filter_then_fill, column",
    [
        (
            pl.col("i").fill_null(0).filter(pl.col("i") > 1),
            pl.col("i").filter(pl.col("i") > 1).fill_null(0),
            "i",
        ),
        (
            pl.col("g").fill_null(0.0).fill_nan(0.0).filter(pl.col("g") > 1),
            pl.col("g").fill_null(0.0).filter(pl.col("g") > 1).fill_nan(0.0),
            "g",
        ),
    ],
    ids=["fill_null", "fill_nan"],
)
def test_polars_filter_then_fill_sum_sensitivity(
    fill_then_filter, filter_then_fill, column
):
    """D: with known lengths, a sum after filter-then-fill allows for the filter: changing one
    row can switch it from filtered out (contributing nothing) to kept, which moves a sum
    clipped to (2, 3) by 3. Known issue (privacy violation): the fill's output context is its
    input's, so the filter is forgotten, and the sum is calibrated for a sensitivity of 1."""
    domain = _grouped_domain("lengths")
    a, b = _filtered_sum_frames(column)

    def plan(c, scale=None):
        return to_lazyframe([]).group_by("k").agg(c.clip(2, 3).sum().dp.noise(scale))

    def sensitivity(c):
        # the loss at noise scale 1
        return dp.m.make_private_lazyframe(
            domain, dp.symmetric_distance(), dp.max_divergence(), plan(c, 1.0)
        ).map(2)

    for c in [fill_then_filter, filter_then_fill]:
        release = zero_noise(domain, plan(c))
        assert release(a).collect()[column].item() == pytest.approx(6)
        assert release(b).collect()[column].item() == pytest.approx(9)
    assert sensitivity(fill_then_filter) >= 3
    assert sensitivity(filter_then_fill) >= 3


@issue("filtered-sum")
def test_polars_filtered_dp_sum_sensitivity():
    """D: with known lengths, ``x.filter(x > 1).dp.sum((2, 3))`` allows for the filter, in the
    measurement and in the Context API's noise scale: changing one row moves it by 3.
    Known issue (privacy violation): ``dp.sum`` fills nulls (and NaNs) itself before clipping,
    after the filter, so the filter is forgotten even with no fill in the query, on a non-null
    column: the sum is calibrated for a sensitivity of 1."""
    schema = {"x": pl.Int64, "k": pl.Int64}
    margin = Margin(by=[pl.col("k")], invariant="lengths", max_length=50, max_groups=3)
    domain = dp.with_margin(
        dp.lazyframe_domain(
            [
                dp.series_domain("x", dp.atom_domain(T="i64")),
                dp.series_domain("k", dp.atom_domain(T="i64")),
            ]
        ),
        margin,
    )
    a = pl.LazyFrame({"x": [1, 3, 3], "k": [0, 0, 0]}, schema=schema)
    b = pl.LazyFrame({"x": [3, 3, 3], "k": [0, 0, 0]}, schema=schema)
    x = pl.col("x")

    def private(agg, **kwargs):
        return dp.m.make_private_lazyframe(
            domain,
            dp.symmetric_distance(),
            dp.max_divergence(),
            a.group_by("k").agg(agg),
            **kwargs,
        )

    release = private(x.filter(x > 1).dp.sum((2, 3)), global_scale=0.0)
    assert release(a).collect()["x"].item() == 6
    assert release(b).collect()["x"].item() == 9
    # an explicit clip and sum allows for the filter: the loss at noise scale 1 is 6
    assert private(x.filter(x > 1).clip(2, 3).sum().dp.noise(scale=1.0)).map(2) == 6.0
    assert private(x.filter(x > 1).dp.sum((2, 3), scale=1.0)).map(2) >= 3

    context = dp.Context.compositor(
        data=a,
        privacy_unit=dp.unit_of(changes=1),
        privacy_loss=dp.loss_of(epsilon=1.0),
        split_evenly_over=1,
        margins=[Margin(by=["k"], invariant="lengths", max_length=50, max_groups=3)],
    )
    query = context.query().group_by("k").agg(x.filter(x > 1).dp.sum((2, 3)))
    assert query.summarize()["scale"].item() >= 3


@issue("filtered-mean")
def test_polars_filter_then_fill_mean():
    """D: with known lengths, ``dp.mean`` costs the same whether the fill comes before or
    after an expression filter. Known issue: after filter-then-fill, the mean treats the
    length as public, but the length's accounting sees the filter, so the loss is infinite."""
    domain = frame_domain(
        [Margin(by=[pl.col("k")], invariant="lengths", max_length=50)]
    )
    lf = to_lazyframe([])
    pred = pl.col("k") > 0

    def loss(column):
        try:
            return dp.m.make_private_lazyframe(
                domain,
                dp.symmetric_distance(),
                dp.max_divergence(),
                lf.group_by("k").agg(column.dp.mean((-5, 5), scale=1.0)),
            ).map(2)
        except dp.OpenDPException as e:
            assert "not finite" in str(e)
            return math.inf

    fill_then_filter = loss(pl.col("i").fill_null(0).filter(pred))
    assert fill_then_filter == 12.0
    assert loss(pl.col("i").filter(pred).fill_null(0)) == fill_then_filter


@issue("bool-numeric-fill")
def test_polars_fill_null_rejects_bool_numeric_fill():
    """A: filling a boolean column with a number, which Polars can't run, is rejected.
    Known issue: OpenDP accepts the plan, which then fails in Polars on every frame
    (so the failure doesn't depend on the data)."""
    plan = to_lazyframe([]).with_columns(pl.col("flag").fill_null(0))
    assert _stable(frame_domain(), plan) is None


@issue("member-frame-margin")
def test_polars_member_with_frame_margin():
    """A frame within a margin with no grouping columns is a member of the domain.
    Known issue: ``LazyFrameDomain.member`` runs a group-by over the margin's columns,
    which Polars rejects when there are none, and the error is reported as non-membership."""
    domain = frame_domain([Margin(by=[], max_length=100)])
    assert _member(domain, to_lazyframe([(1, 1.0, "a", 0, True, 1.0)]))


def test_polars_fill_null_filled_grouping_column_merges_groups():
    data = [(None, None, None, 0, None, None)] * 3 + [
        (None, None, "a", 0, None, None)
    ] * 2
    lf = to_lazyframe(data)
    domain = frame_domain(
        [Margin(by=[pl.col("s")], invariant="lengths", max_length=2, max_groups=2)]
    )
    t = dp.t.make_stable_lazyframe(
        domain, dp.symmetric_distance(), lf.with_columns(pl.col("s").fill_null("a"))
    )
    # the merged group has 5 rows, more than the old max_length, so the margin can't survive
    assert t(lf).collect()["s"].value_counts().rows() == [("a", 5)]
    margin = t.output_domain.get_margin([pl.col("s")])
    assert margin.max_length is None and margin.invariant is None
