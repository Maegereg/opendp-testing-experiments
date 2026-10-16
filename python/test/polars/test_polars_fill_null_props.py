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

Tests named ``test_finding_*``, and branches marked FINDING, pin issues in the library:

* a NaN fill (a literal, or a column that may be NaN) is declared as not NaN,
  so one null row can turn a noisy sum into noise around 0: a privacy violation
* when Polars coerces the column to the fill's type (int to float or string),
  OpenDP still declares the original dtype
* a fill that is a failing cast is declared non-null, so nulls remain in a "non-null" column
* in a grouped aggregation with known lengths, ``filter(...).fill_null(...)`` (and
  ``fill_nan``) forgets that the filter changed the lengths: a sum is charged as if nothing
  were filtered, so a change to one row can move it beyond its sensitivity, a privacy
  violation. ``dp.sum`` fills nulls itself, so ``filter(...).dp.sum(...)`` is affected
  even without a fill; and ``dp.mean`` is charged infinite loss
* a boolean column filled with a number is accepted, though Polars can't run it
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

from _props import (  # noqa: E402
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


def _expect_accepted(target: Target, fill: Fill) -> bool:
    # FINDING: a fill that is a failing cast is wrongly declared non-null, so it's accepted
    return target.kind == OK and (fill.accepted or fill.undeclared_nulls)


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


def _nan_finding(target: Target, fill: Fill, dtype) -> bool:
    """Whether the fill may add NaN to a column that isn't declared as NaN (FINDING)."""
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

    # A1: accepted exactly for supported, non-categorical targets and non-null, row-wise fills
    t = _stable(domain, plan)
    expected = _expect_accepted(target, fill)
    assert (t is not None) == expected, (
        f"{target}.fill_null({fill}) should be {'accepted' if expected else 'rejected'}"
    )
    if t is None:
        return
    if fill.undeclared_nulls:
        event("FINDING: nullable cast fill accepted")

    # A2: the output column is declared non-null and unbounded; other columns are unchanged
    series, declared = _declared(t.output_domain, target.name)
    assert not series.nullable
    assert not _has_bounds(series.element_domain)
    for name in SCHEMA:
        if name != target.name:
            assert str(t.output_domain.get_series_domain(name)) == str(
                domain.get_series_domain(name)
            )

    # A3: the declared dtype is Polars' dtype
    actual = _dtype(plan, target.name)
    if actual is None:
        # FINDING: Polars can't fill a boolean with a number, but OpenDP accepts it
        event("FINDING: Polars can't plan this fill")
    elif _coerced(lf, target, fill):
        # FINDING: Polars coerces the column to the fill's type, but the declared dtype is kept
        event("FINDING: coerced dtype not declared")
        assert declared != actual
    else:
        assert declared == actual

    # A4: the declared column admits NaN if the target or fill may be NaN
    if actual is not None and actual.is_float() and target.nan:
        assert series.element_domain.nan
    if _nan_finding(target, fill, actual) and declared == actual:
        # FINDING: a NaN fill isn't declared
        event("FINDING: NaN fill not declared")
        assert not series.element_domain.nan

    # A5: margins are unchanged, except those grouping by the filled column, which can merge
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
        # FINDING: accepted, but Polars fails on every frame, empty or not
        with pytest.raises(pl.exceptions.PolarsError):
            t(lf).collect()
        return

    # B1: exactly the frame Polars computes, row by row
    out = t(lf)
    assert [row_key(r) for r in frame_rows(out)] == [
        row_key(r) for r in frame_rows(plan)
    ]

    # B2: no nulls remain, nulls become the fill, and other values are unchanged
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

    # B3: the output is a member of the output domain, unless a pinned finding applies
    coerced = _coerced(lf, target, fill)
    nan_added = (
        _nan_finding(target, fill, actual)
        and actual.is_float()
        and filled.is_nan().any()
    )
    if coerced:
        event("FINDING: coerced output isn't a member")
    if nan_added:
        event("FINDING: NaN-filled output isn't a member")
    assert _member(t.output_domain, out) == (not coerced and not nan_added)


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

    # B4: aggregates of filled columns, released with no noise, equal plain Polars
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

    # B5: fills compose with filters and selects, and compute exactly what Polars computes
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

    # C1: filling doesn't change the stability map
    t_identity = dp.t.make_stable_lazyframe(domain, dp.symmetric_distance(), lf)
    assert t.map(d) == t_identity.map(d)

    # C2: filled neighbors are no further apart than the neighbors themselves
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

    # D1: adding a row whose target is null moves the sum by at most the clipping bound, 5
    def release(rows):
        return m(to_lazyframe(rows)).collect().item()

    def plain(rows):
        filled = target.expr.fill_null(fill.expr).cast(pl.Float64)
        return to_lazyframe(rows).select(filled.clip(-5, 5).sum()).collect().item()

    neighbor = data + [_null_row()]
    a, b = release(data), release(neighbor)
    if math.isnan(plain(neighbor)) and not math.isnan(plain(data)):
        # FINDING: the filled NaN poisons the sum, which is released as 0, however large it was
        event("FINDING: NaN fill poisons the sum")
        assert b == 0.0
        if abs(a) > 5:
            event("FINDING: NaN fill violates the sensitivity")
        return
    event("sensitivity checked")
    assert abs(a - b) <= 5 + 1e-9, f"{a} vs {b}"


@given(fill=fills(accepted_only=True))
def test_polars_fill_null_keeps_invariants(fill: Fill):
    lf = to_lazyframe([])

    # D2: filling a non-grouping column keeps the frame length public
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

    # D3: filling before or after an expression filter costs the same
    for name, make in [
        ("sum", lambda c: c.clip(*bounds).sum().dp.noise(scale=1.0)),
        ("dp.sum", lambda c: c.dp.sum(bounds, scale=1.0)),
        ("dp.mean", lambda c: c.dp.mean(bounds, scale=1.0)),
    ]:
        unfiltered = loss(make(i.fill_null(fill.expr)))
        fill_then_filter = loss(make(i.fill_null(fill.expr).filter(pred)))
        filter_then_fill = loss(make(i.filter(pred).fill_null(fill.expr)))
        assert unfiltered < math.inf
        if invariant != "lengths":
            assert filter_then_fill == fill_then_filter < math.inf
            continue

        # FINDING: with known lengths, a fill after the filter forgets the filter
        if name == "dp.mean":
            # the mean releases its length without noise, but the length's accounting
            # sees the filter
            event("FINDING: filter-then-fill mean is charged infinite loss")
            assert fill_then_filter < math.inf
            assert filter_then_fill == math.inf
        elif name == "dp.sum":
            # dp.sum fills nulls itself, after any filter, so either order (or no explicit
            # fill at all) is charged as if nothing were filtered
            event("FINDING: dp.sum after a filter is charged as unfiltered")
            assert fill_then_filter == filter_then_fill == unfiltered
            assert loss(make(i.filter(pred))) == unfiltered
        else:
            event("FINDING: filter-then-fill sum is charged as unfiltered")
            assert filter_then_fill == unfiltered
            assert fill_then_filter >= unfiltered
            if filter_then_fill < fill_then_filter:
                event("FINDING: filter-then-fill sum is charged less")


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

    # D5: the sums move by at most the sensitivity, which is the loss at noise scale 1
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
    if shift <= sensitivity:
        event("sensitivity holds")
        return

    # FINDING: a fill after the filter (explicit, or dp.sum's own) forgets the filter, so
    # the sum is charged as if every row contributed a value within the bounds,
    # though a filtered row contributes nothing
    event(f"FINDING: {how} moves beyond its sensitivity")
    assert how not in _SOUND_SUMS
    assert (
        bounds[0] > 0 or bounds[1] < 0 or max(map(abs, bounds)) > bounds[1] - bounds[0]
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

    # D4: an explicit fill costs the same as dp.sum's own imputation
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

    # E2: the plan built by the context never carries the data
    assert object.__getattribute__(filled, "polars_plan").collect().height == 0

    query = filled.select(dp.len(signed=True), pl.col("i").clip(-5, 5).sum().dp.noise())

    # E1: the resolved measurement fits within this query's share of the budget,
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
    # (membership is checked without margins: LazyFrameDomain.member fails on any frame
    # when the domain has a margin with no grouping columns)
    t_plain = dp.t.make_stable_lazyframe(frame_domain(), dp.symmetric_distance(), plan)
    assert _member(t_plain.output_domain, t_plain(lf))

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


def test_finding_nan_fill_breaks_privacy():
    """FINDING: ``f`` is declared non-NaN, and ``f.fill_null(nan)`` stays declared non-NaN.
    One null row then turns the clipped sum into NaN, which is released as 0 (plus noise),
    so neighbors' releases differ by the whole sum, not the clipping bound."""
    domain = frame_domain([Margin(by=[], max_length=100)])
    data = [(0, 5.0, "a", 0, True, None)] * 99
    neighbor = data + [_null_row()]
    for fill in [math.nan, pl.col("g").fill_null(0.0)]:
        if not isinstance(fill, float):
            neighbor = data + [(None, None, None, 0, None, math.nan)]
        plan = to_lazyframe([]).select(
            pl.col("f").fill_null(fill).clip(-5.0, 5.0).sum().dp.noise()
        )
        t = dp.t.make_stable_lazyframe(
            domain,
            dp.symmetric_distance(),
            to_lazyframe([]).with_columns(pl.col("f").fill_null(fill)),
        )
        assert not t.output_domain.get_series_domain("f").element_domain.nan
        assert not _member(t.output_domain, t(to_lazyframe(neighbor)))

        m = dp.m.make_private_lazyframe(
            domain, dp.symmetric_distance(), dp.max_divergence(), plan, global_scale=1.0
        )
        assert m.map(1) == pytest.approx(1.0)
        release = zero_noise(domain, plan)
        a = release(to_lazyframe(data)).collect().item()
        b = release(to_lazyframe(neighbor)).collect().item()
        assert (a, b) == (495.0, 0.0)  # the sensitivity is 5


def test_finding_fill_dtype_coercion():
    """FINDING: Polars casts the column to the fill's type, but OpenDP keeps the original dtype,
    so the output isn't a member of the output domain, and a float sum is summarized as
    Integer Laplace."""
    lf = to_lazyframe([(None, None, None, 0, None, None), (3, 1.5, "a", 1, True, 0.0)])
    for fill, actual in [
        (0.5, pl.Float64),
        ("z", pl.String),
        (pl.col("f").fill_null(0.0), pl.Float64),
    ]:
        plan = lf.with_columns(pl.col("i").fill_null(fill))
        t = dp.t.make_stable_lazyframe(frame_domain(), dp.symmetric_distance(), plan)
        assert _declared(t.output_domain, "i")[1] == pl.Int64
        assert t(lf).collect()["i"].dtype == actual
        assert not _member(t.output_domain, t(lf))

    context = dp.Context.compositor(
        data=lf,
        privacy_unit=dp.unit_of(contributions=1),
        privacy_loss=dp.loss_of(epsilon=1.0),
        split_evenly_over=1,
        margins=[Margin(by=(), max_length=100)],
    )
    query = context.query().select(pl.col("i").fill_null(0.5).dp.sum((-5, 5)))
    assert query.summarize()["distribution"].to_list() == ["Integer Laplace"]
    assert query.release().collect()["i"].dtype == pl.Float64


def test_finding_nullable_cast_fill():
    """FINDING: a cast that can fail is declared non-null when its input is non-null
    (``make_expr_cast`` keeps the input's nullability), so it passes as a fill,
    and nulls remain in a column declared non-null."""
    lf = to_lazyframe(
        [(None, None, "a", 0, None, None), (None, None, "7", 1, None, None)]
    )
    cast = pl.col("s").fill_null("z").cast(pl.Int64)
    t_cast = dp.t.make_stable_lazyframe(
        frame_domain(), dp.symmetric_distance(), lf.with_columns(cast.alias("x"))
    )
    assert not t_cast.output_domain.get_series_domain("x").nullable
    assert t_cast(lf).collect()["x"].to_list() == [None, 7]

    t = dp.t.make_stable_lazyframe(
        frame_domain(),
        dp.symmetric_distance(),
        lf.with_columns(pl.col("i").fill_null(cast)),
    )
    assert not t.output_domain.get_series_domain("i").nullable
    assert t(lf).collect()["i"].to_list() == [None, 7]
    assert not _member(t.output_domain, t(lf))


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
def test_finding_filter_then_fill_undercharges_sum(
    fill_then_filter, filter_then_fill, column
):
    """FINDING (privacy violation): in a grouped aggregation, the fill's output context is
    its input's, so a preceding filter's effect is forgotten. With known lengths, a sum
    after filter-then-fill is charged as if nothing were filtered: changing one row
    is assumed to move it by at most ``upper - lower``. But a changed row can switch from
    filtered out (contributing nothing) to kept: with bounds (2, 3), the sum moves by 3,
    while the claimed sensitivity is 1."""
    domain = _grouped_domain("lengths")
    index = list(SCHEMA).index(column)

    def frame(values):
        rows_ = []
        for v in values:
            row = [None] * len(SCHEMA)
            row[3], row[index] = 0, v
            rows_.append(tuple(row))
        return to_lazyframe(rows_)

    # neighbors with the same group lengths: the first row changes, and passes the filter
    a, b = frame([1, 3, 3]), frame([3, 3, 3])
    if column == "g":
        a, b = frame([1.0, 3.0, 3.0]), frame([3.0, 3.0, 3.0])

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

    # the change moves the sum by 3: fill-then-filter allows for it, filter-then-fill doesn't
    assert sensitivity(fill_then_filter) == pytest.approx(6)
    assert sensitivity(filter_then_fill) == pytest.approx(1)


def test_finding_filtered_dp_sum_undercharged():
    """FINDING (privacy violation): ``dp.sum`` fills nulls (and NaNs) itself before clipping,
    after any filter, so the same reset applies with no fill in the query, even to a
    non-null column. With known lengths, ``x.filter(x > 1).dp.sum((2, 3))`` is calibrated
    for a sensitivity of 1, but changing one row moves it by 3."""
    schema = {"x": pl.Int64, "k": pl.Int64}
    domain = dp.with_margin(
        dp.lazyframe_domain(
            [
                dp.series_domain("x", dp.atom_domain(T="i64")),
                dp.series_domain("k", dp.atom_domain(T="i64")),
            ]
        ),
        Margin(by=[pl.col("k")], invariant="lengths", max_length=50, max_groups=3),
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
    assert (release(a).collect()["x"].item(), release(b).collect()["x"].item()) == (
        6,
        9,
    )
    # the loss at noise scale 1 is the sensitivity: 1, though the sum moves by 3
    assert private(x.filter(x > 1).dp.sum((2, 3), scale=1.0)).map(2) == 1.0
    # an explicit clip and sum accounts for the filter
    assert private(x.filter(x > 1).clip(2, 3).sum().dp.noise(scale=1.0)).map(2) == 6.0

    # the Context API calibrates the noise to the same sensitivity
    context = dp.Context.compositor(
        data=a,
        privacy_unit=dp.unit_of(changes=1),
        privacy_loss=dp.loss_of(epsilon=1.0),
        split_evenly_over=1,
        margins=[Margin(by=["k"], invariant="lengths", max_length=50, max_groups=3)],
    )
    query = context.query().group_by("k").agg(x.filter(x > 1).dp.sum((2, 3)))
    assert query.summarize()["scale"].to_list() == [1.0]


def test_finding_filter_then_fill_forgets_filter():
    """FINDING: in a grouped aggregation, the fill's output context is the input's,
    so a preceding filter's effect on lengths is forgotten. With known lengths, ``dp.mean``
    then treats the length as public, but its accounting doesn't, and the loss is infinite.
    (``test_finding_filter_then_fill_undercharges_sum`` shows the effect on sums.)"""
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

    assert loss(pl.col("i").fill_null(0).filter(pred)) == 12.0
    assert loss(pl.col("i").filter(pred).fill_null(0)) == math.inf


def test_finding_bool_numeric_fill_accepted():
    """FINDING: Polars can't fill a boolean with a number, but OpenDP accepts the plan.
    It fails in Polars on every frame, so the failure doesn't depend on the data."""
    for data in [
        [],
        [(None, None, None, 0, None, None)],
        [(1, 1.0, "a", 0, True, 1.0)],
    ]:
        lf = to_lazyframe(data)
        plan = lf.with_columns(pl.col("flag").fill_null(0))
        t = dp.t.make_stable_lazyframe(frame_domain(), dp.symmetric_distance(), plan)
        with pytest.raises(pl.exceptions.PolarsError):
            t(lf).collect()


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
