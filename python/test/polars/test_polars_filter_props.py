"""Property-based tests for Polars ``filter`` in OpenDP.

``lf.filter(pred)`` compiles to ``make_stable_filter`` (row filter),
and ``pl.col(x).filter(pred)`` inside an aggregation compiles to ``make_expr_filter`` (expression filter).
Both compile ``pred`` row-by-row, and both are 1-stable.

Properties (labels match the comments below):

* A: the row filter is accepted exactly for supported, boolean, row-wise predicates,
  and keeps every margin descriptor except invariants
* B: the row filter computes exactly what Polars computes, alone and composed
* C: the row filter's stability map is the identity, and holds empirically on neighbors
* D: after a row filter, group keys and lengths are no longer treated as public
* E: the expression filter is only accepted in aggregations, keeps keys public
  but not lengths, and computes exactly what Polars computes
* F: queries built through the Context API respect the privacy budget and carry no data
* G: large frames and extreme margin descriptors
"""

from __future__ import annotations

import math
import time

import pytest

pl = pytest.importorskip("polars")

from hypothesis import assume, event, given, settings, strategies as st  # noqa: E402

import opendp.prelude as dp  # noqa: E402

from test.polars._props import (  # noqa: E402
    Pred,
    accepted_predicates,
    build,
    datasets,
    frame_domain,
    frame_rows,
    margin_lists,
    neighbors,
    predicates,
    row_multiset,
    symmetric_distance,
    to_lazyframe,
    zero_noise,
)

Margin = dp.polars.Margin

#: Queries through the Context API search for a noise scale, which is slow,
#: so they run a fifth as many examples as the active profile.
context_settings = settings(max_examples=max(10, settings().max_examples // 5))


def _assert_accepted_as_expected(built, pred: Pred, what: str):
    if pred.accepted:
        assert built is not None, f"{what}: {pred} should be accepted"
    elif built is not None:
        # an accepted predicate that depends on other rows would break the stability map
        pytest.fail(f"{what}: {pred} should be rejected")


# ---------------------------------------------------------------------------------------------
# A. Row filter: construction and output space
# ---------------------------------------------------------------------------------------------


@given(pred=predicates(), margins=margin_lists())
def test_polars_filter_construction(pred: Pred, margins):
    event(f"predicate kind: {pred.kind}")
    domain = frame_domain(margins)
    lf = to_lazyframe([])

    # A: accepted exactly when the predicate is supported, boolean and row-wise
    t = build(
        lambda: dp.t.make_stable_lazyframe(
            domain, dp.symmetric_distance(), lf.filter(pred.expr)
        )
    )
    _assert_accepted_as_expected(t, pred, "row filter")
    if t is None:
        return

    # A: the schema and size descriptors are kept, but no invariant survives filtering
    assert str(t.output_domain) == str(domain)
    for margin in margins:
        before, after = (
            domain.get_margin(margin.by),
            t.output_domain.get_margin(margin.by),
        )
        assert after.max_length == before.max_length
        assert after.max_groups == before.max_groups
        assert after.invariant is None, (
            f"{margin.by}: invariant {after.invariant} survived"
        )


# ---------------------------------------------------------------------------------------------
# B. Row filter: function
# ---------------------------------------------------------------------------------------------


@given(data=datasets(), pred=accepted_predicates())
def test_polars_filter_matches_polars(data, pred: Pred):
    domain, lf = frame_domain(), to_lazyframe(data)
    t = dp.t.make_stable_lazyframe(
        domain, dp.symmetric_distance(), lf.filter(pred.expr)
    )

    # B: exactly the rows Polars keeps (rows where the predicate is null are dropped)
    out = t(lf)
    expected = frame_rows(lf.filter(pred.expr))
    assert row_multiset(frame_rows(out)) == row_multiset(expected)
    event(
        "all rows kept"
        if len(expected) == len(data)
        else "no rows kept"
        if not expected
        else "some rows kept"
    )

    # B: the output is a member of the output domain
    assert t.output_domain.member(out)

    # B: filters compose with row-wise steps before and after
    plan = (
        lf.with_columns(j=pl.col("i") * 2)
        .filter(pred.expr)
        .filter(pl.col("k") != 1)
        .select("i", "j", "k")
    )
    t_composed = build(
        lambda: dp.t.make_stable_lazyframe(domain, dp.symmetric_distance(), plan)
    )
    if t_composed is not None:
        assert row_multiset(frame_rows(t_composed(lf))) == row_multiset(
            frame_rows(plan)
        )


@given(data=datasets(), pred=accepted_predicates())
def test_polars_filter_private_release_matches_polars(data, pred: Pred):
    domain = frame_domain([Margin(by=[], max_length=100)])
    lf = to_lazyframe(data)

    # B: aggregates of the filtered frame, released with no noise, equal plain Polars
    plan = lf.filter(pred.expr).select(
        dp.len(signed=True),
        pl.col("i").fill_null(0).dp.sum((-5, 5)).alias("sum"),
        pl.col("s").dp.count(signed=True),
        pl.col("i").dp.null_count(signed=True).alias("nulls"),
    )
    released = zero_noise(domain, plan)(lf).collect()
    expected = (
        lf.filter(pred.expr)
        .select(
            pl.len(),
            pl.col("i").fill_null(0).clip(-5, 5).sum().alias("sum"),
            pl.col("s").count(),
            pl.col("i").null_count().alias("nulls"),
        )
        .collect()
    )
    assert [int(v) for v in released.row(0)] == [int(v) for v in expected.row(0)]


# ---------------------------------------------------------------------------------------------
# C. Row filter: stability
# ---------------------------------------------------------------------------------------------


@given(
    data=datasets(), pred=predicates(), d=st.sampled_from([0, 1, 2, 7]), seed=st.data()
)
def test_polars_filter_stability(data, pred: Pred, d, seed):
    domain, lf = frame_domain(), to_lazyframe(data)
    t = build(
        lambda: dp.t.make_stable_lazyframe(
            domain, dp.symmetric_distance(), lf.filter(pred.expr)
        )
    )
    if t is None:
        return

    # C: filtering doesn't change the stability map
    t_identity = dp.t.make_stable_lazyframe(domain, dp.symmetric_distance(), lf)
    assert t.map(d) == t_identity.map(d)

    # C: filtered neighbors are no further apart than the neighbors themselves.
    # This holds for any accepted predicate, including any that should have been rejected.
    other, k = seed.draw(neighbors(data))
    event(f"neighbor distance {k}")
    out, out_other = frame_rows(t(lf)), frame_rows(t(to_lazyframe(other)))
    assert symmetric_distance(out, out_other) <= k
    (bound,) = t.map(k)
    assert bound.per_group == k


# ---------------------------------------------------------------------------------------------
# D. Row filter: invariants in private queries
# ---------------------------------------------------------------------------------------------


def _loss_at_zero_scale(domain, plan, d_in=1, measure=None):
    """The privacy loss of ``plan`` released with no noise, or infinity if it can't be bounded."""
    try:
        return zero_noise(domain, plan, measure).map(d_in)
    except dp.OpenDPException:
        return math.inf


@given(pred=accepted_predicates())
def test_polars_filter_clears_length_invariant(pred: Pred):
    domain = frame_domain([Margin(by=[], invariant="lengths", max_length=100)])
    lf = to_lazyframe([])

    # D: the frame length is public before filtering, but not after
    assert _loss_at_zero_scale(domain, lf.select(dp.len(signed=True))) == 0.0
    assert (
        _loss_at_zero_scale(domain, lf.filter(pred.expr).select(dp.len(signed=True)))
        == math.inf
    )


@given(pred=accepted_predicates())
def test_polars_filter_clears_key_invariant(pred: Pred):
    domain = frame_domain([Margin(by=[pl.col("k")], invariant="keys", max_length=50)])
    lf = to_lazyframe([])

    def private(plan, measure, threshold=None):
        return dp.m.make_private_lazyframe(
            domain,
            dp.symmetric_distance(),
            measure,
            plan,
            global_scale=1.0,
            threshold=threshold,
        )

    # D: public keys can be released without a threshold, but not once rows are filtered
    private(lf.group_by("k").agg(dp.len(signed=True)), dp.max_divergence())
    plan = lf.filter(pred.expr).group_by("k").agg(dp.len(signed=True))
    with pytest.raises(dp.OpenDPException, match="key-set"):
        private(plan, dp.max_divergence())

    approximate = dp.approximate(dp.max_divergence())
    with pytest.raises(dp.OpenDPException):
        private(plan, approximate)
    _, delta = private(plan, approximate, threshold=10).map(1)
    assert delta > 0.0


@context_settings
@given(
    pred=accepted_predicates(),
    contributions=st.integers(1, 3),
    max_length=st.integers(1, 100),
)
def test_polars_filter_keeps_size_descriptors(pred: Pred, contributions, max_length):
    context = dp.Context.compositor(
        data=to_lazyframe([]),
        privacy_unit=dp.unit_of(contributions=contributions),
        privacy_loss=dp.loss_of(epsilon=1.0),
        split_evenly_over=2,
        margins=[Margin(by=(), max_length=max_length)],
    )

    def scales(query):
        return (
            query.select(
                dp.len(signed=True), pl.col("f").fill_null(0.0).dp.sum((-1.0, 1.0))
            )
            .summarize()["scale"]
            .to_list()
        )

    # D: a filter costs nothing extra: the noise scales match the unfiltered query
    assert scales(context.query().filter(pred.expr)) == scales(context.query())


# ---------------------------------------------------------------------------------------------
# E. Expression filter
# ---------------------------------------------------------------------------------------------


def _sum_filtered(pred: Pred):
    return pl.col("i").fill_null(0).filter(pred.expr).dp.sum((-5, 5))


@given(pred=predicates())
def test_polars_expr_filter_construction(pred: Pred):
    event(f"predicate kind: {pred.kind}")
    domain = frame_domain([Margin(by=[pl.col("k")], invariant="keys", max_length=50)])
    lf = to_lazyframe([])

    # E: accepted in aggregations exactly when the predicate is supported, boolean and row-wise
    m = build(
        lambda: dp.m.make_private_lazyframe(
            domain,
            dp.symmetric_distance(),
            dp.max_divergence(),
            lf.group_by("k").agg(_sum_filtered(pred)),
            global_scale=1.0,
        )
    )
    _assert_accepted_as_expected(m, pred, "expression filter")

    # ...and never row-by-row, where it would change the length of the column
    t = build(
        lambda: dp.t.make_stable_lazyframe(
            domain,
            dp.symmetric_distance(),
            lf.with_columns(pl.col("i").filter(pred.expr)),
        )
    )
    assert t is None, f"row-by-row expression filter accepted: {pred}"


def _grouped_sums(lf, pred: Pred) -> dict:
    return {
        k: v
        for k, v in lf.group_by("k")
        .agg(pl.col("i").fill_null(0).clip(-5, 5).filter(pred.expr).sum())
        .collect()
        .rows()
    }


@given(data=datasets(), pred=accepted_predicates(), seed=st.data())
def test_polars_expr_filter_matches_polars(data, pred: Pred, seed):
    domain = frame_domain([Margin(by=[pl.col("k")], invariant="keys", max_length=50)])
    lf = to_lazyframe(data)
    m = zero_noise(domain, lf.group_by("k").agg(_sum_filtered(pred)))

    # E: the release equals Polars, with every key, even those whose rows are all filtered out
    released = dict(m(lf).collect().rows())
    expected = _grouped_sums(lf, pred)
    assert released == expected
    assert set(released) == {row[3] for row in data}
    if any(v == 0 for v in expected.values()):
        event("a group sums to zero")

    # E: on neighbors with the same keys (the invariant), sums move within the sensitivity
    other, k = seed.draw(neighbors(data))
    assume({row[3] for row in other} == {row[3] for row in data})
    released_other = dict(m(to_lazyframe(other)).collect().rows())
    diffs = [abs(released[g] - released_other[g]) for g in released]
    assert sum(diffs) <= 5 * k
    assert sum(d > 0 for d in diffs) <= k


@given(pred=accepted_predicates())
def test_polars_expr_filter_keeps_keys_drops_lengths(pred: Pred):
    lf = to_lazyframe([])

    # E: keys stay public, so no threshold is needed under pure DP
    keys = frame_domain([Margin(by=[pl.col("k")], invariant="keys", max_length=50)])
    dp.m.make_private_lazyframe(
        keys,
        dp.symmetric_distance(),
        dp.max_divergence(),
        lf.group_by("k").agg(_sum_filtered(pred)),
        global_scale=1.0,
    )

    # ...but lengths don't: a column's length is exact only before filtering
    lengths = frame_domain(
        [Margin(by=[pl.col("k")], invariant="lengths", max_length=50)]
    )
    exact = lf.group_by("k").agg(pl.col("i").dp.len(signed=True))
    filtered = lf.group_by("k").agg(pl.col("i").filter(pred.expr).dp.len(signed=True))
    assert _loss_at_zero_scale(lengths, exact) == 0.0
    assert _loss_at_zero_scale(lengths, filtered) == math.inf

    # With explicit noise scales (so loss is sensitivity / scale), aggregates that use a
    # known length must pay for it once the column is filtered: dp.mean releases its
    # denominator without noise only when the length is known.
    def loss(agg):
        return dp.m.make_private_lazyframe(
            lengths,
            dp.symmetric_distance(),
            dp.max_divergence(),
            lf.group_by("k").agg(agg),
        ).map(2)

    column = pl.col("i").fill_null(0)
    for make in [
        lambda c: c.dp.len(scale=1.0, signed=True),
        lambda c: c.dp.mean((-5, 5), scale=1.0),
    ]:
        exact, noisy = loss(make(column)), loss(make(column.filter(pred.expr)))
        assert exact < noisy < math.inf, f"{make(column)}: {exact} vs {noisy} filtered"


# ---------------------------------------------------------------------------------------------
# F. Context API
# ---------------------------------------------------------------------------------------------


@context_settings
@given(
    data=datasets(),
    pred=accepted_predicates(),
    epsilon=st.floats(0.1, 10.0),
    contributions=st.integers(1, 3),
)
def test_polars_filter_context(data, pred: Pred, epsilon, contributions):
    context = dp.Context.compositor(
        data=to_lazyframe(data),
        privacy_unit=dp.unit_of(contributions=contributions),
        privacy_loss=dp.loss_of(epsilon=epsilon),
        split_evenly_over=2,
        margins=[Margin(by=(), max_length=100)],
    )
    filtered = context.query().filter(pred.expr)

    # F: the plan built by the context never carries the data
    assert object.__getattribute__(filtered, "polars_plan").collect().height == 0

    query = filtered.select(
        dp.len(signed=True), pl.col("i").fill_null(0).dp.sum((-5, 5))
    )

    # F: the resolved measurement fits within this query's share of the budget,
    # and releasing it spends exactly that share
    assert query.resolve().map(contributions) <= epsilon / 2
    released = query.release().collect()
    assert released.columns == ["len", "i"]
    assert context.remaining_privacy_loss() == [pytest.approx(epsilon / 2)]


# ---------------------------------------------------------------------------------------------
# G. Large sizes and extremes
# ---------------------------------------------------------------------------------------------


def test_polars_filter_large_frame():
    n = 100_000
    data = [
        (r % 11 - 5 if r % 3 else None, None, "abc"[r % 3], r % 3, r % 2 == 0, None)
        for r in range(n)
    ]
    lf = to_lazyframe(data)
    pred = (pl.col("i") > 0) & pl.col("flag")

    # G: the row filter keeps exactly Polars' rows, in reasonable time
    start = time.monotonic()
    t = dp.t.make_stable_lazyframe(
        frame_domain(), dp.symmetric_distance(), lf.filter(pred)
    )
    out = frame_rows(t(lf))
    assert time.monotonic() - start < 30
    assert row_multiset(out) == row_multiset(frame_rows(lf.filter(pred)))

    # ...and the expression filter's zero-noise release equals Polars, for every key
    keyed = frame_domain([Margin(by=[pl.col("k")], invariant="keys", max_length=n)])
    released = zero_noise(keyed, lf.group_by("k").agg(_sum_filtered(Pred(pred, "ok"))))
    assert dict(released(lf).collect().rows()) == _grouped_sums(lf, Pred(pred, "ok"))


@pytest.mark.parametrize(
    "max_length, max_groups",
    [(2**32 - 1, 1), (1, 2**32 - 1), (2**32 - 1, 2**32 - 1), (2**32 - 1, None)],
)
def test_polars_filter_extreme_margins(max_length, max_groups):
    lf = to_lazyframe([])
    pred = pl.col("i") > 0
    domain = frame_domain(
        [
            Margin(by=[], max_length=max_length),
            Margin(by=[pl.col("k")], max_length=max_length, max_groups=max_groups),
        ]
    )

    # G: filtering keeps extreme descriptors, and releases after it have finite loss
    t = dp.t.make_stable_lazyframe(domain, dp.symmetric_distance(), lf.filter(pred))
    margin = t.output_domain.get_margin([pl.col("k")])
    assert (margin.max_length, margin.max_groups) == (max_length, max_groups)
    for plan in [
        lf.filter(pred).select(dp.len(scale=1.0, signed=True)),
        lf.filter(pred).select(pl.col("i").fill_null(0).dp.sum((-5, 5), scale=1.0)),
        # keys are released with a threshold on the noisy length
        lf.group_by("k").agg(dp.len(signed=True), _sum_filtered(Pred(pred, "ok"))),
    ]:
        m = dp.m.make_private_lazyframe(
            domain,
            dp.symmetric_distance(),
            dp.approximate(dp.max_divergence()),
            plan,
            global_scale=1.0,
            threshold=10,
        )
        epsilon, delta = m.map(1)
        assert math.isfinite(epsilon) and 0 <= delta <= 1


# ---------------------------------------------------------------------------------------------
# Deterministic regression cases
# ---------------------------------------------------------------------------------------------


def test_polars_filter_drops_null_predicate_rows():
    rows = [(1, None, None, 0, flag, None) for flag in [True, None, False]]
    lf = to_lazyframe(rows)
    t = dp.t.make_stable_lazyframe(
        frame_domain(), dp.symmetric_distance(), lf.filter(pl.col("flag"))
    )
    assert frame_rows(t(lf)) == [rows[0]]


def test_polars_filter_literal_predicates():
    rows = [(1, None, None, 0, None, None), (2, 0.5, "a", 1, True, 0.0)]
    lf = to_lazyframe(rows)
    domain = frame_domain([Margin(by=[], invariant="lengths")])
    keep_all = dp.t.make_stable_lazyframe(
        domain, dp.symmetric_distance(), lf.filter(pl.lit(True))
    )
    keep_none = dp.t.make_stable_lazyframe(
        domain, dp.symmetric_distance(), lf.filter(pl.lit(False))
    )
    assert frame_rows(keep_all(lf)) == rows
    assert frame_rows(keep_none(lf)) == []
    # even a filter that keeps every row clears the invariant
    assert keep_all.output_domain.get_margin([]).invariant is None


def test_polars_filter_rejects_invalid_predicates():
    lf = to_lazyframe([])
    invalid = [
        pl.col("i"),
        pl.col("i") > pl.col("i").mean(),
        pl.len() > 3,
        # valid in an aggregation, where it may change the length of the predicate
        pl.col("flag").filter(pl.col("k") > 0),
    ]
    for expr in invalid:
        with pytest.raises(dp.OpenDPException):
            dp.t.make_stable_lazyframe(
                frame_domain(), dp.symmetric_distance(), lf.filter(expr)
            )


def test_polars_expr_filter_keeps_empty_groups():
    rows = [(1, None, None, 0, None, None), (2, None, None, 1, None, None)]
    lf = to_lazyframe(rows)
    domain = frame_domain([Margin(by=[pl.col("k")], invariant="keys", max_length=50)])
    plan = lf.group_by("k").agg(
        pl.col("i").fill_null(0).filter(pl.lit(False)).dp.sum((-5, 5))
    )
    assert dict(zero_noise(domain, plan)(lf).collect().rows()) == {0: 0, 1: 0}
