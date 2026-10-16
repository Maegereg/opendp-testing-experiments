//! Property-based tests for `make_sum`.
//!
//! Every property is checked against an exact reference computed in `IBig`/`RBig`,
//! never in the atomic type `T`, so that overflow or rounding in `T` can't hide a failure.
//!
//! Properties (labels match the comments below):
//! * A: constructor never panics, errors only when it must, and preserves the input space
//! * B: the function agrees with an exact reference (or a proven error bound for floats)
//! * C: the stability map is sound: `|f(x) - f(x')| <= map(d)` whenever `d(x, x') <= d`,
//!   and never under-reports the ideal sensitivity
//!
//! Known issue: a sized float sum over 0 records is rejected ([`KNOWN_FLOAT_SIZE_ZERO`]).
//! The test of the correct behavior is marked `#[should_panic(expected = "known issue")]`,
//! and properties skip size 0 while the flag is set. When it's fixed, that test fails:
//! remove its `should_panic`, and clear the flag.

use std::ops::Bound;

use dashu::integer::IBig;
use dashu::rational::RBig;
use proptest::prelude::*;

use super::float::{CanFloatSumOverflow, Pairwise, SumRelaxation};
use super::int::can_int_sum_overflow;
use super::*;
use crate::domains::Bounds;
use crate::metrics::IntDistance;
use crate::test_props::*;

/// A dataset, plus a list of edits used to derive a neighboring dataset.
#[derive(Debug, Clone)]
struct Case<T> {
    bounds: (T, T),
    sized: bool,
    data: Vec<T>,
    /// a random permutation of `data`
    permuted: Vec<T>,
    edits: Vec<Edit<T>>,
    /// extra input distances to probe the stability map with
    distances: Vec<IntDistance>,
}

// ---------------------------------------------------------------------------------------------
// Integers
// ---------------------------------------------------------------------------------------------

trait SumInt: PropInt + MakeSum<SymmetricDistance> + MakeSum<InsertDeleteDistance> {}
impl<T> SumInt for T where T: PropInt + MakeSum<SymmetricDistance> + MakeSum<InsertDeleteDistance> {}

fn int_case<T: SumInt>() -> impl Strategy<Value = Case<T>> {
    let generic = (bounds(int_value::<T>), 0usize..24);
    let boundary = (1usize..=64, 0u8..3, any::<u8>(), 0usize..3)
        .prop_map(|(n, delta, shape, dn)| (int_boundary_bounds::<T>(n, delta, shape), n + dn - 1));

    prop_oneof![generic, boundary].prop_flat_map(|(bounds, len)| {
        let data = (prop::collection::vec(int_value_in(bounds), len), 0u8..4).prop_map(
            |(mut data, arrange)| {
                // orderings that stress saturation in the order-dependent sums
                let zero = from_big::<T>(IBig::ZERO).unwrap();
                match arrange {
                    1 => data.sort(),
                    2 => data.sort_by(|a, b| b.cmp(a)),
                    3 => data.sort_by_key(|v| *v < zero),
                    _ => (),
                }
                data
            },
        );
        (
            any::<bool>(),
            with_permutation(data),
            edits(int_value_in(bounds)),
            distances(),
        )
            .prop_map(move |(sized, (data, permuted), edits, distances)| Case {
                bounds,
                sized,
                data,
                permuted,
                edits,
                distances,
            })
    })
}

/// Reference for the `SymmetricDistance` sums: separately-saturated negative and positive sums.
/// This coincides with the exact sum when it can't overflow, and with the clamped sum when signs agree.
fn split_ref<T: SumInt>(x: &[T]) -> IBig {
    let (neg, pos) = x
        .iter()
        .map(|v| big(*v))
        .fold((IBig::ZERO, IBig::ZERO), |(neg, pos), v| {
            if v < IBig::ZERO {
                (neg + v, pos)
            } else {
                (neg, pos + v)
            }
        });
    clamp_big::<T>(clamp_big::<T>(neg) + clamp_big::<T>(pos))
}

/// Reference for the `InsertDeleteDistance` sums: a left-to-right saturating fold.
fn fold_ref<T: SumInt>(x: &[T]) -> IBig {
    x.iter()
        .fold(IBig::ZERO, |s, v| clamp_big::<T>(s + big(*v)))
}

fn check_int<T: SumInt>(case: Case<T>) -> TestResult {
    check_int_metric(&case, SymmetricDistance, false)?;
    check_int_metric(&case, InsertDeleteDistance, true)
}

/// Known issue: a sized float sum over 0 records is rejected with an overflow error,
/// because the pairwise overflow check divides by the size (`max_ulp.neg_inf_div(&size_)`).
const KNOWN_FLOAT_SIZE_ZERO: bool = true;

fn check_int_metric<T, MI>(case: &Case<T>, metric: MI, ordered: bool) -> TestResult
where
    MI: Metric<Distance = IntDistance>,
    T: SumInt + MakeSum<MI>,
    (VectorDomain<AtomDomain<T>>, MI): MetricSpace,
{
    let (l, u) = case.bounds;
    let max = int_max::<T>();
    let range = big(u) - big(l);
    let mag = abs_big(big(l)).max(big(u));
    let size = case.sized.then_some(case.data.len());

    let mut domain = VectorDomain::new(ok(AtomDomain::new_closed(case.bounds))?);
    domain.size = size;

    // A: never panics, and only fails when the sensitivity can't be represented in T
    let must_fail = if case.sized {
        range > max
    } else {
        -big(l) > max
    };
    let t = match make_sum(domain.clone(), metric.clone()) {
        Ok(t) => t,
        Err(e) => {
            prop_assert!(must_fail, "unexpected constructor error: {e:?}");
            return Ok(());
        }
    };
    prop_assert!(!must_fail, "constructor should have failed");

    // A: input space is preserved, output domain is all of T
    prop_assert!(t.input_domain == domain);
    prop_assert!(t.input_metric == metric);
    prop_assert!(t.output_domain == AtomDomain::default());

    // B: when the sum can't overflow, it is exact. Also check the overflow predicate itself
    let y = big(ok(t.invoke(&case.data))?);
    let exact = case.data.iter().fold(IBig::ZERO, |s, v| s + big(*v));
    if let Some(n) = size
        && !can_int_sum_overflow(n, case.bounds)
    {
        prop_assert!(
            mag.clone() * IBig::from(n) <= max,
            "overflow predicate unsound"
        );
        prop_assert_eq!(&y, &exact);
    }

    // B: agrees with the saturating reference
    let expected = if ordered {
        fold_ref(&case.data)
    } else {
        split_ref(&case.data)
    };
    prop_assert_eq!(&y, &expected);

    // B: under an unordered metric, the result can't depend on order
    if !ordered {
        prop_assert_eq!(&big(ok(t.invoke(&case.permuted))?), &y);
    }

    // C: the map equals the ideal sensitivity exactly, or fails because it isn't representable
    let ideal = |d: IntDistance| {
        let d = if case.sized { d / 2 } else { d };
        (
            IBig::from(d),
            IBig::from(d) * if case.sized { &range } else { &mag },
        )
    };
    let (x2, k) = neighbor(&case.data, &case.edits, case.sized, ordered);
    let ds = [0, 1, 2, k, k.saturating_add(1)];
    for d in ds.iter().chain(case.distances.iter()) {
        let (d_cast, d_out) = ideal(*d);
        match t.map(d) {
            Ok(v) => prop_assert_eq!(big(v), d_out, "map({}) is not the ideal sensitivity", d),
            Err(_) => prop_assert!(d_cast > max || d_out > max, "map({}) failed spuriously", d),
        }
    }

    // C: stability. Neighbors at distance at most k differ by at most map(k)
    if k > 0 {
        let y2 = big(ok(t.invoke(&x2))?);
        if let Ok(d_out) = t.map(&k) {
            prop_assert!(
                abs_big(y.clone() - y2.clone()) <= big(d_out),
                "stability violated: f(x)={}, f(x')={}, d_in={}, d_out={}",
                y,
                y2,
                k,
                d_out
            );
        }
    }
    Ok(())
}

for_each_int!(ints, int_case, check_int);

// ---------------------------------------------------------------------------------------------
// Floats
// ---------------------------------------------------------------------------------------------

trait SumFloat: PropFloat + MakeSum<SymmetricDistance> + MakeSum<InsertDeleteDistance> {}
impl<T> SumFloat for T where
    T: PropFloat + MakeSum<SymmetricDistance> + MakeSum<InsertDeleteDistance>
{
}

/// Values just below `MAX / 2^j`, where the overflow threshold of size-`2^j` sums sits.
/// Small `j` covers `MAX / n`; large `j` covers the pairwise magnitude limit.
fn near_overflow<T: SumFloat>() -> impl Strategy<Value = T> {
    (prop_oneof![1i32..8, 0i32..64], 0.5f64..1.0, any::<bool>()).prop_map(|(j, frac, neg)| {
        let two = <T as num::NumCast>::from(2).unwrap();
        let frac = <T as num::NumCast>::from(frac).unwrap();
        let v = <T as num::Float>::max_value() / num::Float::powi(two, j) * frac;
        if neg { -v } else { v }
    })
}

fn float_case<T: SumFloat>() -> impl Strategy<Value = Case<T>> {
    let bounds = bounds(|| prop_oneof![4 => float_value::<T>(), 1 => near_overflow::<T>()]);

    (bounds, prop_oneof![0usize..8, 0usize..70]).prop_flat_map(|(bounds, len)| {
        let data = (prop::collection::vec(float_value_in(bounds), len), 0u8..4).prop_map(
            |(mut data, arrange)| {
                // orderings that stress saturation and cancellation
                let zero = <T as num::Zero>::zero();
                match arrange {
                    1 => data.sort_by(|a, b| a.partial_cmp(b).unwrap()),
                    2 => data.sort_by(|a, b| b.partial_cmp(a).unwrap()),
                    3 => data.sort_by_key(|v| *v < zero),
                    _ => (),
                }
                data
            },
        );
        (
            any::<bool>(),
            with_permutation(data),
            edits(float_value_in(bounds)),
            distances(),
        )
            .prop_map(move |(sized, (data, permuted), edits, distances)| Case {
                bounds,
                sized,
                data,
                permuted,
                edits,
                distances,
            })
    })
}

fn check_float<T: SumFloat>(case: Case<T>) -> TestResult {
    check_float_metric(&case, SymmetricDistance, false)?;
    check_float_metric(&case, InsertDeleteDistance, true)
}

fn check_float_metric<T, MI>(case: &Case<T>, metric: MI, ordered: bool) -> TestResult
where
    MI: Metric<Distance = IntDistance>,
    T: SumFloat + MakeSum<MI>,
    (VectorDomain<AtomDomain<T>>, MI): MetricSpace,
{
    let (l, u) = case.bounds;
    let size = case.sized.then_some(case.data.len());

    let Ok(element_domain) = AtomDomain::new_closed(case.bounds) else {
        return Ok(());
    };
    let mut domain = VectorDomain::new(element_domain);
    domain.size = size;

    // A: never panics, and accepts modest finite bounds: with |bounds| <= 2^20 and at most
    // DEFAULT_SIZE_LIMIT records, neither the sum nor its rounding allowance can overflow,
    // so a rejection would be spurious (size 0 is skipped while its known issue stands)
    let limit = RBig::from(1u32 << 20);
    let modest = matches!(
        (rat(l), rat(u)),
        (Some(lr), Some(ur)) if -limit.clone() <= lr && ur <= limit
    ) && size
        .is_none_or(|n| (n > 0 || !KNOWN_FLOAT_SIZE_ZERO) && n <= DEFAULT_SIZE_LIMIT);
    let t = match make_sum(domain.clone(), metric.clone()) {
        Ok(t) => t,
        Err(e) => {
            prop_assert!(!modest, "unexpected constructor error: {e:?}");
            return Ok(());
        }
    };
    // the constructor can only succeed if the bounds are finite
    let (Some(lr), Some(ur)) = (rat(l), rat(u)) else {
        return Err(TestCaseError::fail(
            "constructor accepted non-finite bounds",
        ));
    };

    // A: input space is preserved, output domain excludes NaN
    prop_assert!(t.input_domain == domain);
    prop_assert!(t.input_metric == metric);
    prop_assert!(t.output_domain == AtomDomain::new_non_nan());

    // mirrors the dispatch in `make_sum`, to know which strategy should have been chosen
    let n_eff = size.unwrap_or(DEFAULT_SIZE_LIMIT);
    let can_overflow = ok(Pairwise::<T>::can_float_sum_overflow(n_eff, case.bounds))?;
    // under SymmetricDistance, overflow-prone sums shuffle before summing, so outputs are random
    let randomized = !ordered && can_overflow;
    let relaxation = ok(Pairwise::<T>::relaxation(n_eff, l, u))?;
    let relaxation_r = rat(relaxation).unwrap();

    // B: output is finite (so in the output domain), and accurate when no overflow is possible
    let y = ok(t.invoke(&case.data))?;
    prop_assert!(num::Float::is_finite(y), "non-finite output {:?}", y);
    let exact = case
        .data
        .iter()
        .fold(RBig::ZERO, |s, v| s + rat(*v).unwrap());
    if !can_overflow {
        let error = rat(ok(Pairwise::<T>::error(n_eff, l, u))?).unwrap();
        prop_assert!(
            abs_rat(rat(y).unwrap() - exact.clone()) <= error,
            "rounding error exceeds bound: f(x)={:?}, exact={}",
            y,
            exact
        );
    }

    // B: under an unordered metric, reordering changes the result by at most the relaxation
    if !ordered && !can_overflow {
        let y_perm = ok(t.invoke(&case.permuted))?;
        prop_assert!(abs_rat(rat(y_perm).unwrap() - rat(y).unwrap()) <= relaxation_r.clone());
    }

    // C: the map is non-negative, monotone, and covers the ideal sensitivity plus relaxation
    let range = ur.clone() - lr.clone();
    let mag = abs_rat(lr).max(abs_rat(ur));
    let (x2, k) = neighbor(&case.data, &case.edits, case.sized, ordered);
    let mut ds: Vec<IntDistance> = vec![0, 1, 2, k, k.saturating_add(1)];
    ds.extend(&case.distances);
    ds.sort();
    let mut prev: Option<RBig> = None;
    for d in &ds {
        let Ok(v) = t.map(d) else { continue };
        prop_assert!(!num::Float::is_nan(v), "map({}) is NaN", d);
        let Some(v) = rat(v) else { continue };
        let ideal = if case.sized {
            RBig::from(IBig::from(*d / 2)) * range.clone()
        } else {
            RBig::from(IBig::from(*d)) * mag.clone()
        };
        prop_assert!(
            v >= ideal + relaxation_r.clone(),
            "map({}) under-reports",
            d
        );
        if let Some(p) = &prev {
            prop_assert!(&v >= p, "map is not monotone at d_in={}", d);
        }
        prev = Some(v);
    }

    if randomized {
        // C: the shuffle has stability 1, so the map must be that of the inner ordered sum
        let inner = ok(match size {
            Some(n) => make_sized_bounded_float_ordered_sum::<Pairwise<T>>(n, case.bounds),
            None => make_bounded_float_ordered_sum::<Pairwise<T>>(DEFAULT_SIZE_LIMIT, case.bounds),
        })?;
        for d in &ds {
            match (t.map(d), inner.map(d)) {
                (Ok(a), Ok(b)) => prop_assert!(a == b, "map({}) differs from inner map", d),
                (Err(_), Err(_)) => (),
                _ => prop_assert!(false, "map({}) disagrees with inner map on failure", d),
            }
        }
        return Ok(());
    }

    // C: stability. Neighbors at distance at most k differ by at most map(k)
    if k > 0 {
        let y2 = ok(t.invoke(&x2))?;
        prop_assert!(num::Float::is_finite(y2));
        if let Some(d_out) = t.map(&k).ok().and_then(rat) {
            prop_assert!(
                abs_rat(rat(y).unwrap() - rat(y2).unwrap()) <= d_out,
                "stability violated: f(x)={:?}, f(x')={:?}, d_in={}",
                y,
                y2,
                k
            );
        }
    }
    Ok(())
}

for_each_float!(floats, float_case, check_float);

proptest! {
    /// B: when the dataset exceeds `size_limit`, a random subset of `size_limit` records is summed.
    /// The output must be within the range of any such subset sum, up to rounding error.
    #[test]
    fn prop_float_checked_sum_truncation(
        limit in 1usize..8,
        (a, b) in (-1e6f64..1e6, -1e6f64..1e6),
        fracs in prop::collection::vec(0.0f64..=1.0, 0..20),
    ) {
        let (l, u) = if a <= b { (a, b) } else { (b, a) };
        let data: Vec<f64> = fracs.iter().map(|f| (l + f * (u - l)).clamp(l, u)).collect();
        let t = ok(make_bounded_float_checked_sum::<Pairwise<f64>>(limit, (l, u)))?;
        let y = ok(t.invoke(&data))?;
        prop_assert!(y.is_finite());

        let m = RBig::from(IBig::from(limit.min(data.len())));
        let error = rat(ok(Pairwise::<f64>::error(limit, l, u))?).unwrap();
        let y = rat(y).unwrap();
        prop_assert!(y >= m.clone() * rat(l).unwrap() - error.clone());
        prop_assert!(y <= m * rat(u).unwrap() + error);
    }
}

// ---------------------------------------------------------------------------------------------
// Deterministic regression cases, one or more per dispatch branch
// ---------------------------------------------------------------------------------------------

fn sum<T, MI>(
    bounds: (T, T),
    size: Option<usize>,
    metric: MI,
) -> Fallible<Transformation<VectorDomain<AtomDomain<T>>, MI, AtomDomain<T>, AbsoluteDistance<T>>>
where
    MI: Metric,
    T: MakeSum<MI> + PartialOrd + std::fmt::Debug,
    (VectorDomain<AtomDomain<T>>, MI): MetricSpace,
{
    let mut domain = VectorDomain::new(AtomDomain::new_closed(bounds)?);
    domain.size = size;
    make_sum(domain, metric)
}

#[test]
fn test_sum_requires_closed_bounds() -> Fallible<()> {
    // A: unbounded and half-open domains are rejected
    let unbounded = VectorDomain::new(AtomDomain::<i32>::default());
    assert!(make_sum(unbounded, SymmetricDistance).is_err());
    let unbounded = VectorDomain::new(AtomDomain::<f64>::new_non_nan());
    assert!(make_sum(unbounded, InsertDeleteDistance).is_err());

    let half_open = Bounds::new((Bound::Included(0), Bound::Excluded(10)))?;
    let half_open = VectorDomain::new(AtomDomain::<i32>::new(Some(half_open), None));
    assert!(make_sum(half_open, SymmetricDistance).is_err());

    assert!(AtomDomain::new_closed((f64::NAN, 1.)).is_err());
    Ok(())
}

#[test]
fn test_sum_int_branches() -> Fallible<()> {
    // |i8::MIN| is not representable, so the sensitivity can't be computed
    assert!(sum((-128i8, 0), None, SymmetricDistance).is_err());
    assert!(sum((-128i8, 0), Some(3), SymmetricDistance).is_err());
    assert!(sum((-128i8, 0), None, InsertDeleteDistance).is_err());
    // the range is not representable
    assert!(sum((-100i8, 100), Some(1), SymmetricDistance).is_err());

    // sized, can't overflow: checked sum
    let t = sum((0u8, 255), Some(1), SymmetricDistance)?;
    assert_eq!(t.invoke(&vec![255])?, 255);
    assert_eq!(t.map(&2)?, 255);
    // sized, can overflow, signs agree: monotonic sum
    let t = sum((0u8, 255), Some(2), SymmetricDistance)?;
    assert_eq!(t.invoke(&vec![255, 255])?, 255);
    assert_eq!(t.map(&2)?, 255);
    assert_eq!(t.map(&3)?, 255);

    // sized, can overflow, mixed signs: split sum saturates positives and negatives separately
    let t = sum((-60i8, 60), Some(4), SymmetricDistance)?;
    assert_eq!(t.invoke(&vec![-60, 60, 60, 60])?, 67);
    assert_eq!(t.invoke(&vec![-60, -60, -60, -60])?, -128);
    // sized, can overflow, ordered: saturating fold in order
    let t = sum((-60i8, 60), Some(4), InsertDeleteDistance)?;
    assert_eq!(t.invoke(&vec![-60, 60, 60, 60])?, 120);
    assert_eq!(t.invoke(&vec![60, 60, 60, -60])?, 67);
    // sized, can't overflow, ordered: unordered >> checked sum
    let t = sum((-1i32, 100), Some(3), InsertDeleteDistance)?;
    assert_eq!(t.invoke(&vec![100, -1, 100])?, 199);
    assert_eq!(t.map(&2)?, 101);

    // unsized: monotonic, split, and ordered sums
    let t = sum((0i32, 10), None, SymmetricDistance)?;
    assert_eq!(t.invoke(&vec![1, 2, 3])?, 6);
    assert_eq!(t.map(&1)?, 10);
    let t = sum((-5i32, 10), None, SymmetricDistance)?;
    assert_eq!(t.invoke(&vec![-5, 10])?, 5);
    assert_eq!(t.map(&1)?, 10);
    let t = sum((-1i8, 100), None, InsertDeleteDistance)?;
    assert_eq!(t.invoke(&vec![100, 100, -1])?, 126);
    assert_eq!(t.map(&1)?, 100);
    Ok(())
}

// A: a sized float sum over 0 records is accepted, and sums to 0, as integer sums do.
// Fails for the known issue: it's rejected with an overflow error
#[test]
#[should_panic(expected = "known issue")]
fn test_float_sum_accepts_size_zero() {
    assert_eq!(
        sum((0i32, 1), Some(0), SymmetricDistance)
            .unwrap()
            .invoke(&vec![])
            .unwrap(),
        0
    );
    for result in [
        sum((0f64, 1.), Some(0), SymmetricDistance).and_then(|t| t.invoke(&vec![])),
        sum((0f64, 1.), Some(0), InsertDeleteDistance).and_then(|t| t.invoke(&vec![])),
    ] {
        match result {
            Ok(total) => assert_eq!(total, 0.0),
            Err(e) => panic!("known issue: size 0 is rejected: {e:?}"),
        }
    }
}

#[test]
fn test_sum_float_branches() -> Fallible<()> {
    // sized, can't overflow: checked sum
    let t = sum((0f32, 1.), Some(1 << 20), SymmetricDistance)?;
    assert_eq!(t.invoke(&vec![1.; 1 << 20])?, (1 << 20) as f32);

    // sized, can overflow: shuffle >> ordered sum, which saturates
    let huge = 2f64.powi(1023);
    let t = sum((0f64, huge), Some(2), SymmetricDistance)?;
    assert_eq!(t.invoke(&vec![huge, huge])?, f64::MAX);
    let t = sum((0f64, huge), Some(2), InsertDeleteDistance)?;
    assert_eq!(t.invoke(&vec![huge, huge])?, f64::MAX);
    let t = sum((-huge, 0.), None, SymmetricDistance)?;
    assert_eq!(t.invoke(&vec![-huge, -huge])?, -f64::MAX);

    // magnitudes above 2^1023 are rejected: rounding up to a power of two overflows
    assert!(sum((0f64, f64::MAX), Some(2), SymmetricDistance).is_err());

    // unsized, can't overflow: checked sum with the default size limit
    let t = sum((-1f64, 1.), None, InsertDeleteDistance)?;
    assert_eq!(t.invoke(&vec![1., -1., 0.5])?, 0.5);
    assert!(t.map(&1)? >= 2.);
    Ok(())
}
