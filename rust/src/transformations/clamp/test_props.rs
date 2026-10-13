//! Property-based tests for `make_clamp`.
//!
//! Records are compared by exact identity (floats by bits), and dataset distances are exact.
//!
//! Properties (labels match the comments below):
//! * A: constructor succeeds exactly when its inputs are valid, and builds the expected output space
//! * B: the function clamps each record independently, and never fails on in-domain data
//! * C: under every event-level metric, the function is 1-stable and the map is the identity

use std::fmt::Debug;

use proptest::prelude::*;

use super::*;
use crate::core::Domain;
use crate::metrics::{
    ChangeOneDistance, HammingDistance, InsertDeleteDistance, IntDistance, SymmetricDistance,
};
use crate::test_props::*;
use crate::traits::CheckNull;

/// Atoms that can be clamped and compared exactly.
trait ClampAtom:
    'static + Clone + ProductOrd + PartialOrd + CheckAtom + CheckNull + ExactKey + Debug
{
}
impl<T> ClampAtom for T where
    T: 'static + Clone + ProductOrd + PartialOrd + CheckAtom + CheckNull + ExactKey + Debug
{
}

/// Clamp bounds and an input domain, with datasets to compare.
#[derive(Debug, Clone)]
struct Case<T: CheckAtom> {
    /// may contain NaN, or be bounded independently of `bounds`
    element_domain: AtomDomain<T>,
    sized: bool,
    /// clamp bounds, possibly invalid
    bounds: (T, T),
    data: Vec<T>,
    /// a random permutation of `data`
    permuted: Vec<T>,
    edits: Vec<Edit<T>>,
    /// an arbitrary dataset in the same domain
    other: Vec<T>,
    /// extra input distances to probe the stability map with
    distances: Vec<IntDistance>,
}

/// Datasets over `element_domain` with values from `value()`, clamped to bounds from `bounds`.
fn case<T: ClampAtom, S: Strategy<Value = T>>(
    element_domain: AtomDomain<T>,
    value: impl Fn() -> S,
    bounds: impl Strategy<Value = (T, T)>,
) -> impl Strategy<Value = Case<T>> {
    (
        any::<bool>(),
        bounds,
        with_permutation(prop::collection::vec(value(), 0..40)),
        edits(value()),
        prop::collection::vec(value(), 0..40),
        distances(),
    )
        .prop_map(
            move |(sized, bounds, (data, permuted), edits, mut other, distances)| {
                if sized {
                    // the second dataset must also have the known size
                    other.truncate(data.len());
                    other.extend_from_slice(&data[other.len()..]);
                }
                Case {
                    element_domain: element_domain.clone(),
                    sized,
                    bounds,
                    data,
                    permuted,
                    edits,
                    other,
                    distances,
                }
            },
        )
}

/// Clamp bounds, occasionally in the wrong order.
fn int_clamp_bounds<T: PropInt>() -> impl Strategy<Value = (T, T)> {
    prop_oneof![9 => bounds(int_value::<T>), 1 => (int_value::<T>(), int_value::<T>())]
}

fn int_case<T: PropInt + ClampAtom>() -> impl Strategy<Value = Case<T>> {
    // input bounds are independent of the clamp bounds: they may be disjoint, nested or overlapping
    let bounded = bounds(int_value::<T>).prop_flat_map(|b| {
        case(
            AtomDomain::new_closed(b).unwrap(),
            move || int_value_in(b),
            int_clamp_bounds(),
        )
    });
    prop_oneof![
        case(AtomDomain::default(), int_value::<T>, int_clamp_bounds()),
        bounded,
    ]
}

/// Clamp bounds, occasionally in the wrong order or NaN.
fn float_clamp_bounds<T: PropFloat>() -> impl Strategy<Value = (T, T)> {
    let nan = <T as num::Float>::nan();
    prop_oneof![
        8 => bounds(float_value::<T>),
        1 => (float_value::<T>(), float_value::<T>()),
        1 => (prop_oneof![Just(nan), float_value::<T>()], prop_oneof![Just(nan), float_value::<T>()]),
    ]
}

fn float_case<T: PropFloat + ClampAtom>() -> impl Strategy<Value = Case<T>> {
    let bounded = bounds(float_value::<T>).prop_flat_map(|b| {
        case(
            AtomDomain::new_closed(b).unwrap(),
            move || float_value_in(b),
            float_clamp_bounds(),
        )
    });
    prop_oneof![
        4 => case(AtomDomain::new_non_nan(), float_value::<T>, float_clamp_bounds()),
        4 => bounded,
        // the domain allows NaN, so the constructor must fail
        1 => case(AtomDomain::default(), float_value::<T>, float_clamp_bounds()),
    ]
}

fn check_all<T: ClampAtom>(case: Case<T>) -> TestResult {
    check::<T, SymmetricDistance>(&case)?;
    check::<T, InsertDeleteDistance>(&case)?;
    check::<T, ChangeOneDistance>(&case)?;
    check::<T, HammingDistance>(&case)
}

fn check<T: ClampAtom, M: PropDatasetMetric>(case: &Case<T>) -> TestResult
where
    (VectorDomain<AtomDomain<T>>, M): MetricSpace,
{
    let mut domain = VectorDomain::new(case.element_domain.clone());
    if case.sized {
        domain.size = Some(case.data.len());
    }
    let (l, u) = case.bounds.clone();

    // A1: succeeds iff the domain excludes NaN, the bounds are ordered and non-NaN,
    //     and the domain is sized whenever the metric requires it
    let must_succeed = !case.element_domain.nan()
        && !l.is_null()
        && !u.is_null()
        && l <= u
        && (case.sized || !M::SIZED);
    let t = match make_clamp(domain.clone(), M::default(), case.bounds.clone()) {
        Ok(t) => t,
        Err(e) => {
            prop_assert!(!must_succeed, "unexpected constructor error: {e:?}");
            return Ok(());
        }
    };
    prop_assert!(must_succeed, "constructor accepted invalid input");

    // A2: output metric is the input metric, and output records carry exactly the clamp bounds
    prop_assert!(t.input_domain == domain);
    prop_assert!(t.input_metric == M::default());
    prop_assert!(t.output_metric == M::default());
    let mut element_domain = case.element_domain.clone();
    element_domain.bounds = Some(ok(Bounds::new_closed(case.bounds.clone()))?);
    let output_domain = VectorDomain {
        element_domain,
        size: domain.size,
    };
    prop_assert!(
        t.output_domain == output_domain,
        "output domain {:?}",
        t.output_domain
    );

    // B8: never fails on in-domain data
    let out = ok(t.invoke(&case.data))?;

    // B1/B7: each record is clamped independently
    let clamp = |v: &T| {
        if *v < l {
            l.clone()
        } else if *v > u {
            u.clone()
        } else {
            v.clone()
        }
    };
    let expected = case.data.iter().map(clamp).collect::<Vec<_>>();
    prop_assert_eq!(keys(&out), keys(&expected));

    // B2: output is in the output domain
    prop_assert!(ok(t.output_domain.member(&out))?);

    // B3: idempotent
    prop_assert_eq!(keys(&ok(t.invoke(&out))?), keys(&out));

    // B4: data already within the bounds is unchanged
    if case.data.iter().all(|v| l <= *v && *v <= u) {
        prop_assert_eq!(keys(&out), keys(&case.data));
    }

    // B5: monotone
    for (xi, oi) in case.data.iter().zip(&out) {
        for (xj, oj) in case.data.iter().zip(&out).filter(|(xj, _)| xi <= *xj) {
            prop_assert!(
                oi <= oj,
                "not monotone: {:?} -> {:?}, {:?} -> {:?}",
                xi,
                oi,
                xj,
                oj
            );
        }
    }

    // B6: permuting the input permutes the output
    let out_permuted = ok(t.invoke(&case.permuted))?;
    prop_assert_eq!(symmetric_distance_by_key(&out, &out_permuted), 0);

    // C1: the function doesn't increase the distance between any two datasets
    let (neighbor, k) = M::neighbor(&case.data, &case.edits, case.sized);
    for x2 in [&neighbor, &case.permuted, &case.other] {
        let Some(d_in) = M::exact_distance(&case.data, x2) else {
            continue;
        };
        let out2 = ok(t.invoke(x2))?;
        let d_out = M::exact_distance(&out, &out2).unwrap();
        prop_assert!(
            d_out <= d_in,
            "{:?}: distance grew from {} to {}",
            M::default(),
            d_in,
            d_out
        );
    }

    // C2: the map is the identity
    let probes = [0, 1, 2, k, u32::MAX]
        .into_iter()
        .chain(case.distances.iter().copied());
    for d in probes {
        prop_assert_eq!(ok(t.map(&d))?, d);
    }
    Ok(())
}

fn check_int<T: PropInt + ClampAtom>(case: Case<T>) -> TestResult {
    check_all(case)
}

fn check_float<T: PropFloat + ClampAtom>(case: Case<T>) -> TestResult {
    check_all(case)
}

for_each_int!(ints, int_case, check_int);
for_each_float!(floats, float_case, check_float);

// ---------------------------------------------------------------------------------------------
// Deterministic regression cases
// ---------------------------------------------------------------------------------------------

fn clamp<T: ClampAtom, M: EventLevelMetric>(
    element_domain: AtomDomain<T>,
    size: Option<usize>,
    metric: M,
    bounds: (T, T),
) -> Fallible<Transformation<VectorDomain<AtomDomain<T>>, M, VectorDomain<AtomDomain<T>>, M>>
where
    (VectorDomain<AtomDomain<T>>, M): MetricSpace,
{
    let mut domain = VectorDomain::new(element_domain);
    domain.size = size;
    make_clamp(domain, metric, bounds)
}

#[test]
fn test_clamp_invalid_inputs() -> Fallible<()> {
    // the domain may contain NaN
    assert!(
        clamp(
            AtomDomain::<f64>::default(),
            None,
            SymmetricDistance,
            (0., 1.)
        )
        .is_err()
    );
    // bounds out of order, or NaN
    assert!(
        clamp(
            AtomDomain::<i32>::default(),
            None,
            SymmetricDistance,
            (5, 1)
        )
        .is_err()
    );
    let non_nan = AtomDomain::<f64>::new_non_nan();
    assert!(clamp(non_nan.clone(), None, SymmetricDistance, (f64::NAN, 1.)).is_err());

    // bounded metrics need a known size
    assert!(
        clamp(
            AtomDomain::<i32>::default(),
            None,
            ChangeOneDistance,
            (0, 1)
        )
        .is_err()
    );
    assert!(clamp(AtomDomain::<i32>::default(), None, HammingDistance, (0, 1)).is_err());
    assert!(
        clamp(
            AtomDomain::<i32>::default(),
            Some(3),
            ChangeOneDistance,
            (0, 1)
        )
        .is_ok()
    );
    assert!(
        clamp(
            AtomDomain::<i32>::default(),
            Some(3),
            HammingDistance,
            (0, 1)
        )
        .is_ok()
    );
    Ok(())
}

#[test]
fn test_clamp_float_edges() -> Fallible<()> {
    let non_nan = AtomDomain::<f64>::new_non_nan();

    // -0.0 compares equal to the lower bound 0.0, so it is kept as-is
    let t = clamp(non_nan.clone(), None, SymmetricDistance, (0., 1.))?;
    let out = t.invoke(&vec![-0.0, -1.])?;
    assert_eq!(keys(&out), keys(&[-0.0, 0.]));
    assert!(t.output_domain.member(&out)?);

    // infinite bounds are the identity
    let t = clamp(
        non_nan,
        None,
        InsertDeleteDistance,
        (f64::NEG_INFINITY, f64::INFINITY),
    )?;
    let data = vec![f64::NEG_INFINITY, -f64::MAX, 0., f64::MAX, f64::INFINITY];
    assert_eq!(keys(&t.invoke(&data)?), keys(&data));
    Ok(())
}

#[test]
fn test_clamp_int_edges() -> Fallible<()> {
    let data = vec![i8::MIN, -1, 0, i8::MAX];
    let t = clamp(
        AtomDomain::default(),
        Some(4),
        HammingDistance,
        (i8::MIN, i8::MAX),
    )?;
    assert_eq!(t.invoke(&data)?, data);
    let t = clamp(
        AtomDomain::default(),
        None,
        SymmetricDistance,
        (i8::MAX, i8::MAX),
    )?;
    assert_eq!(t.invoke(&data)?, vec![i8::MAX; 4]);
    Ok(())
}

#[test]
fn test_clamp_replaces_input_bounds() -> Fallible<()> {
    let t = clamp(
        AtomDomain::new_closed((0, 100))?,
        None,
        SymmetricDistance,
        (50, 200),
    )?;
    assert!(t.output_domain.element_domain == AtomDomain::new_closed((50, 200))?);
    assert_eq!(t.invoke(&vec![0, 75, 100])?, vec![50, 75, 100]);
    Ok(())
}

// ---------------------------------------------------------------------------------------------
// Pair atoms
// ---------------------------------------------------------------------------------------------

/// Pairs of small integral floats, so that ties and incomparable pairs are common.
fn small_pair() -> impl Strategy<Value = (f64, f64)> {
    (-3i8..3, -3i8..3).prop_map(|(a, b)| (a as f64, b as f64))
}

proptest! {
    /// D1: whenever clamping pairs succeeds, each output lies within the bounds under the product order,
    /// is in the output domain, and data already within the bounds is unchanged.
    /// See `test_clamp_pairs_fail_on_incomparable_values` for when it fails.
    #[test]
    fn prop_pairs(b in bounds(small_pair), data in prop::collection::vec(small_pair(), 0..10)) {
        let domain = VectorDomain::new(AtomDomain::<(f64, f64)>::new_non_nan());
        let t = ok(make_clamp(domain, SymmetricDistance, b))?;
        let Ok(out) = t.invoke(&data) else { return Ok(()) };
        let ((l0, l1), (u0, u1)) = b;
        for ((x, out), (o0, o1)) in data.iter().zip(&out).zip(&out) {
            prop_assert!(l0 <= *o0 && *o0 <= u0 && l1 <= *o1 && *o1 <= u1, "{:?} -> {:?}", x, out);
            if l0 <= x.0 && x.0 <= u0 && l1 <= x.1 && x.1 <= u1 {
                prop_assert_eq!(x.key(), out.key());
            }
        }
        prop_assert!(ok(t.output_domain.member(&out))?);
    }
}

/// FINDING: the bounds are validated under the lexicographic order (`PartialOrd`),
/// while pairs are clamped, and checked for domain membership, under the product order (`ProductOrd`),
/// which is only partial. So `invoke` can fail on in-domain data, which is observable,
/// and membership errors instead of returning false.
/// This pins the current behavior; pairs are not exposed through FFI.
#[test]
fn test_clamp_pairs_fail_on_incomparable_values() -> Fallible<()> {
    let domain = VectorDomain::new(AtomDomain::<(f64, f64)>::new_non_nan());

    // bounds are ordered lexicographically but not under the product order,
    // so the constructor succeeds, but clamping any record fails
    let t = make_clamp(domain.clone(), SymmetricDistance, ((-1., 1.), (0., 0.)))?;
    assert!(t.invoke(&vec![(0., 0.)]).is_err());
    assert_eq!(t.invoke(&vec![])?, vec![]);

    // bounds are ordered under both, but a record is incomparable with a bound
    let t = make_clamp(domain, SymmetricDistance, ((0., 0.), (1., 1.)))?;
    assert_eq!(
        t.invoke(&vec![(0.5, 0.5), (2., 2.)])?,
        vec![(0.5, 0.5), (1., 1.)]
    );
    assert!(t.invoke(&vec![(2., -1.)]).is_err());
    assert!(t.output_domain.element_domain.member(&(2., -1.)).is_err());
    Ok(())
}
