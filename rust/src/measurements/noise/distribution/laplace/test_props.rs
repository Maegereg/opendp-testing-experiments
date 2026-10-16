//! Property-based tests for `make_laplace`.
//!
//! The mechanism maps each input to an integer index `z` (see [`NoiseAtom::shift`]),
//! adds discrete Laplace noise to `z`, and maps the result back into the atomic type.
//! Privacy maps are checked against the exact privacy loss of that noise:
//! for shifts `z` and `z'`, the max-divergence is exactly `||z - z'||_1 * 2^k / scale`.
//!
//! Properties (labels match the comments below):
//! * A: the constructor accepts exactly the valid arguments, and preserves the input space
//! * B: the privacy map is exactly `(d + rounding) / scale` rounded up,
//!   and bounds the true privacy loss between any two inputs at distance `d`
//! * C: the function preserves shape, is exact without noise, and its noise is in range
//! * D: the noise has the discrete Laplace distribution, independent of the input (statistical)
//!
//! Known issue: the privacy map accepts negative distances within the granularity's rounding
//! allowance ([`KNOWN_NEGATIVE_DISTANCE`]). Its test of the correct behavior is marked
//! `#[should_panic(expected = "known issue: negative distance")]`, and the map property skips
//! those distances while the flag is set. When it's fixed, that test fails: remove its
//! `should_panic`, and clear the flag.

use dashu::integer::IBig;
use dashu::rational::RBig;
use proptest::prelude::*;

// not `super::*`, which would shadow the primitive `f64` with the `core::f64` module
use super::{DiscreteLaplace, make_laplace};
use crate::core::{Measurement, MetricSpace};
use crate::domains::{AtomDomain, VectorDomain};
use crate::error::Fallible;
use crate::measurements::MakeNoise;
use crate::measures::MaxDivergence;
use crate::metrics::{AbsoluteDistance, L1Distance};
use crate::test_props::noise::*;
use crate::test_props::*;
use crate::traits::CastInternalRational;
use crate::traits::samplers::test::check_chi_square_from_probs;

#[derive(Debug, Clone, Copy)]
enum Shape {
    /// `AtomDomain` with `AbsoluteDistance`
    Scalar,
    /// `VectorDomain` with `L1Distance`, optionally of known size
    Vector { sized: bool },
}

/// Constructor arguments, a dataset, and a second dataset of the same length.
#[derive(Debug, Clone)]
struct Case<T, Q> {
    shape: Shape,
    /// whether the element domain may contain NaN
    nan: bool,
    scale: f64,
    k: Option<i32>,
    data: Vec<T>,
    other: Vec<T>,
    /// extra input distances to probe the privacy map with
    distances: Vec<Q>,
}

fn case<T: NoiseAtom, Q: PropDistance>() -> impl Strategy<Value = Case<T, Q>> {
    let shape = prop_oneof![
        Just(Shape::Scalar),
        Just(Shape::Vector { sized: false }),
        Just(Shape::Vector { sized: true }),
    ];
    (
        shape,
        prop::bool::weighted(if T::HAS_NAN { 0.1 } else { 0.0 }),
        scale(),
        T::granularity(),
        0usize..20,
        prop::collection::vec(Q::value(), 0..4),
    )
        .prop_flat_map(|(shape, nan, scale, k, len, distances)| {
            let len = if let Shape::Scalar = shape { 1 } else { len };
            let k_eff = T::k_eff(k);
            let data = prop_oneof![
                3 => prop::collection::vec(T::value(k_eff), len),
                1 => prop::collection::vec(T::near_tie(k_eff), len),
            ];
            data.prop_flat_map(move |data| {
                // each record of the second dataset is unchanged, adjacent, across a rounding tie,
                // or arbitrary. Whole datasets across ties maximize the rounding error.
                let element = |x: &T| {
                    prop_oneof![
                        Just(x.clone()),
                        Just(x.nudge(true)),
                        Just(x.nudge(false)),
                        Just(x.across_tie(k_eff)),
                        T::value(k_eff),
                    ]
                };
                let across = data.iter().map(|x| x.across_tie(k_eff)).collect::<Vec<_>>();
                let other = prop_oneof![
                    3 => data.iter().map(element).collect::<Vec<_>>(),
                    1 => Just(across),
                ];
                (Just(data), other).prop_map({
                    let distances = distances.clone();
                    move |(data, other)| Case {
                        shape,
                        nan,
                        scale,
                        k,
                        data,
                        other,
                        distances: distances.clone(),
                    }
                })
            })
        })
}

/// The measurement, viewed as a function on vectors in either shape.
struct Mechanism<T, Q> {
    invoke: Box<dyn Fn(&Vec<T>) -> Fallible<Vec<T>>>,
    map: Box<dyn Fn(&Q) -> Fallible<f64>>,
}

/// A: constructs the measurement for `case`, checking that construction succeeds
/// exactly when the arguments are valid, and that the input space is preserved.
fn build<T: NoiseAtom, Q: PropDistance>(
    case: &Case<T, Q>,
) -> Result<Option<Mechanism<T, Q>>, TestCaseError>
where
    DiscreteLaplace: MakeNoise<AtomDomain<T>, AbsoluteDistance<Q>, MaxDivergence>
        + MakeNoise<VectorDomain<AtomDomain<T>>, L1Distance<Q>, MaxDivergence>,
    (AtomDomain<T>, AbsoluteDistance<Q>): MetricSpace,
    (VectorDomain<AtomDomain<T>>, L1Distance<Q>): MetricSpace,
{
    let element_domain = T::element_domain(case.nan);
    let known_size = !matches!(case.shape, Shape::Vector { sized: false });
    let valid = case.scale >= 0.0
        && case.scale.is_finite()
        && !(case.nan && T::HAS_NAN)
        && T::k_ok(case.k, known_size);

    let mechanism = match case.shape {
        Shape::Scalar => {
            let metric = AbsoluteDistance::<Q>::default();
            let m = make_laplace(element_domain.clone(), metric.clone(), case.scale, case.k);
            prop_assert_eq!(m.is_ok(), valid, "construction: {:?}", m.as_ref().err());
            let Ok(m) = m else { return Ok(None) };
            prop_assert!(m.input_domain == element_domain);
            prop_assert!(m.input_metric == metric);
            prop_assert!(m.output_measure == MaxDivergence);
            let m2 = m.clone();
            Mechanism {
                invoke: Box::new(move |x: &Vec<T>| Ok(vec![m.invoke(&x[0])?])),
                map: Box::new(move |d: &Q| m2.map(d)),
            }
        }
        Shape::Vector { sized } => {
            let mut domain = VectorDomain::new(element_domain);
            if sized {
                domain = domain.with_size(case.data.len());
            }
            let metric = L1Distance::<Q>::default();
            let m = make_laplace(domain.clone(), metric.clone(), case.scale, case.k);
            prop_assert_eq!(m.is_ok(), valid, "construction: {:?}", m.as_ref().err());
            let Ok(m) = m else { return Ok(None) };
            prop_assert!(m.input_domain == domain);
            prop_assert!(m.input_metric == metric);
            prop_assert!(m.output_measure == MaxDivergence);
            let m2 = m.clone();
            Mechanism {
                invoke: Box::new(move |x: &Vec<T>| m.invoke(x)),
                map: Box::new(move |d: &Q| m2.map(d)),
            }
        }
    };
    Ok(Some(mechanism))
}

/// Known issue: negative distances within the rounding allowance are accepted by the privacy map.
/// See `test_laplace_rejects_negative_distance`.
const KNOWN_NEGATIVE_DISTANCE: bool = true;

fn check<T: NoiseAtom, Q: PropDistance>(case: Case<T, Q>) -> TestResult
where
    DiscreteLaplace: MakeNoise<AtomDomain<T>, AbsoluteDistance<Q>, MaxDivergence>
        + MakeNoise<VectorDomain<AtomDomain<T>>, L1Distance<Q>, MaxDivergence>,
    (AtomDomain<T>, AbsoluteDistance<Q>): MetricSpace,
    (VectorDomain<AtomDomain<T>>, L1Distance<Q>): MetricSpace,
{
    let Some(m) = build(&case)? else {
        return Ok(());
    };
    let k = T::k_eff(case.k);
    let scale = RBig::try_from(case.scale).unwrap();
    // rounding to the granularity may move each element by up to 2^k - 2^k_min.
    // Rounding only happens when the size is known, and a scalar has size 1.
    let n = match case.shape {
        Shape::Scalar => 1,
        Shape::Vector { .. } => case.data.len(),
    };
    let rounding = (pow2(k) - pow2(T::k_min())) * RBig::from(n);

    // B: the map is exactly (d + rounding) / scale, rounded up, and rejects invalid distances:
    // negative or non-finite. While the known issue stands, negative distances within the
    // rounding allowance are skipped
    let check_map = |d: &Q| -> TestResult {
        let out = (m.map)(d);
        let total = match d.exact() {
            Some(d) if d < RBig::ZERO => {
                if KNOWN_NEGATIVE_DISTANCE && d + &rounding >= RBig::ZERO {
                    return Ok(());
                }
                None
            }
            d => d.map(|d| d + &rounding),
        };
        let Some(total) = total else {
            prop_assert!(out.is_err(), "map({:?}) = {:?} should fail", d, out);
            return Ok(());
        };
        let out = ok(out)?;
        if total == RBig::ZERO {
            prop_assert_eq!(out, 0.0, "map({:?})", d);
        } else if scale == RBig::ZERO {
            prop_assert_eq!(out, f64::INFINITY, "map({:?}) with zero scale", d);
        } else {
            prop_assert!(
                is_rounded_up(out, &(total.clone() / &scale)),
                "map({:?}) = {} is not ({} + {}) / {} rounded up",
                d,
                out,
                total.clone() - &rounding,
                rounding,
                case.scale
            );
        }
        Ok(())
    };
    for d in &case.distances {
        check_map(d)?;
    }

    // B: the map bounds the true privacy loss between the two datasets,
    // for every distance at least as large as their exact distance
    let z = case.data.iter().map(|x| x.shift(k)).collect::<Vec<_>>();
    let z2 = case.other.iter().map(|x| x.shift(k)).collect::<Vec<_>>();
    if let Some(d) = l1_exact(&case.data, &case.other) {
        let shift_distance = z
            .iter()
            .zip(&z2)
            .fold(IBig::ZERO, |s, (a, b)| s + abs_big(a - b));
        // None stands for infinity
        let loss = if shift_distance == IBig::ZERO {
            Some(RBig::ZERO)
        } else if scale == RBig::ZERO {
            None
        } else {
            Some(mul_2k(&RBig::from(shift_distance), k) / &scale)
        };
        let probes = [d.clone(), d.clone() * RBig::from(2), d + RBig::ONE];
        for d_in in probes.iter().filter_map(Q::round_up) {
            check_map(&d_in)?;
            let eps = ok((m.map)(&d_in))?;
            prop_assert!(
                at_least(eps, &loss),
                "privacy violated: map({:?}) = {}, but the privacy loss is {:?}",
                d_in,
                eps,
                loss
            );
        }
    }

    // C: the release has one value per input
    let out = ok((m.invoke)(&case.data))?;
    prop_assert_eq!(out.len(), case.data.len());

    let bound = RBig::from(60) * &scale + pow2(k);
    for ((x, z), y) in case.data.iter().zip(&z).zip(&out) {
        // C: without noise, the release is the input rounded to the granularity
        if scale == RBig::ZERO {
            let expected = T::release(z, k);
            prop_assert!(
                y.same(&expected),
                "{:?} released as {:?}, not {:?}",
                x,
                y,
                expected
            );
        }

        // C: never NaN, and always a multiple of 2^k
        prop_assert!(!y.is_nan(), "{:?} released as NaN", x);
        if let Some(e) = y.exact() {
            prop_assert!(
                mul_2k(&e, -k).denominator() == &dashu::integer::UBig::ONE,
                "{:?} released as {:?}, not a multiple of 2^{}",
                x,
                y,
                k
            );
        }

        // C: the noise is within 60 scales, except with probability below e^-59,
        // so saturation can't wrap and the noise can't be in the wrong units
        let center = mul_2k(&RBig::from(z.clone()), k);
        prop_assert!(
            y.near(&center, &bound),
            "{:?} released as {:?}, more than {} from {}",
            x,
            y,
            bound,
            center
        );
    }
    Ok(())
}

proptest! {
    #[test]
    fn prop_u8_u8(case in case::<u8, u8>()) {
        check(case)?;
    }

    #[test]
    fn prop_i8_f64(case in case::<i8, f64>()) {
        check(case)?;
    }

    #[test]
    fn prop_i32_f64(case in case::<i32, f64>()) {
        check(case)?;
    }

    #[test]
    fn prop_i64_i64(case in case::<i64, i64>()) {
        check(case)?;
    }

    #[test]
    fn prop_u64_f64(case in case::<u64, f64>()) {
        check(case)?;
    }

    #[test]
    fn prop_i128_f32(case in case::<i128, f32>()) {
        check(case)?;
    }

    #[test]
    fn prop_ibig_rbig(case in case::<IBig, RBig>()) {
        check(case)?;
    }

    #[test]
    fn prop_f64_f64(case in case::<f64, f64>()) {
        check(case)?;
    }

    #[test]
    fn prop_f32_f32(case in case::<f32, f32>()) {
        check(case)?;
    }

    #[test]
    fn prop_f32_f64(case in case::<f32, f64>()) {
        check(case)?;
    }
}

// ---------------------------------------------------------------------------------------------
// Distribution (statistical)
// ---------------------------------------------------------------------------------------------

/// The number of samples per statistical test.
const SAMPLES: usize = 20_000;

/// The noise added to `x` in `SAMPLES` releases at granularity `2^k`, as integer indices.
fn noise_indices<T: NoiseAtom>(
    m: &Measurement<VectorDomain<AtomDomain<T>>, L1Distance<f64>, MaxDivergence, Vec<T>>,
    x: T,
    k: i32,
) -> Fallible<Vec<IBig>> {
    let z = x.shift(k);
    let out = m.invoke(&vec![x; SAMPLES])?;
    Ok(out
        .iter()
        .map(|y| {
            let i = mul_2k(&y.exact().unwrap(), -k);
            assert_eq!(i.denominator(), &dashu::integer::UBig::ONE);
            i.numerator() - &z
        })
        .collect())
}

// The statistical tests use a fixed grid of parameters rather than proptest,
// so that `PROPTEST_CASES` can't multiply their cost. Each check fails spuriously
// with probability at most 1e-6.

/// Scales of the integer noise indices, and inputs near zero and far from it.
const STAT_SCALES: [f64; 3] = [0.5, 1.7, 4.3];
const STAT_SHIFTS: [i64; 2] = [-3, (1 << 40) + 1];

// D: integer noise is discrete Laplace(scale), whether the input is near zero or large
#[test]
fn test_integer_noise_distribution() -> Fallible<()> {
    for scale in STAT_SCALES {
        for x in STAT_SHIFTS {
            let domain = VectorDomain::new(AtomDomain::<i64>::default());
            let m = make_laplace(domain, L1Distance::<f64>::default(), scale, None)?;
            let noise = noise_indices(&m, x, 0)?;
            let (w, probs) = discrete_laplace_probs(scale, SAMPLES);
            check_chi_square_from_probs(&histogram(&noise, w), &probs)
                .map_err(|e| err!(FailedFunction, "scale {scale}, x {x}: {e:?}"))?;
        }
    }
    Ok(())
}

// D: float noise at a coarse granularity is discrete Laplace(scale / 2^k) on multiples of 2^k
#[test]
fn test_float_noise_distribution() -> Fallible<()> {
    for (index_scale, k) in STAT_SCALES.into_iter().zip([-4, 0, 2]) {
        for z in STAT_SHIFTS {
            let scale = index_scale * 2f64.powi(k);
            let x = f64::from_rational(mul_2k(&RBig::from(z), k));
            let domain = VectorDomain::new(AtomDomain::<f64>::new_non_nan()).with_size(SAMPLES);
            let m = make_laplace(domain, L1Distance::<f64>::default(), scale, Some(k))?;
            let noise = noise_indices(&m, x, k)?;
            let (w, probs) = discrete_laplace_probs(index_scale, SAMPLES);
            check_chi_square_from_probs(&histogram(&noise, w), &probs)
                .map_err(|e| err!(FailedFunction, "scale {scale}, k {k}, x {x}: {e:?}"))?;
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------------------------
// Deterministic regression cases
// ---------------------------------------------------------------------------------------------

#[test]
fn test_laplace_map_edges() -> Fallible<()> {
    let m = make_laplace(
        AtomDomain::<f64>::new_non_nan(),
        AbsoluteDistance::<f64>::default(),
        2.,
        None,
    )?;
    assert_eq!(m.map(&-0.0)?, 0.0);
    assert_eq!(m.map(&1.0)?, 0.5);

    // a negative zero scale is a zero scale: no noise, and infinite loss for any change
    let m = make_laplace(
        AtomDomain::<i32>::default(),
        AbsoluteDistance::<f64>::default(),
        -0.0,
        None,
    )?;
    assert_eq!(m.invoke(&7)?, 7);
    assert_eq!(m.map(&0.0)?, 0.0);
    assert_eq!(m.map(&1.0)?, f64::INFINITY);

    // with a coarse granularity, rounding contributes to the loss even at distance zero
    let m = make_laplace(
        AtomDomain::<f64>::new_non_nan(),
        AbsoluteDistance::<f64>::default(),
        1.,
        Some(0),
    )?;
    assert_eq!(m.map(&0.0)?, 1.0 - f64::from_bits(1));
    Ok(())
}

#[test]
fn test_laplace_invalid_arguments() {
    let int_space = || {
        (
            AtomDomain::<i32>::default(),
            AbsoluteDistance::<f64>::default(),
        )
    };
    let (d, m) = int_space();
    assert!(make_laplace(d, m, 1., Some(1)).is_err());
    let (d, m) = int_space();
    assert!(make_laplace(d, m, 1., Some(0)).is_ok());

    let float_space = || {
        (
            AtomDomain::<f64>::new_non_nan(),
            AbsoluteDistance::<f64>::default(),
        )
    };
    for k in [i32::MIN, -1075] {
        let (d, m) = float_space();
        assert!(make_laplace(d, m, 1., Some(k)).is_err(), "k = {k}");
    }
    for scale in [-1., f64::NAN, f64::INFINITY] {
        let (d, m) = float_space();
        assert!(make_laplace(d, m, scale, None).is_err(), "scale = {scale}");
    }

    // rounding to a coarse granularity requires a known size
    let vector = VectorDomain::new(AtomDomain::<f64>::new_non_nan());
    assert!(make_laplace(vector.clone(), L1Distance::<f64>::default(), 1., Some(0)).is_err());
    assert!(
        make_laplace(
            vector.with_size(3),
            L1Distance::<f64>::default(),
            1.,
            Some(0)
        )
        .is_ok()
    );
    let (d, m) = float_space();
    assert!(make_laplace(d, m, 1., Some(0)).is_ok());

    // NaN-allowing domains are rejected
    let nan_domain = AtomDomain::<f64>::default();
    assert!(make_laplace(nan_domain, AbsoluteDistance::<f64>::default(), 1., None).is_err());
}

#[test]
fn test_laplace_rounding_ties() -> Fallible<()> {
    let m = make_laplace(
        AtomDomain::<f64>::new_non_nan(),
        AbsoluteDistance::<f64>::default(),
        0.,
        Some(2),
    )?;
    // ties at odd multiples of 2 round towards positive infinity
    assert_eq!(m.invoke(&2.0)?, 4.0);
    assert_eq!(m.invoke(&-2.0)?, 0.0);
    assert_eq!(m.invoke(&-6.0)?, -4.0);
    // infinities are clamped to the largest finite values before rounding
    assert_eq!(m.invoke(&f64::NEG_INFINITY)?, -f64::MAX);

    // rounding MAX to a granularity beyond its precision overflows to infinity
    let m = make_laplace(
        AtomDomain::<f64>::new_non_nan(),
        AbsoluteDistance::<f64>::default(),
        0.,
        Some(1000),
    )?;
    assert_eq!(m.invoke(&f64::MAX)?, f64::INFINITY);
    Ok(())
}

/// B: the privacy map rejects every negative distance, whatever the granularity.
/// Fails for the known issue: negativity is checked only after adding the rounding allowance
/// for the granularity, so negative distances smaller than the allowance are accepted
/// whenever `k > k_min`. No pair of inputs is at a negative distance, so privacy is unaffected,
/// but the map is inconsistent with the default granularity, which rejects every negative distance.
#[test]
#[should_panic(expected = "known issue: negative distance")]
fn test_laplace_rejects_negative_distance() {
    let space = || {
        (
            AtomDomain::<f64>::new_non_nan(),
            AbsoluteDistance::<f64>::default(),
        )
    };

    let (d, m) = space();
    assert!(make_laplace(d, m, 1., None).unwrap().map(&-0.5).is_err());

    // with k = 0 the allowance is 1 - 2^-1074
    let (d, m) = space();
    let meas = make_laplace(d, m, 1., Some(0)).unwrap();
    assert!(meas.map(&-1.0).is_err());
    let out = meas.map(&-0.5);
    assert!(
        out.is_err(),
        "known issue: negative distance: map(-0.5) = {out:?}"
    );
}
