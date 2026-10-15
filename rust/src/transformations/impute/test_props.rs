//! Property-based tests for `make_impute_uniform_float`.
//!
//! Records are compared by exact identity (floats by bits), and dataset distances are exact.
//!
//! Imputed values come from system entropy, so the outputs of two datasets can't be coupled
//! from outside. Stability is instead checked exactly on the parts of the output that the
//! function determines: with every imputed row relabelled as NaN, outputs must be
//! no further apart than inputs. Without NaN, that is exact stability of the outputs themselves.
//! The imputed values are checked by their support, and statistically for uniformity.
//!
//! `rand 0.7.3`'s `Uniform::new`, which runs once per imputed row, loops about
//! `max(|lower|, |upper|) / (2 (upper - lower))` times. Generated bounds keep that cost low,
//! and narrower bounds are probed separately (see `test_impute_adjacent_bounds_hang`).
//!
//! Properties (labels match the comments below):
//! * A: the constructor succeeds exactly when the bounds are valid, and builds the expected output space
//! * B: non-NaN rows pass through bit for bit, and NaN rows are replaced with values in `[lower, upper)`
//! * C: the map is the identity, and is sound and tight
//! * D: imputed values are uniform and independent (statistical)
//! * E: large datasets, extreme and infinite bounds, and huge sizes

use std::fmt::Debug;

use proptest::prelude::*;

use super::*;
use crate::metrics::{
    ChangeOneDistance, HammingDistance, InsertDeleteDistance, IntDistance, MicrodataMetric,
    SymmetricDistance,
};
use crate::test_props::*;
use crate::traits::samplers::test::check_chi_square_from_probs;

/// Float atoms that can be imputed and compared exactly.
trait ImputeAtom: PropFloat + SampleUniform + ExactKey + Debug {}
impl ImputeAtom for f32 {}
impl ImputeAtom for f64 {}

fn cast<T: ImputeAtom>(v: f64) -> T {
    <T as num::NumCast>::from(v).unwrap()
}

fn to_f64<T: ImputeAtom>(v: T) -> f64 {
    num::ToPrimitive::to_f64(&v).unwrap()
}

/// The element domain of the input.
#[derive(Debug, Clone)]
enum Kind<T> {
    /// NaN is allowed, so there may be rows to impute
    Nan,
    /// NaN is not allowed, so the function should be the identity
    NonNan,
    /// closed bounds, without NaN
    Closed((T, T)),
}

/// An input domain, imputation bounds, and datasets to compare.
#[derive(Debug, Clone)]
struct Case<T> {
    /// possibly invalid
    bounds: (T, T),
    kind: Kind<T>,
    /// whether the input domain records the length of `data`
    sized: bool,
    data: Vec<T>,
    /// a random permutation of `data`
    permuted: Vec<T>,
    edits: Vec<Edit<T>>,
    /// an arbitrary dataset in the same domain, with the same length if sized
    other: Vec<T>,
    /// extra input distances to probe the stability map with
    distances: Vec<IntDistance>,
}

impl<T: ImputeAtom> Case<T> {
    fn input_domain(&self, sized: bool) -> VectorDomain<AtomDomain<T>> {
        let element_domain = match self.kind {
            Kind::Nan => AtomDomain::default(),
            Kind::NonNan => AtomDomain::new_non_nan(),
            Kind::Closed(b) => AtomDomain::new_closed(b).unwrap(),
        };
        let domain = VectorDomain::new(element_domain);
        if sized {
            domain.with_size(self.data.len())
        } else {
            domain
        }
    }
}

/// The reference for when the constructor accepts the bounds.
fn valid<T: ImputeAtom>((lower, upper): (T, T)) -> bool {
    !lower.is_nan() && !upper.is_nan() && lower < upper
}

/// About twice the number of iterations `Uniform::new` takes to build a sampler over `[lower, upper)`.
fn sampler_cost<T: ImputeAtom>((lower, upper): (T, T)) -> f64 {
    let (l, u) = (to_f64(lower), to_f64(upper));
    if !valid((l, u)) {
        return 0.0;
    }
    // the width is infinite when it overflows, so the cost is 0
    l.abs().max(u.abs()) / (u - l)
}

/// The sampler cost above which datasets are kept short.
const SLOW: f64 = 1024.0;
/// The largest sampler cost generated.
const MAX_COST: f64 = 65536.0;

/// Finite values, biased towards the edges of the type.
fn finite<T: ImputeAtom>() -> impl Strategy<Value = T> {
    let max = <T as num::Float>::max_value();
    float_value::<T>().prop_map(move |v| if v.is_infinite() { max.copysign(v) } else { v })
}

/// Imputation bounds: mostly valid and finite, sometimes narrow, extreme or invalid.
fn impute_bounds<T: ImputeAtom>() -> impl Strategy<Value = (T, T)> {
    let zero = <T as num::Zero>::zero();
    let nan = <T as num::Float>::nan();
    let max = <T as num::Float>::max_value();
    let min_pos = <T as num::Float>::min_positive_value();
    let tiny = min_pos * <T as num::Float>::epsilon();
    let two = cast::<T>(2.0);
    let special = vec![
        (-zero, zero),
        (zero, -zero),
        (-max, max),
        (-max, zero),
        (zero, max),
        (max / two, max),
        (min_pos, min_pos * two),
        (tiny, tiny * cast(3.0)),
        (-tiny, tiny),
        (zero, tiny),
    ];
    let invalid = prop_oneof![
        bounds(finite::<T>).prop_map(|(l, u)| (u, l)),
        finite::<T>().prop_map(|v| (v, v)),
        finite::<T>().prop_map(move |v| (nan, v)),
        finite::<T>().prop_map(move |v| (v, nan)),
    ];
    prop_oneof![
        10 => bounds(finite::<T>),
        // a relative width of 2^-r
        2 => (finite::<T>(), 0i32..=24).prop_map(move |(l, r)| {
            let u = l + l.abs() * <T as num::Float>::powi(two, -r);
            (l, if u > l { u } else { l.next_up() })
        }),
        // a few representable values
        1 => (finite::<T>(), 1usize..=4).prop_map(|(l, k)| (l, (0..k).fold(l, |u, _| u.next_up()))),
        2 => prop::sample::select(special),
        2 => invalid,
    ]
    .prop_map(move |(l, u)| {
        // keep the bounds finite, since infinite bounds panic (see `test_impute_infinite_bounds_panic`)
        let (l, u) = (
            if l.is_infinite() { max.copysign(l) } else { l },
            if u.is_infinite() { max.copysign(u) } else { u },
        );
        if sampler_cost((l, u)) <= MAX_COST {
            return (l, u);
        }
        // too slow to sample: widen to a relative width of 2^-12
        let w = l.abs() * <T as num::Float>::powi(two, -12);
        if (l + w).is_finite() {
            (l, l + w)
        } else {
            (l - w, l)
        }
    })
}

fn case<T: ImputeAtom>() -> impl Strategy<Value = Case<T>> {
    let kind = prop_oneof![
        3 => Just(Kind::Nan),
        1 => Just(Kind::NonNan),
        1 => bounds(finite::<T>).prop_map(Kind::Closed),
    ];
    (impute_bounds::<T>(), kind, nan_percent(), any::<bool>()).prop_flat_map(
        |(bounds, kind, nan_percent, sized)| {
            let value = match kind {
                Kind::Nan => nan_heavy_float::<T>(nan_percent),
                Kind::NonNan => nan_heavy_float::<T>(0),
                Kind::Closed(b) => float_value_in(b).boxed(),
            };
            let len = if sampler_cost(bounds) > SLOW {
                (0usize..4).boxed()
            } else {
                prop_oneof![39 => 0usize..40, 1 => 10_000usize..100_000].boxed()
            };
            len.prop_flat_map(move |len| {
                (
                    with_permutation(dataset(value.clone(), len)),
                    edits(value.clone()),
                    dataset(value.clone(), len.min(40)),
                    any::<bool>(),
                    distances(),
                )
                    .prop_map({
                        let kind = kind.clone();
                        move |((data, permuted), edits, mut other, same_len, distances)| {
                            if sized || same_len {
                                // the second dataset must also have the known length
                                other.truncate(data.len());
                                other.extend_from_slice(&data[other.len()..]);
                            }
                            Case {
                                bounds,
                                kind: kind.clone(),
                                sized,
                                data,
                                permuted,
                                edits,
                                other,
                                distances,
                            }
                        }
                    })
            })
        },
    )
}

fn check_all<T: ImputeAtom>(case: Case<T>) -> TestResult {
    check::<T, SymmetricDistance>(&case, case.sized)?;
    check::<T, InsertDeleteDistance>(&case, case.sized)?;
    // these metrics require a known size
    check::<T, ChangeOneDistance>(&case, true)?;
    check::<T, HammingDistance>(&case, true)
}

/// `x` with every NaN replaced by the same NaN, so that NaN payloads don't distinguish records.
fn canonical<T: ImputeAtom>(x: &[T]) -> Vec<T> {
    let nan = <T as num::Float>::nan();
    x.iter()
        .map(|&v| if v.is_nan() { nan } else { v })
        .collect()
}

/// `out` with the rows that were imputed (NaN in `x`) relabelled as NaN.
fn relabel<T: ImputeAtom>(x: &[T], out: &[T]) -> Vec<T> {
    let nan = <T as num::Float>::nan();
    x.iter()
        .zip(out)
        .map(|(v, &o)| if v.is_nan() { nan } else { o })
        .collect()
}

fn check<T, M>(case: &Case<T>, sized: bool) -> TestResult
where
    T: ImputeAtom,
    M: PropDatasetMetric<Distance = IntDistance>,
    (VectorDomain<AtomDomain<T>>, M): MetricSpace,
{
    let input_domain = case.input_domain(sized);
    let (lower, upper) = case.bounds;

    // A1: construction succeeds exactly when neither bound is NaN and lower < upper
    let t = make_impute_uniform_float::<M, T>(input_domain.clone(), M::default(), case.bounds);
    prop_assert_eq!(
        t.is_ok(),
        valid(case.bounds),
        "construction: {:?}",
        t.as_ref().err()
    );
    let Ok(t) = t else {
        return Ok(());
    };

    // A2: the output elements are any non-NaN float (input bounds are dropped), with the input size
    let mut output_domain = VectorDomain::new(AtomDomain::new_non_nan());
    output_domain.size = input_domain.size;
    prop_assert!(t.input_domain == input_domain);
    prop_assert!(t.input_metric == M::default());
    prop_assert!(t.output_domain == output_domain);
    prop_assert!(t.output_metric == M::default());

    // C1: the map is the identity
    for d in [0, 1, u32::MAX].iter().chain(&case.distances) {
        prop_assert_eq!(ok(t.map(d))?, *d, "map({})", d);
    }

    let impute = |x: &Vec<T>| -> Result<Vec<T>, TestCaseError> {
        let out = ok(t.invoke(x))?;
        // B1: in the output domain, so no NaN is left
        prop_assert!(
            ok(t.output_domain.member(&out))?,
            "output isn't in the output domain"
        );
        check_row_wise(x, &out, |v, o| {
            if !v.is_nan() {
                // B2/B4: non-NaN rows, including ±0, ±inf and subnormals, pass through bit for bit
                (v.key() == o.key())
                    .then_some(())
                    .ok_or(format!("{v:?} changed to {o:?}"))
            } else {
                // B3/B5: imputed in [lower, upper), so equal to lower when the bounds are adjacent
                (lower <= *o && *o < upper)
                    .then_some(())
                    .ok_or(format!("imputed {o:?}, outside [{lower:?}, {upper:?})"))
            }
        })?;
        Ok(out)
    };

    let out = impute(&case.data)?;

    // C2/C3: with imputed rows relabelled as NaN, outputs are no further apart than inputs.
    // The exact insert-delete distance takes quadratic time, so it's skipped for large datasets.
    let affordable = |x: &[T]| !<M as MicrodataMetric>::ORDERED || x.len() <= 2_000;
    let (neighbor, _) = M::neighbor(&case.data, &case.edits, sized);
    // B6: a permutation is imputed row by row too
    for other in [neighbor, case.permuted.clone(), case.other.clone()] {
        if sized && other.len() != case.data.len() {
            continue;
        }
        let out_other = impute(&other)?;
        if !(affordable(&case.data) && affordable(&other)) {
            continue;
        }
        let Some(d_in) = M::exact_distance(&canonical(&case.data), &canonical(&other)) else {
            continue;
        };
        let d_in = d_in as IntDistance;
        let d_out = M::exact_distance(&relabel(&case.data, &out), &relabel(&other, &out_other))
            .unwrap() as IntDistance;
        prop_assert!(
            d_out <= ok(t.map(&d_in))?,
            "stability violated: inputs at distance {} gave outputs at distance {}",
            d_in,
            d_out
        );
    }
    Ok(())
}

for_each_float!(floats, case, check_all);

// ---------------------------------------------------------------------------------------------
// Constructor and function: regression cases
// ---------------------------------------------------------------------------------------------

fn impute_f64(
    bounds: (f64, f64),
) -> Fallible<
    Transformation<
        VectorDomain<AtomDomain<f64>>,
        SymmetricDistance,
        VectorDomain<AtomDomain<f64>>,
        SymmetricDistance,
    >,
> {
    make_impute_uniform_float(VectorDomain::default(), SymmetricDistance, bounds)
}

#[test]
fn test_impute_invalid_bounds() {
    let nan = f64::NAN;
    for bounds in [
        (-0.0, 0.0),
        (0.0, -0.0),
        (1.0, 1.0),
        (3.0, 2.0),
        (nan, 1.0),
        (0.0, nan),
    ] {
        assert!(impute_f64(bounds).is_err(), "{bounds:?} should be rejected");
    }
}

#[test]
fn test_impute_passes_special_values_through() -> Fallible<()> {
    let x = vec![-0.0, f64::INFINITY, f64::NEG_INFINITY, 5e-324, f64::MAX];
    let out = impute_f64((2.0, 3.0))?.invoke(&x)?;
    assert_eq!(keys(&out), keys(&x));
    Ok(())
}

#[test]
fn test_impute_drops_input_bounds() -> Fallible<()> {
    let t = make_impute_uniform_float(
        VectorDomain::new(AtomDomain::new_closed((0.0, 10.0))?),
        SymmetricDistance,
        (20.0, 30.0),
    )?;
    assert_eq!(t.output_domain.element_domain, AtomDomain::new_non_nan());
    Ok(())
}

fn imputes_with<M>(sized: bool) -> Fallible<()>
where
    M: PropDatasetMetric<Distance = IntDistance>,
    (VectorDomain<AtomDomain<f64>>, M): MetricSpace,
{
    let mut domain = VectorDomain::default();
    if sized {
        domain = domain.with_size(2);
    }
    let t = make_impute_uniform_float(domain, M::default(), (2.0, 3.0))?;
    let out = t.invoke(&vec![1.0, f64::NAN])?;
    assert_eq!(out[0], 1.0);
    assert!((2.0..3.0).contains(&out[1]));
    Ok(())
}

#[test]
fn test_impute_every_metric() -> Fallible<()> {
    imputes_with::<SymmetricDistance>(false)?;
    imputes_with::<InsertDeleteDistance>(false)?;
    imputes_with::<ChangeOneDistance>(true)?;
    imputes_with::<HammingDistance>(true)
}

// ---------------------------------------------------------------------------------------------
// Tightness of the stability map
// ---------------------------------------------------------------------------------------------

fn tightness<M>() -> Fallible<()>
where
    M: PropDatasetMetric<Distance = IntDistance>,
    (VectorDomain<AtomDomain<f64>>, M): MetricSpace,
{
    // C4: changing one record changes one output record, so the constant 1 can't be lowered
    let t = make_impute_uniform_float(
        VectorDomain::default().with_size(1),
        M::default(),
        (0.0, 1.0),
    )?;
    let (x, x2) = (vec![1.0], vec![2.0]);
    let d_in = M::exact_distance(&x, &x2).unwrap() as u32;
    let d_out = M::exact_distance(&t.invoke(&x)?, &t.invoke(&x2)?).unwrap() as u32;
    assert!(d_in > 0);
    assert_eq!(d_out, t.map(&d_in)?);
    Ok(())
}

#[test]
fn test_impute_map_is_tight() -> Fallible<()> {
    tightness::<SymmetricDistance>()?;
    tightness::<InsertDeleteDistance>()?;
    tightness::<ChangeOneDistance>()?;
    tightness::<HammingDistance>()
}

// ---------------------------------------------------------------------------------------------
// Randomness (statistical)
// ---------------------------------------------------------------------------------------------

/// The number of samples per statistical test. Each check fails spuriously with probability at most 1e-6.
const SAMPLES: usize = 20_000;

/// Imputes `n` NaN rows with values in `bounds`.
fn draws<T: ImputeAtom>(bounds: (T, T), n: usize) -> Fallible<Vec<T>> {
    make_impute_uniform_float(VectorDomain::default(), SymmetricDistance, bounds)?
        .invoke(&vec![<T as num::Float>::nan(); n])
}

fn uniformity<T: ImputeAtom>() -> Fallible<()> {
    let tiny = to_f64(<T as num::Float>::min_positive_value()) * 1e3;
    let huge = to_f64(<T as num::Float>::max_value()) / 1e3;
    for (l, u) in [(0.0, 1.0), (-3.0, 5.0), (huge / 10.0, huge), (-tiny, tiny)] {
        let bounds = (cast::<T>(l), cast::<T>(u));
        let counts = bin_counts(&draws(bounds, SAMPLES)?, bounds, 10);
        check_chi_square_from_probs(&counts, &uniform_probs(10))?;
    }
    Ok(())
}

// D1: imputed values are uniform over the bounds, at every scale
#[test]
fn test_impute_is_uniform() -> Fallible<()> {
    uniformity::<f32>()?;
    uniformity::<f64>()
}

fn independence<T: ImputeAtom>() -> Fallible<()> {
    let bounds = (cast::<T>(0.0), cast::<T>(1.0));
    // pairs of adjacent rows in one dataset fall uniformly in a 5 x 5 grid
    let out = draws(bounds, SAMPLES)?;
    let bins = bin_counts(&out, bounds, 5);
    let bin = |v: T| {
        bin_counts(&[v], bounds, 5)
            .iter()
            .position(|&c| c == 1)
            .unwrap()
    };
    let mut pairs = vec![0u64; 25];
    for p in out.chunks(2) {
        pairs[bin(p[0]) * 5 + bin(p[1])] += 1;
    }
    check_chi_square_from_probs(&bins, &uniform_probs(5))?;
    check_chi_square_from_probs(&pairs, &uniform_probs(25))?;
    // the first row of separate invocations is also uniform, so the sampler isn't reseeded identically
    let firsts = (0..2_000)
        .map(|_| draws(bounds, 1).map(|o| o[0]))
        .collect::<Fallible<Vec<T>>>()?;
    check_chi_square_from_probs(&bin_counts(&firsts, bounds, 5), &uniform_probs(5))
}

// D2: imputed values are independent of each other, within and across invocations
#[test]
fn test_impute_is_independent() -> Fallible<()> {
    independence::<f32>()?;
    independence::<f64>()
}

// D3: over a range of a few f32 values, imputation is a continuous uniform draw rounded to
// the nearest float, so `lower` has half the probability of each other value.
// This only costs accuracy, and it's pinned to describe the behavior.
// (f64 ranges this narrow hang: see `test_impute_adjacent_bounds_hang`.)
#[test]
fn test_impute_few_values_round_to_nearest() -> Fallible<()> {
    for k in [2usize, 4] {
        let lower = 1.0f32;
        let values = (0..k)
            .scan(lower, |v, _| {
                let current = *v;
                *v = v.next_up();
                Some(current)
            })
            .collect::<Vec<_>>();
        let upper = values[k - 1].next_up();
        // each draw runs Uniform::new's loop about 2^22 times, so this uses fewer samples
        let out = draws((lower, upper), 600)?;
        let counts = values
            .iter()
            .map(|v| out.iter().filter(|o| o.to_bits() == v.to_bits()).count() as u64)
            .collect::<Vec<_>>();
        assert_eq!(counts.iter().sum::<u64>(), 600, "draws outside {values:?}");
        let mut probs = vec![1.0; k];
        probs[0] = 0.5;
        let total = k as f64 - 0.5;
        let probs = probs.iter().map(|p| p / total).collect::<Vec<_>>();
        check_chi_square_from_probs(&counts, &probs)?;
    }
    Ok(())
}

fn overflowing_range<T: ImputeAtom>() -> Fallible<()> {
    let max = <T as num::Float>::max_value();
    let out = draws((-max, max), 2_000)?;
    let zero = <T as num::Zero>::zero();
    let non_negative = out.iter().filter(|&&v| v >= zero).count();
    assert!(out.iter().all(|&v| -max <= v && v < max));
    assert_eq!(
        non_negative, 0,
        "expected every draw to be negative (the finding), got {non_negative} non-negative draws"
    );
    Ok(())
}

// D4: FINDING: when `upper - lower` overflows, rand shrinks the width from infinity to MAX,
// so draws only cover [lower, lower + MAX). Over (-MAX, MAX) every imputed value is negative,
// where a uniform draw would be non-negative half of the time.
// Draws stay in bounds and are row-local, so this isn't a privacy failure.
#[test]
fn test_impute_overflowing_range_is_biased() -> Fallible<()> {
    overflowing_range::<f32>()?;
    overflowing_range::<f64>()
}

// ---------------------------------------------------------------------------------------------
// E. Large datasets, extreme bounds and huge sizes
// ---------------------------------------------------------------------------------------------

// E2: a million NaN rows are all imputed in bounds
#[test]
fn test_impute_large_dataset() -> Fallible<()> {
    let start = std::time::Instant::now();
    let t = impute_f64((0.0, 1.0))?;
    let out = t.invoke(&vec![f64::NAN; 1_000_000])?;
    assert_eq!(out.len(), 1_000_000);
    assert!(out.iter().all(|v| (0.0..1.0).contains(v)));
    assert!(t.output_domain.member(&out)?);
    assert!(start.elapsed() < std::time::Duration::from_secs(60));
    Ok(())
}

fn extreme_bounds<T: ImputeAtom>(bounds: &[(T, T)]) -> Fallible<()> {
    let nan = <T as num::Float>::nan();
    for &(l, u) in bounds {
        let t = make_impute_uniform_float(VectorDomain::default(), SymmetricDistance, (l, u))?;
        let out = t.invoke(&vec![nan; 200])?;
        assert!(
            out.iter().all(|&v| l <= v && v < u),
            "draws outside [{l:?}, {u:?})"
        );
    }
    Ok(())
}

// E3: extreme finite bounds construct and impute within bounds
#[test]
fn test_impute_extreme_bounds() -> Fallible<()> {
    macro_rules! extreme {
        ($ty:ident) => {{
            let (max, min_pos) = ($ty::MAX, $ty::MIN_POSITIVE);
            let tiny = min_pos * $ty::EPSILON;
            extreme_bounds::<$ty>(&[
                (-max, max),
                (-max, 0.0),
                (max / 2.0, max),
                (min_pos, 2.0 * min_pos),
                (tiny, 3.0 * tiny),
                (-tiny, tiny),
                (0.0, tiny),
            ])
        }};
    }
    extreme!(f32)?;
    extreme!(f64)?;
    // adjacent values at the top of the range are only affordable for f32
    extreme_bounds(&[
        (-f32::MAX, (-f32::MAX).next_up()),
        (f32::MAX.next_down(), f32::MAX),
    ])
}

fn infinite_bounds<T: ImputeAtom>() -> Fallible<()> {
    let (zero, inf, nan) = (
        <T as num::Zero>::zero(),
        <T as num::Float>::infinity(),
        <T as num::Float>::nan(),
    );
    for bounds in [(-inf, zero), (zero, inf), (-inf, inf)] {
        let t = make_impute_uniform_float(VectorDomain::default(), SymmetricDistance, bounds)?;
        // data without NaN passes through
        let x = vec![zero, inf, -inf];
        assert_eq!(keys(&t.invoke(&x)?), keys(&x));
        // the first NaN panics, instead of an error at construction
        let result =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| t.invoke(&vec![nan])));
        assert!(
            result.is_err(),
            "expected imputing with {bounds:?} to panic, got {result:?}"
        );
    }
    Ok(())
}

// E4: FINDING: infinite bounds are accepted by the constructor,
// but imputing any NaN then panics in `Uniform::new` ("non-finite boundaries").
#[test]
fn test_impute_infinite_bounds_panic() -> Fallible<()> {
    infinite_bounds::<f32>()?;
    infinite_bounds::<f64>()
}

// E5: huge sizes are kept in the output domain, and the map doesn't depend on them
#[test]
fn test_impute_huge_sizes() -> Fallible<()> {
    for size in [u32::MAX as usize, usize::MAX] {
        let t = make_impute_uniform_float(
            VectorDomain::new(AtomDomain::<f64>::default()).with_size(size),
            ChangeOneDistance,
            (0.0, 1.0),
        )?;
        assert_eq!(t.output_domain.size, Some(size));
        assert_eq!(t.map(&u32::MAX)?, u32::MAX);
    }
    Ok(())
}

/// Imputes one NaN between adjacent f64 values. `Uniform::new` then loops about 2^51 times.
/// Ignored, because it doesn't finish. Run by [`test_impute_adjacent_bounds_hang`].
#[test]
#[ignore]
fn probe_impute_adjacent_bounds() {
    let _ = impute_f64((1.0, 1.0f64.next_up()))
        .unwrap()
        .invoke(&vec![f64::NAN]);
}

// FINDING: narrow f64 bounds are accepted by the constructor, but each imputed row then takes
// time proportional to max(|lower|, |upper|) / (upper - lower) inside `Uniform::new`.
// Adjacent values never finish, and wider bounds are still slow per row:
// (1, 1 + 1e-10) takes about 2 s per row, and a one-second window at a Unix timestamp
// (1.7e9, 1.7e9 + 1) about 250 ms per row, in release builds.
// The probe runs in a child process, since it hangs.
#[test]
fn test_impute_adjacent_bounds_hang() {
    let result = run_ignored_test(
        "transformations::impute::test_props::probe_impute_adjacent_bounds",
        std::time::Duration::from_secs(10),
    );
    assert!(
        result.is_none(),
        "expected the probe to hang, but it finished: {result:?}"
    );
}
