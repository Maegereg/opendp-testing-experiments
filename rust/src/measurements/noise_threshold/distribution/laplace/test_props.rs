//! Property-based tests for `make_laplace_threshold`.
//!
//! The mechanism maps each value to an integer index `z` (see [`NoiseAtom::shift`]),
//! adds discrete Laplace noise to `z`, keeps the key iff the noisy index passes the threshold
//! (`≥ T`, or `≤ T` for a negative integer threshold), and maps kept indices back into the atomic type.
//! The privacy map is checked against exact references: ε against `l1 / scale`,
//! and δ against the probability that a key present in only one dataset is released.
//!
//! Properties (labels match the comments below):
//! * A: the constructor and privacy map accept exactly the valid arguments
//! * B: released keys come from the input and pass the threshold, on the granularity grid
//! * C: the privacy map: ε exactly, δ against the intended formula, monotonicity,
//!   and exact divergence on single-key neighbors
//! * D: noise, release probabilities and independence (statistical)
//! * E: large maps, extreme values, distances and scales
//!
//! FINDING (F1): δ is computed from `P[Z > T - l∞]`, but a key is released when `v + Z ≥ T`,
//! so the δ needed is `P[Z ≥ T - l∞]`, larger by a factor of `e^{1/scale}`.
//! The privacy map therefore underestimates δ, and the measurement isn't (ε, δ)-DP for the δ it claims.
//! Tests marked FINDING pin this, and flip when it's fixed.
//!
//! FINDING (F2): a float threshold is rounded to the nearest multiple of `2^k`,
//! so values below the threshold can be released.

use std::collections::HashMap;
use std::fmt::Debug;

use dashu::integer::IBig;
use dashu::rational::RBig;
use proptest::prelude::*;

use super::make_laplace_threshold;
use crate::core::Measurement;
use crate::domains::{AtomDomain, MapDomain};
use crate::error::Fallible;
use crate::measures::{Approximate, MaxDivergence};
use crate::metrics::{AbsoluteDistance, L0PInfDistance, L01InfDistance};
use crate::test_props::noise::*;
use crate::test_props::*;
use crate::traits::InfCast;
use crate::traits::samplers::test::check_chi_square_from_probs;

type Meas<T, Q> = Measurement<
    MapDomain<AtomDomain<u32>, AtomDomain<T>>,
    L01InfDistance<AbsoluteDistance<Q>>,
    Approximate<MaxDivergence>,
    HashMap<u32, T>,
>;

/// Value types that can be thresholded, with the distance type of their input metric.
trait ThresholdAtom: NoiseAtom {
    /// The distance type: `f64` for primitives, so exact distances can be rounded up into it.
    type Q: Clone + Debug + 'static;
    /// Floats: the threshold is rounded to the grid, and must be finite and non-negative.
    const FLOAT: bool;

    fn make(
        nan: bool,
        scale: f64,
        threshold: Self,
        k: Option<i32>,
    ) -> Fallible<Meas<Self, Self::Q>>;
    /// The smallest distance at least `x`, if there is one.
    fn q_up(x: &RBig) -> Option<Self::Q>;
    /// The exact value of a distance, or `None` if it isn't finite.
    fn q_exact(q: &Self::Q) -> Option<RBig>;
    /// Arbitrary distances, valid or not.
    fn q_arb() -> BoxedStrategy<Self::Q>;
    /// Thresholds, valid or not, at granularity `2^k`.
    fn threshold(k: i32) -> BoxedStrategy<Self>;
    /// Whether the threshold keeps values at or below it (a negative integer threshold).
    fn keeps_below(&self) -> bool;
    /// Whether the sign bit is set (for floats, including `-0.0`), or the integer is negative.
    fn sign_negative(&self) -> bool {
        self.keeps_below()
    }
}

fn f64_distances() -> BoxedStrategy<f64> {
    prop_oneof![
        3 => (0u32..40).prop_map(f64::from),
        2 => 0f64..40.,
        1 => prop::sample::select(vec![
            0.0, -0.0, 0.5, u32::MAX as f64, 1e300, f64::MAX, -1.0, f64::INFINITY, f64::NAN
        ]),
    ]
    .boxed()
}

macro_rules! impl_threshold_atom_int {
    ($($ty:ty)+) => {$(
        impl ThresholdAtom for $ty {
            type Q = f64;
            const FLOAT: bool = false;
            fn make(nan: bool, scale: f64, threshold: Self, k: Option<i32>) -> Fallible<Meas<Self, f64>> {
                make_laplace_threshold(
                    MapDomain::new(AtomDomain::default(), Self::element_domain(nan)),
                    L0PInfDistance(AbsoluteDistance::default()),
                    scale,
                    threshold,
                    k,
                )
            }
            fn q_up(x: &RBig) -> Option<f64> {
                f64::inf_cast(x.clone()).ok()
            }
            fn q_exact(q: &f64) -> Option<RBig> {
                rat(*q)
            }
            fn q_arb() -> BoxedStrategy<f64> {
                f64_distances()
            }
            fn threshold(_k: i32) -> BoxedStrategy<Self> {
                prop_oneof![
                    3 => (0i64..30).prop_map(|t| from_big(clamp_big::<$ty>(IBig::from(t))).unwrap()),
                    1 => (-30i64..0).prop_map(|t| from_big(clamp_big::<$ty>(IBig::from(t))).unwrap()),
                    2 => int_value::<$ty>(),
                ]
                .boxed()
            }
            fn keeps_below(&self) -> bool {
                big(*self) < IBig::ZERO
            }
        }
    )+};
}
impl_threshold_atom_int!(u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize);

impl ThresholdAtom for IBig {
    type Q = RBig;
    const FLOAT: bool = false;
    fn make(nan: bool, scale: f64, threshold: Self, k: Option<i32>) -> Fallible<Meas<Self, RBig>> {
        make_laplace_threshold(
            MapDomain::new(AtomDomain::default(), Self::element_domain(nan)),
            L0PInfDistance(AbsoluteDistance::default()),
            scale,
            threshold,
            k,
        )
    }
    fn q_up(x: &RBig) -> Option<RBig> {
        Some(x.clone())
    }
    fn q_exact(q: &RBig) -> Option<RBig> {
        Some(q.clone())
    }
    fn q_arb() -> BoxedStrategy<RBig> {
        prop_oneof![
            (0u32..40).prop_map(RBig::from),
            (-3i64..80, 1u8..4).prop_map(|(n, d)| RBig::from_parts(n.into(), d.into())),
        ]
        .boxed()
    }
    fn threshold(_k: i32) -> BoxedStrategy<Self> {
        prop_oneof![
            3 => (0i64..30).prop_map(IBig::from),
            1 => (-30i64..0).prop_map(IBig::from),
            1 => Self::value(0),
        ]
        .boxed()
    }
    fn keeps_below(&self) -> bool {
        *self < IBig::ZERO
    }
}

macro_rules! impl_threshold_atom_float {
    ($($ty:ident)+) => {$(
        impl ThresholdAtom for $ty {
            type Q = f64;
            const FLOAT: bool = true;
            fn make(nan: bool, scale: f64, threshold: Self, k: Option<i32>) -> Fallible<Meas<Self, f64>> {
                make_laplace_threshold(
                    MapDomain::new(AtomDomain::default(), Self::element_domain(nan)),
                    L0PInfDistance(AbsoluteDistance::default()),
                    scale,
                    threshold,
                    k,
                )
            }
            fn q_up(x: &RBig) -> Option<f64> {
                f64::inf_cast(x.clone()).ok()
            }
            fn q_exact(q: &f64) -> Option<RBig> {
                rat(*q)
            }
            fn q_arb() -> BoxedStrategy<f64> {
                f64_distances()
            }
            fn threshold(k: i32) -> BoxedStrategy<Self> {
                let on_grid = move |t: i64| <$ty as NoiseAtom>::release(&IBig::from(t), k);
                prop_oneof![
                    3 => (0i64..30).prop_map(on_grid),
                    2 => (0.0..30.0 as $ty),
                    1 => float_value::<$ty>(),
                    1 => prop::sample::select(vec![0.0, -0.0, -1.0, $ty::INFINITY, $ty::NAN]),
                ]
                .boxed()
            }
            fn keeps_below(&self) -> bool {
                false
            }
            fn sign_negative(&self) -> bool {
                self.is_sign_negative()
            }
        }
    )+};
}
impl_threshold_atom_float!(f32 f64);

// ---------------------------------------------------------------------------------------------
// Generators
// ---------------------------------------------------------------------------------------------

/// Constructor arguments, two neighboring maps, and extra distances to probe the map with.
#[derive(Debug, Clone)]
struct Case<T: ThresholdAtom> {
    /// whether the value domain may contain NaN (rejected for floats)
    nan: bool,
    scale: f64,
    k: Option<i32>,
    threshold: T,
    data: HashMap<u32, T>,
    other: HashMap<u32, T>,
    distances: Vec<(u32, T::Q, T::Q)>,
}

/// A granularity exponent safe to compute with: `k` if the type accepts it, otherwise `k_min`.
fn k_safe<T: ThresholdAtom>(k: Option<i32>) -> i32 {
    let k = T::k_eff(k);
    if T::FLOAT && k != i32::MIN && k >= T::k_min() && k <= 1100 {
        k
    } else {
        T::k_min()
    }
}

/// Values on the grid within a few steps of the threshold, or arbitrary values.
fn values<T: ThresholdAtom>(threshold: T, k: i32) -> BoxedStrategy<T> {
    // a NaN threshold is rejected at construction, so any values will do
    let t = if threshold.is_nan() {
        IBig::ZERO
    } else {
        threshold.shift(k)
    };
    // the direction values must move in to pass the threshold
    let toward = if threshold.keeps_below() { -1 } else { 1 };
    prop_oneof![
        2 => (-4i64..=4).prop_map({
            let t = t.clone();
            move |d| T::release(&(t.clone() + IBig::from(d)), k)
        }),
        // far past the threshold, so almost always released
        1 => (20i64..40).prop_map(move |d| T::release(&(t.clone() + IBig::from(d * toward)), k)),
        2 => T::value(k),
    ]
    .boxed()
}

fn case<T: ThresholdAtom>() -> impl Strategy<Value = Case<T>> {
    (
        prop_oneof![9 => Just(false), 1 => Just(T::HAS_NAN)],
        noise::scale(),
        T::granularity(),
    )
        .prop_flat_map(|(nan, scale, k)| {
            let ks = k_safe::<T>(k);
            T::threshold(ks).prop_flat_map(move |threshold| {
                let value = values(threshold.clone(), ks);
                let maps = prop_oneof![
                    29 => map_neighbors(value.clone(), 12).boxed(),
                    // a large map: many keys repeating a short pattern of values
                    1 => (prop::collection::vec(value.clone(), 1..8), 10_000u32..50_000)
                        .prop_map(|(pattern, n)| {
                            let x: HashMap<u32, T> =
                                (0..n).map(|i| (i, pattern[i as usize % pattern.len()].clone())).collect();
                            let mut x2 = x.clone();
                            x2.remove(&0);
                            (x, x2)
                        })
                        .boxed(),
                ];
                (
                    Just(threshold),
                    maps,
                    prop::collection::vec((0u32..5, T::q_arb(), T::q_arb()), 0..4),
                )
                    .prop_map(move |(threshold, (data, other), distances)| Case {
                        nan,
                        scale,
                        k,
                        threshold,
                        data,
                        other,
                        distances,
                    })
            })
        })
}

// ---------------------------------------------------------------------------------------------
// References
// ---------------------------------------------------------------------------------------------

/// The reference for when construction succeeds.
fn valid<T: ThresholdAtom>(case: &Case<T>) -> bool {
    if !(case.scale.is_finite() && case.scale >= 0.0) {
        return false;
    }
    if !T::FLOAT {
        return case.k.unwrap_or(0) == 0;
    }
    let k = T::k_eff(case.k);
    k != i32::MIN
        && k >= T::k_min()
        && !case.nan
        && case.threshold.exact().is_some()
        // the check is on the sign bit, so `-0.0` is rejected too
        && !case.threshold.sign_negative()
}

/// What the privacy map should return for `d_in`.
#[derive(Debug)]
enum Expect {
    /// an error
    Err,
    /// `(0, 0)`: nothing differs once sensitivities are tightened
    Zero,
    /// `(∞, 1)`: no noise
    NoNoise,
    /// ε is `eps` rounded up, and δ comes from `l0` keys at distance `d` from instability;
    /// computing the tail bound may fail with an error, for extreme arguments
    Value {
        eps: RBig,
        d: IBig,
        l0: u32,
        scale: RBig,
    },
}

fn expect_map<T: ThresholdAtom>(case: &Case<T>, (l0, l1, li): &(u32, T::Q, T::Q)) -> Expect {
    let k = T::k_eff(case.k);
    let (Some(mut l1), Some(mut li)) = (T::q_exact(l1), T::q_exact(li)) else {
        return Expect::Err;
    };
    let t_int = case.threshold.shift(k);
    let t_mag = if t_int < IBig::ZERO { -t_int } else { t_int };
    if T::FLOAT {
        if li > case.threshold.exact().unwrap() {
            return Expect::Err;
        }
        // rounding to the grid can move each value by up to 2^k - 2^k_min
        let round = pow2(k) - pow2(T::k_min());
        l1 = mul_2k(&(l1 + round.clone() * RBig::from(*l0)), -k);
        li = mul_2k(&(li + round), -k);
    }
    let (l1, li) = (l1.floor(), li.floor());
    if l1 < IBig::ZERO || li < IBig::ZERO {
        return Expect::Err;
    }
    let l1 = l1.min(li.clone() * IBig::from(*l0));
    let li = li.min(l1.clone());
    if l1 == IBig::ZERO {
        return Expect::Zero;
    }
    if case.scale == 0.0 {
        return Expect::NoNoise;
    }
    if li > t_mag {
        return Expect::Err;
    }
    let scale = mul_2k(&rat(case.scale).unwrap(), -k);
    Expect::Value {
        eps: RBig::from(l1) / scale.clone(),
        d: t_mag - li,
        l0: *l0,
        scale,
    }
}

fn to_f64(x: &RBig) -> f64 {
    f64::inf_cast(x.clone()).unwrap_or(f64::INFINITY)
}

/// Whether the released index `z` passes the threshold index `t`.
fn passes(z: &IBig, t: &IBig) -> bool {
    if *t < IBig::ZERO { z <= t } else { z >= t }
}

// ---------------------------------------------------------------------------------------------
// Properties
// ---------------------------------------------------------------------------------------------

fn check<T: ThresholdAtom>(case: Case<T>) -> TestResult {
    // A: construction succeeds exactly when the arguments are valid
    let m = T::make(case.nan, case.scale, case.threshold.clone(), case.k);
    prop_assert_eq!(
        m.is_ok(),
        valid(&case),
        "construction: {:?}",
        m.as_ref().err()
    );
    let Ok(m) = m else {
        return Ok(());
    };
    let k = T::k_eff(case.k);
    let t_int = case.threshold.shift(k);

    // A: the output space
    prop_assert!(
        m.input_domain == MapDomain::new(AtomDomain::default(), T::element_domain(case.nan))
    );

    // A, C: the privacy map, on the exact distance between the maps and on extra probes
    let mut probes = case.distances.clone();
    if let Some((l0, l1, li)) = map_distance_exact(&case.data, &case.other)
        && let (Some(l1), Some(li)) = (T::q_up(&l1), T::q_up(&li))
    {
        probes.push((l0 as u32, l1, li));
    }
    for d_in in &probes {
        let expected = expect_map(&case, d_in);
        let actual = m.map(d_in);
        match (&expected, actual) {
            (Expect::Err, actual) => prop_assert!(
                actual.is_err(),
                "map({d_in:?}) = {actual:?}, expected an error"
            ),
            (Expect::Zero, actual) => prop_assert_eq!(ok(actual)?, (0.0, 0.0), "map({:?})", d_in),
            (Expect::NoNoise, actual) => {
                prop_assert_eq!(ok(actual)?, (f64::INFINITY, 1.0), "map({:?})", d_in)
            }
            (Expect::Value { eps, d, l0, scale }, actual) => {
                let Ok((e, delta)) = actual else {
                    // A: only the tail bounds or ε may fail to compute, for extreme arguments
                    let msg = format!("{:?}", actual.unwrap_err());
                    prop_assert!(
                        msg.contains("tail bound")
                            || msg.contains("overflow")
                            || msg.contains("finite"),
                        "map({d_in:?}) failed: {msg}"
                    );
                    continue;
                };
                // C: ε is l1 / scale, rounded up
                prop_assert!(
                    is_rounded_up(e, eps),
                    "map({:?}): ε = {}, exact {}",
                    d_in,
                    e,
                    eps
                );
                // A: δ is a probability
                prop_assert!(
                    (0.0..=1.0).contains(&delta),
                    "map({:?}): δ = {}",
                    d_in,
                    delta
                );
                // C: δ bounds the probability that any of l0 keys at distance d from instability
                // crosses it, as the code intends: P[Z > d] per key
                let s = to_f64(scale);
                if (1e-300..1e300).contains(&s) {
                    let d = to_f64(&RBig::from(d.clone()));
                    let intended = any_of(discrete_laplace_tail_ge(s, d + 1.0), *l0 as f64);
                    prop_assert!(
                        delta >= intended * (1.0 - 1e-9),
                        "map({:?}): δ = {} < {}",
                        d_in,
                        delta,
                        intended
                    );
                }
                // C: monotone in each of l0, l1 and l∞
                for bumped in bump::<T>(d_in) {
                    if let Ok((e2, delta2)) = m.map(&bumped) {
                        prop_assert!(
                            e2 >= e && delta2 >= delta,
                            "map isn't monotone: {:?} -> {:?}",
                            d_in,
                            bumped
                        );
                    }
                }
            }
        }
    }

    // B: the function
    for x in [&case.data, &case.other] {
        let out = ok(m.invoke(x))?;
        for (key, released) in &out {
            // B: released keys come from the input
            let original = x.get(key);
            prop_assert!(
                original.is_some(),
                "released key {} isn't in the input",
                key
            );
            let original = original.unwrap();
            if released.is_nan() {
                return Err(TestCaseError::fail(format!("released NaN for {key}")));
            }
            // B: released values are on the grid (or saturated), so releasing them again is the identity
            prop_assert!(
                released.exact().is_none() || T::release(&released.shift(k), k).same(released),
                "released {:?} isn't on the grid 2^{}",
                released,
                k
            );
            // B: released values pass the (rounded) threshold, and integer saturation never wraps
            let threshold_value = T::release(&t_int, k);
            let ok_side = if case.threshold.keeps_below() {
                released.exact() <= threshold_value.exact()
            } else {
                released
                    .exact()
                    .is_none_or(|r| threshold_value.exact().is_some_and(|t| r >= t))
            };
            prop_assert!(
                ok_side,
                "released {:?} doesn't pass threshold {:?}",
                released,
                case.threshold
            );
            // B: without noise, the release is the input on the grid
            if case.scale == 0.0 {
                prop_assert!(T::release(&original.shift(k), k).same(released));
            }
        }
        if case.scale == 0.0 {
            // B: without noise, exactly the passing keys are released
            let expected = x
                .iter()
                .filter(|(_, v)| passes(&v.shift(k), &t_int))
                .count();
            prop_assert_eq!(out.len(), expected);
        }
    }
    Ok(())
}

/// `d_in` with each of `l0`, `l1` and `l∞` increased by one, where representable.
fn bump<T: ThresholdAtom>((l0, l1, li): &(u32, T::Q, T::Q)) -> Vec<(u32, T::Q, T::Q)> {
    let (Some(e1), Some(ei)) = (T::q_exact(l1), T::q_exact(li)) else {
        return vec![];
    };
    let mut out = vec![];
    if let Some(l0) = l0.checked_add(1) {
        out.push((l0, l1.clone(), li.clone()));
    }
    if let Some(l1) = T::q_up(&(e1 + RBig::ONE)) {
        out.push((*l0, l1, li.clone()));
    }
    if let Some(li) = T::q_up(&(ei + RBig::ONE)) {
        out.push((*l0, l1.clone(), li));
    }
    out
}

for_each_int!(ints, case, check);
for_each_float!(floats, case, check);

proptest! {
    #[test]
    fn prop_ibig(case in case::<IBig>()) {
        check(case)?;
    }
}

// ---------------------------------------------------------------------------------------------
// C: exact divergence on single-key neighbors
// ---------------------------------------------------------------------------------------------

fn i64_threshold(scale: f64, threshold: i64) -> Meas<i64, f64> {
    i64::make(false, scale, threshold, None).unwrap()
}

proptest! {
    // C: for a key present in both maps, at counts v and w, the exact divergence between
    // their outputs is within the claimed (ε, δ), in both directions
    #[test]
    fn prop_single_key_divergence(
        scale in 0.3f64..20.,
        // the counts differ by at most the threshold, which the map requires
        (threshold, v, w) in (1i64..30, -40i64..40)
            .prop_flat_map(|(t, v)| (Just(t), Just(v), v - t..=v + t)),
    ) {
        let li = (v - w).abs();
        let m = i64_threshold(scale, threshold);
        let (eps, delta) = ok(m.map(&(1, li as f64, li as f64)))?;
        for (p, q) in [(v, w), (w, v)] {
            let (_, upper) = single_key_hockey_stick(scale, Some(p), Some(q), threshold, eps);
            prop_assert!(upper <= delta + 1e-9, "divergence {} > δ {} at ε {}", upper, delta, eps);
        }
    }

    // FINDING (F1): for a key present in only one map, with count v ≤ T, the exact divergence
    // is the probability that it's released, P[Z ≥ T - v], which exceeds the claimed δ
    #[test]
    fn prop_finding_absent_key_exceeds_delta(
        // P[Z ≥ T - v] = α^(T - v) / (1 + α) is at least about 1e-12 when T - v ≤ 27 scale,
        // and below about 1e-16 δ is dominated by its conservative rounding in f64
        (scale, threshold, v_offset) in (0.3f64..20., 1i64..30).prop_flat_map(|(s, t)| {
            let max_offset = ((27.0 * s) as i64).min(t - 1);
            (Just(s), Just(t), 0..=max_offset)
        }),
    ) {
        let v = threshold - v_offset;
        let m = i64_threshold(scale, threshold);
        let (eps, delta) = ok(m.map(&(1, v as f64, v as f64)))?;
        let (lower, _) = single_key_hockey_stick(scale, Some(v), None, threshold, eps);
        prop_assert!(lower > delta, "expected the divergence {} to exceed δ {}", lower, delta);
        // ... by exactly one step of the noise distribution: δ is P[Z > T - v]
        let intended = discrete_laplace_tail_ge(scale, (threshold - v + 1) as f64);
        prop_assert!((delta - intended).abs() <= 1e-9 * intended.max(1e-300) + 1e-15);
    }
}

// FINDING (F1): the minimal case. With scale 1 and threshold 1, the map claims δ = P[Z > 0],
// but the empty map never releases `a` while `{a: 1}` releases it with probability P[Z ≥ 0].
#[test]
fn test_finding_delta_off_by_one() -> Fallible<()> {
    let m = i64_threshold(1.0, 1);
    let (eps, delta) = m.map(&(1, 1.0, 1.0))?;
    let a = (-1.0f64).exp();
    assert_eq!(eps, 1.0);
    assert!((delta - a / (1.0 + a)).abs() < 1e-12, "δ = {delta}");
    let released = 1.0 / (1.0 + a);
    assert!(
        released > 2.0 * delta,
        "P[release] = {released}, δ = {delta}"
    );
    // the float path has the same off-by-one
    let m = f64::make(false, 1.0, 1.0, Some(0))?;
    let (_, delta) = m.map(&(1, 1.0, 1.0))?;
    // rounding adds 1 - 2^k_min to l∞, which floors back to 1
    assert!((delta - a / (1.0 + a)).abs() < 1e-12, "δ = {delta}");
    Ok(())
}

// FINDING (F1), C: l0 keys at the threshold, against the empty map.
// The map's formula is otherwise exact: correcting the tail argument by one recovers the requirement.
#[test]
fn test_finding_several_absent_keys() -> Fallible<()> {
    for (scale, threshold, l0) in [(1.0, 3, 1), (2.0, 5, 3), (5.0, 10, 10)] {
        let m = i64_threshold(scale, threshold);
        let (_, delta) = m.map(&(l0, threshold as f64 * l0 as f64, threshold as f64))?;
        let required = any_of(discrete_laplace_tail_ge(scale, 0.0), l0 as f64);
        let intended = any_of(discrete_laplace_tail_ge(scale, 1.0), l0 as f64);
        assert!(delta < required, "δ = {delta} covers {required}");
        assert!(
            (delta - intended).abs() <= 1e-9 * intended,
            "δ = {delta}, intended {intended}"
        );
    }
    Ok(())
}

// ---------------------------------------------------------------------------------------------
// D. Randomness (statistical)
// ---------------------------------------------------------------------------------------------

/// The number of samples per statistical test. Each check fails spuriously with probability at most 1e-6.
const SAMPLES: usize = 20_000;

// D: released values far above the threshold are the count plus discrete Laplace noise,
// for integers and for floats in units of 2^k
#[test]
fn test_threshold_noise_distribution() -> Fallible<()> {
    let m = i64_threshold(3.0, 1);
    let x = HashMap::from([(0u32, 1000i64)]);
    let noise = (0..SAMPLES)
        .map(|_| Ok(IBig::from(m.invoke(&x)?[&0] - 1000)))
        .collect::<Fallible<Vec<_>>>()?;
    let (w, probs) = discrete_laplace_probs(3.0, SAMPLES);
    check_chi_square_from_probs(&histogram(&noise, w), &probs)?;

    // scale 0.75 at granularity 2^-2 is scale 3 in units of the granularity
    let m = f64::make(false, 0.75, 1.0, Some(-2))?;
    let x = HashMap::from([(0u32, 1000.0f64)]);
    let noise = (0..SAMPLES)
        .map(|_| Ok(m.invoke(&x)?[&0].shift(-2) - IBig::from(4000)))
        .collect::<Fallible<Vec<_>>>()?;
    check_chi_square_from_probs(&histogram(&noise, w), &probs)
}

// D: a key with count v is released with probability P[Z ≥ T - v], not P[Z > T - v]
#[test]
fn test_threshold_release_probability() -> Fallible<()> {
    let (scale, threshold) = (2.0, 5);
    let m = i64_threshold(scale, threshold);
    for v in threshold - 2..=threshold + 2 {
        let x = HashMap::from([(0u32, v)]);
        let mut released = 0u64;
        for _ in 0..SAMPLES {
            released += m.invoke(&x)?.contains_key(&0) as u64;
        }
        let p = discrete_laplace_tail_ge(scale, (threshold - v) as f64);
        check_chi_square_from_probs(&[released, SAMPLES as u64 - released], &[p, 1.0 - p])?;
    }
    Ok(())
}

// D: keys are released independently
#[test]
fn test_threshold_keys_independent() -> Fallible<()> {
    let (scale, threshold) = (2.0, 5);
    let m = i64_threshold(scale, threshold);
    let x = HashMap::from([(0u32, threshold), (1u32, threshold)]);
    let mut counts = [0u64; 4];
    for _ in 0..SAMPLES {
        let out = m.invoke(&x)?;
        counts[out.contains_key(&0) as usize * 2 + out.contains_key(&1) as usize] += 1;
    }
    let p = discrete_laplace_tail_ge(scale, 0.0);
    let q = 1.0 - p;
    check_chi_square_from_probs(&counts, &[q * q, q * p, p * q, p * p])
}

// ---------------------------------------------------------------------------------------------
// E. Large maps, extreme values, distances and scales
// ---------------------------------------------------------------------------------------------

// E: a map with 100,000 keys: every released key passes, and the map handles l0 = 100,000
#[test]
fn test_threshold_large_map() -> Fallible<()> {
    let start = std::time::Instant::now();
    let m = i64_threshold(2.0, 50);
    let x = (0..100_000u32)
        .map(|i| (i, (i % 100) as i64))
        .collect::<HashMap<_, _>>();
    let out = m.invoke(&x)?;
    assert!(out.iter().all(|(k, v)| x.contains_key(k) && *v >= 50));
    assert!(
        out.len() > 40_000 && out.len() < 60_000,
        "released {}",
        out.len()
    );
    let (_, delta) = m.map(&(100_000, 100_000.0, 1.0))?;
    assert!((0.0..=1.0).contains(&delta));
    assert!(start.elapsed() < std::time::Duration::from_secs(60));
    Ok(())
}

// E: counts near the limits of the type saturate rather than wrap,
// and thresholds at the limits convert exactly
#[test]
fn test_threshold_saturation() -> Fallible<()> {
    let m = u8::make(false, 10.0, 200, None)?;
    let x = HashMap::from([(0u32, 255u8)]);
    let outs = (0..2_000)
        .map(|_| m.invoke(&x))
        .collect::<Fallible<Vec<_>>>()?;
    assert!(outs.iter().all(|o| o.get(&0).is_none_or(|v| *v >= 200)));
    assert!(
        outs.iter().any(|o| o.get(&0) == Some(&255)),
        "expected saturation at 255"
    );

    // a negative threshold keeps values at or below it, saturating at MIN
    let m = i8::make(false, 10.0, -100, None)?;
    let x = HashMap::from([(0u32, -128i8)]);
    let outs = (0..2_000)
        .map(|_| m.invoke(&x))
        .collect::<Fallible<Vec<_>>>()?;
    assert!(outs.iter().all(|o| o.get(&0).is_none_or(|v| *v <= -100)));
    assert!(
        outs.iter().any(|o| o.get(&0) == Some(&-128)),
        "expected saturation at -128"
    );

    // thresholds at the limits: l∞ up to |T| is accepted, and above it isn't
    let m = u64::make(false, 1.0, u64::MAX, None)?;
    assert!(m.map(&(1, 1.0, 1.0)).is_ok());
    let m = i128::make(false, 1.0, i128::MIN, None)?;
    assert!(m.map(&(1, 1.0, 1.0)).is_ok());
    let m = i64_threshold(1.0, 10);
    assert!(m.map(&(1, 10.0, 10.0)).is_ok());
    assert!(m.map(&(1, 11.0, 11.0)).is_err());
    Ok(())
}

// E: huge l0 and l1 keep δ a probability, and never panic
#[test]
fn test_threshold_huge_distances() -> Fallible<()> {
    let m = i64_threshold(1.0, 1_000);
    for d_in in [
        (u32::MAX, 1.0, 1.0),
        (u32::MAX, 1e300, 1_000.0),
        (1, f64::MAX, 1.0),
    ] {
        if let Ok((eps, delta)) = m.map(&d_in) {
            assert!(
                eps >= 0.0 && (0.0..=1.0).contains(&delta),
                "{d_in:?}: ({eps}, {delta})"
            );
        }
    }
    Ok(())
}

// E: scale extremes: no noise gives (∞, 1); tiny and huge scales give a valid map or an error
#[test]
fn test_threshold_scale_extremes() -> Fallible<()> {
    let m = i64_threshold(0.0, 10);
    assert_eq!(m.map(&(1, 1.0, 1.0))?, (f64::INFINITY, 1.0));
    let x = HashMap::from([(0u32, 9i64), (1, 10), (2, 11)]);
    assert_eq!(m.invoke(&x)?, HashMap::from([(1u32, 10i64), (2, 11)]));
    for scale in [f64::from_bits(1), 1e-300, 1e300, f64::MAX] {
        let m = i64_threshold(scale, 10);
        if let Ok((eps, delta)) = m.map(&(1, 1.0, 1.0)) {
            assert!(
                eps >= 0.0 && (0.0..=1.0).contains(&delta),
                "scale {scale}: ({eps}, {delta})"
            );
        }
        let _ = m.invoke(&x)?;
    }
    Ok(())
}

// E: float values at the edges of the type, at the smallest and a large granularity
#[test]
fn test_threshold_float_extremes() -> Fallible<()> {
    let x = HashMap::from([(0u32, f64::MAX), (1, f64::from_bits(1)), (2, -f64::MAX)]);
    for k in [f64::K_MIN, 0, 1000] {
        let m = f64::make(false, 0.0, 0.0, Some(k))?;
        let out = m.invoke(&x)?;
        // without noise, the release is the value rounded to the grid
        for (key, v) in &out {
            assert!(f64::release(&x[key].shift(k), k).same(v), "k = {k}: {v}");
        }
        assert!(!out.contains_key(&2));
    }
    Ok(())
}

// FINDING (F2): a float threshold is rounded to the nearest multiple of 2^k,
// so values below the threshold can be released: here 1.0 with threshold 1.3
#[test]
fn test_finding_float_threshold_rounded() -> Fallible<()> {
    let m = f64::make(false, 0.0, 1.3, Some(0))?;
    let out = m.invoke(&HashMap::from([(0u32, 1.0f64)]))?;
    assert_eq!(out, HashMap::from([(0u32, 1.0)]));
    Ok(())
}

// Float thresholds must be non-negative and finite, including -0.0; integer thresholds may be negative
#[test]
fn test_threshold_sign_rules() {
    assert!(f64::make(false, 1.0, -0.0, None).is_err());
    assert!(f64::make(false, 1.0, -1.0, None).is_err());
    assert!(f64::make(false, 1.0, f64::INFINITY, None).is_err());
    assert!(f64::make(true, 1.0, 1.0, None).is_err());
    assert!(i64::make(false, 1.0, -1, None).is_ok());
}
