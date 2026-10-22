//! Verification of the discrete Laplace threshold privacy map.
//!
//! The map bounds the privacy loss of releasing a noisy map with thresholding. On integer maps
//! within `(l0, l1, li)`, with `Δ1 = min(⌊l1⌋, ⌊li⌋ l0)` and `Δ∞ = min(⌊li⌋, Δ1)`, the release
//! is `(ε, δ)`-close for `ε >= Δ1 / s` (the Laplace mechanism on the keys both maps hold) and
//! `δ >= 1 - (1 - Pr[Z > T - Δ∞])^l0` (the keys only one map holds, each released when its noisy
//! value, at most `Δ∞ + Z`, exceeds the threshold `T`). This is cited (`laplace_threshold_mechanism`).
use creusot_std::{
    logic::{Int, real::Real},
    prelude::*,
};
use dashu::{integer::UBig, rational::RBig};

use std::collections::HashMap;

use crate::{
    core::{Measurement, PrivacyMap},
    domains::{AtomDomain, MapDomain},
    measurements::{DiscreteLaplace, MakeNoiseThreshold, ZExpFamily, laplace_bound},
    measures::{Approximate, MaxDivergence},
    metrics::{AbsoluteDistance, L01InfDistance},
    verification::privacy::m_valid,
    verification::{RealModel, float::FloatModel, privacy::noise_threshold_map_private},
};

/// `Pr[Z > t]` for `Z` discrete Laplace with scale `s > 0`
/// (`verification/lean/OpenDPVerification/Threshold.lean`, `tailGt`).
#[logic(opaque)]
pub fn dlap_tail_gt(_s: Real, _t: Int) -> Real {
    dead
}

/// `Pr[C > t]` for `C` continuous Laplace with scale `s > 0`, `e^{-t/s} / 2` for `t >= 0`.
#[logic(opaque)]
pub fn clap_tail_gt(_s: Real, _t: Real) -> Real {
    dead
}

/// The continuous tail bounds the discrete one, and both are probabilities.
///
/// Trusted, proved in Lean (`OpenDP.Threshold.continuous_ge_discrete`): for `t >= 0`,
/// `Pr[Z > t] = e^{-t/s} e^{-1/s} / (1 + e^{-1/s}) <= e^{-t/s} / 2`.
#[trusted]
#[logic(opaque)]
#[ensures(result)]
#[ensures(forall<s: Real, t: Int> s > Real::from_int(0) && t >= 0 ==>
    clap_tail_gt(s, Real::from_int(t)) >= dlap_tail_gt(s, t))]
#[ensures(forall<s: Real, t: Int> dlap_tail_gt(s, t) >= Real::from_int(0))]
#[ensures(forall<s: Real, t: Real> clap_tail_gt(s, t) >= Real::from_int(0))]
pub fn tail_facts() -> bool {
    dead
}

/// `x^n` for `n >= 0`.
#[logic(open)]
#[variant(n)]
pub fn rpow(x: Real, n: Int) -> Real {
    pearlite! { if n <= 0 { Real::from_int(1) } else { x * rpow(x, n - 1) } }
}

/// `n` is the floor of `x`.
#[logic(open)]
pub fn is_floor(n: Int, x: Real) -> bool {
    pearlite! { Real::from_int(n) <= x && x < Real::from_int(n + 1) }
}

/// The floor is unique.
#[logic]
#[requires(is_floor(n, x) && is_floor(m, x))]
#[ensures(n == m)]
pub fn floor_unique(n: Int, m: Int, x: Real) {
    pearlite! {
        proof_assert!(Real::from_int(n) < Real::from_int(m + 1) && Real::from_int(m) < Real::from_int(n + 1));
    }
}

/// The smaller of two integers.
#[logic(open)]
pub fn imin(a: Int, b: Int) -> Int {
    pearlite! { if a <= b { a } else { b } }
}

/// `(eps, delta)` bounds the privacy loss of the discrete Laplace threshold mechanism with scale
/// `s` and threshold magnitude `t`, on integer maps within `(l0, l1, li)`.
#[logic(open)]
pub fn threshold_bound(l0: Int, l1: Real, li: Real, s: Real, t: Int, eps: f64, delta: f64) -> bool {
    pearlite! {
        l1 >= Real::from_int(0) && li >= Real::from_int(0)
        && forall<n1: Int, ni: Int> is_floor(n1, l1) && is_floor(ni, li) ==> {
            let d1 = imin(n1, ni * l0);
            let di = imin(ni, d1);
            // identical releases
            (d1 == 0 && eps.finite() && eps.real() == Real::from_int(0)
                && delta.finite() && delta.real() == Real::from_int(0))
            // the Laplace mechanism on the stable keys, and the unstable keys
            || (d1 > 0 && laplace_bound(Real::from_int(d1), s, eps) && delta.finite()
                && (delta.real() >= Real::from_int(1)
                    || (s > Real::from_int(0) && di <= t && exists<ds: Real>
                        dlap_tail_gt(s, t - di) <= ds && ds <= Real::from_int(1)
                        && delta.real() >= Real::from_int(1) - rpow(Real::from_int(1) - ds, l0))))
        }
    }
}

/// Introduces `threshold_bound` for a positive sensitivity and scale, from the floors `n1`, `ni`
/// of `l1`, `li`, and a tail bound `ds`.
#[logic]
#[requires(l1 >= Real::from_int(0) && li >= Real::from_int(0) && is_floor(n1, l1) && is_floor(ni, li))]
#[requires(d1 == imin(n1, ni * l0) && di == imin(ni, d1) && d1 > 0)]
#[requires(laplace_bound(Real::from_int(d1), s, eps) && s > Real::from_int(0) && di <= t && delta.finite())]
#[requires(dlap_tail_gt(s, t - di) <= ds && ds <= Real::from_int(1))]
#[requires(delta.real() >= Real::from_int(1)
    || delta.real() >= Real::from_int(1) - rpow(Real::from_int(1) - ds, l0))]
#[ensures(result && threshold_bound(l0, l1, li, s, t, eps, delta))]
pub fn bound_intro(
    l0: Int,
    l1: Real,
    li: Real,
    s: Real,
    t: Int,
    eps: f64,
    delta: f64,
    n1: Int,
    ni: Int,
    d1: Int,
    di: Int,
    ds: Real,
) -> bool {
    pearlite! {
        proof_assert!(forall<m1: Int, mi: Int> is_floor(m1, l1) && is_floor(mi, li) ==> {
            floor_unique(m1, n1, l1);
            floor_unique(mi, ni, li);
            m1 == n1 && mi == ni
        });
        true
    }
}

/// The discrete Laplace threshold mechanism: a privacy map bounding the privacy loss as in
/// `threshold_bound` meets the Proof Definition of `NoiseThresholdPrivacyMap` for `ZExpFamily<1>`.
///
/// Trusted (cited, Kind C): Rogers (2023), Theorem 7, as adapted in OpenDP's
/// `NoiseThresholdPrivacyMap_for_ZExpFamily1`, with the release rule `v + Z > T`. Keys held by both
/// maps are released like the vector Laplace mechanism on their values, with L1 sensitivity
/// `Δ1` (`laplace_mechanism`, proved in Lean). Each of the at most `l0` keys held by only one map
/// has a value of magnitude at most `Δ∞`, so it is released with probability at most
/// `Pr[Z > T - Δ∞]`, and none is released with probability at least `(1 - Pr[Z > T - Δ∞])^l0`.
/// Integer maps within `(l0, l1, li)` are within `(l0, ⌊l1⌋, ⌊li⌋)`, and within `Δ1` in L1 and
/// `Δ∞` in L∞.
#[trusted]
#[logic(opaque)]
#[requires(rv.scale.deep_model() >= Real::from_int(0))]
#[requires(forall<d: (u32, RBig, RBig), o: (f64, f64)> map.post()[d][Ok(o)] ==>
    threshold_bound(d.0@, d.1.deep_model(), d.2.deep_model(), rv.scale.deep_model(), t.deep_model(), o.0, o.1))]
#[ensures(result && noise_threshold_map_private(rv, map, t.deep_model()))]
pub fn laplace_threshold_mechanism(
    rv: ZExpFamily<1>,
    map: PrivacyMap<L01InfDistance<AbsoluteDistance<RBig>>, Approximate<MaxDivergence>>,
    t: UBig,
) -> bool {
    dead
}

/// `make_laplace_threshold` on `f64` counts keyed by `String` returns valid measurements.
#[logic]
#[requires(<DiscreteLaplace as MakeNoiseThreshold<MapDomain<AtomDomain<String>, AtomDomain<f64>>, L01InfDistance<AbsoluteDistance<f64>>, Approximate<MaxDivergence>>>::noise_threshold_claim(m))]
#[ensures(m_valid(m))]
pub fn make_laplace_threshold_f64_valid(
    m: Measurement<
        MapDomain<AtomDomain<String>, AtomDomain<f64>>,
        L01InfDistance<AbsoluteDistance<f64>>,
        Approximate<MaxDivergence>,
        HashMap<String, f64>,
    >,
) {
}

/// `make_laplace_threshold` on `i32` counts keyed by `String` returns valid measurements.
#[logic]
#[requires(<DiscreteLaplace as MakeNoiseThreshold<MapDomain<AtomDomain<String>, AtomDomain<i32>>, L01InfDistance<AbsoluteDistance<i32>>, Approximate<MaxDivergence>>>::noise_threshold_claim(m))]
#[ensures(m_valid(m))]
pub fn make_laplace_threshold_i32_valid(
    m: Measurement<
        MapDomain<AtomDomain<String>, AtomDomain<i32>>,
        L01InfDistance<AbsoluteDistance<i32>>,
        Approximate<MaxDivergence>,
        HashMap<String, i32>,
    >,
) {
}
