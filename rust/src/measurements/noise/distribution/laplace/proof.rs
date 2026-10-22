//! Verification of the discrete Laplace privacy map.
//!
//! The map returns `d_in / scale`, rounded up to `f64`, with `0` at `d_in = 0` and infinity when
//! `scale = 0`. That this bounds the privacy loss is the discrete Laplace mechanism theorem, which
//! is cited (`laplace_mechanism`).
use creusot_std::{logic::real::Real, prelude::*};
use dashu::rational::RBig;

use crate::{
    core::{Measurement, PrivacyMap},
    domains::{AtomDomain, VectorDomain},
    measurements::{DiscreteLaplace, MakeNoise, ZExpFamily},
    measures::MaxDivergence,
    metrics::{AbsoluteDistance, L1Distance},
    verification::{
        RealModel,
        float::FloatModel,
        privacy::{m_valid, noise_map_private},
    },
};

/// `o` bounds the privacy loss (max-divergence) of the discrete Laplace mechanism with scale `s`,
/// on inputs within L1 distance `d`: 0 if `d = 0`, at least `d / s` if `s > 0`, and infinite if
/// `s = 0`.
#[logic(open)]
pub fn laplace_bound(d: Real, s: Real, o: f64) -> bool {
    pearlite! {
        d >= Real::from_int(0) && (
            (d == Real::from_int(0) && o.real() == Real::from_int(0) && o.finite())
            || (s > Real::from_int(0) && o.real() >= d / s)
            || (s == Real::from_int(0) && o == f64::INFINITY))
    }
}

/// The discrete Laplace mechanism: a privacy map bounding the privacy loss as in `laplace_bound`
/// meets the Proof Definition of `NoisePrivacyMap` for `ZExpFamily<1>`.
///
/// Trusted (cited, Kind C): for integer vectors `x`, `x'` with `||x - x'||_1 <= d`, adding
/// independent discrete Laplace noise with scale `s > 0` to each coordinate gives outputs within
/// max-divergence `d / s` (Ghosh, Roughgarden and Sundararajan 2012; Canonne, Kamath and Steinke
/// 2020, as cited by OpenDP's `NoisePrivacyMap_for_ZExpFamily1`). For `d = 0` the inputs are equal,
/// so the divergence is 0; an infinite bound always holds.
#[trusted]
#[logic(opaque)]
#[requires(rv.scale.deep_model() >= Real::from_int(0))]
#[requires(forall<d: RBig, o: f64> map.post()[d][Ok(o)] ==>
    laplace_bound(d.deep_model(), rv.scale.deep_model(), o))]
#[ensures(result && noise_map_private(rv, map))]
pub fn laplace_mechanism(
    rv: ZExpFamily<1>,
    map: PrivacyMap<L1Distance<RBig>, MaxDivergence>,
) -> bool {
    dead
}

/// `make_laplace` on `f64` vectors under the L1 distance returns valid measurements.
#[logic]
#[requires(<DiscreteLaplace as MakeNoise<VectorDomain<AtomDomain<f64>>, L1Distance<f64>, MaxDivergence>>::noise_claim(m))]
#[ensures(m_valid(m))]
pub fn make_laplace_f64_vector_valid(
    m: Measurement<VectorDomain<AtomDomain<f64>>, L1Distance<f64>, MaxDivergence, Vec<f64>>,
) {
}

/// `make_laplace` on `f64` scalars under the absolute distance returns valid measurements.
#[logic]
#[requires(<DiscreteLaplace as MakeNoise<AtomDomain<f64>, AbsoluteDistance<f64>, MaxDivergence>>::noise_claim(m))]
#[ensures(m_valid(m))]
pub fn make_laplace_f64_scalar_valid(
    m: Measurement<AtomDomain<f64>, AbsoluteDistance<f64>, MaxDivergence, f64>,
) {
}

/// `make_laplace` on `i32` vectors under the L1 distance returns valid measurements.
#[logic]
#[requires(<DiscreteLaplace as MakeNoise<VectorDomain<AtomDomain<i32>>, L1Distance<i32>, MaxDivergence>>::noise_claim(m))]
#[ensures(m_valid(m))]
pub fn make_laplace_i32_vector_valid(
    m: Measurement<VectorDomain<AtomDomain<i32>>, L1Distance<i32>, MaxDivergence, Vec<i32>>,
) {
}
