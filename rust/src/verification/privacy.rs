//! The privacy semantics of measurements and transformations.
//!
//! Privacy is a property of output distributions, which the logic does not model. A measurement's
//! privacy guarantee is therefore an uninterpreted predicate, `m_valid`: OpenDP's definition of a
//! valid measurement (for every `d_in`, if the privacy map returns `d_out`, then the output
//! distributions on any two `d_in`-close inputs in the input domain are `d_out`-close under the
//! output measure). Likewise `t_valid` for transformations (outputs in the output domain, and
//! outputs on `d_in`-close inputs are `map(d_in)`-close).
//!
//! The facts about them are assumptions, listed in `verification/TRUST.md`:
//! - the theorems of differential privacy that OpenDP's proofs cite: chaining a valid transformation
//!   into a valid measurement, and post-processing (contracts of `make_chain_mt`, `make_chain_pm`);
//! - the mechanism theorems (`laplace_mechanism`, proved in Lean);
//! - the definitions of the metrics, for the transformations proved stable here (`t_valid_*`).
use creusot_std::{logic::Int, prelude::*};
use dashu::integer::IBig;

use std::collections::HashMap;

use crate::{
    core::{Domain, Function, Measure, Measurement, Metric, PrivacyMap, Transformation},
    domains::{AtomDomain, MapDomain, VectorDomain},
    metrics::{AbsoluteDistance, LpDistance},
    traits::Hashable,
};

/// `m` is a valid measurement.
#[logic(opaque)]
pub fn m_valid<DI: Domain, MI: Metric, MO: Measure, TO>(_m: Measurement<DI, MI, MO, TO>) -> bool {
    dead
}

/// `t` is a valid transformation.
#[logic(opaque)]
pub fn t_valid<DI: Domain, MI: Metric, DO: Domain, MO: Metric>(
    _t: Transformation<DI, MI, DO, MO>,
) -> bool {
    dead
}

/// `f` adds independent noise from the distribution `rv` to each element of its input: by the
/// Proof Definition of `Sample`, `f(x)_i = x_i + Z_i` with `Z_i` independent samples of `rv`.
#[logic(opaque)]
pub fn adds_noise<RV>(_f: Function<Vec<IBig>, Vec<IBig>>, _rv: RV) -> bool {
    dead
}

/// `map` meets the Proof Definition of `NoisePrivacyMap` for the distribution `rv`: if `x`, `x'`
/// are `d_in`-close under `MI` and `map(d_in) = d_out`, then `x + Z` and `x' + Z` (`Z` iid from
/// `rv`) are `d_out`-close under `MO`.
#[logic(opaque)]
pub fn noise_map_private<RV, MI: Metric, MO: Measure>(_rv: RV, _map: PrivacyMap<MI, MO>) -> bool {
    dead
}

/// A measurement that adds noise from `rv` with a privacy map meeting `NoisePrivacyMap`'s Proof
/// Definition is valid.
///
/// Trusted: this is the definition of a valid measurement, given the two Proof Definitions.
#[trusted]
#[logic(opaque)]
#[requires(adds_noise(m.function, rv) && noise_map_private(rv, m.privacy_map))]
#[ensures(result && m_valid(m))]
pub fn noise_measurement_valid<MI: Metric, MO: Measure, RV>(
    m: Measurement<VectorDomain<AtomDomain<IBig>>, MI, MO, Vec<IBig>>,
    rv: RV,
) -> bool {
    dead
}

/// A transformation from a scalar to the vector holding just that scalar, with the identity
/// stability map, is valid from `AbsoluteDistance<Q>` to `LpDistance<P, Q>`.
///
/// Trusted: the `L_p` distance between two one-element vectors is the absolute distance between
/// their elements (definitions of the two metrics), and `[x]` has size 1. Cloning a value (or a
/// domain) does not change it.
#[trusted]
#[logic(opaque)]
#[requires(t.output_domain.element_domain.deep_model() == t.input_domain.deep_model())]
#[requires(t.output_domain.size == Some(1usize))]
#[requires(forall<x: T> inv(x) ==> t.function.pre()[x])]
#[requires(forall<x: T, y: Vec<T>> t.function.post()[x][Ok(y)] ==>
    y@.len() == 1 && T::clone.postcondition((&x,), y@[0]))]
#[requires(forall<d: Q, o: Q> t.stability_map.post()[d][Ok(o)] ==> Q::clone.postcondition((&d,), o))]
#[ensures(result && t_valid(t))]
pub fn singleton_valid<T: crate::traits::CheckAtom, const P: usize, Q: Clone>(
    t: Transformation<
        AtomDomain<T>,
        AbsoluteDistance<Q>,
        VectorDomain<AtomDomain<T>>,
        LpDistance<P, Q>,
    >,
) -> bool {
    dead
}

/// `f` releases a noisy map with thresholding: by the Proof Definition of
/// `NoiseThresholdPrivacyMap`, it discards pairs with value zero, replaces each remaining value `v`
/// by `v + Z` with `Z` independent samples of `rv`, and discards the pairs whose noisy value is not
/// beyond `threshold` (strictly greater than a non-negative threshold, strictly less than a
/// negative one), in an order independent of the input.
#[logic(opaque)]
pub fn adds_noise_threshold<K, RV>(
    _f: Function<HashMap<K, IBig>, HashMap<K, IBig>>,
    _rv: RV,
    _threshold: IBig,
) -> bool {
    dead
}

/// `map` meets the Proof Definition of `NoiseThresholdPrivacyMap` for the distribution `rv` and a
/// threshold of magnitude `threshold`: if `x`, `x'` are `d_in`-close under `MI` and
/// `map(d_in) = d_out`, then the thresholded noisy releases of `x` and `x'` are `d_out`-close.
#[logic(opaque)]
pub fn noise_threshold_map_private<RV, MI: Metric, MO: Measure>(
    _rv: RV,
    _map: PrivacyMap<MI, MO>,
    _threshold: Int,
) -> bool {
    dead
}

/// A measurement on maps whose function releases noise from `rv` with thresholding, and whose
/// privacy map meets `NoiseThresholdPrivacyMap`'s Proof Definition for `rv` and the magnitude of
/// the threshold, is valid.
///
/// Trusted: the definition of a valid measurement, given the two Proof Definitions.
#[trusted]
#[logic(opaque)]
#[requires(adds_noise_threshold(m.function, rv, threshold))]
#[requires(noise_threshold_map_private(rv, m.privacy_map,
    if threshold.deep_model() >= 0 { threshold.deep_model() } else { -threshold.deep_model() }))]
#[ensures(result && m_valid(m))]
pub fn noise_threshold_measurement_valid<K: Hashable, MI: Metric, MO: Measure, RV>(
    m: Measurement<MapDomain<AtomDomain<K>, AtomDomain<IBig>>, MI, MO, HashMap<K, IBig>>,
    rv: RV,
    threshold: IBig,
) -> bool {
    dead
}
