use dashu::{
    base::Sign,
    integer::{IBig, UBig},
    rational::RBig,
};
use opendp_derive::{bootstrap, proven};

use crate::{
    accuracy::{
        conservative_continuous_laplacian_tail_to_alpha,
        conservative_discrete_laplacian_tail_to_alpha,
    },
    core::{Measure, Measurement, Metric, MetricSpace, PrivacyMap},
    error::Fallible,
    measurements::{
        DiscreteLaplace, MakeNoiseThreshold, NoiseDomain, NoisePrivacyMap,
        NoiseThresholdPrivacyMap, ZExpFamily, nature::Nature,
    },
    measures::{Approximate, MaxDivergence},
    metrics::{AbsoluteDistance, L1Distance, L01InfDistance},
    traits::{InfPowI, InfSub, option_min},
};

#[cfg(feature = "ffi")]
pub(crate) mod ffi;

#[cfg(creusot)]
mod proof;
#[cfg(creusot)]
use crate::{
    measurements::laplace_bound,
    verification::{RealModel, float::FloatModel, privacy::noise_threshold_map_private},
};
#[cfg(creusot)]
use creusot_std::{
    logic::real::Real,
    macros::{ensures, proof_assert, requires, snapshot, trusted},
    model::DeepModel,
};
#[cfg(creusot)]
pub use proof::*;

#[cfg(test)]
mod test;

#[bootstrap(
    features("contrib"),
    arguments(threshold(c_type = "void *", rust_type = "TV"), k(default = b"null")),
    generics(DI(suppress), MI(suppress), MO(default = "Approximate<MaxDivergence>")),
    derived_types(TV = "$get_value_type(get_carrier_type(input_domain))")
)]
/// Make a Measurement that uses propose-test-release to release a hashmap of counts.
///
/// This function takes a noise granularity in terms of 2^k.
/// Larger granularities are more computationally efficient, but have a looser privacy map.
/// If k is not set, k defaults to the smallest granularity.
///
/// # Citations
/// * [Rogers23 A Unifying Privacy Analysis Framework for Unknown Domain Algorithms in Differential Privacy](https://arxiv.org/abs/2309.09170)
/// * [CKS20 The Discrete Gaussian for Differential Privacy](https://arxiv.org/abs/2004.00010)
///
/// # Proof Navigation
/// * This constructor delegates to [`MakeNoiseThreshold`] for [`DiscreteLaplace`].
/// * Threshold-specific privacy accounting is implemented by [`NoiseThresholdPrivacyMap`].
/// * See also [`make_noise_threshold`] for the distribution-agnostic entry point.
///
/// # Runtime
/// For an input map with `m` entries, each release performs `O(m)` wrapper work
/// plus one discrete-Laplace draw per entry.
///
/// # Utility
/// If an item's value is separated from the threshold by margin `g`,
/// the probability of thresholding it incorrectly decays as `O(exp(-g / scale))`
/// up to constants from the discrete/continuous Laplace tail bounds.
///
/// # Arguments
/// * `input_domain` - Domain of the input.
/// * `input_metric` - Metric for the input domain.
/// * `scale` - Noise scale parameter for the laplace distribution. `scale` == standard_deviation / sqrt(2).
/// * `threshold` - Exclude counts that are not greater than this value (or not less than it, if negative).
/// * `k` - The noise granularity in terms of 2^k.
///
/// # Generics
/// * `DI` - Input Domain.
/// * `MI` - Input Metric.
/// * `MO` - Output Measure.
#[cfg_attr(creusot, ensures(forall<m: Measurement<DI, MI, MO, DI::Carrier>> result == Ok(m) ==>
    <DiscreteLaplace as MakeNoiseThreshold<DI, MI, MO>>::noise_threshold_claim(m)))]
pub fn make_laplace_threshold<DI: NoiseDomain, MI: Metric, MO: 'static + Measure>(
    input_domain: DI,
    input_metric: MI,
    scale: f64,
    threshold: DI::Atom,
    k: Option<i32>,
) -> Fallible<Measurement<DI, MI, MO, DI::Carrier>>
where
    DiscreteLaplace: MakeNoiseThreshold<DI, MI, MO, Threshold = DI::Atom>,
    (DI, MI): MetricSpace,
{
    DiscreteLaplace { scale, k }.make_noise_threshold((input_domain, input_metric), threshold)
}

#[proven(
    proof_path = "measurements/noise_threshold/distribution/laplace/MakeNoiseThreshold_for_DiscreteLaplace.tex"
)]
impl<DI: NoiseDomain, MI: Metric, MO: 'static + Measure> MakeNoiseThreshold<DI, MI, MO>
    for DiscreteLaplace
where
    (DI, MI): MetricSpace,
    DI::Atom: Nature,
    <DI::Atom as Nature>::RV<1>: MakeNoiseThreshold<DI, MI, MO, Threshold = DI::Atom>,
{
    type Threshold = DI::Atom;

    #[cfg(creusot)]
    #[creusot_std::macros::logic(open)]
    fn noise_threshold_claim(m: Measurement<DI, MI, MO, DI::Carrier>) -> bool {
        <<DI::Atom as Nature>::RV<1> as MakeNoiseThreshold<DI, MI, MO>>::noise_threshold_claim(m)
    }

    #[cfg_attr(creusot, ensures(forall<m: Measurement<DI, MI, MO, DI::Carrier>> result == Ok(m) ==>
        Self::noise_threshold_claim(m)))]
    fn make_noise_threshold(
        self,
        input_space: (DI, MI),
        threshold: DI::Atom,
    ) -> Fallible<Measurement<DI, MI, MO, DI::Carrier>> {
        DI::Atom::new_distribution(self.scale, self.k)?.make_noise_threshold(input_space, threshold)
    }
}

#[proven(
    proof_path = "measurements/noise_threshold/distribution/laplace/NoiseThresholdPrivacyMap_for_ZExpFamily1.tex"
)]
impl NoiseThresholdPrivacyMap<L01InfDistance<AbsoluteDistance<RBig>>, Approximate<MaxDivergence>>
    for ZExpFamily<1>
{
    #[cfg_attr(creusot, ensures(forall<map: PrivacyMap<L01InfDistance<AbsoluteDistance<RBig>>, Approximate<MaxDivergence>>>
        result == Ok(map) ==> noise_threshold_map_private(*self, map, threshold.deep_model())))]
    fn noise_threshold_privacy_map(
        &self,
        _input_metric: &L01InfDistance<AbsoluteDistance<RBig>>,
        output_measure: &Approximate<MaxDivergence>,
        threshold: UBig,
    ) -> Fallible<PrivacyMap<L01InfDistance<AbsoluteDistance<RBig>>, Approximate<MaxDivergence>>>
    {
        let noise_privacy_map =
            self.noise_privacy_map(&L1Distance::default(), &output_measure.0)?;
        let scale = self.scale.clone();

        #[cfg(creusot)]
        let t = snapshot!(threshold);
        let map = PrivacyMap::new_fallible(move |d_in: &(u32, RBig, RBig)| {
            threshold_loss(d_in, &scale, &threshold, &noise_privacy_map)
        });
        #[cfg(creusot)]
        proof_assert!(self.scale.deep_model() >= Real::from_int(0));
        #[cfg(creusot)]
        proof_assert!(forall<d: (u32, RBig, RBig), o: (f64, f64)> map.post()[d][Ok(o)] ==>
            threshold_bound(d.0@, d.1.deep_model(), d.2.deep_model(), self.scale.deep_model(), t.deep_model(), o.0, o.1));
        #[cfg(creusot)]
        proof_assert!(laplace_threshold_mechanism(*self, map, *t));
        Ok(map)
    }
}

/// The privacy loss `(epsilon, delta)` of the discrete Laplace threshold mechanism with `scale` and
/// a threshold of magnitude `threshold`, on maps within `(l0, l1, li)`.
#[cfg_attr(creusot, requires(scale.deep_model() >= Real::from_int(0)))]
#[cfg_attr(creusot, requires(forall<d: RBig, o: f64> noise_privacy_map.post()[d][Ok(o)] ==>
    laplace_bound(d.deep_model(), scale.deep_model(), o)))]
#[cfg_attr(creusot, ensures(forall<o: (f64, f64)> result == Ok(o) ==>
    threshold_bound(d_in.0@, d_in.1.deep_model(), d_in.2.deep_model(), scale.deep_model(),
        threshold.deep_model(), o.0, o.1)))]
fn threshold_loss(
    d_in: &(u32, RBig, RBig),
    scale: &RBig,
    threshold: &UBig,
    noise_privacy_map: &PrivacyMap<L1Distance<RBig>, MaxDivergence>,
) -> Fallible<(f64, f64)> {
    let (l0, l1, li) = d_in;
    let (Sign::Positive, l1) = l1.floor().into_parts() else {
        return fallible!(FailedMap, "l1 sensitivity ({l1}) must be non-negative");
    };

    let (Sign::Positive, li) = li.floor().into_parts() else {
        return fallible!(
            FailedMap,
            "l-infinity sensitivity ({li}) must be non-negative"
        );
    };

    #[cfg(creusot)]
    let (n1, ni) = (snapshot!(l1.deep_model()), snapshot!(li.deep_model()));
    #[cfg(creusot)]
    proof_assert!(forall<m1: creusot_std::logic::Int, mi: creusot_std::logic::Int>
    is_floor(m1, d_in.1.deep_model()) && is_floor(mi, d_in.2.deep_model()) ==> {
        floor_unique(m1, *n1, d_in.1.deep_model());
        floor_unique(mi, *ni, d_in.2.deep_model());
        m1 == *n1 && mi == *ni
    });
    let l1 = l1.min(&li * l0);
    let li = li.min(l1.clone());
    #[cfg(creusot)]
    proof_assert!(l1.deep_model() == imin(*n1, *ni * l0@) && li.deep_model() == imin(*ni, l1.deep_model()));
    #[cfg(creusot)]
    let di = snapshot!(li.deep_model());

    if l1.is_zero() {
        let out = (f64_zero(), f64_zero());
        #[cfg(creusot)]
        proof_assert!(threshold_bound(d_in.0@, d_in.1.deep_model(), d_in.2.deep_model(), scale.deep_model(), threshold.deep_model(), out.0, out.1));
        return Ok(out);
    }

    if scale.is_zero() {
        let out = (f64::INFINITY, f64_one());
        #[cfg(creusot)]
        proof_assert!(threshold_bound(d_in.0@, d_in.1.deep_model(), d_in.2.deep_model(), scale.deep_model(), threshold.deep_model(), out.0, out.1));
        return Ok(out);
    }

    let l1r = RBig::from(l1);
    let rho = noise_privacy_map.eval(&l1r)?;

    if li > *threshold {
        return fallible!(
            FailedMap,
            "threshold ({threshold}) must not be smaller than l-infinity sensitivity {li}"
        );
    }

    let d_instability = threshold - li;
    #[cfg(creusot)]
    let d = snapshot!(d_instability.deep_model());

    #[cfg(creusot)]
    proof_assert!(tail_facts());
    let Some(delta_single) = option_min(
        conservative_discrete_laplacian_tail_to_alpha(scale.clone(), d_instability.clone()).ok(),
        conservative_continuous_laplacian_tail_to_alpha(scale.clone(), d_instability.into()).ok(),
    ) else {
        return fallible!(FailedMap, "failed to compute tail bound in privacy map");
    };

    #[cfg(creusot)]
    proof_assert!(delta_single.finite() && delta_single.real() <= Real::from_int(1));
    #[cfg(creusot)]
    proof_assert!(delta_single.real() >= dlap_tail_gt(scale.deep_model(), *d));
    let delta_joint = joint_delta(delta_single, *l0)?;

    // delta is only sensibly at most 1
    let out = (rho, min_one(delta_joint));
    #[cfg(creusot)]
    proof_assert!(laplace_bound(l1r.deep_model(), scale.deep_model(), rho));
    #[cfg(creusot)]
    proof_assert!(*di <= threshold.deep_model() && *d == threshold.deep_model() - *di);
    #[cfg(creusot)]
    proof_assert!(out.1.finite() && (out.1.real() >= Real::from_int(1)
        || out.1.real() >= Real::from_int(1) - rpow(Real::from_int(1) - delta_single.real(), l0@)));
    #[cfg(creusot)]
    proof_assert!(
        dlap_tail_gt(scale.deep_model(), threshold.deep_model() - *di) <= delta_single.real()
            && delta_single.real() <= Real::from_int(1)
    );
    #[cfg(creusot)]
    proof_assert!(bound_intro(d_in.0@, d_in.1.deep_model(), d_in.2.deep_model(), scale.deep_model(),
        threshold.deep_model(), out.0, out.1, *n1, *ni, imin(*n1, *ni * l0@), *di, delta_single.real()));
    Ok(out)
}

/// `1 - (1 - delta_single)^l0`, rounded up: the probability that one of `l0` independent events of
/// probability at most `delta_single` occurs.
// Trusted: `neg_inf_sub` rounds `1 - delta_single` down, `neg_inf_powi` rounds the (non-negative)
// power down, and `inf_sub` rounds the result up.
#[cfg_attr(creusot, trusted)]
#[cfg_attr(creusot, requires(delta_single.finite() && Real::from_int(0) <= delta_single.real()
    && delta_single.real() <= Real::from_int(1)))]
#[cfg_attr(creusot, ensures(forall<o: f64> result == Ok(o) ==> o.finite()
    && o.real() >= Real::from_int(1) - rpow(Real::from_int(1) - delta_single.real(), l0@)))]
fn joint_delta(delta_single: f64, l0: u32) -> Fallible<f64> {
    (1.0).inf_sub(
        &(1.0)
            .neg_inf_sub(&delta_single)?
            .neg_inf_powi(IBig::from(l0))?,
    )
}

/// `x.min(1.0)`.
// Trusted: Creusot does not translate float literals in specifications.
#[cfg_attr(creusot, trusted)]
#[cfg_attr(creusot, requires(x.finite()))]
#[cfg_attr(creusot, ensures(result.finite()))]
#[cfg_attr(creusot, ensures(x.real() >= Real::from_int(1) ==> result.real() == Real::from_int(1)))]
#[cfg_attr(creusot, ensures(x.real() < Real::from_int(1) ==> result == x))]
fn min_one(x: f64) -> f64 {
    x.min(1.0)
}

/// `0.0`.
// Trusted: Creusot does not translate float literals in specifications.
#[cfg_attr(creusot, trusted)]
#[cfg_attr(creusot, ensures(result.finite() && result.real() == Real::from_int(0)))]
fn f64_zero() -> f64 {
    0.0
}

/// `1.0`.
// Trusted: Creusot does not translate float literals in specifications.
#[cfg_attr(creusot, trusted)]
#[cfg_attr(creusot, ensures(result.finite() && result.real() == Real::from_int(1)))]
fn f64_one() -> f64 {
    1.0
}
