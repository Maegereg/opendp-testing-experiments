use core::f64;

use dashu::{base::Sign, rational::RBig};
use opendp_derive::{bootstrap, proven};

use crate::core::{Measure, Metric, MetricSpace};
use crate::measurements::noise::nature::Nature;
use crate::measurements::{MakeNoise, NoiseDomain, NoisePrivacyMap, ZExpFamily};
#[cfg(creusot)]
use crate::verification::{RealModel, float::FloatModel, privacy::noise_map_private};
use crate::{
    core::{Domain, Measurement, PrivacyMap},
    error::Fallible,
    measures::MaxDivergence,
    metrics::L1Distance,
    traits::InfCast,
};

#[cfg(creusot)]
use creusot_std::{
    macros::{ensures, proof_assert, requires},
    model::DeepModel,
};

#[cfg(creusot)]
mod proof;
#[cfg(creusot)]
pub use proof::*;

#[cfg(test)]
mod test;

#[cfg(feature = "ffi")]
pub(crate) mod ffi;

#[bootstrap(
    features("contrib"),
    arguments(k(default = b"null")),
    generics(DI(suppress), MI(suppress), MO(default = "MaxDivergence"))
)]
/// Make a Measurement that adds noise from the Laplace(`scale`) distribution to the input.
///
/// Valid inputs for `input_domain` and `input_metric` are:
///
/// | `input_domain`                  | input type   | `input_metric`         |
/// | ------------------------------- | ------------ | ---------------------- |
/// | `atom_domain(T)` (default)      | `T`          | `absolute_distance(T)` |
/// | `vector_domain(atom_domain(T))` | `Vec<T>`     | `l1_distance(T)`       |
///
/// Internally, all sampling is done using the discrete Laplace distribution.
///
/// # Citations
/// * [GRS12 Universally Utility-Maximizing Privacy Mechanisms](https://theory.stanford.edu/~tim/papers/priv.pdf)
/// * [CKS20 The Discrete Gaussian for Differential Privacy](https://arxiv.org/pdf/2004.00010.pdf#subsection.5.2)
///
/// # Arguments
/// * `input_domain` - Domain of the data type to be released.
/// * `input_metric` - Metric of the data type to be released.
/// * `scale` - Noise scale parameter for the Laplace distribution. `scale` == standard_deviation / sqrt(2).
/// * `k` - The noise granularity in terms of 2^k, only valid for domains over floats.
///
/// # Generics
/// * `DI` - Domain of the data type to be released. Valid values are `VectorDomain<AtomDomain<T>>` or `AtomDomain<T>`
/// * `MI` - Metric used to measure distance between members of the input domain.
/// * `MO` - Measure used to quantify privacy loss. Valid values are just `MaxDivergence`
#[cfg_attr(creusot, ensures(forall<m: Measurement<DI, MI, MO, DI::Carrier>> result == Ok(m) ==>
    <DiscreteLaplace as MakeNoise<DI, MI, MO>>::noise_claim(m)))]
pub fn make_laplace<DI: Domain, MI: Metric, MO: Measure>(
    input_domain: DI,
    input_metric: MI,
    scale: f64,
    k: Option<i32>,
) -> Fallible<Measurement<DI, MI, MO, DI::Carrier>>
where
    DiscreteLaplace: MakeNoise<DI, MI, MO>,
    (DI, MI): MetricSpace,
{
    DiscreteLaplace { scale, k }.make_noise((input_domain, input_metric))
}

/// The privacy loss `0.0`.
// Trusted: Creusot does not translate float literals in specifications.
#[cfg_attr(creusot, creusot_std::macros::trusted)]
#[cfg_attr(creusot, ensures(result.finite() && result.real() == creusot_std::logic::real::Real::from_int(0)))]
fn zero_loss() -> f64 {
    0.0
}

pub struct DiscreteLaplace {
    pub scale: f64,
    pub k: Option<i32>,
}

/// Laplace mechanism
#[proven(proof_path = "measurements/noise/distribution/laplace/MakeNoise_for_DiscreteLaplace.tex")]
impl<DI: NoiseDomain, MI: Metric, MO: 'static + Measure> MakeNoise<DI, MI, MO> for DiscreteLaplace
where
    (DI, MI): MetricSpace,
    DI::Atom: Nature,
    <DI::Atom as Nature>::RV<1>: MakeNoise<DI, MI, MO>,
{
    #[cfg(creusot)]
    #[creusot_std::macros::logic(open)]
    fn noise_claim(m: Measurement<DI, MI, MO, DI::Carrier>) -> bool {
        <<DI::Atom as Nature>::RV<1> as MakeNoise<DI, MI, MO>>::noise_claim(m)
    }

    #[cfg_attr(creusot, ensures(forall<m: Measurement<DI, MI, MO, DI::Carrier>> result == Ok(m) ==>
        Self::noise_claim(m)))]
    fn make_noise(self, input_space: (DI, MI)) -> Fallible<Measurement<DI, MI, MO, DI::Carrier>> {
        DI::Atom::new_distribution(self.scale, self.k)?.make_noise(input_space)
    }
}

#[proven(
    proof_path = "measurements/noise/distribution/laplace/NoisePrivacyMap_for_ZExpFamily1.tex"
)]
impl NoisePrivacyMap<L1Distance<RBig>, MaxDivergence> for ZExpFamily<1> {
    #[cfg_attr(creusot, ensures(forall<map: PrivacyMap<L1Distance<RBig>, MaxDivergence>> result == Ok(map) ==>
        noise_map_private(*self, map)))]
    #[cfg_attr(creusot, ensures(forall<map: PrivacyMap<L1Distance<RBig>, MaxDivergence>> result == Ok(map) ==>
        self.scale.deep_model() >= creusot_std::logic::real::Real::from_int(0)
        && forall<d: RBig, o: f64> map.post()[d][Ok(o)] ==>
            laplace_bound(d.deep_model(), self.scale.deep_model(), o)))]
    fn noise_privacy_map(
        &self,
        _input_metric: &L1Distance<RBig>,
        _output_measure: &MaxDivergence,
    ) -> Fallible<PrivacyMap<L1Distance<RBig>, MaxDivergence>> {
        let scale = self.scale.clone();
        if scale.sign() == Sign::Negative {
            return fallible!(MakeMeasurement, "scale ({}) must not be negative", scale);
        }
        #[cfg(creusot)]
        proof_assert!(scale.deep_model() == self.scale.deep_model());
        let map = PrivacyMap::new_fallible(move |d_in: &RBig| laplace_loss(d_in, &scale));
        #[cfg(creusot)]
        proof_assert!(laplace_mechanism(*self, map));
        Ok(map)
    }
}

/// The privacy loss of the discrete Laplace mechanism with `scale`, at L1 sensitivity `d_in`.
#[cfg_attr(creusot, requires(scale.deep_model() >= creusot_std::logic::real::Real::from_int(0)))]
#[cfg_attr(creusot, ensures(forall<o: f64> result == Ok(o) ==>
    laplace_bound(d_in.deep_model(), scale.deep_model(), o)))]
fn laplace_loss(d_in: &RBig, scale: &RBig) -> Fallible<f64> {
    if d_in.sign() == Sign::Negative {
        return fallible!(FailedMap, "sensitivity ({}) must be positive", d_in);
    }

    if d_in.is_zero() {
        return Ok(zero_loss());
    }

    if scale.is_zero() {
        return Ok(f64::INFINITY);
    }

    // d_in / scale
    f64::inf_cast(d_in / scale.clone())
}
