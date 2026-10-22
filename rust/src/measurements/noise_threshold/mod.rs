use std::collections::HashMap;

use dashu::base::Sign;
use dashu::integer::{IBig, UBig};
use dashu::rational::RBig;
use opendp_derive::proven;

use crate::core::{Domain, Function, Measure, Measurement, Metric, MetricSpace, PrivacyMap};
use crate::domains::{AtomDomain, MapDomain};
use crate::error::Fallible;
use crate::metrics::{AbsoluteDistance, L0PInfDistance};
use crate::traits::Hashable;

use super::{Sample, ZExpFamily};

#[cfg(test)]
mod test;

mod distribution;
pub use distribution::*;

mod nature;

#[cfg(creusot)]
use crate::verification::privacy::{
    adds_noise_threshold, noise_threshold_map_private, noise_threshold_measurement_valid,
};
#[cfg(creusot)]
use creusot_std::{
    macros::{ensures, proof_assert, snapshot},
    model::DeepModel,
};

/// Make a measurement that samples from a random variable `RV`.
pub trait MakeNoiseThreshold<DI: Domain, MI: Metric, MO: Measure>
where
    (DI, MI): MetricSpace,
{
    type Threshold;

    /// Ghost model: what `make_noise_threshold` is proved to guarantee of the measurements it
    /// returns (`m_valid(m)`, or nothing for impls outside the verified scope).
    #[cfg(creusot)]
    #[creusot_std::macros::logic]
    fn noise_threshold_claim(m: Measurement<DI, MI, MO, DI::Carrier>) -> bool;

    /// # Proof Definition
    /// For any choice of arguments to `self`,
    /// returns a valid measurement or error.
    #[cfg_attr(creusot, ensures(forall<m: Measurement<DI, MI, MO, DI::Carrier>> result == Ok(m) ==>
        Self::noise_threshold_claim(m)))]
    fn make_noise_threshold(
        self,
        input_space: (DI, MI),
        threshold: Self::Threshold,
    ) -> Fallible<Measurement<DI, MI, MO, DI::Carrier>>;
}

pub trait NoiseThresholdPrivacyMap<MI: Metric, MO: Measure>: Sample {
    /// # Proof Definition
    /// Given a distribution `self`,
    /// returns `Err(e)` if `self` is not a valid distribution.
    /// Otherwise the output is `Ok(privacy_map)`
    /// where `privacy_map` observes the following:
    ///
    /// Define `function(x)` as a function that discards pairs with value zero,
    /// updates each remaining pair to `(k_i, v_i + Z_i)`
    /// where `Z_i` are iid samples from `self`,
    /// and discards pairs where `v_i + Z_i` is not beyond the threshold
    /// (strictly greater than a non-negative threshold, or strictly less than a negative one).
    /// The ordering of returned pairs is independent from the input ordering.
    ///
    /// For every pair of elements $x, x'$ in `MapDomain<AtomDomain<TK>, AtomDomain<IBig>>`,
    /// and for every pair (`d_in`, `d_out`),
    /// where `d_in` has the associated type for `input_metric` and `d_out` has the associated type for `output_measure`,
    /// if $x, x'$ are `d_in`-close under `input_metric`, `privacy_map(d_in)` does not raise an exception,
    /// and `privacy_map(d_in) <= d_out`,
    /// then `function(x)`, `function(x')` are `d_out`-close under `output_measure`.
    #[cfg_attr(creusot, ensures(forall<map: PrivacyMap<MI, MO>> result == Ok(map) ==>
        noise_threshold_map_private(*self, map, threshold.deep_model())))]
    fn noise_threshold_privacy_map(
        &self,
        input_metric: &MI,
        output_measure: &MO,
        threshold: UBig,
    ) -> Fallible<PrivacyMap<MI, MO>>;
}

#[proven(proof_path = "measurements/noise_threshold/MakeNoiseThreshold_IBig_for_RV.tex")]
impl<TK, const P: usize, MO: 'static + Measure>
    MakeNoiseThreshold<
        MapDomain<AtomDomain<TK>, AtomDomain<IBig>>,
        L0PInfDistance<P, AbsoluteDistance<RBig>>,
        MO,
    > for ZExpFamily<P>
where
    TK: Hashable,
    ZExpFamily<P>: NoiseThresholdPrivacyMap<L0PInfDistance<P, AbsoluteDistance<RBig>>, MO>,
{
    type Threshold = IBig;

    #[cfg(creusot)]
    #[creusot_std::macros::logic(open)]
    fn noise_threshold_claim(
        m: Measurement<
            MapDomain<AtomDomain<TK>, AtomDomain<IBig>>,
            L0PInfDistance<P, AbsoluteDistance<RBig>>,
            MO,
            HashMap<TK, IBig>,
        >,
    ) -> bool {
        crate::verification::privacy::m_valid(m)
    }

    #[cfg_attr(creusot, ensures(forall<m: Measurement<MapDomain<AtomDomain<TK>, AtomDomain<IBig>>, L0PInfDistance<P, AbsoluteDistance<RBig>>, MO, HashMap<TK, IBig>>>
        result == Ok(m) ==> crate::verification::privacy::m_valid(m)))]
    fn make_noise_threshold(
        self,
        (input_domain, input_metric): (
            MapDomain<AtomDomain<TK>, AtomDomain<IBig>>,
            L0PInfDistance<P, AbsoluteDistance<RBig>>,
        ),
        threshold: IBig,
    ) -> Fallible<
        Measurement<
            MapDomain<AtomDomain<TK>, AtomDomain<IBig>>,
            L0PInfDistance<P, AbsoluteDistance<RBig>>,
            MO,
            HashMap<TK, IBig>,
        >,
    > {
        let output_measure = MO::default();
        let threshold_magnitude = threshold.clone().into_parts().1;
        let privacy_map =
            self.noise_threshold_privacy_map(&input_metric, &output_measure, threshold_magnitude)?;

        #[cfg(creusot)]
        let (rv, t) = (snapshot!(self), snapshot!(threshold));
        let result = Measurement::new(
            input_domain,
            input_metric,
            output_measure,
            noise_threshold_function(self, threshold),
            privacy_map,
        );
        #[cfg(creusot)]
        proof_assert!(forall<m: Measurement<MapDomain<AtomDomain<TK>, AtomDomain<IBig>>, L0PInfDistance<P, AbsoluteDistance<RBig>>, MO, HashMap<TK, IBig>>>
            result == Ok(m) ==> noise_threshold_measurement_valid(m, *rv, *t));
        result
    }
}

/// The function that releases the pairs of `data` whose value is not zero, with noise from
/// `distribution` added to the values, and keeps those whose noisy value is beyond `threshold`.
// Trusted: the closure drops zero values, applies `distribution.sample` to each remaining value,
// which by the Proof Definition of `Sample` returns `v + Z` with independent samples `Z` of
// `distribution` (the samplers are not verified here), and keeps the pairs `is_beyond` accepts.
// The ordering of a `HashMap` does not depend on the order of insertion.
#[cfg_attr(creusot, creusot_std::macros::trusted)]
#[cfg_attr(
    creusot,
    ensures(adds_noise_threshold(result, distribution, threshold))
)]
fn noise_threshold_function<TK: Hashable, RV: Sample>(
    distribution: RV,
    threshold: IBig,
) -> Function<HashMap<TK, IBig>, HashMap<TK, IBig>> {
    Function::new_fallible(move |data: &HashMap<TK, IBig>| {
        data.into_iter()
            // a key with value zero is the same as a missing key (the metric's additive identity)
            .filter(|(_, v)| !v.is_zero())
            // noise output count
            .map(|(k, v)| Ok((k.clone(), distribution.sample(v)?)))
            // only keep keys with values beyond the threshold, and errors
            .filter(|r| r.as_ref().map_or(true, |p| is_beyond(&p.1, &threshold)))
            // fail the whole computation if any noise addition failed
            .collect()
    })
}

/// `value` is beyond `threshold`: strictly greater than a non-negative threshold, or strictly less
/// than a negative one.
#[cfg_attr(creusot, ensures(result == if threshold.deep_model() >= 0 {
    value.deep_model() > threshold.deep_model()
} else {
    value.deep_model() < threshold.deep_model()
}))]
fn is_beyond(value: &IBig, threshold: &IBig) -> bool {
    match threshold.sign() {
        Sign::Positive => value > threshold,
        Sign::Negative => value < threshold,
    }
}
