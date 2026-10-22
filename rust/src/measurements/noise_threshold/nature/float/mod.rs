use std::collections::HashMap;

use dashu::{integer::IBig, rational::RBig};
use opendp_derive::proven;

use crate::{
    core::{Function, Measure, Measurement, StabilityMap, Transformation},
    domains::{AtomDomain, MapDomain},
    error::Fallible,
    measurements::{
        MakeNoiseThreshold, NoiseThresholdPrivacyMap, ZExpFamily,
        nature::float::{
            FloatExpFamily, find_nearest_multiple_of_2k, get_min_k, get_rounding_distance,
            integerize_scale, x_mul_2k,
        },
    },
    metrics::{AbsoluteDistance, L0PInfDistance},
    traits::{CastInternalRational, ExactIntCast, Float, Hashable, Number},
    verification::MaybeDeepModel,
};

use super::map_values;
#[cfg(creusot)]
use super::{MapToBigint, float_to_bigint_map_valid, map_rounding_is_stable, step};
#[cfg(creusot)]
use crate::{
    measurements::nature::float::{
        fclamp, float_conversion_facts, number_conversion_facts, rounding_distance, rounds_to,
    },
    verification::{
        RealModel,
        dashu::pow2r,
        float::{FloatModel, float_grid},
        privacy::t_valid,
    },
};
#[cfg(creusot)]
use creusot_std::{
    logic::real::Real,
    macros::{ensures, proof_assert, requires, snapshot},
    model::DeepModel,
};

#[cfg(test)]
mod test;

#[proven(
    proof_path = "measurements/noise_threshold/nature/float/MakeNoiseThreshold_MapDomain_for_FloatExpFamily.tex"
)]
impl<TK, TV, const P: usize, QI: Number, MO: 'static + Measure>
    MakeNoiseThreshold<
        MapDomain<AtomDomain<TK>, AtomDomain<TV>>,
        L0PInfDistance<P, AbsoluteDistance<QI>>,
        MO,
    > for FloatExpFamily<P>
where
    TK: Hashable + MaybeDeepModel,
    TV: Float,
    RBig: TryFrom<TV> + TryFrom<QI>,
    i32: ExactIntCast<TV::Bits>,
    ZExpFamily<P>: NoiseThresholdPrivacyMap<L0PInfDistance<P, AbsoluteDistance<RBig>>, MO>,
{
    type Threshold = TV;

    /// The mechanism is proved valid for `P = 1` (the Laplace threshold mechanism).
    #[cfg(creusot)]
    #[creusot_std::macros::logic(open)]
    fn noise_threshold_claim(
        m: Measurement<
            MapDomain<AtomDomain<TK>, AtomDomain<TV>>,
            L0PInfDistance<P, AbsoluteDistance<QI>>,
            MO,
            HashMap<TK, TV>,
        >,
    ) -> bool {
        if P == 1usize {
            crate::verification::privacy::m_valid(m)
        } else {
            true
        }
    }

    #[cfg_attr(creusot, ensures(forall<m: Measurement<MapDomain<AtomDomain<TK>, AtomDomain<TV>>, L0PInfDistance<P, AbsoluteDistance<QI>>, MO, HashMap<TK, TV>>>
        result == Ok(m) ==> Self::noise_threshold_claim(m)))]
    fn make_noise_threshold(
        self,
        input_space: (
            MapDomain<AtomDomain<TK>, AtomDomain<TV>>,
            L0PInfDistance<P, AbsoluteDistance<QI>>,
        ),
        threshold: TV,
    ) -> Fallible<
        Measurement<
            MapDomain<AtomDomain<TK>, AtomDomain<TV>>,
            L0PInfDistance<P, AbsoluteDistance<QI>>,
            MO,
            HashMap<TK, TV>,
        >,
    > {
        let FloatExpFamily { scale, k } = self;
        let distribution = ZExpFamily {
            scale: integerize_scale(scale, k)?,
        };
        #[cfg(creusot)]
        proof_assert!(k@ > i32::MIN@ && float_conversion_facts::<TV>());

        if is_negative(&threshold) {
            return fallible!(
                FailedFunction,
                "threshold ({threshold}) must not be negative"
            );
        }

        let Ok(r_threshold) = RBig::try_from(threshold) else {
            return fallible!(FailedFunction, "threshold ({threshold}) must be finite");
        };

        let r_threshold = x_mul_2k(r_threshold, -k).round();

        let t_int = make_float_to_bigint_threshold::<TK, TV, P, QI>(input_space, threshold, k)?;
        let m_noise = distribution.make_noise_threshold(t_int.output_space(), r_threshold)?;
        #[cfg(creusot)]
        proof_assert!(P == 1usize ==> crate::verification::privacy::t_valid(t_int)
            && crate::verification::privacy::m_valid(m_noise));
        let m_int = t_int >> m_noise;
        #[cfg(creusot)]
        proof_assert!(P == 1usize ==> forall<m: Measurement<MapDomain<AtomDomain<TK>, AtomDomain<TV>>, L0PInfDistance<P, AbsoluteDistance<QI>>, MO, HashMap<TK, IBig>>>
            m_int == Ok(m) ==> crate::verification::privacy::m_valid(m));
        m_int >> then_deintegerize_hashmap(k)?
    }
}

#[proven(
    proof_path = "measurements/noise_threshold/nature/float/make_float_to_bigint_threshold.tex"
)]
#[cfg_attr(creusot, ensures(forall<t: MapToBigint<TK, TV, P, QI>> result == Ok(t) ==>
    (P == 1usize ==> t_valid(t))))]
fn make_float_to_bigint_threshold<TK, TV, const P: usize, QI: Number>(
    (input_domain, input_metric): (
        MapDomain<AtomDomain<TK>, AtomDomain<TV>>,
        L0PInfDistance<P, AbsoluteDistance<QI>>,
    ),
    threshold: TV,
    k: i32,
) -> Fallible<
    Transformation<
        MapDomain<AtomDomain<TK>, AtomDomain<TV>>,
        L0PInfDistance<P, AbsoluteDistance<QI>>,
        MapDomain<AtomDomain<TK>, AtomDomain<IBig>>,
        L0PInfDistance<P, AbsoluteDistance<RBig>>,
    >,
>
where
    TK: Hashable + MaybeDeepModel,
    TV: Float,
    RBig: TryFrom<TV> + TryFrom<QI>,
    i32: ExactIntCast<TV::Bits>,
{
    #[cfg(creusot)]
    proof_assert!(float_conversion_facts::<TV>());
    if input_domain.value_domain.nan() {
        return fallible!(
            MakeTransformation,
            "input_domain hashmap values may not contain NaN elements"
        );
    }
    let Ok(r_threshold) = RBig::try_from(threshold) else {
        return fallible!(MakeTransformation, "threshold ({threshold}) must be finite");
    };
    let k_min = get_min_k::<TV>();
    if k < k_min {
        return fallible!(
            MakeTransformation,
            "k ({k}) must not be smaller than {k_min}"
        );
    }
    #[cfg(creusot)]
    proof_assert!(float_grid::<TV>() && k@ > i32::MIN@);
    let key_domain = input_domain.key_domain.clone();
    let result = Transformation::new(
        input_domain,
        input_metric,
        MapDomain {
            key_domain,
            value_domain: AtomDomain::<IBig>::default(),
        },
        L0PInfDistance::default(),
        Function::new(move |arg: &HashMap<TK, TV>| discretize_map(arg, k)),
        StabilityMap::new_fallible(move |d_in: &(u32, QI, QI)| {
            float_threshold_distance::<TV, P, QI>(d_in, &r_threshold, threshold, k)
        }),
    );
    #[cfg(creusot)]
    proof_assert!(P == 1usize ==> map_rounding_is_stable::<TV>(k@));
    #[cfg(creusot)]
    proof_assert!(P == 1usize ==> forall<t: MapToBigint<TK, TV, P, QI>> result == Ok(t) ==>
        float_to_bigint_map_valid(t, k@));
    result
}

/// Rounds each value of `arg`, clamped to the finite range, to the nearest multiple of `2^k`,
/// keeping the keys.
#[cfg_attr(creusot, requires(k@ > i32::MIN@))]
#[cfg_attr(creusot, ensures(forall<key: TK::DeepModelTy> result@.contains(key) == arg@.contains(key)))]
#[cfg_attr(creusot, ensures(forall<key: TK::DeepModelTy> arg@.contains(key) ==>
    rounds_to(arg@[key], result@[key], k@)))]
fn discretize_map<TK: Hashable + MaybeDeepModel, TV: Float>(
    arg: &HashMap<TK, TV>,
    k: i32,
) -> HashMap<TK, IBig>
where
    RBig: TryFrom<TV>,
{
    map_values(arg, |val: &TV| discretize_value(val, k))
}

/// Rounds `val`, clamped to the finite range, to the nearest multiple of `2^k`, as the integer
/// multiple.
#[cfg_attr(creusot, requires(k@ > i32::MIN@))]
#[cfg_attr(creusot, ensures(rounds_to(*val, result, k@)))]
fn discretize_value<TV: Float>(val: &TV, k: i32) -> IBig
where
    RBig: TryFrom<TV>,
{
    #[cfg(creusot)]
    proof_assert!(float_conversion_facts::<TV>());
    let clamped = val.clamp(TV::MIN_FINITE, TV::MAX_FINITE);
    #[cfg(creusot)]
    proof_assert!(clamped == fclamp(*val));
    let val = RBig::try_from(clamped).unwrap_or(RBig::from(0usize));
    find_nearest_multiple_of_2k(val, k)
}

/// The distances between discretized maps: `l0`, `(lp + l0 step) / 2^k` and `(li + step) / 2^k`,
/// where `step = 2^k - 2^min_k` is the rounding slack per key.
#[cfg_attr(creusot, requires(k@ > i32::MIN@))]
#[cfg_attr(creusot, ensures(forall<o: (u32, RBig, RBig)> result == Ok(o) ==> P == 1usize ==>
    o.0 == d_in.0
    && o.1.deep_model() == (d_in.1.real() + Real::from_int(d_in.0@) * step::<TV>(k@)) * pow2r(-k@)
    && o.2.deep_model() == (d_in.2.real() + step::<TV>(k@)) * pow2r(-k@)))]
fn float_threshold_distance<TV: Float, const P: usize, QI: Number>(
    d_in: &(u32, QI, QI),
    r_threshold: &RBig,
    threshold: TV,
    k: i32,
) -> Fallible<(u32, RBig, RBig)>
where
    RBig: TryFrom<QI>,
    i32: ExactIntCast<TV::Bits>,
{
    #[cfg(creusot)]
    proof_assert!(number_conversion_facts::<QI>());
    let (l0, lp, li) = d_in;
    // Lp sensitivity
    let r_lp = match RBig::try_from(*lp) {
        Ok(r_lp) => r_lp,
        Err(_) => return fallible!(FailedMap, "l{P} ({lp:?}) must be finite"),
    };
    let r_lp_round = get_rounding_distance::<TV, P>(k, Some(*l0 as usize))?;
    #[cfg(creusot)]
    proof_assert!(P == 1usize ==> r_lp_round.deep_model() == Real::from_int(l0@) * step::<TV>(k@));
    let r_lp = x_mul_2k(r_lp + r_lp_round.clone(), -k);

    // L\infty sensitivity
    let r_li = match RBig::try_from(*li) {
        Ok(r_li) => r_li,
        Err(_) => return fallible!(FailedMap, "li ({li:?}) must be finite"),
    };

    // this check is not necessary for stability,
    // but it gives a more understandable error message
    if r_li > *r_threshold {
        return fallible!(
            FailedMap,
            "threshold ({threshold}) must not be smaller than l-infinity sensitivity ({li:?})"
        );
    }
    let r_li_round = get_rounding_distance::<TV, P>(k, Some(1))?;
    #[cfg(creusot)]
    proof_assert!(P == 1usize ==> r_li_round.deep_model() == step::<TV>(k@));
    let r_li = x_mul_2k(r_li + r_li_round.clone(), -k);

    Ok((*l0, r_lp, r_li))
}

#[proven(proof_path = "measurements/noise_threshold/nature/float/then_deintegerize_hashmap.tex")]
// Trusted: a post-processor (any function is valid); `HashMap` iteration has no specification here.
#[cfg_attr(creusot, creusot_std::macros::trusted)]
pub fn then_deintegerize_hashmap<K: Hashable, V: Clone + CastInternalRational>(
    k: i32,
) -> Fallible<Function<HashMap<K, IBig>, HashMap<K, V>>> {
    if k == i32::MIN {
        return fallible!(MakeTransformation, "k must not be i32::MIN");
    }
    Ok(Function::new(move |x: &HashMap<K, IBig>| {
        (x.clone().into_iter())
            .map(|(key, val)| (key, V::from_rational(x_mul_2k(RBig::from(val), k))))
            .collect()
    }))
}

/// `v` is negative (`is_sign_negative`).
// Trusted: `num::Float::is_sign_negative` has no precondition; its result only selects an error.
#[cfg_attr(creusot, creusot_std::macros::trusted)]
fn is_negative<TV: Float>(v: &TV) -> bool {
    v.is_sign_negative()
}
