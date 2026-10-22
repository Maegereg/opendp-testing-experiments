use std::collections::HashMap;

use dashu::{
    integer::{IBig, UBig},
    rational::RBig,
};
use opendp_derive::proven;

use crate::{
    core::{Function, Measure, Measurement, StabilityMap, Transformation},
    domains::{AtomDomain, MapDomain},
    error::Fallible,
    measurements::{
        MakeNoiseThreshold, NoiseThresholdPrivacyMap, ZExpFamily,
        nature::{float::integerize_scale, integer::IntExpFamily},
    },
    metrics::{AbsoluteDistance, L0PInfDistance},
    traits::{Hashable, Integer, Number, SaturatingCast},
    verification::MaybeDeepModel,
};

use super::map_values;
#[cfg(creusot)]
use super::{MapToBigint, int_to_bigint_map_valid};
#[cfg(creusot)]
use crate::{
    measurements::nature::float::number_conversion_facts,
    measurements::nature::integer::ibig_from_facts,
    verification::{RealModel, integer::integer_real, privacy::t_valid},
};
#[cfg(creusot)]
use creusot_std::{
    logic::real::Real,
    macros::{ensures, proof_assert},
    model::DeepModel,
};

#[cfg(test)]
mod test;

#[proven(
    proof_path = "measurements/noise_threshold/nature/integer/MakeNoiseThreshold_MapDomain_for_IntExpFamily.tex"
)]
impl<TK, TV, const P: usize, QI: Number, MO: 'static + Measure>
    MakeNoiseThreshold<
        MapDomain<AtomDomain<TK>, AtomDomain<TV>>,
        L0PInfDistance<P, AbsoluteDistance<QI>>,
        MO,
    > for IntExpFamily<P>
where
    TK: Hashable + MaybeDeepModel,
    TV: Integer + SaturatingCast<IBig>,
    IBig: From<TV>,
    RBig: TryFrom<QI>,
    UBig: TryFrom<TV>,
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
        let distribution = ZExpFamily {
            scale: integerize_scale(self.scale, 0)?,
        };

        let t_int = make_int_to_bigint_threshold::<TK, TV, P, QI>(input_space)?;
        let m_noise =
            distribution.make_noise_threshold(t_int.output_space(), IBig::from(threshold))?;
        let f_native_int = then_saturating_cast_hashmap();

        t_int >> m_noise >> f_native_int
    }
}

/// # Proof Definition
/// For any choice of arguments, returns a valid transformation.
#[proven(
    proof_path = "measurements/noise_threshold/nature/integer/make_int_to_bigint_threshold.tex"
)]
#[cfg_attr(creusot, ensures(forall<t: MapToBigint<TK, TV, P, QI>> result == Ok(t) ==>
    (P == 1usize ==> t_valid(t))))]
fn make_int_to_bigint_threshold<TK, TV, const P: usize, QI: Number>(
    input_space: (
        MapDomain<AtomDomain<TK>, AtomDomain<TV>>,
        L0PInfDistance<P, AbsoluteDistance<QI>>,
    ),
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
    TV: Integer + SaturatingCast<IBig>,
    IBig: From<TV>,
    RBig: TryFrom<QI>,
{
    let (input_domain, input_metric) = input_space;
    let key_domain = input_domain.key_domain.clone();
    let result = Transformation::new(
        input_domain,
        input_metric,
        MapDomain {
            key_domain,
            value_domain: AtomDomain::<IBig>::default(),
        },
        L0PInfDistance::default(),
        Function::new(move |arg: &HashMap<TK, TV>| ints_to_bigints_map(arg)),
        StabilityMap::new_fallible(move |d_in: &(u32, QI, QI)| {
            int_threshold_distance::<P, QI>(d_in)
        }),
    );
    #[cfg(creusot)]
    proof_assert!(forall<x: TV> {
        integer_real(x);
        x.real() == Real::from_int(x.deep_model())
    });
    #[cfg(creusot)]
    proof_assert!(P == 1usize ==> forall<t: MapToBigint<TK, TV, P, QI>> result == Ok(t) ==>
        int_to_bigint_map_valid(t));
    result
}

/// Converts each value of `arg` to `IBig`, keeping the keys.
#[cfg_attr(creusot, ensures(forall<k: TK::DeepModelTy> result@.contains(k) == arg@.contains(k)))]
#[cfg_attr(creusot, ensures(forall<k: TK::DeepModelTy> arg@.contains(k) ==>
    result@[k].deep_model() == arg@[k].deep_model()))]
fn ints_to_bigints_map<TK: Hashable + MaybeDeepModel, TV: Integer>(
    arg: &HashMap<TK, TV>,
) -> HashMap<TK, IBig>
where
    IBig: From<TV>,
{
    #[cfg(creusot)]
    proof_assert!(ibig_from_facts::<TV>());
    map_values(arg, |v: &TV| IBig::from(*v))
}

/// Converts the distances `(l0, lp, li)` to `RBig`, exactly.
#[cfg_attr(creusot, ensures(forall<o: (u32, RBig, RBig)> result == Ok(o) ==>
    o.0 == d_in.0 && o.1.deep_model() == d_in.1.real() && o.2.deep_model() == d_in.2.real()))]
fn int_threshold_distance<const P: usize, QI: Number>(
    d_in: &(u32, QI, QI),
) -> Fallible<(u32, RBig, RBig)>
where
    RBig: TryFrom<QI>,
{
    #[cfg(creusot)]
    proof_assert!(number_conversion_facts::<QI>());
    let (l0, lp, li) = d_in;
    let lp = match RBig::try_from(*lp) {
        Ok(lp) => lp,
        Err(_) => return fallible!(FailedMap, "l{P} ({lp:?}) must be finite"),
    };
    let li = match RBig::try_from(*li) {
        Ok(li) => li,
        Err(_) => return fallible!(FailedMap, "li ({:?}) must be finite", li),
    };
    Ok((*l0, lp, li))
}

/// # Proof Definition
/// For any choice of arguments, returns a valid postprocessor.
#[proven(
    proof_path = "measurements/noise_threshold/nature/integer/then_saturating_cast_hashmap.tex"
)]
// Trusted: a post-processor (any function is valid); `HashMap` iteration has no specification here.
#[cfg_attr(creusot, creusot_std::macros::trusted)]
fn then_saturating_cast_hashmap<TK: Hashable, TV: SaturatingCast<IBig>>()
-> Function<HashMap<TK, IBig>, HashMap<TK, TV>> {
    Function::new(move |arg: &HashMap<TK, IBig>| {
        arg.iter()
            .map(|(k, v)| (k.clone(), TV::saturating_cast(v.clone())))
            .collect()
    })
}
