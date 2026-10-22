use dashu::{integer::IBig, rational::RBig};
use opendp_derive::proven;

use crate::{
    core::{Function, Measure, Measurement, StabilityMap, Transformation},
    domains::{AtomDomain, VectorDomain},
    error::Fallible,
    measurements::{MakeNoise, NoisePrivacyMap, ZExpFamily},
    metrics::{AbsoluteDistance, LpDistance},
    traits::{Integer, Number, SaturatingCast},
    transformations::{make_vec, then_index_or_default},
};

use super::float::integerize_scale;

#[cfg(creusot)]
mod proof;
#[cfg(creusot)]
use super::float::number_conversion_facts;
#[cfg(creusot)]
use crate::verification::privacy::t_valid;
#[cfg(creusot)]
use creusot_std::{
    macros::{ensures, invariant, proof_assert, snapshot},
    model::DeepModel,
};
#[cfg(creusot)]
pub use proof::*;

#[cfg(test)]
mod test;

pub struct IntExpFamily<const P: usize> {
    pub scale: f64,
}

/// # Proof Definition
/// For any choice of arguments, returns a valid measurement.
#[proven(proof_path = "measurements/noise/nature/integer/make_int_to_bigint.tex")]
#[cfg_attr(creusot, ensures(forall<t: IntToBigint<T, P, QI>> result == Ok(t) ==> t_valid(t)))]
fn make_int_to_bigint<T: Integer, const P: usize, QI: Number>(
    (input_domain, input_metric): (VectorDomain<AtomDomain<T>>, LpDistance<P, QI>),
) -> Fallible<
    Transformation<
        VectorDomain<AtomDomain<T>>,
        LpDistance<P, QI>,
        VectorDomain<AtomDomain<IBig>>,
        LpDistance<P, RBig>,
    >,
>
where
    IBig: From<T>,
    RBig: TryFrom<QI>,
{
    let result = Transformation::new(
        input_domain.clone(),
        input_metric,
        VectorDomain {
            element_domain: AtomDomain::<IBig>::default(),
            size: input_domain.size.clone(),
        },
        LpDistance::default(),
        Function::new(move |x: &Vec<T>| ints_to_bigints(x)),
        StabilityMap::new_fallible(move |d_in: &QI| to_rbig(d_in)),
    );
    #[cfg(creusot)]
    proof_assert!(forall<t: IntToBigint<T, P, QI>> result == Ok(t) ==> int_to_bigint_valid(t));
    result
}

/// Converts each element of `x` to `IBig`.
#[cfg_attr(creusot, ensures(result@.len() == x@.len()))]
#[cfg_attr(creusot, ensures(forall<i> 0 <= i && i < x@.len() ==>
    result@[i].deep_model() == x@[i].deep_model()))]
fn ints_to_bigints<T: Integer>(x: &Vec<T>) -> Vec<IBig>
where
    IBig: From<T>,
{
    #[cfg(creusot)]
    proof_assert!(ibig_from_facts::<T>());
    let mut out: Vec<IBig> = Vec::with_capacity(x.len());
    #[cfg_attr(creusot, invariant(out@.len() == produced.len()
        && forall<j> 0 <= j && j < out@.len() ==> out@[j].deep_model() == x@[j].deep_model()))]
    for i in 0..x.len() {
        out.push(IBig::from(x[i]));
    }
    out
}

/// Converts the distance `d_in` to `RBig`, exactly.
#[cfg_attr(creusot, ensures(forall<o: RBig> result == Ok(o) ==> o.deep_model() == (*d_in).real()))]
fn to_rbig<QI: Number>(d_in: &QI) -> Fallible<RBig>
where
    RBig: TryFrom<QI>,
{
    #[cfg(creusot)]
    proof_assert!(number_conversion_facts::<QI>());
    let d_in = *d_in;
    RBig::try_from(d_in).map_err(|_| err!(FailedMap, "d_in ({d_in:?}) must be finite"))
}

/// Integer scalar mechanism
#[proven(
    proof_path = "measurements/noise/nature/integer/MakeNoise_AtomDomain_for_IntExpFamily.tex"
)]
impl<T, const P: usize, QI, MO> MakeNoise<AtomDomain<T>, AbsoluteDistance<QI>, MO>
    for IntExpFamily<P>
where
    T: Integer + SaturatingCast<IBig>,
    QI: Number,
    MO: 'static + Measure,
    IBig: From<T>,
    RBig: TryFrom<QI>,
    ZExpFamily<P>: NoisePrivacyMap<LpDistance<P, RBig>, MO>,
{
    /// The mechanism is proved valid for `P = 1` (the Laplace mechanism).
    #[cfg(creusot)]
    #[creusot_std::macros::logic(open)]
    fn noise_claim(m: Measurement<AtomDomain<T>, AbsoluteDistance<QI>, MO, T>) -> bool {
        if P == 1usize {
            crate::verification::privacy::m_valid(m)
        } else {
            true
        }
    }

    #[cfg_attr(creusot, creusot_std::macros::ensures(forall<m: Measurement<AtomDomain<T>, AbsoluteDistance<QI>, MO, T>>
        result == Ok(m) ==> Self::noise_claim(m)))]
    fn make_noise(
        self,
        input_space: (AtomDomain<T>, AbsoluteDistance<QI>),
    ) -> Fallible<Measurement<AtomDomain<T>, AbsoluteDistance<QI>, MO, T>> {
        let t_vec = make_vec(input_space)?;
        let m_noise = self.make_noise(t_vec.output_space())?;

        t_vec >> m_noise >> then_index_or_default(0)
    }
}

/// Integer vector mechanism
#[proven(
    proof_path = "measurements/noise/nature/integer/MakeNoise_VectorDomain_for_IntExpFamily.tex"
)]
impl<T, const P: usize, QI: Number, MO>
    MakeNoise<VectorDomain<AtomDomain<T>>, LpDistance<P, QI>, MO> for IntExpFamily<P>
where
    T: Integer + SaturatingCast<IBig>,
    MO: 'static + Measure,
    IBig: From<T>,
    RBig: TryFrom<QI>,
    ZExpFamily<P>: NoisePrivacyMap<LpDistance<P, RBig>, MO>,
{
    /// The mechanism is proved valid for `P = 1` (the Laplace mechanism).
    #[cfg(creusot)]
    #[creusot_std::macros::logic(open)]
    fn noise_claim(
        m: Measurement<VectorDomain<AtomDomain<T>>, LpDistance<P, QI>, MO, Vec<T>>,
    ) -> bool {
        if P == 1usize {
            crate::verification::privacy::m_valid(m)
        } else {
            true
        }
    }

    #[cfg_attr(creusot, creusot_std::macros::ensures(forall<m: Measurement<VectorDomain<AtomDomain<T>>, LpDistance<P, QI>, MO, Vec<T>>>
        result == Ok(m) ==> Self::noise_claim(m)))]
    fn make_noise(
        self,
        input_space: (VectorDomain<AtomDomain<T>>, LpDistance<P, QI>),
    ) -> Fallible<Measurement<VectorDomain<AtomDomain<T>>, LpDistance<P, QI>, MO, Vec<T>>> {
        let distribution = ZExpFamily {
            scale: integerize_scale(self.scale, 0)?,
        };

        let t_int = make_int_to_bigint(input_space)?;
        let m_noise = distribution.make_noise(t_int.output_space())?;
        t_int >> m_noise >> then_saturating_cast()
    }
}

/// # Proof Definition
/// For any choice of arguments, returns a valid postprocessor.
#[cfg_attr(creusot, creusot_std::macros::trusted)]
#[proven(proof_path = "measurements/noise/nature/integer/then_saturating_cast.tex")]
fn then_saturating_cast<TO: SaturatingCast<IBig>>() -> Function<Vec<IBig>, Vec<TO>> {
    Function::new(move |x: &Vec<IBig>| x.into_iter().cloned().map(TO::saturating_cast).collect())
}
