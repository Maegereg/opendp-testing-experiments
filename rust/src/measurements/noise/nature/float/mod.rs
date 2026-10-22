use dashu::{integer::IBig, rational::RBig};
use opendp_derive::proven;

use crate::{
    core::{Function, Measure, Measurement, StabilityMap, Transformation},
    domains::{AtomDomain, VectorDomain},
    error::Fallible,
    measurements::{MakeNoise, NoisePrivacyMap, ZExpFamily},
    metrics::{AbsoluteDistance, LpDistance},
    traits::{CastInternalRational, ExactIntCast, Float, FloatBits, Number},
    transformations::{make_vec, then_index_or_default},
};

mod utilities;
pub(crate) use utilities::*;

#[cfg(creusot)]
mod proof;
#[cfg(creusot)]
use crate::verification::{cast_metric::number_clone, dashu::pow2r, float::float_grid};
#[cfg(creusot)]
use creusot_std::{
    macros::{ensures, invariant, proof_assert, requires, snapshot},
    model::DeepModel,
};
#[cfg(creusot)]
pub use proof::*;

#[cfg(test)]
mod test;

pub struct FloatExpFamily<const P: usize> {
    pub scale: f64,
    pub k: i32,
}

/// Float vector mechanism
#[proven(
    proof_path = "measurements/noise/nature/float/MakeNoise_VectorDomain_for_FloatExpFamily.tex"
)]
impl<T: Float, const P: usize, QI: Number, MO: 'static + Measure>
    MakeNoise<VectorDomain<AtomDomain<T>>, LpDistance<P, QI>, MO> for FloatExpFamily<P>
where
    i32: ExactIntCast<<T as FloatBits>::Bits>,
    RBig: TryFrom<T> + TryFrom<QI>,
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

    #[cfg_attr(creusot, ensures(forall<m: Measurement<VectorDomain<AtomDomain<T>>, LpDistance<P, QI>, MO, Vec<T>>>
        result == Ok(m) ==> Self::noise_claim(m)))]
    fn make_noise(
        self,
        input_space: (VectorDomain<AtomDomain<T>>, LpDistance<P, QI>),
    ) -> Fallible<Measurement<VectorDomain<AtomDomain<T>>, LpDistance<P, QI>, MO, Vec<T>>> {
        let FloatExpFamily { scale, k } = self;
        let distribution = ZExpFamily {
            scale: integerize_scale(scale, k)?,
        };

        #[cfg(creusot)]
        let dom = snapshot!(input_space.0);
        let t_int = make_float_to_bigint(input_space, k)?;
        #[cfg(creusot)]
        proof_assert!(P == 1usize ==> float_to_bigint_is_valid(t_int, *dom, k));
        let m_noise = distribution.make_noise(t_int.output_space())?;
        t_int >> m_noise >> then_deintegerize_vec(self.k)?
    }
}

#[proven(proof_path = "measurements/noise/nature/float/make_float_to_bigint.tex")]
#[cfg_attr(creusot, ensures(forall<t: FloatToBigint<T, P, QI>> result == Ok(t) ==>
    float_to_bigint_contract(t, input_space.0, k)))]
fn make_float_to_bigint<T: Float, const P: usize, QI: Number>(
    input_space: (VectorDomain<AtomDomain<T>>, LpDistance<P, QI>),
    k: i32,
) -> Fallible<
    Transformation<
        VectorDomain<AtomDomain<T>>,
        LpDistance<P, QI>,
        VectorDomain<AtomDomain<IBig>>,
        LpDistance<P, RBig>,
    >,
>
where
    i32: ExactIntCast<<T as FloatBits>::Bits>,
    RBig: TryFrom<T> + TryFrom<QI>,
{
    let (input_domain, input_metric) = input_space;
    #[cfg(creusot)]
    let dom = snapshot!(input_domain);
    if input_domain.element_domain.nan() {
        return fallible!(
            MakeTransformation,
            "input_domain may not contain NaN elements"
        );
    }
    let size = input_domain.size;
    let rounding_distance = get_rounding_distance::<T, P>(k, size)?;
    #[cfg(creusot)]
    proof_assert!(float_grid::<T>() && k@ > i32::MIN@);
    #[cfg(creusot)]
    proof_assert!(P == 1usize ==> rounding_distance.deep_model() == proof::rounding_distance::<T>(k@, dom.size));

    Transformation::new(
        input_domain,
        input_metric.clone(),
        VectorDomain {
            element_domain: AtomDomain::<IBig>::default(),
            size,
        },
        LpDistance::default(),
        Function::new(move |arg: &Vec<T>| discretize_vec(arg, k)),
        StabilityMap::new_fallible(move |d_in: &QI| {
            discretized_distance(d_in, &rounding_distance, k)
        }),
    )
}

/// The distance between discretized datasets: `(d_in + rounding_distance) / 2^k`.
#[cfg_attr(creusot, requires(k@ > i32::MIN@))]
#[cfg_attr(creusot, ensures(forall<o: RBig> result == Ok(o) ==>
    o.deep_model() == ((*d_in).real() + rounding_distance.deep_model()) * pow2r(-k@)))]
fn discretized_distance<QI: Number>(d_in: &QI, rounding_distance: &RBig, k: i32) -> Fallible<RBig>
where
    RBig: TryFrom<QI>,
{
    #[cfg(creusot)]
    proof_assert!(number_conversion_facts::<QI>() && number_clone::<QI>());
    let d_in = RBig::try_from(d_in.clone())
        .map_err(|_| err!(FailedMap, "d_in ({:?}) must be finite", d_in))?;
    Ok(x_mul_2k(d_in + rounding_distance.clone(), -k))
}

/// Rounds each element of `arg`, clamped to the finite range, to the nearest multiple of `2^k`,
/// returned as the integer multiple.
#[cfg_attr(creusot, requires(k@ > i32::MIN@))]
#[cfg_attr(creusot, ensures(result@.len() == arg@.len()))]
#[cfg_attr(creusot, ensures(forall<i> 0 <= i && i < arg@.len() ==> rounds_to(arg@[i], result@[i], k@)))]
fn discretize_vec<T: Float>(arg: &Vec<T>, k: i32) -> Vec<IBig>
where
    RBig: TryFrom<T>,
{
    #[cfg(creusot)]
    proof_assert!(float_conversion_facts::<T>());
    let mut out = Vec::with_capacity(arg.len());
    #[cfg_attr(creusot, invariant(out@.len() == produced.len()
        && forall<j> 0 <= j && j < out@.len() ==> rounds_to(arg@[j], out@[j], k@)))]
    for i in 0..arg.len() {
        let clamped = arg[i].clamp(T::MIN_FINITE, T::MAX_FINITE);
        #[cfg(creusot)]
        proof_assert!(clamped == fclamp(arg@[i@]));
        let x_i = RBig::try_from(clamped).unwrap_or(RBig::from(0usize));
        #[cfg(creusot)]
        proof_assert!(arg@[i@].non_null() ==> x_i.deep_model() == fclamp(arg@[i@]).real());
        let n = find_nearest_multiple_of_2k(x_i, k);
        #[cfg(creusot)]
        proof_assert!(rounds_to(arg@[i@], n, k@));
        out.push(n);
    }
    out
}

/// Float scalar mechanism
#[proven(
    proof_path = "measurements/noise/nature/float/MakeNoise_AtomDomain_for_FloatExpFamily.tex"
)]
impl<T: Float, const P: usize, QI: Number, MO: 'static + Measure>
    MakeNoise<AtomDomain<T>, AbsoluteDistance<QI>, MO> for FloatExpFamily<P>
where
    i32: ExactIntCast<<T as FloatBits>::Bits>,
    RBig: TryFrom<T> + TryFrom<QI>,
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

    #[cfg_attr(creusot, ensures(forall<m: Measurement<AtomDomain<T>, AbsoluteDistance<QI>, MO, T>>
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

#[cfg_attr(creusot, creusot_std::macros::trusted)]
#[proven(proof_path = "measurements/noise/nature/float/then_deintegerize_vec.tex")]
pub fn then_deintegerize_vec<TO: CastInternalRational>(
    k: i32,
) -> Fallible<Function<Vec<IBig>, Vec<TO>>> {
    if k == i32::MIN {
        return fallible!(MakeTransformation, "k must not be i32::MIN");
    }
    Ok(Function::new(move |x: &Vec<IBig>| {
        x.iter()
            .cloned()
            .map(|x_i| TO::from_rational(x_mul_2k(RBig::from(x_i), k)))
            .collect()
    }))
}
