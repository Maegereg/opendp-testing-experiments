use dashu::{integer::IBig, rational::RBig};
use opendp_derive::proven;

use crate::{
    core::{Measure, Measurement},
    domains::AtomDomain,
    error::Fallible,
    measurements::{MakeNoise, NoisePrivacyMap, ZExpFamily},
    metrics::{AbsoluteDistance, LpDistance},
    transformations::{make_vec, then_index_or_default},
};

#[cfg(test)]
mod test;

/// IBig scalar mechanism
#[proven(proof_path = "measurements/noise/nature/bigint/MakeNoise_AtomDomain_for_ZExpFamily.tex")]
impl<const P: usize, MO> MakeNoise<AtomDomain<IBig>, AbsoluteDistance<RBig>, MO> for ZExpFamily<P>
where
    MO: 'static + Measure,
    ZExpFamily<P>: NoisePrivacyMap<LpDistance<P, RBig>, MO>,
{
    /// The mechanism is proved valid for `P = 1` (the Laplace mechanism).
    #[cfg(creusot)]
    #[creusot_std::macros::logic(open)]
    fn noise_claim(m: Measurement<AtomDomain<IBig>, AbsoluteDistance<RBig>, MO, IBig>) -> bool {
        if P == 1usize {
            crate::verification::privacy::m_valid(m)
        } else {
            true
        }
    }

    #[cfg_attr(creusot, creusot_std::macros::ensures(forall<m: Measurement<AtomDomain<IBig>, AbsoluteDistance<RBig>, MO, IBig>>
        result == Ok(m) ==> Self::noise_claim(m)))]
    fn make_noise(
        self,
        input_space: (AtomDomain<IBig>, AbsoluteDistance<RBig>),
    ) -> Fallible<Measurement<AtomDomain<IBig>, AbsoluteDistance<RBig>, MO, IBig>> {
        let t_vec = make_vec(input_space)?;
        let m_noise = self.make_noise(t_vec.output_space())?;

        t_vec >> m_noise >> then_index_or_default(0)
    }
}
