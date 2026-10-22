use opendp_derive::proven;

#[cfg(creusot)]
use crate::verification::privacy::{singleton_valid, t_valid};
use crate::{
    core::{Function, StabilityMap, Transformation},
    domains::{AtomDomain, VectorDomain},
    error::Fallible,
    metrics::{AbsoluteDistance, LpDistance},
    traits::CheckAtom,
};
// Under Creusot, `vec!` builds the vector through functions with specifications.
#[cfg(creusot)]
use creusot_std::macros::{ensures, proof_assert};
#[cfg(creusot)]
use creusot_std::prelude::vec;

#[proven(proof_path = "transformations/scalar_to_vector/make_vec.tex")]
#[cfg_attr(creusot, ensures(forall<t: Transformation<AtomDomain<T>, AbsoluteDistance<Q>, VectorDomain<AtomDomain<T>>, LpDistance<P, Q>>>
    result == Ok(t) ==> t_valid(t)))]
pub fn make_vec<T, const P: usize, Q>(
    (input_domain, input_metric): (AtomDomain<T>, AbsoluteDistance<Q>),
) -> Fallible<
    Transformation<
        AtomDomain<T>,
        AbsoluteDistance<Q>,
        VectorDomain<AtomDomain<T>>,
        LpDistance<P, Q>,
    >,
>
where
    T: CheckAtom,
    Q: 'static + Clone,
{
    let result = Transformation::new(
        input_domain.clone(),
        input_metric,
        VectorDomain::new(input_domain).with_size(1),
        LpDistance::default(),
        Function::new(move |arg: &T| vec![arg.clone()]),
        StabilityMap::new(Clone::clone),
    );
    #[cfg(creusot)]
    proof_assert!(forall<t: Transformation<AtomDomain<T>, AbsoluteDistance<Q>, VectorDomain<AtomDomain<T>>, LpDistance<P, Q>>>
        result == Ok(t) ==> singleton_valid(t));
    result
}

// Post-processing: no contract is needed.
#[cfg_attr(creusot, creusot_std::macros::trusted)]
#[proven(proof_path = "transformations/scalar_to_vector/then_index_or_default.tex")]
pub(crate) fn then_index_or_default<T: Clone + Default>(i: usize) -> Function<Vec<T>, T> {
    Function::new(move |vec: &Vec<T>| vec.get(i).cloned().unwrap_or_default())
}
