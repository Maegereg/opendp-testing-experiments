use opendp_derive::bootstrap;

use super::saturating_sum;
use crate::{
    core::{Function, StabilityMap, Transformation},
    domains::{AtomDomain, VectorDomain},
    error::Fallible,
    metrics::{AbsoluteDistance, InsertDeleteDistance, IntDistance},
    traits::Integer,
};
#[cfg(creusot)]
use creusot_std::macros::ensures;

#[cfg(creusot)]
mod proof;
#[cfg(creusot)]
pub use proof::*;

#[cfg(feature = "ffi")]
mod ffi;

#[bootstrap(features("contrib"), generics(T(example = "$get_first(bounds)")))]
/// Make a Transformation that computes the sum of bounded ints.
/// You may need to use `make_ordered_random` to impose an ordering on the data.
///
/// # Citations
/// * [CSVW22 Widespread Underestimation of Sensitivity...](https://arxiv.org/pdf/2207.10635.pdf)
/// * [DMNS06 Calibrating Noise to Sensitivity in Private Data Analysis](https://people.csail.mit.edu/asmith/PS/sensitivity-tcc-final.pdf)
///
/// # Arguments
/// * `bounds` - Tuple of lower and upper bounds for data in the input domain.
///
/// # Generics
/// * `T` - Atomic Input Type and Output Type
#[cfg_attr(creusot, ensures(forall<t: OrderedIntSum<T>> result == Ok(t) ==> int_ordered_sum_contract(t, bounds)))]
pub fn make_bounded_int_ordered_sum<T>(
    bounds: (T, T),
) -> Fallible<
    Transformation<
        VectorDomain<AtomDomain<T>>,
        InsertDeleteDistance,
        AtomDomain<T>,
        AbsoluteDistance<T>,
    >,
>
where
    T: Integer,
{
    let (lower, upper) = bounds;
    Transformation::new(
        VectorDomain::new(AtomDomain::new_closed(bounds)?),
        InsertDeleteDistance,
        AtomDomain::default(),
        AbsoluteDistance::default(),
        Function::new(|arg: &Vec<T>| saturating_sum(arg)),
        StabilityMap::new_from_constant(lower.alerting_abs()?.total_max(upper)?),
    )
}

#[bootstrap(features("contrib"), generics(T(example = "$get_first(bounds)")))]
/// Make a Transformation that computes the sum of bounded ints with known dataset size.
///
/// This uses a restricted-sensitivity proof that takes advantage of known dataset size for better utility.
/// You may need to use `make_ordered_random` to impose an ordering on the data.
///
/// # Citations
/// * [CSVW22 Widespread Underestimation of Sensitivity...](https://arxiv.org/pdf/2207.10635.pdf)
/// * [DMNS06 Calibrating Noise to Sensitivity in Private Data Analysis](https://people.csail.mit.edu/asmith/PS/sensitivity-tcc-final.pdf)
///
/// # Arguments
/// * `size` - Number of records in input data.
/// * `bounds` - Tuple of lower and upper bounds for data in the input domain.
///
/// # Generics
/// * `T` - Atomic Input Type and Output Type
#[cfg_attr(creusot, ensures(forall<t: OrderedIntSum<T>> result == Ok(t) ==> sized_int_ordered_sum_contract(t, size, bounds)))]
pub fn make_sized_bounded_int_ordered_sum<T>(
    size: usize,
    bounds: (T, T),
) -> Fallible<
    Transformation<
        VectorDomain<AtomDomain<T>>,
        InsertDeleteDistance,
        AtomDomain<T>,
        AbsoluteDistance<T>,
    >,
>
where
    T: Integer,
{
    let (lower, upper) = bounds;
    let range = upper.inf_sub(&lower)?;
    Transformation::new(
        VectorDomain::new(AtomDomain::new_closed(bounds)?).with_size(size),
        InsertDeleteDistance,
        AtomDomain::default(),
        AbsoluteDistance::default(),
        Function::new(|arg: &Vec<T>| saturating_sum(arg)),
        StabilityMap::new_fallible(
            // If d_in is odd, we still only consider databases with (d_in - 1) / 2 substitutions,
            //    so floor division is acceptable
            move |d_in: &IntDistance| T::inf_cast(d_in / 2)?.inf_mul(&range),
        ),
    )
}

#[cfg(test)]
mod test;
