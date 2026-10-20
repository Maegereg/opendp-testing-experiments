use std::iter::Sum;

use opendp_derive::bootstrap;

use super::{can_int_sum_overflow, int_sum};
use crate::{
    core::{Function, StabilityMap, Transformation},
    domains::{AtomDomain, VectorDomain},
    error::Fallible,
    metrics::{AbsoluteDistance, IntDistance, SymmetricDistance},
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
/// The effective range is reduced, as (bounds * size) must not overflow.
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
#[cfg_attr(creusot, ensures(forall<t: SizedIntSum<T>> result == Ok(t) ==> sized_int_checked_sum_contract(t, size, bounds)))]
pub fn make_sized_bounded_int_checked_sum<T: Integer>(
    size: usize,
    bounds: (T, T),
) -> Fallible<
    Transformation<
        VectorDomain<AtomDomain<T>>,
        SymmetricDistance,
        AtomDomain<T>,
        AbsoluteDistance<T>,
    >,
>
where
    for<'a> T: Sum<&'a T>,
{
    if can_int_sum_overflow(size, bounds) {
        return fallible!(
            MakeTransformation,
            "potential for overflow when computing function. You could resolve this by choosing tighter clipping bounds or by using a data type with greater bit-depth."
        );
    }

    let (lower, upper) = bounds;
    let range = upper.inf_sub(&lower)?;
    Transformation::new(
        VectorDomain::new(AtomDomain::new_closed(bounds)?).with_size(size),
        SymmetricDistance,
        AtomDomain::default(),
        AbsoluteDistance::default(),
        Function::new(|arg: &Vec<T>| int_sum(arg)),
        StabilityMap::new_fallible(
            // If d_in is odd, we still only consider databases with (d_in - 1) / 2 substitutions,
            //    so floor division is acceptable
            move |d_in: &IntDistance| T::inf_cast(d_in / 2)?.inf_mul(&range),
        ),
    )
}

#[cfg(test)]
mod test;
