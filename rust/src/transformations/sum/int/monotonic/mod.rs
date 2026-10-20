use opendp_derive::bootstrap;

use super::{int_zero, saturating_sum};
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
/// Make a Transformation that computes the sum of bounded ints,
/// where all values share the same sign.
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
#[cfg_attr(creusot, ensures(forall<t: IntSum<T>> result == Ok(t) ==> int_monotonic_sum_contract(t, bounds)))]
pub fn make_bounded_int_monotonic_sum<T: Integer>(
    bounds: (T, T),
) -> Fallible<
    Transformation<
        VectorDomain<AtomDomain<T>>,
        SymmetricDistance,
        AtomDomain<T>,
        AbsoluteDistance<T>,
    >,
> {
    if !signs_agree(bounds) {
        return fallible!(
            MakeTransformation,
            "monotonic summation requires bounds to share the same sign"
        );
    }

    let (lower, upper) = bounds;

    Transformation::new(
        VectorDomain::new(AtomDomain::new_closed(bounds)?),
        SymmetricDistance,
        AtomDomain::default(),
        AbsoluteDistance::default(),
        Function::new(|arg: &Vec<T>| saturating_sum(arg)),
        StabilityMap::new_from_constant(lower.alerting_abs()?.total_max(upper)?),
    )
}

#[bootstrap(features("contrib"), generics(T(example = "$get_first(bounds)")))]
/// Make a Transformation that computes the sum of bounded ints,
/// where all values share the same sign.
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
#[cfg_attr(creusot, ensures(forall<t: IntSum<T>> result == Ok(t) ==> sized_int_monotonic_sum_contract(t, size, bounds)))]
pub fn make_sized_bounded_int_monotonic_sum<T: Integer>(
    size: usize,
    bounds: (T, T),
) -> Fallible<
    Transformation<
        VectorDomain<AtomDomain<T>>,
        SymmetricDistance,
        AtomDomain<T>,
        AbsoluteDistance<T>,
    >,
> {
    if !signs_agree(bounds) {
        return fallible!(
            MakeTransformation,
            "monotonic summation requires bounds to share the same sign"
        );
    }

    let (lower, upper) = bounds;
    let range = upper.inf_sub(&lower)?;

    Transformation::new(
        VectorDomain::new(AtomDomain::new_closed(bounds)?).with_size(size),
        SymmetricDistance,
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

/// # Proof Definition
/// Returns true if and only if the signs of `a` and `b` agree,
/// assuming that values of zero always agree.
#[cfg_attr(creusot, ensures(result == ((a.deep_model() >= 0 && b.deep_model() >= 0)
    || (a.deep_model() <= 0 && b.deep_model() <= 0))))]
pub(crate) fn signs_agree<T: Integer>((a, b): (T, T)) -> bool {
    let _0 = int_zero::<T>();
    a == _0 || b == _0 || (a > _0) == (b > _0)
}

#[cfg(test)]
mod test;
