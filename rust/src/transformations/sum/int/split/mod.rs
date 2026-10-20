use opendp_derive::bootstrap;

use super::split_saturating_sum;
#[cfg(creusot)]
use crate::verification::integer::{clamp, isum_neg, isum_pos};
use crate::{
    core::{Function, StabilityMap, Transformation},
    domains::{AtomDomain, VectorDomain},
    error::Fallible,
    metrics::{AbsoluteDistance, IntDistance, SymmetricDistance},
    traits::Integer,
};
#[cfg(creusot)]
use creusot_std::{macros::ensures, model::DeepModel};

#[cfg(creusot)]
mod proof;
#[cfg(creusot)]
pub use proof::*;

#[cfg(feature = "ffi")]
mod ffi;

#[doc(hidden)]
pub trait SplitSatSum: Integer {
    /// Method which takes an iterator and generates `Self` from the elements by
    /// "summing up" the items.
    #[allow(clippy::ptr_arg)]
    #[cfg_attr(creusot, ensures(result.deep_model()
        == clamp::<Self>(clamp::<Self>(isum_neg(v@)) + clamp::<Self>(isum_pos(v@)))))]
    fn split_sat_sum(v: &Vec<Self>) -> Self;
}

// Unsigned integers have no negative elements, so this is the saturating sum.
// Signed integers sum negative and positive elements separately,
// so that saturation does not depend on the order of the elements.
macro_rules! impl_int_split_sat_sum {
    ($($ty:ty)+) => ($(impl SplitSatSum for $ty {
        #[cfg_attr(creusot, ensures(result.deep_model()
            == clamp::<Self>(clamp::<Self>(isum_neg(v@)) + clamp::<Self>(isum_pos(v@)))))]
        fn split_sat_sum(v: &Vec<Self>) -> Self {
            split_saturating_sum(v)
        }
    })+);
}

impl_int_split_sat_sum! { u8 u16 u32 u64 u128 usize }
impl_int_split_sat_sum! { i8 i16 i32 i64 i128 isize }

#[bootstrap(features("contrib"), generics(T(example = "$get_first(bounds)")))]
/// Make a Transformation that computes the sum of bounded ints.
/// Adds the saturating sum of the positives to the saturating sum of the negatives.
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
#[cfg_attr(creusot, ensures(forall<t: IntSum<T>> result == Ok(t) ==> int_split_sum_contract(t, bounds)))]
pub fn make_bounded_int_split_sum<T>(
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
    T: Integer + SplitSatSum,
{
    let (lower, upper) = bounds;

    Transformation::new(
        VectorDomain::new(AtomDomain::new_closed(bounds)?),
        SymmetricDistance,
        AtomDomain::default(),
        AbsoluteDistance::default(),
        Function::new(|arg: &Vec<T>| T::split_sat_sum(arg)),
        StabilityMap::new_from_constant(lower.alerting_abs()?.total_max(upper)?),
    )
}

#[bootstrap(features("contrib"), generics(T(example = "$get_first(bounds)")))]
/// Make a Transformation that computes the sum of bounded ints with known dataset size.
///
/// This uses a restricted-sensitivity proof that takes advantage of known dataset size for better utility.
/// Adds the saturating sum of the positives to the saturating sum of the negatives.
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
#[cfg_attr(creusot, ensures(forall<t: IntSum<T>> result == Ok(t) ==> sized_int_split_sum_contract(t, size, bounds)))]
pub fn make_sized_bounded_int_split_sum<T>(
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
    T: Integer + SplitSatSum,
{
    let (lower, upper) = bounds;
    let range = upper.inf_sub(&lower)?;
    Transformation::new(
        VectorDomain::new(AtomDomain::new_closed(bounds)?).with_size(size),
        SymmetricDistance,
        AtomDomain::default(),
        AbsoluteDistance::default(),
        Function::new(|arg: &Vec<T>| T::split_sat_sum(arg)),
        StabilityMap::new_fallible(
            // If d_in is odd, we still only consider databases with (d_in - 1) / 2 substitutions,
            //    so floor division is acceptable
            move |d_in: &IntDistance| T::inf_cast(d_in / 2)?.inf_mul(&range),
        ),
    )
}

#[cfg(test)]
mod test;
