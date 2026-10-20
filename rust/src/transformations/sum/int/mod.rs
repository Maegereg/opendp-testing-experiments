mod checked;
pub use checked::*;

mod monotonic;
pub use monotonic::*;

mod ordered;
pub use ordered::*;

mod split;
pub use split::*;

use std::iter::Sum;

use crate::error::Fallible;
use crate::traits::Integer;
#[cfg(creusot)]
use crate::verification::{
    integer::{integer_saturating_add, isum, prefix_sums_fit, sat_sum},
    real_abs,
};
#[cfg(creusot)]
use creusot_std::{
    logic::real::Real,
    macros::{ensures, invariant, proof_assert, requires, trusted},
};

/// # Proof Definition
/// Returns true if, given data with `size` records, each of which has data bounded between `lower` and `upper`,
/// the true sum of the records exceeds the greatest value representable of type `T`.
// If false, there is a representable bound on `size * max(|lower|, upper)`.
#[cfg_attr(creusot, ensures(!result ==> exists<mag: T, bound: T>
    mag.real() >= real_abs(lower.real()) && mag.real() >= upper.real()
    && bound.real() >= mag.real() * Real::from_int(size@)))]
pub(crate) fn can_int_sum_overflow<T: Integer>(size: usize, (lower, upper): (T, T)) -> bool {
    (|| -> Fallible<()> {
        let size = T::exact_int_cast(size)?;
        let mag = lower.alerting_abs()?.total_max(upper)?;
        mag.inf_mul(&size)?;
        Ok(())
    })()
    .is_err()
}

/// Sum the elements of `arg`, as `arg.iter().sum()` does.
// Trusted: `Iterator::sum` for integers adds the elements in order,
// so it returns the exact sum when no prefix sum overflows.
#[cfg_attr(creusot, trusted)]
#[cfg_attr(creusot, requires(prefix_sums_fit(arg@)))]
#[cfg_attr(creusot, ensures(result.deep_model() == isum(arg@)))]
pub(crate) fn int_sum<T: Integer>(arg: &Vec<T>) -> T
where
    for<'a> T: Sum<&'a T>,
{
    arg.iter().sum()
}

/// Zero.
// Trusted: `num::Zero::zero` has no specification.
#[cfg_attr(creusot, trusted)]
#[cfg_attr(creusot, ensures(result.deep_model() == 0))]
pub(crate) fn int_zero<T: Integer>() -> T {
    T::zero()
}

/// Sum the elements of `arg` with saturating arithmetic, from left to right.
///
/// Equivalent to `arg.iter().fold(T::zero(), |sum, v| sum.saturating_add(v))`.
#[cfg_attr(creusot, ensures(result.deep_model() == sat_sum(arg@)))]
pub(crate) fn saturating_sum<T: Integer>(arg: &Vec<T>) -> T {
    let mut sum = int_zero::<T>();
    let mut i = 0;
    #[cfg_attr(creusot, invariant(i@ <= arg@.len()))]
    #[cfg_attr(creusot, invariant(sum.deep_model() == sat_sum(arg@.subsequence(0, i@))))]
    while i < arg.len() {
        #[cfg(creusot)]
        proof_assert!({ integer_saturating_add(sum, arg[i@]); true });
        #[cfg(creusot)]
        proof_assert!(arg@.subsequence(0, i@ + 1).subsequence(0, i@) == arg@.subsequence(0, i@));
        sum = sum.saturating_add(&arg[i]);
        i += 1;
    }
    #[cfg(creusot)]
    proof_assert!(arg@.subsequence(0, arg@.len()) == arg@);
    sum
}
