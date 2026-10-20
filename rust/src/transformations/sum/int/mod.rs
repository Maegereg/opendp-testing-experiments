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
    dataset::sum,
    integer::{isum, prefix_sums_fit},
    real_abs,
};
#[cfg(creusot)]
use creusot_std::{
    logic::real::Real,
    macros::{ensures, requires, trusted},
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
