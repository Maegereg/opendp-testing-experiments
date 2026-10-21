use opendp_derive::bootstrap;

use crate::{
    core::{Function, StabilityMap, Transformation},
    domains::{AtomDomain, VectorDomain},
    error::Fallible,
    metrics::{AbsoluteDistance, InsertDeleteDistance, IntDistance},
    traits::{AlertingAbs, InfAdd, InfCast, InfMul, InfSub, ProductOrd},
};

use super::{Float, Pairwise, Sequential, SumRelaxation};
#[cfg(creusot)]
use creusot_std::{
    logic::Seq,
    macros::{ensures, logic, trusted},
};

#[cfg(creusot)]
mod proof;
#[cfg(creusot)]
pub use proof::*;

#[cfg(feature = "ffi")]
mod ffi;

#[bootstrap(
    features("contrib"),
    arguments(bounds(rust_type = "(T, T)")),
    generics(S(default = "Pairwise<T>")),
    derived_types(T = "$get_atom_or_infer(S, get_first(bounds))")
)]
/// Make a Transformation that computes the sum of bounded floats with known ordering.
///
/// Only useful when `make_bounded_float_checked_sum` returns an error due to potential for overflow.
/// You may need to use `make_ordered_random` to impose an ordering on the data.
/// The utility loss from overestimating the `size_limit` is small.
///
/// | S (summation algorithm) | input type     |
/// | ----------------------- | -------------- |
/// | `Sequential<S::Item>`   | `Vec<S::Item>` |
/// | `Pairwise<S::Item>`     | `Vec<S::Item>` |
///
/// `S::Item` is the type of all of the following:
/// each bound, each element in the input data, the output data, and the output sensitivity.
///
/// For example, to construct a transformation that pairwise-sums `f32` half-precision floats,
/// set `S` to `Pairwise<f32>`.
///
/// # Citations
/// * [CSVW22 Widespread Underestimation of Sensitivity...](https://arxiv.org/pdf/2207.10635.pdf)
/// * [DMNS06 Calibrating Noise to Sensitivity in Private Data Analysis](https://people.csail.mit.edu/asmith/PS/sensitivity-tcc-final.pdf)
///
/// # Arguments
/// * `size_limit` - Upper bound on the number of records in input data. Used to bound sensitivity.
/// * `bounds` - Tuple of lower and upper bounds for data in the input domain.
///
/// # Generics
/// * `S` - Summation algorithm to use over some data type `T` (`T` is shorthand for `S::Item`)
#[cfg_attr(creusot, ensures(forall<t: FloatOrderedSum<S::Item>> result == Ok(t) ==>
    float_ordered_sum_contract::<S>(t, size_limit, bounds)))]
pub fn make_bounded_float_ordered_sum<S>(
    size_limit: usize,
    bounds: (S::Item, S::Item),
) -> Fallible<
    Transformation<
        VectorDomain<AtomDomain<S::Item>>,
        InsertDeleteDistance,
        AtomDomain<S::Item>,
        AbsoluteDistance<S::Item>,
    >,
>
where
    S: SaturatingSum,
    S::Item: 'static + Float,
{
    let (lower, upper) = bounds;
    let ideal_sensitivity = upper
        .inf_sub(&lower)?
        .total_max(lower.alerting_abs()?.total_max(upper)?)?;
    let relaxation = S::relaxation(size_limit, lower, upper)?;

    Transformation::new(
        VectorDomain::new(AtomDomain::new_closed(bounds)?),
        InsertDeleteDistance,
        AtomDomain::new_non_nan(),
        AbsoluteDistance::default(),
        Function::new(move |arg: &Vec<S::Item>| {
            S::saturating_sum(&arg[..size_limit.min(arg.len())])
        }),
        StabilityMap::new_fallible(move |d_in: &IntDistance| {
            // d_out =  |BS*(v) - BS*(v')| where BS* is the finite sum and BS the ideal sum
            //       <= |BS*(v) - BS(v)| + |BS(v) - BS(v')| + |BS(v') - BS*(v')|
            //       <= d_in * ideal_sens + 2 * error
            //       =  d_in * ideal_sens + relaxation
            S::Item::inf_cast(*d_in)?
                .inf_mul(&ideal_sensitivity)?
                .inf_add(&relaxation)
        }),
    )
}

#[bootstrap(
    features("contrib"),
    arguments(bounds(rust_type = "(T, T)")),
    generics(S(default = "Pairwise<T>")),
    derived_types(T = "$get_atom_or_infer(S, get_first(bounds))")
)]
/// Make a Transformation that computes the sum of bounded floats with known ordering and dataset size.
///
/// Only useful when `make_bounded_float_checked_sum` returns an error due to potential for overflow.
/// This uses a restricted-sensitivity proof that takes advantage of known dataset size for better utility.
/// You may need to use `make_ordered_random` to impose an ordering on the data.
///
/// | S (summation algorithm) | input type     |
/// | ----------------------- | -------------- |
/// | `Sequential<S::Item>`   | `Vec<S::Item>` |
/// | `Pairwise<S::Item>`     | `Vec<S::Item>` |
///
/// `S::Item` is the type of all of the following:
/// each bound, each element in the input data, the output data, and the output sensitivity.
///
/// For example, to construct a transformation that pairwise-sums `f32` half-precision floats,
/// set `S` to `Pairwise<f32>`.
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
/// * `S` - Summation algorithm to use over some data type `T` (`T` is shorthand for `S::Item`)
#[cfg_attr(creusot, ensures(forall<t: FloatOrderedSum<S::Item>> result == Ok(t) ==>
    sized_float_ordered_sum_contract::<S>(t, size, bounds)))]
pub fn make_sized_bounded_float_ordered_sum<S>(
    size: usize,
    bounds: (S::Item, S::Item),
) -> Fallible<
    Transformation<
        VectorDomain<AtomDomain<S::Item>>,
        InsertDeleteDistance,
        AtomDomain<S::Item>,
        AbsoluteDistance<S::Item>,
    >,
>
where
    S: SaturatingSum,
    S::Item: 'static + Float,
{
    let (lower, upper) = bounds;
    let ideal_sensitivity = upper.inf_sub(&lower)?;
    let relaxation = S::relaxation(size, lower, upper)?;

    Transformation::new(
        VectorDomain::new(AtomDomain::new_closed(bounds)?).with_size(size),
        InsertDeleteDistance,
        AtomDomain::new_non_nan(),
        AbsoluteDistance::default(),
        Function::new(move |arg: &Vec<S::Item>| S::saturating_sum(arg)),
        StabilityMap::new_fallible(move |d_in: &IntDistance| {
            // d_out =  |BS*(v) - BS*(v')| where BS* is the finite sum and BS the ideal sum
            //       <= |BS*(v) - BS(v)| + |BS(v) - BS(v')| + |BS(v') - BS*(v')|
            //       <= d_in / 2 * (U - L) + 2 * error
            //       =  d_in / 2 * (U - L) + relaxation
            S::Item::inf_cast(d_in / 2)?
                .inf_mul(&ideal_sensitivity)?
                .inf_add(&relaxation)
        }),
    )
}

#[doc(hidden)]
pub trait SaturatingSum: SumRelaxation {
    /// The result of `saturating_sum`.
    #[cfg(creusot)]
    #[logic]
    fn saturating_sum_logic(arg: Seq<Self::Item>) -> Self::Item;

    #[cfg_attr(creusot, ensures(result == Self::saturating_sum_logic(arg@)))]
    fn saturating_sum(arg: &[Self::Item]) -> Self::Item;
}

impl<T: Float> SaturatingSum for Sequential<T> {
    /// `OpenDP.Float.Fmt.satSeqSum` (`verification/lean`).
    #[cfg(creusot)]
    #[logic(opaque)]
    fn saturating_sum_logic(arg: Seq<T>) -> T {
        dead
    }

    // Trusted: the fold is modeled in Lean (`satSeqSum`), which bounds its rounding error.
    #[cfg_attr(creusot, trusted)]
    #[cfg_attr(creusot, ensures(result == Self::saturating_sum_logic(arg@)))]
    fn saturating_sum(arg: &[T]) -> T {
        arg.iter().fold(T::zero(), |sum, v| sum.saturating_add(v))
    }
}

impl<T: Float> SaturatingSum for Pairwise<T> {
    /// Unspecified: the pairwise saturating sum is not stable (`FINDINGS.md`, F2).
    #[cfg(creusot)]
    #[logic(opaque)]
    fn saturating_sum_logic(arg: Seq<T>) -> T {
        dead
    }

    #[cfg_attr(creusot, trusted)]
    #[cfg_attr(creusot, ensures(result == Self::saturating_sum_logic(arg@)))]
    fn saturating_sum(arg: &[T]) -> T {
        match arg.len() {
            0 => T::zero(),
            1 => arg[0],
            n => {
                let m = n / 2;
                Self::saturating_sum(&arg[..m]).saturating_add(&Self::saturating_sum(&arg[m..]))
            }
        }
    }
}

#[cfg(test)]
mod test;
