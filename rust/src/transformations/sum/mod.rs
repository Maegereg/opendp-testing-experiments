#[cfg(feature = "ffi")]
mod ffi;

mod int;
pub use int::*;

mod float;
pub use float::*;
use opendp_derive::bootstrap;

use crate::core::{Metric, MetricSpace, Transformation};
use crate::domains::{AtomDomain, VectorDomain};
use crate::error::*;
use crate::metrics::{AbsoluteDistance, InsertDeleteDistance, SymmetricDistance};
use crate::traits::{CheckAtom, Float, Integer};
use crate::transformations::{make_ordered_random, make_unordered};
#[cfg(creusot)]
use creusot_std::prelude::*;
use int::{can_int_sum_overflow, signs_agree};
use std::iter::Sum;

#[cfg(creusot)]
mod proof;
#[cfg(creusot)]
pub use proof::*;

#[cfg(all(test, feature = "partials"))]
mod test;

#[bootstrap(features("contrib"), generics(MI(suppress), T(suppress)))]
/// Make a Transformation that computes the sum of bounded data.
/// Use `make_clamp` to bound data.
///
/// If dataset size is known, uses a restricted-sensitivity proof that takes advantage of known dataset size for better utility.
///
/// # Citations
/// * [CSVW22 Widespread Underestimation of Sensitivity...](https://arxiv.org/pdf/2207.10635.pdf)
/// * [DMNS06 Calibrating Noise to Sensitivity in Private Data Analysis](https://people.csail.mit.edu/asmith/PS/sensitivity-tcc-final.pdf)
///
/// # Arguments
/// * `input_domain` - Domain of the input data.
/// * `input_metric` - One of `SymmetricDistance` or `InsertDeleteDistance`.
/// * `bounds` - Tuple of lower and upper bounds for data in the input domain.
///
/// # Generics
/// * `MI` - Input Metric. One of `SymmetricDistance` or `InsertDeleteDistance`.
/// * `T` - Atomic Input Type and Output Type.
#[cfg_attr(creusot, ensures(forall<t: Transformation<VectorDomain<AtomDomain<T>>, MI, AtomDomain<T>, AbsoluteDistance<T>>>
    result == Ok(t) ==> T::sum_is_stable(t, input_domain)))]
pub fn make_sum<MI, T>(
    input_domain: VectorDomain<AtomDomain<T>>,
    input_metric: MI,
) -> Fallible<Transformation<VectorDomain<AtomDomain<T>>, MI, AtomDomain<T>, AbsoluteDistance<T>>>
where
    MI: Metric,
    T: MakeSum<MI>,
    (VectorDomain<AtomDomain<T>>, MI): MetricSpace,
    (AtomDomain<T>, AbsoluteDistance<T>): MetricSpace,
{
    T::make_sum(input_domain, input_metric)
}

// make_sum

// implementations delegate to:
// make_(sized_)?bounded_int_(checked|monotonic|ordered|split)_sum
// make_(sized_)?bounded_float_(checked|ordered)_sum

#[doc(hidden)]
pub trait MakeSum<MI: Metric>: CheckAtom
where
    (VectorDomain<AtomDomain<Self>>, MI): MetricSpace,
    (AtomDomain<Self>, AbsoluteDistance<Self>): MetricSpace,
{
    /// Ghost model: `t` is stable on `input_domain` (defined by each implementation).
    #[cfg(creusot)]
    #[logic(prophetic)]
    fn sum_is_stable(
        t: Transformation<
            VectorDomain<AtomDomain<Self>>,
            MI,
            AtomDomain<Self>,
            AbsoluteDistance<Self>,
        >,
        input_domain: VectorDomain<AtomDomain<Self>>,
    ) -> bool;

    /// # Proof Definition
    /// For any given input domain and input metric,
    /// returns `Ok(out)` where `out` is a valid transformation,
    /// or `Err(e)`.
    #[cfg_attr(creusot, ensures(forall<t: Transformation<VectorDomain<AtomDomain<Self>>, MI, AtomDomain<Self>, AbsoluteDistance<Self>>>
        result == Ok(t) ==> Self::sum_is_stable(t, input_domain)))]
    fn make_sum(
        input_domain: VectorDomain<AtomDomain<Self>>,
        input_metric: MI,
    ) -> Fallible<
        Transformation<
            VectorDomain<AtomDomain<Self>>,
            MI,
            AtomDomain<Self>,
            AbsoluteDistance<Self>,
        >,
    >;
}

#[cfg_attr(creusot, ensures(forall<t: SumT<T, SymmetricDistance>> result == Ok(t) ==>
    int_sym_sum_is_stable(t, input_domain)))]
fn make_int_sum_symmetric<T>(
    input_domain: VectorDomain<AtomDomain<T>>,
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
    for<'a> T: Sum<&'a T>,
{
    let bounds = input_domain
        .element_domain
        .bounds
        .ok_or_else(|| {
            err!(
                MakeTransformation,
                "`input_domain` must be bounded. Use `make_clamp` to bound data."
            )
        })?
        .get_closed()?;

    if let Some(size) = input_domain.size {
        if !can_int_sum_overflow(size, bounds) {
            // 1. if the sum can't overflow, don't need to worry about saturation arithmetic
            #[cfg(creusot)]
            proof_assert!(sized_int_checked_lift(size, bounds));
            make_sized_bounded_int_checked_sum(size, bounds)
        } else if signs_agree(bounds) {
            // 2. a monotonic sum is less efficient due to saturation arithmetic
            #[cfg(creusot)]
            proof_assert!(sized_int_monotonic_lift(size, bounds));
            make_sized_bounded_int_monotonic_sum(size, bounds)
        } else {
            // 3. a split sum is the least efficient, because it needs saturation arithmetic and separate pos/neg sums
            #[cfg(creusot)]
            proof_assert!(sized_int_split_lift(size, bounds));
            make_sized_bounded_int_split_sum(size, bounds)
        }
    } else {
        // data size unknown, so checked sum is not applicable
        if signs_agree(bounds) {
            // 1. if bounds share sign, then a simple saturating addition is associative
            #[cfg(creusot)]
            proof_assert!(int_monotonic_lift(bounds));
            make_bounded_int_monotonic_sum(bounds)
        } else {
            // 2. split sum is the cheapest remaining fallback when order is unknown
            #[cfg(creusot)]
            proof_assert!(int_split_lift(bounds));
            make_bounded_int_split_sum(bounds)
        }
    }
}

#[cfg_attr(creusot, ensures(forall<t: SumT<T, InsertDeleteDistance>> result == Ok(t) ==>
    int_id_sum_is_stable(t, input_domain)))]
fn make_int_sum_insert_delete<T>(
    input_domain: VectorDomain<AtomDomain<T>>,
    input_metric: InsertDeleteDistance,
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
    for<'a> T: Sum<&'a T>,
{
    let bounds = input_domain
        .element_domain
        .bounds
        .ok_or_else(|| {
            err!(
                MakeTransformation,
                "`input_domain` must be bounded. Use `make_clamp` to bound data."
            )
        })?
        .get_closed()?;

    if let Some(size) = input_domain.size {
        if !can_int_sum_overflow(size, bounds) {
            // 1. if the sum can't overflow,
            //    then do a no-op unordering and use a more computationally efficient sum without saturation arithmetic
            let domain = VectorDomain::new(AtomDomain::new_closed(bounds)?).with_size(size);
            let t0 = make_unordered(domain, input_metric)?;
            let t1 = make_sized_bounded_int_checked_sum(size, bounds);
            #[cfg(creusot)]
            proof_assert!(sized_int_checked_lift(size, bounds) && int_unordered_lift(bounds, Some(size))
                && forall<t: SumT<T, SymmetricDistance>> t1 == Ok(t) ==> int_sym_stable(t, bounds, Some(size)));
            t0 >> t1?
        } else {
            // when input metric is ordered, ordered sum doesn't need a shuffle, making it comparatively cheaper
            // - ordered sum is more efficient than a split sum because splitting unnecessary
            // - ordered sum is tied with monotonic sum, but not conditional on monotonicity
            #[cfg(creusot)]
            proof_assert!(sized_int_ordered_lift(size, bounds));
            make_sized_bounded_int_ordered_sum(size, bounds)
        }
    } else {
        // data size unknown, so checked sum is not applicable

        // when input metric is ordered, ordered sum doesn't need a shuffle, making it comparatively cheaper
        // - ordered sum is more efficient than a split sum because splitting unnecessary
        // - ordered sum is tied with monotonic sum, but not conditional on monotonicity
        #[cfg(creusot)]
        proof_assert!(int_ordered_lift(bounds));
        make_bounded_int_ordered_sum(bounds)
    }
}

macro_rules! impl_make_sum_int {
    ($($ty:ty)+) => {
        $(impl MakeSum<SymmetricDistance> for $ty {
            #[cfg(creusot)]
            #[logic(open, prophetic)]
            fn sum_is_stable(t: SumT<Self, SymmetricDistance>, input_domain: VectorDomain<AtomDomain<Self>>) -> bool {
                pearlite! { int_sym_sum_is_stable(t, input_domain) }
            }

            #[cfg_attr(creusot, ensures(forall<t: SumT<Self, SymmetricDistance>> result == Ok(t) ==>
                Self::sum_is_stable(t, input_domain)))]
            fn make_sum(
                input_domain: VectorDomain<AtomDomain<Self>>,
                _input_metric: SymmetricDistance,
            ) -> Fallible<Transformation<VectorDomain<AtomDomain<Self>>, SymmetricDistance, AtomDomain<Self>, AbsoluteDistance<Self>>> {
                make_int_sum_symmetric(input_domain)
            }
        })+
        $(impl MakeSum<InsertDeleteDistance> for $ty {
            #[cfg(creusot)]
            #[logic(open, prophetic)]
            fn sum_is_stable(t: SumT<Self, InsertDeleteDistance>, input_domain: VectorDomain<AtomDomain<Self>>) -> bool {
                pearlite! { int_id_sum_is_stable(t, input_domain) }
            }

            #[cfg_attr(creusot, ensures(forall<t: SumT<Self, InsertDeleteDistance>> result == Ok(t) ==>
                Self::sum_is_stable(t, input_domain)))]
            fn make_sum(
                input_domain: VectorDomain<AtomDomain<Self>>,
                input_metric: InsertDeleteDistance,
            ) -> Fallible<Transformation<VectorDomain<AtomDomain<Self>>, InsertDeleteDistance, AtomDomain<Self>, AbsoluteDistance<Self>>> {
                make_int_sum_insert_delete(input_domain, input_metric)
            }
        })+
    };
}
impl_make_sum_int! { u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize }

const DEFAULT_SIZE_LIMIT: usize = 1_048_576; // 2^20

#[cfg_attr(creusot, ensures(forall<t: SumT<T, SymmetricDistance>> result == Ok(t) ==>
    float_sym_sum_is_stable(t, input_domain)))]
fn make_float_sum_symmetric<T>(
    input_domain: VectorDomain<AtomDomain<T>>,
    input_metric: SymmetricDistance,
) -> Fallible<
    Transformation<
        VectorDomain<AtomDomain<T>>,
        SymmetricDistance,
        AtomDomain<T>,
        AbsoluteDistance<T>,
    >,
>
where
    T: 'static + Float,
{
    let bounds = input_domain
        .element_domain
        .bounds
        .as_ref()
        .ok_or_else(|| {
            err!(
                MakeTransformation,
                "`input_domain` must be bounded. Use `make_clamp` to bound data."
            )
        })?
        .get_closed()?;

    if let Some(size) = input_domain.size {
        if !Pairwise::<T>::can_float_sum_overflow(size, bounds)? {
            // 1. try the checked sum first, as floats are unlikely to overflow
            #[cfg(creusot)]
            proof_assert!(sized_float_checked_lift(size, bounds, DEFAULT_SIZE_LIMIT));
            make_sized_bounded_float_checked_sum::<Pairwise<_>>(size, bounds)
        } else {
            // 2. fall back to ordered summation
            let t0 = make_ordered_random(input_domain, input_metric)?;
            let t1 = make_sized_bounded_float_ordered_sum::<Sequential<_>>(size, bounds);
            #[cfg(creusot)]
            proof_assert!(sized_shuffled_float_ordered_lift(size, bounds, DEFAULT_SIZE_LIMIT)
                && forall<t: SumT<T, InsertDeleteDistance>> t1 == Ok(t) ==> sized_seq_ordered_contract(t, size, bounds));
            t0 >> t1?
        }
    } else {
        if !Pairwise::<T>::can_float_sum_overflow(DEFAULT_SIZE_LIMIT, bounds)? {
            // 1. if the sum can't overflow, then use a more computationally efficient sum without saturation arithmetic
            let t = make_bounded_float_checked_sum::<Pairwise<_>>(DEFAULT_SIZE_LIMIT, bounds);
            #[cfg(creusot)]
            proof_assert!(float_checked_lift(DEFAULT_SIZE_LIMIT, bounds)
                && forall<t2: SumT<T, SymmetricDistance>> t == Ok(t2) ==> float_sym_stable(t2, bounds, None, DEFAULT_SIZE_LIMIT));
            t
        } else {
            // 2. sum can overflow, so shuffle and use an ordered sum
            let t0 = make_ordered_random(input_domain, input_metric)?;
            let t1 = make_bounded_float_ordered_sum::<Sequential<_>>(DEFAULT_SIZE_LIMIT, bounds);
            #[cfg(creusot)]
            proof_assert!(shuffled_float_ordered_lift(DEFAULT_SIZE_LIMIT, bounds)
                && forall<t: SumT<T, InsertDeleteDistance>> t1 == Ok(t) ==> seq_ordered_contract(t, DEFAULT_SIZE_LIMIT, bounds));
            t0 >> t1?
        }
    }
}

#[cfg_attr(creusot, ensures(forall<t: SumT<T, InsertDeleteDistance>> result == Ok(t) ==>
    float_id_sum_is_stable(t, input_domain)))]
fn make_float_sum_insert_delete<T>(
    input_domain: VectorDomain<AtomDomain<T>>,
    input_metric: InsertDeleteDistance,
) -> Fallible<
    Transformation<
        VectorDomain<AtomDomain<T>>,
        InsertDeleteDistance,
        AtomDomain<T>,
        AbsoluteDistance<T>,
    >,
>
where
    T: 'static + Float,
{
    let bounds = input_domain
        .element_domain
        .bounds
        .as_ref()
        .ok_or_else(|| {
            err!(
                MakeTransformation,
                "`input_domain` must be bounded. Use `make_clamp` to bound data."
            )
        })?
        .get_closed()?;

    if let Some(size) = input_domain.size {
        if !Pairwise::<T>::can_float_sum_overflow(size, bounds)? {
            // 1. if the sum can't overflow,
            //    then do a no-op unordering and use a more computationally efficient sum without saturation arithmetic
            let t0 = make_unordered(input_domain, input_metric)?;
            let t1 = make_sized_bounded_float_checked_sum::<Pairwise<_>>(size, bounds);
            #[cfg(creusot)]
            proof_assert!(sized_float_checked_lift(size, bounds, DEFAULT_SIZE_LIMIT) && float_unordered_lift(bounds, Some(size), DEFAULT_SIZE_LIMIT)
                && forall<t: SumT<T, SymmetricDistance>> t1 == Ok(t) ==> float_sym_stable(t, bounds, Some(size), DEFAULT_SIZE_LIMIT));
            t0 >> t1?
        } else {
            // 2. fall back to ordered summation
            #[cfg(creusot)]
            proof_assert!(sized_float_ordered_lift(size, bounds, DEFAULT_SIZE_LIMIT));
            make_sized_bounded_float_ordered_sum::<Sequential<_>>(size, bounds)
        }
    } else {
        if !Pairwise::<T>::can_float_sum_overflow(DEFAULT_SIZE_LIMIT, bounds)? {
            // 1. if the sum can't overflow,
            //    then do a no-op unordering and use a more computationally efficient sum without saturation arithmetic
            let t0 = make_unordered(input_domain, input_metric)?;
            let t1 = make_bounded_float_checked_sum::<Pairwise<_>>(DEFAULT_SIZE_LIMIT, bounds);
            #[cfg(creusot)]
            proof_assert!(float_checked_lift(DEFAULT_SIZE_LIMIT, bounds) && float_unordered_lift(bounds, None, DEFAULT_SIZE_LIMIT)
                && forall<t: SumT<T, SymmetricDistance>> t1 == Ok(t) ==> float_sym_stable(t, bounds, None, DEFAULT_SIZE_LIMIT));
            t0 >> t1?
        } else {
            // 2. sum can overflow, but data is already sorted, so use a saturating sum
            let t = make_bounded_float_ordered_sum::<Sequential<_>>(DEFAULT_SIZE_LIMIT, bounds);
            #[cfg(creusot)]
            proof_assert!(float_ordered_lift(DEFAULT_SIZE_LIMIT, bounds)
                && forall<t2: SumT<T, InsertDeleteDistance>> t == Ok(t2) ==> seq_ordered_contract(t2, DEFAULT_SIZE_LIMIT, bounds));
            t
        }
    }
}

macro_rules! impl_make_sum_float {
    ($($ty:ty)+) => {
        $(impl MakeSum<SymmetricDistance> for $ty {
            #[cfg(creusot)]
            #[logic(open, prophetic)]
            fn sum_is_stable(t: SumT<Self, SymmetricDistance>, input_domain: VectorDomain<AtomDomain<Self>>) -> bool {
                pearlite! { float_sym_sum_is_stable(t, input_domain) }
            }

            #[cfg_attr(creusot, ensures(forall<t: SumT<Self, SymmetricDistance>> result == Ok(t) ==>
                Self::sum_is_stable(t, input_domain)))]
            fn make_sum(
                input_domain: VectorDomain<AtomDomain<Self>>,
                input_metric: SymmetricDistance,
            ) -> Fallible<Transformation<VectorDomain<AtomDomain<Self>>, SymmetricDistance, AtomDomain<Self>, AbsoluteDistance<Self>>> {
                make_float_sum_symmetric(input_domain, input_metric)
            }
        })+

        $(impl MakeSum<InsertDeleteDistance> for $ty {
            #[cfg(creusot)]
            #[logic(open, prophetic)]
            fn sum_is_stable(t: SumT<Self, InsertDeleteDistance>, input_domain: VectorDomain<AtomDomain<Self>>) -> bool {
                pearlite! { float_id_sum_is_stable(t, input_domain) }
            }

            #[cfg_attr(creusot, ensures(forall<t: SumT<Self, InsertDeleteDistance>> result == Ok(t) ==>
                Self::sum_is_stable(t, input_domain)))]
            fn make_sum(
                input_domain: VectorDomain<AtomDomain<Self>>,
                input_metric: InsertDeleteDistance,
            ) -> Fallible<Transformation<VectorDomain<AtomDomain<Self>>, InsertDeleteDistance, AtomDomain<Self>, AbsoluteDistance<Self>>> {
                make_float_sum_insert_delete(input_domain, input_metric)
            }
        })+
    };
}
impl_make_sum_float! { f32 f64 }
