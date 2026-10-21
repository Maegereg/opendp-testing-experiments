mod checked;
use std::marker::PhantomData;

pub use checked::*;

mod ordered;
pub use ordered::*;

#[cfg(creusot)]
use crate::verification::{
    RealModel,
    float::{log2, mag, pow2, pw_depth, unit_roundoff, usize_le_pow2_64},
};
use crate::{
    error::Fallible,
    traits::{Float, InfAdd},
};
#[cfg(creusot)]
use creusot_std::{
    logic::{Int, real::Real},
    macros::{ensures, logic, proof_assert, requires, trusted},
};

#[cfg(creusot)]
mod proof;
#[cfg(creusot)]
use proof::*;

/// Marker type to represent sequential, or recursive summation
pub struct Sequential<T>(PhantomData<T>);

/// Marker type to represent pairwise, or cascading summation
pub struct Pairwise<T>(PhantomData<T>);

#[doc(hidden)]
pub trait SumRelaxation {
    type Item: Float;

    /// Summing `n` values whose absolute values sum to `a` makes a rounding error of at most `e`,
    /// provided that the sum does not overflow.
    #[cfg(creusot)]
    #[logic]
    fn error_bound(n: Int, a: Real, e: Real) -> bool;

    /// A bound for `m` values summing to `b` in absolute value also holds for fewer, smaller values.
    #[cfg(creusot)]
    #[logic(law)]
    #[requires(0 <= n && n <= m && Real::from_int(0) <= a && a <= b)]
    #[requires(Self::error_bound(m, b, e))]
    #[ensures(Self::error_bound(n, a, e))]
    fn error_bound_mono(n: Int, m: Int, a: Real, b: Real, e: Real);

    /// Bounds the rounding error of summing `size` values within `[lower, upper]`.
    #[cfg_attr(creusot, ensures(forall<e: Self::Item> result == Ok(e) ==> Self::error_bound(
        size@, Real::from_int(size@) * mag(lower.real(), upper.real()), e.real())))]
    fn error(size: usize, lower: Self::Item, upper: Self::Item) -> Fallible<Self::Item>;

    /// Bounds twice the rounding error of summing `size` values within `[lower, upper]`.
    #[cfg_attr(creusot, ensures(forall<r: Self::Item> result == Ok(r) ==> exists<e: Real>
        Self::error_bound(size@, Real::from_int(size@) * mag(lower.real(), upper.real()), e)
        && r.real() >= e + e))]
    fn relaxation(size: usize, lower: Self::Item, upper: Self::Item) -> Fallible<Self::Item> {
        let error = Self::error(size, lower, upper)?;
        error.inf_add(&error)
    }
}

/// `2^MANTISSA_BITS`.
// Trusted: `inf_powi` only promises to round up, but powers of two are computed exactly.
#[cfg_attr(creusot, trusted)]
#[cfg_attr(creusot, ensures(forall<out: T> result == Ok(out) ==>
    out.real() == Real::from_int(pow2(T::mantissa_bits()))))]
fn pow2_mantissa_bits<T: Float>() -> Fallible<T> {
    let _2 = T::exact_int_cast(2)?;
    _2.inf_powi(T::MANTISSA_BITS.into())
}

/// One.
// Trusted: `num::One::one` has no specification.
#[cfg_attr(creusot, trusted)]
#[cfg_attr(creusot, ensures(result.real() == Real::from_int(1)))]
fn float_one<T: Float>() -> T {
    T::one()
}

impl<T: Float> SumRelaxation for Sequential<T> {
    type Item = T;

    /// `n u a`, where `u` is the unit roundoff. For the exact sum, the error is at most
    /// `(n - 1) u a` for any `n`: S. M. Rump, "Error estimation of floating-point summation and
    /// dot product", BIT Numerical Mathematics 52 (2012), and C.-P. Jeannerod and S. M. Rump,
    /// "Improved error bounds for inner products in floating-point arithmetic",
    /// SIAM J. Matrix Anal. Appl. 34(2) (2013). For the saturating sum, with `a = n m`, it is at
    /// most `n u a` (proved in Lean: `OpenDP.Float.Fmt.satSeqSum_err`).
    #[cfg(creusot)]
    #[logic(open)]
    fn error_bound(n: Int, a: Real, e: Real) -> bool {
        pearlite! { Real::from_int(0) <= e && Real::from_int(n) * a * unit_roundoff::<T>() <= e }
    }

    #[cfg(creusot)]
    #[logic(law)]
    #[requires(0 <= n && n <= m && Real::from_int(0) <= a && a <= b)]
    #[requires(Self::error_bound(m, b, e))]
    #[ensures(Self::error_bound(n, a, e))]
    fn error_bound_mono(n: Int, m: Int, a: Real, b: Real, e: Real) {
        seq_error_mono::<T>(n, m, a, b, e)
    }

    #[cfg_attr(creusot, ensures(forall<e: T> result == Ok(e) ==> Self::error_bound(
        size@, Real::from_int(size@) * mag(lower.real(), upper.real()), e.real())))]
    fn error(size: usize, lower: Self::Item, upper: Self::Item) -> Fallible<Self::Item> {
        let size_ = T::exact_int_cast(size)?;

        // n^2 / 2^(k - 1) max(|L|, U)
        let size_sq = size_.inf_mul(&size_)?;
        let p = pow2_mantissa_bits::<T>()?;
        let scaled = size_sq.inf_div(&p)?;
        let mag_ = lower.alerting_abs()?.total_max(upper)?;
        let error = scaled.inf_mul(&mag_)?;
        #[cfg(creusot)]
        proof_assert!(size_.real() == Real::from_int(size@));
        #[cfg(creusot)]
        proof_assert!(size_sq.real() >= size_.real() * size_.real());
        #[cfg(creusot)]
        proof_assert!(scaled.real() >= size_sq.real() / Real::from_int(pow2(T::mantissa_bits())));
        #[cfg(creusot)]
        proof_assert!(mag_.real() == mag(lower.real(), upper.real()));
        #[cfg(creusot)]
        proof_assert!(mag_.real() >= Real::from_int(0));
        #[cfg(creusot)]
        proof_assert!(error.real() >= scaled.real() * mag_.real());
        #[cfg(creusot)]
        proof_assert!(size@ >= 0);
        #[cfg(creusot)]
        proof_assert!(seq_error_chain::<T>(size@, size_sq.real(), scaled.real(), mag_.real(), error.real()));
        Ok(error)
    }
}

impl<T: Float> SumRelaxation for Pairwise<T> {
    type Item = T;

    /// `gamma(h) a`, where `gamma(h) = h u / (1 - h u)`, `u` is the unit roundoff and
    /// `h = ceil(log2(n))` is the depth of the recursion (requires `h u < 1`):
    /// N. J. Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed. (2002), §4.2.
    #[cfg(creusot)]
    #[logic(open)]
    fn error_bound(n: Int, a: Real, e: Real) -> bool {
        pearlite! {
            let hu = Real::from_int(pw_depth(n)) * unit_roundoff::<T>();
            hu < Real::from_int(1) && hu / (Real::from_int(1) - hu) * a <= e
        }
    }

    #[cfg(creusot)]
    #[logic(law)]
    #[requires(0 <= n && n <= m && Real::from_int(0) <= a && a <= b)]
    #[requires(Self::error_bound(m, b, e))]
    #[ensures(Self::error_bound(n, a, e))]
    fn error_bound_mono(n: Int, m: Int, a: Real, b: Real, e: Real) {
        pw_error_mono::<T>(n, m, a, b, e)
    }

    #[cfg_attr(creusot, ensures(forall<e: T> result == Ok(e) ==> Self::error_bound(
        size@, Real::from_int(size@) * mag(lower.real(), upper.real()), e.real())))]
    fn error(size: usize, lower: Self::Item, upper: Self::Item) -> Fallible<Self::Item> {
        let size_ = T::exact_int_cast(size)?;
        // u * k where k = log_2(n)
        let log2_size = size_.inf_log2()?;
        let p = pow2_mantissa_bits::<T>()?;
        let uk = log2_size.inf_div(&p)?;
        // (uk / (1 - uk)) n max(|L|, U)
        let denom = float_one::<T>().neg_inf_sub(&uk)?;
        let ratio = uk.inf_div(&denom)?;
        let scaled = ratio.inf_mul(&size_)?;
        let mag_ = lower.alerting_abs()?.total_max(upper)?;
        let error = scaled.inf_mul(&mag_)?;
        #[cfg(creusot)]
        proof_assert!(size_.real() == Real::from_int(size@));
        #[cfg(creusot)]
        proof_assert!(log2_size.real() >= log2(size_.real()));
        #[cfg(creusot)]
        proof_assert!(T::rounds_close(log2(size_.real()), log2_size.real()));
        #[cfg(creusot)]
        proof_assert!(p.real() == Real::from_int(pow2(T::mantissa_bits())));
        #[cfg(creusot)]
        proof_assert!(uk.real() >= log2_size.real() / p.real());
        #[cfg(creusot)]
        proof_assert!(T::rounds_close(log2_size.real() / p.real(), uk.real()));
        #[cfg(creusot)]
        proof_assert!(denom.real() <= Real::from_int(1) - uk.real());
        #[cfg(creusot)]
        proof_assert!(T::rounds_close(Real::from_int(1) - uk.real(), denom.real()));
        #[cfg(creusot)]
        proof_assert!(ratio.real() >= uk.real() / denom.real());
        #[cfg(creusot)]
        proof_assert!(scaled.real() >= ratio.real() * size_.real());
        #[cfg(creusot)]
        proof_assert!(mag_.real() == mag(lower.real(), upper.real()));
        #[cfg(creusot)]
        proof_assert!(mag_.real() >= Real::from_int(0));
        #[cfg(creusot)]
        proof_assert!(error.real() >= scaled.real() * mag_.real());
        #[cfg(creusot)]
        proof_assert!(usize_le_pow2_64(size));
        #[cfg(creusot)]
        proof_assert!(pw_error_chain::<T>(
            size@,
            log2_size.real(),
            uk.real(),
            denom.real(),
            ratio.real(),
            scaled.real(),
            mag_.real(),
            error.real(),
        ));
        Ok(error)
    }
}
