//! Floating-point numbers and the rounding error of float sums.
//!
//! Floats are modeled by the real numbers they represent (`RealModel::real`, left opaque), plus
//! whether they are finite. Float arithmetic is not modeled: properties of float sums enter as
//! contracts of the summation functions, either cited from the literature (rounding error) or
//! proved in Lean (absence of overflow). See `verification/TRUST.md`.
use creusot_std::{
    logic::{Int, real::Real},
    prelude::*,
};

use super::{RealModel, dataset::fsum, real_abs};
use crate::traits::Float;

/// The logical model of a float type.
pub trait FloatModel: RealModel {
    /// `self` is finite: neither NaN nor an infinity. Only then is `real` meaningful.
    #[logic]
    fn finite(self) -> bool;

    /// The number of explicitly stored mantissa bits (`FloatBits::MANTISSA_BITS`).
    #[logic]
    fn mantissa_bits() -> Int;

    /// The largest finite value (`MAX`).
    #[logic]
    fn max_finite() -> Real;
}

impl FloatModel for f64 {
    #[logic(opaque)]
    fn finite(self) -> bool {
        dead
    }
    #[logic(open)]
    fn mantissa_bits() -> Int {
        52
    }
    #[logic(opaque)]
    fn max_finite() -> Real {
        dead
    }
}

impl FloatModel for f32 {
    #[logic(opaque)]
    fn finite(self) -> bool {
        dead
    }
    #[logic(open)]
    fn mantissa_bits() -> Int {
        23
    }
    #[logic(opaque)]
    fn max_finite() -> Real {
        dead
    }
}

/// Facts about every `Float` type.
///
/// Trusted: generic code cannot see the float type, but these hold for `f32` and `f64`,
/// the only implementors of `Float` (see their `FloatModel` and `RealModel` impls).
#[trusted]
#[logic(opaque)]
#[ensures(T::mantissa_bits() >= 23)]
#[ensures(T::max_finite() > Real::from_int(0))]
#[ensures(forall<v: Real, out: Real> T::rounds_close(v, out) ==>
    real_abs(out - v) <= real_abs(v) / Real::from_int(2) + Real::from_int(1) / Real::from_int(1024))]
pub fn float_facts<T: Float>() {
    dead
}

/// `2^k` for `k >= 0`.
#[logic(open)]
#[variant(k)]
pub fn pow2(k: Int) -> Int {
    pearlite! { if k <= 0 { 1 } else { 2 * pow2(k - 1) } }
}

#[logic]
#[requires(0 <= j && j <= k)]
#[ensures(1 <= pow2(j) && pow2(j) <= pow2(k))]
#[variant(k)]
pub fn pow2_mono(j: Int, k: Int) {
    pearlite! { if k > 0 { if j < k { pow2_mono(j, k - 1) } else { pow2_mono(k - 1, k - 1) } } }
}

#[logic]
#[ensures(result && x@ <= pow2(64))]
pub fn usize_le_pow2_64(x: usize) -> bool {
    pearlite! { proof_assert!(pow2(64) == 18446744073709551616); true }
}

/// The unit roundoff of `T`: `2^-(MANTISSA_BITS + 1)`, the largest relative error of rounding to
/// nearest. Note that OpenDP's float sums use `2^-MANTISSA_BITS`, twice this.
#[logic(open)]
pub fn unit_roundoff<T: Float>() -> Real {
    pearlite! { Real::from_int(1) / Real::from_int(2 * pow2(T::mantissa_bits())) }
}

/// The base-2 logarithm.
#[logic(opaque)]
pub fn log2(x: Real) -> Real {
    dead
}

/// Trusted (mathematics): `log2` is increasing and `log2(2^j) = j`.
#[trusted]
#[logic(opaque)]
#[requires(j >= 0 && x >= Real::from_int(pow2(j)))]
#[ensures(log2(x) >= Real::from_int(j))]
pub fn log2_ge(x: Real, j: Int) {
    dead
}

/// Trusted (mathematics): `log2` is increasing and `log2(2^j) = j`.
#[trusted]
#[logic(opaque)]
#[requires(j >= 0 && Real::from_int(0) < x && x <= Real::from_int(pow2(j)))]
#[ensures(log2(x) <= Real::from_int(j))]
pub fn log2_le(x: Real, j: Int) {
    dead
}

/// Depth of the recursion of OpenDP's pairwise sum of `n` values, which splits them into
/// `n / 2` and `n - n / 2` values: `ceil(log2(n))`. Each value takes part in at most this many
/// additions.
#[logic(open)]
#[variant(n)]
pub fn pw_depth(n: Int) -> Int {
    pearlite! { if n <= 1 { 0 } else { 1 + pw_depth(n - n / 2) } }
}

#[logic]
#[requires(n <= m)]
#[ensures(0 <= pw_depth(n) && pw_depth(n) <= pw_depth(m))]
#[variant(m)]
pub fn pw_depth_mono(n: Int, m: Int) {
    pearlite! { if n > 1 { pw_depth_mono(n - n / 2, m - m / 2) } else if m > 1 { pw_depth_mono(n, m - m / 2) } }
}

/// The depth is `ceil(log2(n))`: `2^(depth - 1) < n`.
#[logic]
#[requires(n >= 2)]
#[ensures(pw_depth(n) >= 1 && pow2(pw_depth(n) - 1) < n)]
#[variant(n)]
pub fn pw_depth_lower(n: Int) {
    pearlite! { if n - n / 2 >= 2 { pw_depth_lower(n - n / 2) } }
}

/// The depth is at most twice `log2(n)`. This is the slack that makes OpenDP's pairwise error
/// bound, which uses `log2(n)`, sound (`FINDINGS.md`, D1).
#[logic]
#[requires(n >= 1)]
#[ensures(Real::from_int(pw_depth(n)) <= Real::from_int(2) * log2(Real::from_int(n)))]
#[ensures(log2(Real::from_int(n)) >= Real::from_int(0))]
pub fn pw_depth_log2(n: Int) {
    pearlite! {
        log2_ge(Real::from_int(n), 0);
        if n >= 2 {
            pw_depth_lower(n);
            if pw_depth(n) == 1 {
                log2_ge(Real::from_int(n), 1)
            } else {
                log2_ge(Real::from_int(n), pw_depth(n) - 1)
            }
        }
    }
}

/// The real values of a sequence of floats.
#[logic(open)]
pub fn reals<T: RealModel>(s: Seq<T>) -> Seq<Real> {
    pearlite! { s.map(|x: T| x.real()) }
}

/// The sum of the absolute values of `s`.
#[logic(open)]
pub fn abs_sum(s: Seq<Real>) -> Real {
    pearlite! { fsum(s, |v| real_abs(v)) }
}

/// The magnitude of bounds: `max(|lower|, upper)`, which bounds `|x|` for any `x` within them.
#[logic(open)]
pub fn mag(lower: Real, upper: Real) -> Real {
    pearlite! { if real_abs(lower) >= upper { real_abs(lower) } else { upper } }
}

/// Every element of `x` is a finite float within `bounds`: the elements of
/// `AtomDomain::new_closed(bounds)`.
#[logic(open)]
pub fn float_in_bounds<T: Float>(x: Seq<T>, bounds: (T, T)) -> bool {
    pearlite! {
        forall<i> 0 <= i && i < x.len() ==>
            x[i].finite() && bounds.0.real() <= x[i].real() && x[i].real() <= bounds.1.real()
    }
}

/// Values within bounds have absolute values summing to at most `len * mag`.
#[logic]
#[requires(float_in_bounds(x, bounds))]
#[ensures(Real::from_int(0) <= abs_sum(reals(x)))]
#[ensures(abs_sum(reals(x)) <= Real::from_int(x.len()) * mag(bounds.0.real(), bounds.1.real()))]
#[ensures(forall<i> 0 <= i && i < x.len() ==> bounds.0.real() <= reals(x)[i] && reals(x)[i] <= bounds.1.real())]
pub fn abs_sum_bound<T: Float>(x: Seq<T>, bounds: (T, T)) {
    pearlite! {
        let m = mag(bounds.0.real(), bounds.1.real());
        crate::verification::dataset::fsum_bounds(reals(x), |v| real_abs(v), Real::from_int(0), m)
    }
}
