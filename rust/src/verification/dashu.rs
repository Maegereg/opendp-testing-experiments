//! Specifications of the `dashu` arbitrary-precision operations used by verified code.
//!
//! `IBig`, `UBig` and `RBig` are modeled by their (opaque) deep models in creusot-std's fork: the
//! integer or rational number they represent. Every operation is assumed exact, as `dashu`
//! documents. Integer division and right shifts are stated by inequalities, which fix the rounding
//! direction: `/` truncates towards zero, and `>>` rounds down (arithmetic shift, checked by
//! running it on negative values).
//!
//! Trusted: these are assumptions about `dashu`, listed in `verification/TRUST.md`.
use creusot_std::{
    logic::{Int, real::Real},
    prelude::*,
};
use dashu::{
    base::Sign,
    integer::{IBig, UBig},
    rational::RBig,
};
use std::ops::{Add, Div, Mul, MulAssign, Neg, Shl, ShlAssign, Shr, Sub};

use super::{
    RealModel,
    float::{FloatModel, pow2},
};

/// `2^k` as a real, for any integer `k`.
#[logic(open)]
pub fn pow2r(k: Int) -> Real {
    pearlite! {
        if k >= 0 { Real::from_int(pow2(k)) } else { Real::from_int(1) / Real::from_int(pow2(-k)) }
    }
}

/// `2^k` is positive.
#[logic]
#[requires(k >= 0)]
#[ensures(pow2(k) >= 1)]
#[variant(k)]
pub fn pow2_pos(k: Int) {
    pearlite! { if k > 0 { pow2_pos(k - 1) } }
}

/// `2^(j + k) = 2^j 2^k` for `j, k >= 0`.
#[logic]
#[requires(j >= 0 && k >= 0)]
#[ensures(pow2(j + k) == pow2(j) * pow2(k))]
#[variant(k)]
pub fn pow2_add(j: Int, k: Int) {
    pearlite! { if k > 0 { pow2_add(j, k - 1) } }
}

/// `2^(j + k) = 2^j 2^k`, and `2^k > 0`, for any integers `j`, `k`.
#[logic]
#[ensures(result && pow2r(k) > Real::from_int(0) && pow2r(j + k) == pow2r(j) * pow2r(k))]
pub fn pow2r_add(j: Int, k: Int) -> bool {
    pearlite! {
        pow2_pos(if j >= 0 { j } else { -j });
        pow2_pos(if k >= 0 { k } else { -k });
        pow2_pos(if j + k >= 0 { j + k } else { -(j + k) });
        if j >= 0 && k >= 0 {
            pow2_add(j, k);
        } else if j < 0 && k < 0 {
            pow2_add(-j, -k);
            real_mul_inv(pow2(-j), pow2(-k));
        } else if j >= 0 {
            if j + k >= 0 {
                pow2_add(j + k, -k);
                real_mul_div(pow2(j + k), pow2(-k));
            } else {
                pow2_add(j, -(j + k));
                real_div_mul(pow2(j), pow2(-(j + k)));
            }
        } else if j + k >= 0 {
            pow2_add(j + k, -j);
            real_mul_div(pow2(j + k), pow2(-j));
        } else {
            pow2_add(k, -(j + k));
            real_div_mul(pow2(k), pow2(-(j + k)));
        };
        true
    }
}

/// `1 / (a b) = (1 / a)(1 / b)` for positive integers.
#[logic]
#[requires(a >= 1 && b >= 1)]
#[ensures(Real::from_int(1) / Real::from_int(a * b)
    == (Real::from_int(1) / Real::from_int(a)) * (Real::from_int(1) / Real::from_int(b)))]
fn real_mul_inv(a: Int, b: Int) {
    pearlite! { proof_assert!(Real::from_int(a * b) == Real::from_int(a) * Real::from_int(b)) }
}

/// `(a b) (1 / b) = a` for positive integers.
#[logic]
#[requires(a >= 1 && b >= 1)]
#[ensures(Real::from_int(a * b) * (Real::from_int(1) / Real::from_int(b)) == Real::from_int(a))]
#[ensures(Real::from_int(b) * (Real::from_int(1) / Real::from_int(a * b))
    == Real::from_int(1) / Real::from_int(a))]
fn real_mul_div(a: Int, b: Int) {
    pearlite! { proof_assert!(Real::from_int(a * b) == Real::from_int(a) * Real::from_int(b)) }
}

/// `a (1 / (a b)) = 1 / b` for positive integers.
#[logic]
#[requires(a >= 1 && b >= 1)]
#[ensures(Real::from_int(a) * (Real::from_int(1) / Real::from_int(a * b))
    == Real::from_int(1) / Real::from_int(b))]
#[ensures((Real::from_int(1) / Real::from_int(a * b)) * Real::from_int(a)
    == Real::from_int(1) / Real::from_int(b))]
fn real_div_mul(a: Int, b: Int) {
    pearlite! { proof_assert!(Real::from_int(a * b) == Real::from_int(a) * Real::from_int(b)) }
}

/// `2^k` is strictly increasing.
#[logic]
#[requires(j < k)]
#[ensures(result && pow2r(j) < pow2r(k))]
pub fn pow2r_lt(j: Int, k: Int) -> bool {
    pearlite! {
        pow2r_add(j, k - j);
        pow2_pos(k - j - 1);
        proof_assert!(pow2(k - j) == 2 * pow2(k - j - 1));
        proof_assert!(pow2r(k - j) >= Real::from_int(2));
        true
    }
}

/// Scaling a fraction `n / d` by `2^k`, through its numerator (`k >= 0`) or denominator (`k < 0`).
#[logic]
#[requires(d >= 1)]
#[ensures(result)]
#[ensures(pow2(if k >= 0 { k } else { -k }) >= 1)]
#[ensures(k >= 0 ==> Real::from_int(n * pow2(k)) / Real::from_int(d)
    == Real::from_int(n) / Real::from_int(d) * pow2r(k))]
#[ensures(k < 0 ==> Real::from_int(n) / Real::from_int(d * pow2(-k))
    == Real::from_int(n) / Real::from_int(d) * pow2r(k))]
pub fn pow2r_scale(n: Int, d: Int, k: Int) -> bool {
    pearlite! {
        pow2_pos(if k >= 0 { k } else { -k });
        if k >= 0 {
            proof_assert!(Real::from_int(n * pow2(k)) == Real::from_int(n) * Real::from_int(pow2(k)));
        } else {
            proof_assert!(Real::from_int(d * pow2(-k)) == Real::from_int(d) * Real::from_int(pow2(-k)));
        };
        true
    }
}

/// Facts about the models of `dashu` numbers.
///
/// Trusted: a `UBig` is a natural number.
#[trusted]
#[logic(opaque)]
#[ensures(result)]
#[ensures(forall<u: UBig> u.deep_model() >= 0)]
pub fn dashu_facts() -> bool {
    dead
}

extern_spec! {
    impl IBig {
        #[ensures((result == Sign::Positive) == (self.deep_model() >= 0))]
        fn sign(&self) -> Sign;
    }

    impl RBig {
        #[ensures(result.1.deep_model() > 0)]
        #[ensures(self.deep_model()
            == Real::from_int(result.0.deep_model()) / Real::from_int(result.1.deep_model()))]
        fn into_parts(self) -> (IBig, UBig);

        #[requires(denominator.deep_model() != 0)]
        #[ensures(result.deep_model()
            == Real::from_int(numerator.deep_model()) / Real::from_int(denominator.deep_model()))]
        fn from_parts(numerator: IBig, denominator: UBig) -> RBig;

        #[ensures(result == (self.deep_model() == Real::from_int(0)))]
        fn is_zero(&self) -> bool;

        #[ensures((result == Sign::Negative) == (self.deep_model() < Real::from_int(0)))]
        fn sign(&self) -> Sign;
    }

    impl ShlAssign<usize> for IBig {
        #[ensures((^self).deep_model() == (*self).deep_model() * pow2(rhs@))]
        fn shl_assign(&mut self, rhs: usize);
    }

    impl ShlAssign<usize> for UBig {
        #[ensures((^self).deep_model() == (*self).deep_model() * pow2(rhs@))]
        fn shl_assign(&mut self, rhs: usize);
    }

    impl Shl<usize> for IBig {
        #[ensures(result.deep_model() == self.deep_model() * pow2(rhs@))]
        fn shl(self, rhs: usize) -> IBig;
    }

    impl Shr<usize> for IBig {
        #[ensures(result.deep_model() * pow2(rhs@) <= self.deep_model())]
        #[ensures(self.deep_model() < (result.deep_model() + 1) * pow2(rhs@))]
        fn shr(self, rhs: usize) -> IBig;
    }

    impl Add<i32> for IBig {
        #[ensures(result.deep_model() == self.deep_model() + rhs@)]
        fn add(self, rhs: i32) -> IBig;
    }

    impl<'a> Sub<&'a UBig> for IBig {
        #[ensures(result.deep_model() == self.deep_model() - rhs.deep_model())]
        fn sub(self, rhs: &'a UBig) -> IBig;
    }

    impl Div<UBig> for IBig {
        #[requires(rhs.deep_model() != 0)]
        #[ensures(rhs.deep_model() > 0 && self.deep_model() >= 0 ==>
            result.deep_model() * rhs.deep_model() <= self.deep_model()
            && self.deep_model() < (result.deep_model() + 1) * rhs.deep_model())]
        #[ensures(rhs.deep_model() > 0 && self.deep_model() < 0 ==>
            (result.deep_model() - 1) * rhs.deep_model() < self.deep_model()
            && self.deep_model() <= result.deep_model() * rhs.deep_model())]
        fn div(self, rhs: UBig) -> IBig;
    }

    impl Sub<RBig> for RBig {
        #[ensures(result.deep_model() == self.deep_model() - rhs.deep_model())]
        fn sub(self, rhs: RBig) -> RBig;
    }

    impl Add<RBig> for RBig {
        #[ensures(result.deep_model() == self.deep_model() + rhs.deep_model())]
        fn add(self, rhs: RBig) -> RBig;
    }

    impl Mul<RBig> for RBig {
        #[ensures(result.deep_model() == self.deep_model() * rhs.deep_model())]
        fn mul(self, rhs: RBig) -> RBig;
    }

    impl MulAssign<RBig> for RBig {
        #[ensures((^self).deep_model() == (*self).deep_model() * rhs.deep_model())]
        fn mul_assign(&mut self, rhs: RBig);
    }

    impl<'a> Div<RBig> for &'a RBig {
        #[requires(rhs.deep_model() != Real::from_int(0))]
        #[ensures(result.deep_model() == self.deep_model() / rhs.deep_model())]
        fn div(self, rhs: RBig) -> RBig;
    }

    impl Neg for IBig {
        #[ensures(result.deep_model() == -self.deep_model())]
        fn neg(self) -> IBig;
    }

    impl IBig {
        #[ensures((result.0 == Sign::Positive) == (self.deep_model() >= 0))]
        #[ensures(result.1.deep_model() == if self.deep_model() >= 0 { self.deep_model() } else { -self.deep_model() })]
        fn into_parts(self) -> (Sign, UBig);
    }

    impl UBig {
        #[ensures(result == (self.deep_model() == 0))]
        fn is_zero(&self) -> bool;
    }

    impl RBig {
        // Only used to round a threshold; no property of the result is needed.
        fn round(&self) -> IBig;

        #[ensures(Real::from_int(result.deep_model()) <= self.deep_model())]
        #[ensures(self.deep_model() < Real::from_int(result.deep_model() + 1))]
        fn floor(&self) -> IBig;
    }

    impl<'l, 'r> Mul<&'r u32> for &'l UBig {
        #[ensures(result.deep_model() == self.deep_model() * rhs@)]
        fn mul(self, rhs: &'r u32) -> UBig;
    }

    impl<'l> Sub<UBig> for &'l UBig {
        #[requires(rhs.deep_model() <= self.deep_model())]
        #[ensures(result.deep_model() == self.deep_model() - rhs.deep_model())]
        fn sub(self, rhs: UBig) -> UBig;
    }

    impl Clone for IBig {
        #[ensures(result.deep_model() == self.deep_model())]
        fn clone(&self) -> IBig;
    }

    impl Clone for UBig {
        #[ensures(result.deep_model() == self.deep_model())]
        fn clone(&self) -> UBig;
    }

    impl From<UBig> for RBig {
        #[ensures(result.deep_model() == Real::from_int(value.deep_model()))]
        fn from(value: UBig) -> RBig;
    }

    impl Clone for RBig {
        #[ensures(result.deep_model() == self.deep_model())]
        fn clone(&self) -> RBig;
    }

    impl From<usize> for RBig {
        #[ensures(result.deep_model() == Real::from_int(value@))]
        fn from(value: usize) -> RBig;
    }

    impl From<IBig> for RBig {
        #[ensures(result.deep_model() == Real::from_int(value.deep_model()))]
        fn from(value: IBig) -> RBig;
    }

    impl TryFrom<f64> for RBig {
        #[ensures(forall<r: RBig> result == Ok(r) ==> value.finite() && r.deep_model() == value.real())]
        #[ensures(value.finite() ==> exists<r: RBig> result == Ok(r))]
        fn try_from(value: f64) -> Result<RBig, dashu::base::ConversionError>;
    }

    impl TryFrom<f32> for RBig {
        #[ensures(forall<r: RBig> result == Ok(r) ==> value.finite() && r.deep_model() == value.real())]
        #[ensures(value.finite() ==> exists<r: RBig> result == Ok(r))]
        fn try_from(value: f32) -> Result<RBig, dashu::base::ConversionError>;
    }
}
