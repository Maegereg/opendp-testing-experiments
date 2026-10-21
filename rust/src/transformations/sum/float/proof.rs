//! Verification of the float summation error bounds (`SumRelaxation::error`).
//!
//! Each `error` computes a bound with outward-rounded arithmetic. These lemmas show that the
//! computed value bounds the cited rounding error (`SumRelaxation::error_bound`) of summing
//! `size` values within the bounds. For the pairwise sum, this needs the slack in OpenDP's
//! choice of `u` (`FINDINGS.md`, D1), and accurate rounding in `inf_log2`, `inf_div` and
//! `neg_inf_sub` (D4).
use creusot_std::{
    logic::{Int, real::Real},
    prelude::*,
};

use crate::{
    traits::Float,
    verification::float::{
        float_facts, log2, log2_le, pow2, pow2_mono, pw_depth, pw_depth_log2, pw_depth_mono,
        unit_roundoff,
    },
};

/// The unit roundoff is `1 / (2 * 2^MANTISSA_BITS)`, and `2^MANTISSA_BITS >= 1024`.
#[logic]
#[ensures(Real::from_int(pow2(T::mantissa_bits())) >= Real::from_int(1024))]
#[ensures(unit_roundoff::<T>() > Real::from_int(0))]
#[ensures(unit_roundoff::<T>() * Real::from_int(2) * Real::from_int(pow2(T::mantissa_bits())) == Real::from_int(1))]
pub fn roundoff_facts<T: Float>() {
    pearlite! {
        float_facts::<T>();
        pow2_mono(10, T::mantissa_bits());
        proof_assert!(pow2(10) == 1024)
    }
}

/// Dividing by a positive number is monotone.
#[logic]
#[requires(a <= b && c > Real::from_int(0))]
#[ensures(a / c <= b / c)]
pub fn div_mono(a: Real, b: Real, c: Real) {
    pearlite! { proof_assert!(b / c - a / c == (b - a) / c) }
}

/// Dividing a non-negative number by a larger positive number gives a smaller result.
#[logic]
#[requires(x >= Real::from_int(0) && Real::from_int(0) < a && a <= b)]
#[ensures(x / b <= x / a)]
pub fn div_antimono(x: Real, a: Real, b: Real) {
    pearlite! {
        proof_assert!(x / a - x / b == x * (b - a) / (a * b));
        proof_assert!(a * b > Real::from_int(0));
        proof_assert!(x * (b - a) >= Real::from_int(0))
    }
}

/// The sequential bound: `(n - 1) * (n * mag) * u <= n^2 / 2^MANTISSA_BITS * mag <= e`.
#[logic]
#[requires(n >= 0)]
#[requires(s2 >= Real::from_int(n) * Real::from_int(n))]
#[requires(q >= s2 / Real::from_int(pow2(T::mantissa_bits())))]
#[requires(m >= Real::from_int(0))]
#[requires(e >= q * m)]
// (`result` is `true`: calling the lemma in a `proof_assert!` triggers its conclusion.)
#[ensures(result && Real::from_int(0) <= e
    && Real::from_int(n - 1) * (Real::from_int(n) * m) * unit_roundoff::<T>() <= e)]
pub fn seq_error_chain<T: Float>(n: Int, s2: Real, q: Real, m: Real, e: Real) -> bool {
    pearlite! {
        roundoff_facts::<T>();
        let p = Real::from_int(pow2(T::mantissa_bits()));
        let u = unit_roundoff::<T>();
        let nn = Real::from_int(n);
        proof_assert!(nn * nn >= Real::from_int(0));
        proof_assert!(s2 / p >= nn * nn / p);
        proof_assert!(nn * nn / p >= Real::from_int(0));
        proof_assert!(q >= Real::from_int(0));
        proof_assert!(q * m >= Real::from_int(0));
        // (n - 1) * n * m * u <= n * n * m * u = n * n * m / (2p) <= n * n * m / p
        proof_assert!(nn * m * u >= Real::from_int(0));
        proof_assert!(Real::from_int(n - 1) * (nn * m * u) <= nn * (nn * m * u));
        proof_assert!(nn * (nn * m * u) == (nn * nn / p) * m / Real::from_int(2));
        proof_assert!((nn * nn / p) * m <= (s2 / p) * m);
        proof_assert!((s2 / p) * m <= q * m);
        proof_assert!(Real::from_int(n - 1) * (nn * m) * u == Real::from_int(n - 1) * (nn * m * u));
        true
    }
}

#[logic]
#[requires(0 <= n && n <= m && Real::from_int(0) <= a && a <= b)]
#[requires(Real::from_int(0) <= e && Real::from_int(m - 1) * b * unit_roundoff::<T>() <= e)]
#[ensures(Real::from_int(0) <= e && Real::from_int(n - 1) * a * unit_roundoff::<T>() <= e)]
pub fn seq_error_mono<T: Float>(n: Int, m: Int, a: Real, b: Real, e: Real) {
    pearlite! {
        roundoff_facts::<T>();
        let u = unit_roundoff::<T>();
        if n >= 1 {
            proof_assert!(Real::from_int(n - 1) * a <= Real::from_int(m - 1) * a);
            proof_assert!(Real::from_int(m - 1) * a <= Real::from_int(m - 1) * b);
            proof_assert!(Real::from_int(n - 1) * a * u <= Real::from_int(m - 1) * b * u)
        } else {
            proof_assert!(Real::from_int(n - 1) * a * u <= Real::from_int(0))
        }
    }
}

/// `x / (1 - x)` is non-negative and increasing on `[0, 1)`.
#[logic]
#[requires(Real::from_int(0) <= x && x <= y && y < Real::from_int(1))]
#[ensures(Real::from_int(0) <= x / (Real::from_int(1) - x))]
#[ensures(x / (Real::from_int(1) - x) <= y / (Real::from_int(1) - y))]
pub fn gamma_mono(x: Real, y: Real) {
    pearlite! {
        let one = Real::from_int(1);
        proof_assert!(x * (one - y) <= y * (one - x));
        proof_assert!(x / (one - x) == x * (one - y) / ((one - x) * (one - y)));
        proof_assert!(y / (one - y) == y * (one - x) / ((one - x) * (one - y)))
    }
}

#[logic]
#[requires(0 <= n && n <= m && Real::from_int(0) <= a && a <= b)]
#[requires({
    let hu = Real::from_int(pw_depth(m)) * unit_roundoff::<T>();
    hu < Real::from_int(1) && hu / (Real::from_int(1) - hu) * b <= e
})]
#[ensures({
    let hu = Real::from_int(pw_depth(n)) * unit_roundoff::<T>();
    hu < Real::from_int(1) && hu / (Real::from_int(1) - hu) * a <= e
})]
pub fn pw_error_mono<T: Float>(n: Int, m: Int, a: Real, b: Real, e: Real) {
    pearlite! {
        roundoff_facts::<T>();
        pw_depth_mono(n, m);
        let u = unit_roundoff::<T>();
        let x = Real::from_int(pw_depth(n)) * u;
        let y = Real::from_int(pw_depth(m)) * u;
        proof_assert!(Real::from_int(0) <= x && x <= y);
        gamma_mono(x, y);
        let one = Real::from_int(1);
        proof_assert!(x / (one - x) * a <= y / (one - y) * a);
        proof_assert!(y / (one - y) * a <= y / (one - y) * b)
    }
}

/// The pairwise bound. With `n >= 1`, `log2(n) <= 64`, so the computed `uk` is small, `1 - uk`
/// is rounded down to a positive value, and `gamma(depth(n)) <= gamma(2 u log2(n)) <= ratio`.
#[logic]
#[requires(0 <= n && n <= pow2(64))]
#[requires(l >= log2(Real::from_int(n)) && T::rounds_close(log2(Real::from_int(n)), l))]
#[requires({
    let lp = l / Real::from_int(pow2(T::mantissa_bits()));
    uk >= lp && T::rounds_close(lp, uk)
})]
#[requires(den <= Real::from_int(1) - uk && T::rounds_close(Real::from_int(1) - uk, den))]
#[requires(ratio >= uk / den)]
#[requires(sc >= ratio * Real::from_int(n))]
#[requires(m >= Real::from_int(0))]
#[requires(e >= sc * m)]
#[ensures(result && {
    let hu = Real::from_int(pw_depth(n)) * unit_roundoff::<T>();
    hu < Real::from_int(1) && hu / (Real::from_int(1) - hu) * (Real::from_int(n) * m) <= e
})]
pub fn pw_error_chain<T: Float>(
    n: Int,
    l: Real,
    uk: Real,
    den: Real,
    ratio: Real,
    sc: Real,
    m: Real,
    e: Real,
) -> bool {
    pearlite! {
        roundoff_facts::<T>();
        float_facts::<T>();
        let zero = Real::from_int(0);
        let one = Real::from_int(1);
        let eta = one / Real::from_int(1024);
        let nn = Real::from_int(n);
        let p = Real::from_int(pow2(T::mantissa_bits()));
        let u = unit_roundoff::<T>();
        let hu = Real::from_int(pw_depth(n)) * u;
        if n == 0 {
            proof_assert!(hu == zero);
            proof_assert!(sc >= zero && sc * m >= zero)
        } else {
            let lg = log2(nn);
            pw_depth_log2(n);
            log2_le(nn, 64);
            // the computed log2(n) is at most 96 + eta, so uk < 1/4
            proof_assert!(zero <= lg && lg <= Real::from_int(64));
            proof_assert!(l <= lg + lg / Real::from_int(2) + eta);
            proof_assert!(zero <= l && l <= Real::from_int(97));
            proof_assert!(zero <= l / p && l / p <= Real::from_int(97) / Real::from_int(1024));
            proof_assert!(uk <= l / p + l / p / Real::from_int(2) + eta);
            proof_assert!(zero <= uk && uk < one / Real::from_int(4));
            // 1 - uk is rounded down to a positive value
            proof_assert!(den >= (one - uk) - (one - uk) / Real::from_int(2) - eta);
            proof_assert!(den > zero);
            div_antimono(uk, den, one - uk);
            proof_assert!(uk / den >= uk / (one - uk));
            // depth(n) * u <= 2 log2(n) * u = log2(n) / p <= l / p <= uk
            proof_assert!(hu <= Real::from_int(2) * lg * u);
            proof_assert!(Real::from_int(2) * lg * u == lg / p);
            div_mono(lg, l, p);
            proof_assert!(lg / p <= l / p);
            pw_depth_mono(n, n);
            proof_assert!(Real::from_int(pw_depth(n)) >= zero && u > zero);
            proof_assert!(zero <= hu);
            gamma_mono(hu, uk);
            let g = hu / (one - hu);
            proof_assert!(g <= ratio);
            proof_assert!(nn * m >= zero);
            proof_assert!(g * (nn * m) <= ratio * (nn * m));
            proof_assert!(ratio * (nn * m) == ratio * nn * m);
            proof_assert!(ratio * nn * m <= sc * m)
        };
        true
    }
}
