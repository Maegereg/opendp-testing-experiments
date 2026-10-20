//! Sums of integer datasets, and when they can be computed without overflow.
use creusot_std::{
    logic::{Int, real::Real, such_that},
    prelude::*,
};

use super::dataset::sum;
use super::real_abs;
use crate::traits::Integer;

// Facts about the values of every `Integer` type.
//
// Trusted: generic code cannot see the integer type, but these hold for each of
// `u8`..`u128`, `usize`, `i8`..`i128` and `isize`, the only implementors of `Integer`.

/// `real` is the (mathematical) integer that the value represents.
#[trusted]
#[logic(opaque)]
#[ensures(x.real() == Real::from_int(x.deep_model()))]
pub fn integer_real<T: Integer>(x: T) {
    dead
}

/// Zero is representable.
#[trusted]
#[logic(opaque)]
#[ensures(exists<z: T> z.deep_model() == 0)]
pub fn integer_zero<T: Integer>() {
    dead
}

/// Representable values form an interval of integers.
#[trusted]
#[logic(opaque)]
#[requires(x.deep_model() <= p && p <= y.deep_model())]
#[ensures(exists<z: T> z.deep_model() == p)]
pub fn integer_interval<T: Integer>(x: T, y: T, p: Int) {
    dead
}

/// If the type has negative values, the negation of any non-negative value is representable.
#[trusted]
#[logic(opaque)]
#[requires(x.deep_model() < 0 && y.deep_model() >= 0)]
#[ensures(exists<z: T> z.deep_model() == -y.deep_model())]
pub fn integer_neg<T: Integer>(x: T, y: T) {
    dead
}

/// The real values of a dataset.
#[logic(open)]
pub fn reals<T: Integer>(s: Seq<T>) -> Seq<Real> {
    pearlite! { s.map(|x: T| x.real()) }
}

/// The (mathematical) sum of the integers in `s`.
#[logic(open)]
#[variant(s.len())]
pub fn isum<T: Integer>(s: Seq<T>) -> Int {
    pearlite! {
        if s.len() == 0 { 0 } else { isum(s.subsequence(0, s.len() - 1)) + s[s.len() - 1].deep_model() }
    }
}

/// The real sum of an integer dataset is its integer sum.
#[logic]
#[ensures(sum(reals(s)) == Real::from_int(isum(s)))]
#[variant(s.len())]
pub fn isum_real<T: Integer>(s: Seq<T>) {
    pearlite! {
        if s.len() > 0 {
            integer_real(s[s.len() - 1]);
            let init = s.subsequence(0, s.len() - 1);
            proof_assert!(reals(s).subsequence(0, s.len() - 1) == reals(init));
            isum_real(init)
        }
    }
}

/// Every prefix sum of `s` is representable in `T`, so summing `s` in order cannot overflow.
#[logic(open)]
pub fn prefix_sums_fit<T: Integer>(s: Seq<T>) -> bool {
    pearlite! {
        forall<k: Int> 0 <= k && k <= s.len() ==>
            exists<z: T> z.deep_model() == isum(s.subsequence(0, k))
    }
}

/// Elementwise bounds give bounds on the sum.
#[logic]
#[requires(forall<i> 0 <= i && i < s.len() ==> lo <= s[i].deep_model() && s[i].deep_model() <= hi)]
#[ensures(lo * s.len() <= isum(s) && isum(s) <= hi * s.len())]
#[variant(s.len())]
pub fn isum_bounds<T: Integer>(s: Seq<T>, lo: Int, hi: Int) {
    pearlite! { if s.len() > 0 { isum_bounds(s.subsequence(0, s.len() - 1), lo, hi) } }
}

/// The prefix sum of length `k` is representable.
#[logic]
#[requires(forall<i> 0 <= i && i < s.len() ==> lo.deep_model() <= s[i].deep_model() && s[i].deep_model() <= hi.deep_model())]
#[requires(bound.deep_model() >= s.len() * lo.deep_model() && bound.deep_model() >= -(s.len() * lo.deep_model()))]
#[requires(bound.deep_model() >= s.len() * hi.deep_model())]
#[requires(0 <= k && k <= s.len())]
#[ensures(exists<z: T> z.deep_model() == isum(s.subsequence(0, k)))]
pub fn prefix_sum_fits<T: Integer>(s: Seq<T>, lo: T, hi: T, bound: T, k: Int) {
    pearlite! {
        let p = s.subsequence(0, k);
        isum_bounds(p, lo.deep_model(), hi.deep_model());
        // isum(p) <= k * hi <= bound (k * hi <= max(0, n * hi) <= bound)
        proof_assert!(k * hi.deep_model() <= bound.deep_model());
        let lower = if lo.deep_model() >= 0 {
            // 0 <= k * lo <= isum(p), and 0 is representable
            proof_assert!(0 <= k * lo.deep_model());
            integer_zero::<T>();
            such_that(|z: T| z.deep_model() == 0)
        } else {
            // -bound <= n * lo <= k * lo <= isum(p), and -bound is representable (as lo < 0)
            proof_assert!(k * lo.deep_model() >= s.len() * lo.deep_model());
            integer_neg(lo, bound);
            such_that(|z: T| z.deep_model() == -bound.deep_model())
        };
        integer_interval(lower, bound, isum(p))
    }
}

/// All prefix sums are representable.
#[logic]
#[requires(forall<i> 0 <= i && i < s.len() ==> lo.deep_model() <= s[i].deep_model() && s[i].deep_model() <= hi.deep_model())]
#[requires(bound.deep_model() >= s.len() * lo.deep_model() && bound.deep_model() >= -(s.len() * lo.deep_model()))]
#[requires(bound.deep_model() >= s.len() * hi.deep_model())]
#[requires(0 <= k && k <= s.len() + 1)]
#[ensures(forall<j: Int> 0 <= j && j < k ==> exists<z: T> z.deep_model() == isum(s.subsequence(0, j)))]
#[variant(k)]
pub fn prefix_sums_fit_upto<T: Integer>(s: Seq<T>, lo: T, hi: T, bound: T, k: Int) {
    pearlite! {
        if k > 0 {
            prefix_sum_fits(s, lo, hi, bound, k - 1);
            prefix_sums_fit_upto(s, lo, hi, bound, k - 1)
        }
    }
}

/// A dataset within `[lo, hi]` whose length times the larger magnitude of the bounds is at most
/// a representable `bound` can be summed without overflow.
#[logic]
#[requires(forall<i> 0 <= i && i < s.len() ==> lo.deep_model() <= s[i].deep_model() && s[i].deep_model() <= hi.deep_model())]
#[requires(bound.deep_model() >= s.len() * lo.deep_model() && bound.deep_model() >= -(s.len() * lo.deep_model()))]
#[requires(bound.deep_model() >= s.len() * hi.deep_model())]
#[ensures(prefix_sums_fit(s))]
pub fn bounded_sums_fit<T: Integer>(s: Seq<T>, lo: T, hi: T, bound: T) {
    prefix_sums_fit_upto(s, lo, hi, bound, s.len() + 1)
}

/// Turns the real-valued facts established by `can_int_sum_overflow` into integer facts.
#[logic]
#[requires(n >= 0)]
#[requires(mag.real() >= real_abs(lo.real()) && mag.real() >= hi.real())]
#[requires(bound.real() >= mag.real() * Real::from_int(n))]
#[ensures(bound.deep_model() >= n * lo.deep_model() && bound.deep_model() >= -(n * lo.deep_model()))]
#[ensures(bound.deep_model() >= n * hi.deep_model())]
pub fn overflow_witness<T: Integer>(lo: T, hi: T, mag: T, bound: T, n: Int) {
    pearlite! {
        integer_real(lo);
        integer_real(hi);
        integer_real(mag);
        integer_real(bound);
        proof_assert!(Real::from_int(mag.deep_model()) * Real::from_int(n) == Real::from_int(mag.deep_model() * n));
        proof_assert!(bound.deep_model() >= mag.deep_model() * n);
        proof_assert!(mag.deep_model() >= lo.deep_model() && mag.deep_model() >= -lo.deep_model());
        proof_assert!(mag.deep_model() >= hi.deep_model());
        proof_assert!(mag.deep_model() * n >= lo.deep_model() * n);
        proof_assert!(mag.deep_model() * n >= -lo.deep_model() * n);
        proof_assert!(mag.deep_model() * n >= hi.deep_model() * n)
    }
}

/// Integer bounds on the elements of a dataset are also real bounds on its real values.
#[logic]
#[requires(forall<i> 0 <= i && i < s.len() ==> lo.deep_model() <= s[i].deep_model() && s[i].deep_model() <= hi.deep_model())]
#[requires(0 <= k && k <= s.len())]
#[ensures(forall<i> 0 <= i && i < k ==> lo.real() <= reals(s)[i] && reals(s)[i] <= hi.real())]
#[variant(k)]
pub fn real_bounds<T: Integer>(s: Seq<T>, lo: T, hi: T, k: Int) {
    pearlite! {
        if k > 0 {
            integer_real(lo);
            integer_real(hi);
            integer_real(s[k - 1]);
            real_bounds(s, lo, hi, k - 1)
        }
    }
}
