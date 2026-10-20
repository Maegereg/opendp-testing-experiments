//! Ordered datasets, the insert-delete distance between them,
//! and the stability of saturating sums under it.
//!
//! `sub(z, x, dx)` holds when `z` is a subsequence of `x`, and `dx` is the sequence of elements of
//! `x` that are not in `z`. Two datasets `x` and `y` are within insert-delete distance `d`
//! (`id_close`) when they have a common subsequence `z` with `(|x| - |z|) + (|y| - |z|) <= d`:
//! `x` becomes `y` by deleting `dx` and inserting `dy`. This is the definition of
//! [`InsertDeleteDistance`](crate::metrics::InsertDeleteDistance).
use creusot_std::{
    logic::{Int, such_that},
    prelude::*,
};

use super::integer::{
    clamp, clamp_lipschitz, int_max, int_min, integer_range, isum, isum_neg, isum_pos,
    monotone_sat_sum, sat_sum,
};
use crate::traits::Integer;

/// `z` is a subsequence of `x`, and `dx` is the sequence of the other elements of `x`.
#[logic(open)]
#[variant(x.len())]
pub fn sub<T: Integer>(z: Seq<T>, x: Seq<T>, dx: Seq<T>) -> bool {
    pearlite! {
        if x.len() == 0 {
            z.len() == 0 && dx.len() == 0
        } else {
            let xi = x.subsequence(0, x.len() - 1);
            (dx.len() > 0 && dx[dx.len() - 1] == x[x.len() - 1]
                && sub(z, xi, dx.subsequence(0, dx.len() - 1)))
            || (z.len() > 0 && z[z.len() - 1] == x[x.len() - 1]
                && sub(z.subsequence(0, z.len() - 1), xi, dx))
        }
    }
}

/// `x` and `y` are within insert-delete distance `d`.
#[logic(open)]
pub fn id_close<T: Integer>(x: Seq<T>, y: Seq<T>, d: Int) -> bool {
    pearlite! {
        exists<z: Seq<T>, dx: Seq<T>, dy: Seq<T>> sub(z, x, dx) && sub(z, y, dy) && dx.len() + dy.len() <= d
    }
}

/// Every element of `s` lies within `[lo, hi]`.
#[logic(open)]
pub fn bounded<T: Integer>(s: Seq<T>, lo: Int, hi: Int) -> bool {
    pearlite! { forall<i> 0 <= i && i < s.len() ==> lo <= s[i].deep_model() && s[i].deep_model() <= hi }
}

/// A saturating sum lies within the range of `T`.
#[logic]
#[ensures(int_min::<T>() <= sat_sum(s) && sat_sum(s) <= int_max::<T>())]
pub fn sat_sum_in_range<T: Integer>(s: Seq<T>) {
    pearlite! { integer_range(such_that(|z: T| true)) }
}

/// Adding `e` with saturation moves a value in range by between `min(e, 0)` and `max(e, 0)`.
#[logic]
#[requires(int_min::<T>() <= s && s <= int_max::<T>())]
#[ensures(clamp::<T>(s + e) - s >= (if e < 0 { e } else { 0 }))]
#[ensures(clamp::<T>(s + e) - s <= (if e > 0 { e } else { 0 }))]
pub fn clamp_shift<T: Integer>(s: Int, e: Int) {}

/// Adding the same value with saturation keeps a difference within any interval around zero.
#[logic]
#[requires(lo <= 0 && 0 <= hi && lo <= a - b && a - b <= hi)]
#[ensures(lo <= clamp::<T>(a + e) - clamp::<T>(b + e) && clamp::<T>(a + e) - clamp::<T>(b + e) <= hi)]
pub fn clamp_same<T: Integer>(a: Int, b: Int, e: Int, lo: Int, hi: Int) {
    pearlite! { clamp_lipschitz::<T>(a + e, b + e) }
}

/// Deleting `dx` from `x` (leaving `z`) changes the length and exact sum by those of `dx`,
/// keeps elements within bounds, and moves the saturating sum by between the sums of the
/// negative and positive parts of `dx`.
#[logic]
#[requires(sub(z, x, dx))]
#[ensures(x.len() == z.len() + dx.len())]
#[ensures(isum(x) == isum(z) + isum(dx))]
#[ensures(isum_neg(dx) <= sat_sum(x) - sat_sum(z) && sat_sum(x) - sat_sum(z) <= isum_pos(dx))]
#[ensures(forall<lo: Int, hi: Int> bounded(x, lo, hi) ==> bounded(dx, lo, hi) && bounded(z, lo, hi))]
#[variant(x.len())]
pub fn sub_facts<T: Integer>(z: Seq<T>, x: Seq<T>, dx: Seq<T>) {
    pearlite! {
        if x.len() > 0 {
            let xi = x.subsequence(0, x.len() - 1);
            let e = x[x.len() - 1];
            sat_sum_in_range(xi);
            sat_sum_in_range(z);
            if dx.len() > 0 && dx[dx.len() - 1] == e && sub(z, xi, dx.subsequence(0, dx.len() - 1)) {
                // `e` was deleted
                let dxi = dx.subsequence(0, dx.len() - 1);
                sub_facts(z, xi, dxi);
                clamp_shift::<T>(sat_sum(xi), e.deep_model());
                proof_assert!(forall<lo: Int, hi: Int> bounded(x, lo, hi) ==> bounded(xi, lo, hi));
                proof_assert!(forall<i> 0 <= i && i < dxi.len() ==> dx[i] == dxi[i])
            } else {
                // `e` was kept
                let zi = z.subsequence(0, z.len() - 1);
                sub_facts(zi, xi, dx);
                sat_sum_in_range(zi);
                parts_bounds(dx, int_min::<T>(), int_max::<T>());
                clamp_same::<T>(sat_sum(xi), sat_sum(zi), e.deep_model(), isum_neg(dx), isum_pos(dx));
                proof_assert!(forall<lo: Int, hi: Int> bounded(x, lo, hi) ==> bounded(xi, lo, hi));
                proof_assert!(forall<i> 0 <= i && i < zi.len() ==> z[i] == zi[i])
            }
        } else {
            proof_assert!(z.len() == 0 && dx.len() == 0)
        }
    }
}

/// Bounds on the sums of the negative and positive parts of a bounded sequence.
#[logic]
#[requires(bounded(s, lo, hi))]
#[ensures(isum_neg(s) <= 0 && isum_pos(s) >= 0)]
#[ensures(isum_neg(s) >= s.len() * (if lo < 0 { lo } else { 0 }))]
#[ensures(isum_pos(s) <= s.len() * (if hi > 0 { hi } else { 0 }))]
#[ensures(isum_pos(s) + isum_neg(s) == isum(s))]
#[variant(s.len())]
pub fn parts_bounds<T: Integer>(s: Seq<T>, lo: Int, hi: Int) {
    pearlite! {
        if s.len() > 0 {
            let si = s.subsequence(0, s.len() - 1);
            proof_assert!(bounded(si, lo, hi));
            parts_bounds(si, lo, hi)
        }
    }
}

/// A witness that `x` and `y` are within insert-delete distance `d`.
#[logic]
#[requires(id_close(x, y, d))]
#[ensures(sub(result.0, x, result.1) && sub(result.0, y, result.2))]
#[ensures(result.1.len() + result.2.len() <= d)]
pub fn decompose<T: Integer>(x: Seq<T>, y: Seq<T>, d: Int) -> (Seq<T>, Seq<T>, Seq<T>) {
    pearlite! {
        such_that(|t: (Seq<T>, Seq<T>, Seq<T>)| sub(t.0, x, t.1) && sub(t.0, y, t.2) && t.1.len() + t.2.len() <= d)
    }
}

/// The saturating sum is stable under the insert-delete distance: `d * mag`.
#[logic]
#[requires(id_close(x, y, d))]
#[requires(bounded(x, lo, hi) && bounded(y, lo, hi))]
#[requires(mag >= -lo && mag >= hi && mag >= 0)]
#[ensures(sat_sum(x) - sat_sum(y) <= d * mag && sat_sum(y) - sat_sum(x) <= d * mag)]
pub fn unsized_sat_sum_sensitivity<T: Integer>(
    x: Seq<T>,
    y: Seq<T>,
    d: Int,
    lo: Int,
    hi: Int,
    mag: Int,
) {
    pearlite! {
        let (z, dx, dy) = decompose(x, y, d);
        sub_facts(z, x, dx);
        sub_facts(z, y, dy);
        parts_bounds(dx, lo, hi);
        parts_bounds(dy, lo, hi);
        proof_assert!(dx.len() * (if hi > 0 { hi } else { 0 }) <= dx.len() * mag);
        proof_assert!(dx.len() * (if lo < 0 { lo } else { 0 }) >= -(dx.len() * mag));
        proof_assert!(dy.len() * (if hi > 0 { hi } else { 0 }) <= dy.len() * mag);
        proof_assert!(dy.len() * (if lo < 0 { lo } else { 0 }) >= -(dy.len() * mag));
        proof_assert!((dx.len() + dy.len()) * mag <= d * mag)
    }
}

/// With datasets of equal size, the saturating sum is stable: `(d / 2) * (hi - lo)`.
#[logic]
#[requires(id_close(x, y, d))]
#[requires(x.len() == y.len())]
#[requires(bounded(x, lo, hi) && bounded(y, lo, hi) && lo <= hi)]
#[ensures(sat_sum(x) - sat_sum(y) <= (d / 2) * (hi - lo) && sat_sum(y) - sat_sum(x) <= (d / 2) * (hi - lo))]
pub fn sized_sat_sum_sensitivity<T: Integer>(x: Seq<T>, y: Seq<T>, d: Int, lo: Int, hi: Int) {
    pearlite! {
        let (z, dx, dy) = decompose(x, y, d);
        sub_facts(z, x, dx);
        sub_facts(z, y, dy);
        parts_bounds(dx, lo, hi);
        parts_bounds(dy, lo, hi);
        let k = dx.len();
        proof_assert!(k == dy.len() && 2 * k <= d && k <= d / 2);
        proof_assert!(k * (hi - lo) <= (d / 2) * (hi - lo));
        if lo <= 0 && 0 <= hi {
            // the saturating sums move by at most k * hi and k * (-lo) in each direction
            proof_assert!(k * hi - k * lo == k * (hi - lo))
        } else {
            // all elements share a sign: the saturating sums are clamped exact sums
            monotone_sat_sum(x);
            monotone_sat_sum(y);
            clamp_lipschitz::<T>(isum(x), isum(y));
            isum_bounds_seq(dx, lo, hi);
            isum_bounds_seq(dy, lo, hi);
            proof_assert!(k * hi - k * lo == k * (hi - lo))
        }
    }
}

/// Elementwise bounds give bounds on the sum.
#[logic]
#[requires(bounded(s, lo, hi))]
#[ensures(s.len() * lo <= isum(s) && isum(s) <= s.len() * hi)]
#[variant(s.len())]
pub fn isum_bounds_seq<T: Integer>(s: Seq<T>, lo: Int, hi: Int) {
    pearlite! {
        if s.len() > 0 {
            let si = s.subsequence(0, s.len() - 1);
            proof_assert!(bounded(si, lo, hi));
            isum_bounds_seq(si, lo, hi)
        }
    }
}
