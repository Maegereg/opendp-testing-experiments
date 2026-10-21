//! Clamped sums of reals, and their stability under the insert-delete distance.
//!
//! The real counterpart of [`ordered`](super::ordered): `csum(s, c)` adds the elements of `s`
//! from left to right, clamping the running sum to `[-c, c]` after every addition. The
//! saturating float sums of OpenDP are within a rounding error of `csum(s, MAX)`.
use creusot_std::{
    logic::{Int, real::Real, such_that},
    prelude::*,
};

use super::dataset::{fsum, neg_part, pos_part, sum};

/// `v` clamped to `[-c, c]`.
#[logic(open)]
pub fn clamp(v: Real, c: Real) -> Real {
    pearlite! { if v < -c { -c } else if v > c { c } else { v } }
}

/// Clamping is 1-Lipschitz.
#[logic]
#[requires(c >= Real::from_int(0))]
#[ensures(p <= q ==> clamp(p, c) <= clamp(q, c) && clamp(q, c) - clamp(p, c) <= q - p)]
#[ensures(q <= p ==> clamp(q, c) <= clamp(p, c) && clamp(p, c) - clamp(q, c) <= p - q)]
pub fn clamp_lipschitz(p: Real, q: Real, c: Real) {}

/// The clamped left fold of `s`, starting from zero.
#[logic(open)]
#[variant(s.len())]
pub fn csum(s: Seq<Real>, c: Real) -> Real {
    pearlite! {
        if s.len() == 0 { Real::from_int(0) } else { clamp(csum(s.subsequence(0, s.len() - 1), c) + s[s.len() - 1], c) }
    }
}

/// `z` is a subsequence of `x`, and `dx` is the sequence of the other elements of `x`.
#[logic(open)]
#[variant(x.len())]
pub fn sub(z: Seq<Real>, x: Seq<Real>, dx: Seq<Real>) -> bool {
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

/// `x` and `y` are within insert-delete distance `d`
/// ([`InsertDeleteDistance`](crate::metrics::InsertDeleteDistance)).
#[logic(open)]
pub fn id_close(x: Seq<Real>, y: Seq<Real>, d: Int) -> bool {
    pearlite! {
        exists<z: Seq<Real>, dx: Seq<Real>, dy: Seq<Real>> sub(z, x, dx) && sub(z, y, dy) && dx.len() + dy.len() <= d
    }
}

/// Every element of `s` lies within `[lo, hi]`.
#[logic(open)]
pub fn bounded(s: Seq<Real>, lo: Real, hi: Real) -> bool {
    pearlite! { forall<i> 0 <= i && i < s.len() ==> lo <= s[i] && s[i] <= hi }
}

/// The sum of the negative elements of `s`.
#[logic(open)]
pub fn neg_sum(s: Seq<Real>) -> Real {
    pearlite! { fsum(s, |v| neg_part(v)) }
}

/// The sum of the positive elements of `s`.
#[logic(open)]
pub fn pos_sum(s: Seq<Real>) -> Real {
    pearlite! { fsum(s, |v| pos_part(v)) }
}

/// A clamped sum lies within `[-c, c]`.
#[logic]
#[requires(c >= Real::from_int(0))]
#[ensures(-c <= csum(s, c) && csum(s, c) <= c)]
pub fn csum_in_range(s: Seq<Real>, c: Real) {}

/// Adding `e` with clamping moves a value in range by between `min(e, 0)` and `max(e, 0)`.
#[logic]
#[requires(-c <= s && s <= c)]
#[ensures(clamp(s + e, c) - s >= neg_part(e))]
#[ensures(clamp(s + e, c) - s <= pos_part(e))]
pub fn clamp_shift(s: Real, e: Real, c: Real) {}

/// Adding the same value with clamping keeps a difference within any interval around zero.
#[logic]
#[requires(c >= Real::from_int(0))]
#[requires(lo <= Real::from_int(0) && Real::from_int(0) <= hi && lo <= a - b && a - b <= hi)]
#[ensures(lo <= clamp(a + e, c) - clamp(b + e, c) && clamp(a + e, c) - clamp(b + e, c) <= hi)]
pub fn clamp_same(a: Real, b: Real, e: Real, c: Real, lo: Real, hi: Real) {
    pearlite! { clamp_lipschitz(a + e, b + e, c) }
}

/// Bounds on the sums of the negative and positive parts.
#[logic]
#[ensures(neg_sum(s) <= Real::from_int(0) && pos_sum(s) >= Real::from_int(0))]
#[ensures(pos_sum(s) + neg_sum(s) == sum(s))]
#[ensures(forall<lo: Real, hi: Real> bounded(s, lo, hi) ==>
    neg_sum(s) >= Real::from_int(s.len()) * neg_part(lo) && pos_sum(s) <= Real::from_int(s.len()) * pos_part(hi))]
#[variant(s.len())]
pub fn parts_bounds(s: Seq<Real>) {
    pearlite! {
        if s.len() > 0 {
            let si = s.subsequence(0, s.len() - 1);
            proof_assert!(forall<lo: Real, hi: Real> bounded(s, lo, hi) ==> bounded(si, lo, hi));
            parts_bounds(si)
        }
    }
}

/// Deleting `dx` from `x` (leaving `z`) changes the length and exact sum by those of `dx`,
/// keeps elements within bounds, and moves the clamped sum by between the sums of the negative
/// and positive parts of `dx`.
#[logic]
#[requires(c >= Real::from_int(0))]
#[requires(sub(z, x, dx))]
#[ensures(x.len() == z.len() + dx.len())]
#[ensures(sum(x) == sum(z) + sum(dx))]
#[ensures(neg_sum(dx) <= csum(x, c) - csum(z, c) && csum(x, c) - csum(z, c) <= pos_sum(dx))]
#[ensures(forall<lo: Real, hi: Real> bounded(x, lo, hi) ==> bounded(dx, lo, hi) && bounded(z, lo, hi))]
#[variant(x.len())]
pub fn sub_facts(z: Seq<Real>, x: Seq<Real>, dx: Seq<Real>, c: Real) {
    pearlite! {
        if x.len() > 0 {
            let xi = x.subsequence(0, x.len() - 1);
            let e = x[x.len() - 1];
            csum_in_range(xi, c);
            csum_in_range(z, c);
            proof_assert!(forall<lo: Real, hi: Real> bounded(x, lo, hi) ==> bounded(xi, lo, hi));
            if dx.len() > 0 && dx[dx.len() - 1] == e && sub(z, xi, dx.subsequence(0, dx.len() - 1)) {
                // `e` was deleted
                let dxi = dx.subsequence(0, dx.len() - 1);
                sub_facts(z, xi, dxi, c);
                clamp_shift(csum(xi, c), e, c);
                proof_assert!(forall<i> 0 <= i && i < dxi.len() ==> dx[i] == dxi[i]);
                proof_assert!(neg_sum(dx) == neg_sum(dxi) + neg_part(e));
                proof_assert!(pos_sum(dx) == pos_sum(dxi) + pos_part(e))
            } else {
                // `e` was kept
                let zi = z.subsequence(0, z.len() - 1);
                sub_facts(zi, xi, dx, c);
                csum_in_range(zi, c);
                parts_bounds(dx);
                clamp_same(csum(xi, c), csum(zi, c), e, c, neg_sum(dx), pos_sum(dx));
                proof_assert!(forall<i> 0 <= i && i < zi.len() ==> z[i] == zi[i])
            }
        } else {
            proof_assert!(z.len() == 0 && dx.len() == 0)
        }
    }
}

/// A witness that `x` and `y` are within insert-delete distance `d`.
#[logic]
#[requires(id_close(x, y, d))]
#[ensures(sub(result.0, x, result.1) && sub(result.0, y, result.2))]
#[ensures(result.1.len() + result.2.len() <= d)]
pub fn decompose(x: Seq<Real>, y: Seq<Real>, d: Int) -> (Seq<Real>, Seq<Real>, Seq<Real>) {
    pearlite! {
        such_that(|t: (Seq<Real>, Seq<Real>, Seq<Real>)| sub(t.0, x, t.1) && sub(t.0, y, t.2) && t.1.len() + t.2.len() <= d)
    }
}

/// The clamped sum is stable under the insert-delete distance: `d * mag`.
#[logic]
#[requires(c >= Real::from_int(0))]
#[requires(id_close(x, y, d))]
#[requires(bounded(x, lo, hi) && bounded(y, lo, hi))]
#[requires(mag >= -lo && mag >= hi && mag >= Real::from_int(0))]
#[ensures(csum(x, c) - csum(y, c) <= Real::from_int(d) * mag && csum(y, c) - csum(x, c) <= Real::from_int(d) * mag)]
pub fn unsized_csum_sensitivity(
    x: Seq<Real>,
    y: Seq<Real>,
    d: Int,
    c: Real,
    lo: Real,
    hi: Real,
    mag: Real,
) {
    pearlite! {
        let (z, dx, dy) = decompose(x, y, d);
        sub_facts(z, x, dx, c);
        sub_facts(z, y, dy, c);
        parts_bounds(dx);
        parts_bounds(dy);
        let kx = Real::from_int(dx.len());
        let ky = Real::from_int(dy.len());
        proof_assert!(kx * pos_part(hi) <= kx * mag && kx * neg_part(lo) >= -(kx * mag));
        proof_assert!(ky * pos_part(hi) <= ky * mag && ky * neg_part(lo) >= -(ky * mag));
        proof_assert!(kx + ky <= Real::from_int(d));
        proof_assert!((kx + ky) * mag <= Real::from_int(d) * mag)
    }
}

/// If all elements share a sign, the clamped sum is the clamped exact sum.
#[logic]
#[requires(c >= Real::from_int(0))]
#[ensures((forall<i> 0 <= i && i < s.len() ==> s[i] >= Real::from_int(0)) ==>
    csum(s, c) == clamp(sum(s), c) && sum(s) >= Real::from_int(0))]
#[ensures((forall<i> 0 <= i && i < s.len() ==> s[i] <= Real::from_int(0)) ==>
    csum(s, c) == clamp(sum(s), c) && sum(s) <= Real::from_int(0))]
#[variant(s.len())]
pub fn monotone_csum(s: Seq<Real>, c: Real) {
    pearlite! {
        if s.len() > 0 {
            let si = s.subsequence(0, s.len() - 1);
            proof_assert!(forall<i> 0 <= i && i < si.len() ==> si[i] == s[i]);
            monotone_csum(si, c)
        }
    }
}

/// With datasets of equal size, the clamped sum is stable: `(d / 2) * (hi - lo)`.
#[logic]
#[requires(c >= Real::from_int(0))]
#[requires(id_close(x, y, d))]
#[requires(x.len() == y.len())]
#[requires(bounded(x, lo, hi) && bounded(y, lo, hi) && lo <= hi)]
#[ensures(csum(x, c) - csum(y, c) <= Real::from_int(d / 2) * (hi - lo)
    && csum(y, c) - csum(x, c) <= Real::from_int(d / 2) * (hi - lo))]
pub fn sized_csum_sensitivity(x: Seq<Real>, y: Seq<Real>, d: Int, c: Real, lo: Real, hi: Real) {
    pearlite! {
        let (z, dx, dy) = decompose(x, y, d);
        sub_facts(z, x, dx, c);
        sub_facts(z, y, dy, c);
        parts_bounds(dx);
        parts_bounds(dy);
        let k = Real::from_int(dx.len());
        proof_assert!(dx.len() == dy.len() && 2 * dx.len() <= d && dx.len() <= d / 2);
        proof_assert!(k <= Real::from_int(d / 2));
        proof_assert!(k * (hi - lo) <= Real::from_int(d / 2) * (hi - lo));
        if lo <= Real::from_int(0) && Real::from_int(0) <= hi {
            // the clamped sums move by at most k * hi and k * (-lo) in each direction
            proof_assert!(k * hi - k * lo == k * (hi - lo))
        } else {
            // all elements share a sign: the clamped sums are clamped exact sums
            proof_assert!(lo > Real::from_int(0) ==>
                (forall<i> 0 <= i && i < x.len() ==> x[i] >= Real::from_int(0))
                && (forall<i> 0 <= i && i < y.len() ==> y[i] >= Real::from_int(0)));
            proof_assert!(hi < Real::from_int(0) ==>
                (forall<i> 0 <= i && i < x.len() ==> x[i] <= Real::from_int(0))
                && (forall<i> 0 <= i && i < y.len() ==> y[i] <= Real::from_int(0)));
            monotone_csum(x, c);
            monotone_csum(y, c);
            clamp_lipschitz(sum(x), sum(y), c);
            crate::verification::dataset::sum_bounds(dx, lo, hi);
            crate::verification::dataset::sum_bounds(dy, lo, hi);
            proof_assert!(k * hi - k * lo == k * (hi - lo))
        }
    }
}
