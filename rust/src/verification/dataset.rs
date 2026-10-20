//! Datasets as multisets of reals, and the symmetric distance between them.
//!
//! A dataset `x: Vec<T>` is modeled by the sequence of the real values of its elements.
//! Two datasets are within symmetric distance `d` (`sym_close`) when they share a common
//! sub-multiset `c` and differ only by extra elements `a` and `b` with `|a| + |b| <= d`.
//! This is equivalent to the definition of [`SymmetricDistance`](crate::metrics::SymmetricDistance):
//! the size of the symmetric difference of the two multisets is at most `d`.
use creusot_std::{
    logic::{Mapping, real::Real, such_that},
    prelude::*,
};

use super::real_abs;

/// Number of occurrences of `v` in `s`.
#[logic(open)]
#[variant(s.len())]
pub fn count(s: Seq<Real>, v: Real) -> Int {
    pearlite! {
        if s.len() == 0 { 0 } else {
            count(s.subsequence(0, s.len() - 1), v) + if s[s.len() - 1] == v { 1 } else { 0 }
        }
    }
}

#[logic]
#[ensures(count(s, v) >= 0)]
#[variant(s.len())]
pub fn count_nonneg(s: Seq<Real>, v: Real) {
    pearlite! { if s.len() > 0 { count_nonneg(s.subsequence(0, s.len() - 1), v) } }
}

/// Sum of the elements of `s`.
#[logic(open)]
#[variant(s.len())]
pub fn sum(s: Seq<Real>) -> Real {
    pearlite! {
        if s.len() == 0 { Real::from_int(0) } else { sum(s.subsequence(0, s.len() - 1)) + s[s.len() - 1] }
    }
}

/// `a` and `b` are equal as multisets.
#[logic(open)]
pub fn same(a: Seq<Real>, b: Seq<Real>) -> bool {
    pearlite! { forall<v: Real> count(a, v) == count(b, v) }
}

/// `x` and `y` are within symmetric distance `d`: they share a common core `c`,
/// and differ only by the extra elements `a` (in `x`) and `b` (in `y`).
/// This is equivalent to |multiset(x) Δ multiset(y)| <= d.
#[logic(open)]
pub fn sym_close(x: Seq<Real>, y: Seq<Real>, d: Int) -> bool {
    pearlite! {
        exists<c: Seq<Real>, a: Seq<Real>, b: Seq<Real>>
            same(x, c.concat(a)) && same(y, c.concat(b)) && a.len() + b.len() <= d
    }
}

#[logic]
#[ensures(count(a.concat(b), v) == count(a, v) + count(b, v))]
#[variant(b.len())]
pub fn count_concat(a: Seq<Real>, b: Seq<Real>, v: Real) {
    pearlite! {
        if b.len() > 0 {
            proof_assert!(a.concat(b).subsequence(0, a.len() + b.len() - 1)
                == a.concat(b.subsequence(0, b.len() - 1)));
            count_concat(a, b.subsequence(0, b.len() - 1), v)
        } else {
            proof_assert!(a.concat(b).ext_eq(a));
        }
    }
}

#[logic]
#[ensures(sum(a.concat(b)) == sum(a) + sum(b))]
#[variant(b.len())]
pub fn sum_concat(a: Seq<Real>, b: Seq<Real>) {
    pearlite! {
        if b.len() > 0 {
            proof_assert!(a.concat(b).subsequence(0, a.len() + b.len() - 1)
                == a.concat(b.subsequence(0, b.len() - 1)));
            sum_concat(a, b.subsequence(0, b.len() - 1))
        } else {
            proof_assert!(a.concat(b).ext_eq(a));
        }
    }
}

#[logic]
#[requires(0 <= j && j < t.len())]
#[ensures(forall<v: Real> count(t, v) == count(t.removed(j), v) + if t[j] == v { 1 } else { 0 })]
#[ensures(sum(t) == sum(t.removed(j)) + t[j])]
#[ensures(t.removed(j).len() == t.len() - 1)]
#[variant(t.len())]
pub fn removed(t: Seq<Real>, j: Int) {
    pearlite! {
        if j < t.len() - 1 {
            let init = t.subsequence(0, t.len() - 1);
            proof_assert!(t.removed(j).subsequence(0, t.len() - 2) == init.removed(j));
            proof_assert!(t.removed(j)[t.len() - 2] == t[t.len() - 1]);
            removed(init, j)
        } else {
            proof_assert!(t.removed(j) == t.subsequence(0, t.len() - 1));
        }
    }
}

#[logic]
#[requires(count(t, v) > 0)]
#[ensures(exists<j> 0 <= j && j < t.len() && t[j] == v)]
#[variant(t.len())]
pub fn count_pos(t: Seq<Real>, v: Real) {
    pearlite! {
        if t[t.len() - 1] != v { count_pos(t.subsequence(0, t.len() - 1), v) }
    }
}

/// Multiset-equal sequences have the same length and sum.
#[logic]
#[requires(same(s, t))]
#[ensures(s.len() == t.len())]
#[ensures(sum(s) == sum(t))]
#[variant(s.len())]
pub fn same_sum(s: Seq<Real>, t: Seq<Real>) {
    pearlite! {
        if s.len() == 0 {
            if t.len() > 0 {
                // t has an element that s lacks
                count_nonneg(t.subsequence(0, t.len() - 1), t[t.len() - 1]);
                proof_assert!(count(t, t[t.len() - 1]) > 0);
                proof_assert!(count(s, t[t.len() - 1]) == 0);
            }
        } else {
            let x = s[s.len() - 1];
            let s0 = s.subsequence(0, s.len() - 1);
            count_nonneg(s0, x);
            proof_assert!(count(t, x) > 0);
            count_pos(t, x);
            let j = such_that(|j: Int| 0 <= j && j < t.len() && t[j] == x);
            removed(t, j);
            proof_assert!(same(s0, t.removed(j)));
            same_sum(s0, t.removed(j))
        }
    }
}

/// Every element of a sub-multiset of `x` lies within any bounds of `x`.
#[logic]
#[requires(same(x, c.concat(a)))]
#[requires(forall<i> 0 <= i && i < x.len() ==> lo <= x[i] && x[i] <= hi)]
#[requires(0 <= i && i < a.len())]
#[ensures(lo <= a[i] && a[i] <= hi)]
pub fn sub_bounded(x: Seq<Real>, c: Seq<Real>, a: Seq<Real>, lo: Real, hi: Real, i: Int) {
    pearlite! {
        count_concat(c, a, a[i]);
        removed(a, i);
        count_nonneg(a.removed(i), a[i]);
        count_nonneg(c, a[i]);
        proof_assert!(count(x, a[i]) > 0);
        count_pos(x, a[i])
    }
}

#[logic]
#[requires(same(x, c.concat(a)))]
#[requires(forall<i> 0 <= i && i < x.len() ==> lo <= x[i] && x[i] <= hi)]
#[requires(0 <= n && n <= a.len())]
#[ensures(forall<i> 0 <= i && i < n ==> lo <= a[i] && a[i] <= hi)]
#[variant(n)]
pub fn sub_bounded_upto(x: Seq<Real>, c: Seq<Real>, a: Seq<Real>, lo: Real, hi: Real, n: Int) {
    pearlite! {
        if n > 0 {
            sub_bounded(x, c, a, lo, hi, n - 1);
            sub_bounded_upto(x, c, a, lo, hi, n - 1)
        }
    }
}

/// A witness that `x` and `y` are within symmetric distance `d`.
#[logic]
#[requires(sym_close(x, y, d))]
#[ensures(same(x, result.0.concat(result.1)) && same(y, result.0.concat(result.2)))]
#[ensures(result.1.len() + result.2.len() <= d)]
pub fn decompose(x: Seq<Real>, y: Seq<Real>, d: Int) -> (Seq<Real>, Seq<Real>, Seq<Real>) {
    pearlite! {
        such_that(|t: (Seq<Real>, Seq<Real>, Seq<Real>)|
            same(x, t.0.concat(t.1)) && same(y, t.0.concat(t.2)) && t.1.len() + t.2.len() <= d)
    }
}

/// Elementwise bounds give bounds on the sum.
#[logic]
#[requires(forall<i> 0 <= i && i < a.len() ==> lo <= a[i] && a[i] <= hi)]
#[ensures(lo * Real::from_int(a.len()) <= sum(a) && sum(a) <= hi * Real::from_int(a.len()))]
#[variant(a.len())]
pub fn sum_bounds(a: Seq<Real>, lo: Real, hi: Real) {
    pearlite! { if a.len() > 0 { sum_bounds(a.subsequence(0, a.len() - 1), lo, hi) } }
}

/// The sensitivity of the sum of a sized, bounded dataset under the symmetric distance.
#[logic]
#[requires(sym_close(x, y, d))]
#[requires(d >= 0)]
#[requires(x.len() == y.len())]
#[requires(lo <= hi)]
#[requires(forall<i> 0 <= i && i < x.len() ==> lo <= x[i] && x[i] <= hi)]
#[requires(forall<i> 0 <= i && i < y.len() ==> lo <= y[i] && y[i] <= hi)]
#[ensures(sum(x) - sum(y) <= Real::from_int(d / 2) * (hi - lo))]
#[ensures(sum(y) - sum(x) <= Real::from_int(d / 2) * (hi - lo))]
pub fn sized_sum_sensitivity(x: Seq<Real>, y: Seq<Real>, d: Int, lo: Real, hi: Real) {
    pearlite! {
        let (c, a, b) = decompose(x, y, d);
        same_sum(x, c.concat(a));
        same_sum(y, c.concat(b));
        sum_concat(c, a);
        sum_concat(c, b);
        sub_bounded_upto(x, c, a, lo, hi, a.len());
        sub_bounded_upto(y, c, b, lo, hi, b.len());
        sum_bounds(a, lo, hi);
        sum_bounds(b, lo, hi);
        // a and b have equal length k, and 2k <= d
        proof_assert!(x.len() == c.len() + a.len() && y.len() == c.len() + b.len());
        proof_assert!(a.len() == b.len());
        proof_assert!(a.len() <= d / 2);
        proof_assert!(sum(x) - sum(y) == sum(a) - sum(b));
        proof_assert!(sum(a) - sum(b) <= Real::from_int(a.len()) * (hi - lo));
        proof_assert!(Real::from_int(a.len()) <= Real::from_int(d / 2));
        proof_assert!(Real::from_int(a.len()) * (hi - lo) <= Real::from_int(d / 2) * (hi - lo))
    }
}

/// The sensitivity of the sum of a bounded dataset of unknown size under the symmetric distance.
#[logic]
#[requires(sym_close(x, y, d))]
#[requires(d >= 0)]
#[requires(forall<i> 0 <= i && i < x.len() ==> lo <= x[i] && x[i] <= hi)]
#[requires(forall<i> 0 <= i && i < y.len() ==> lo <= y[i] && y[i] <= hi)]
#[requires(mag >= lo && mag >= -lo && mag >= hi && mag >= -hi)]
#[ensures(sum(x) - sum(y) <= Real::from_int(d) * mag)]
#[ensures(sum(y) - sum(x) <= Real::from_int(d) * mag)]
pub fn unsized_sum_sensitivity(x: Seq<Real>, y: Seq<Real>, d: Int, lo: Real, hi: Real, mag: Real) {
    pearlite! {
        let (c, a, b) = decompose(x, y, d);
        same_sum(x, c.concat(a));
        same_sum(y, c.concat(b));
        sum_concat(c, a);
        sum_concat(c, b);
        sub_bounded_upto(x, c, a, lo, hi, a.len());
        sub_bounded_upto(y, c, b, lo, hi, b.len());
        sum_bounds(a, -mag, mag);
        sum_bounds(b, -mag, mag);
        proof_assert!(sum(x) - sum(y) == sum(a) - sum(b));
        proof_assert!(Real::from_int(a.len()) + Real::from_int(b.len()) <= Real::from_int(d));
        proof_assert!((Real::from_int(a.len()) + Real::from_int(b.len())) * mag <= Real::from_int(d) * mag)
    }
}

/// Sum of `f` over the elements of `s`.
#[logic(open)]
#[variant(s.len())]
pub fn fsum(s: Seq<Real>, f: Mapping<Real, Real>) -> Real {
    pearlite! {
        if s.len() == 0 { Real::from_int(0) } else { fsum(s.subsequence(0, s.len() - 1), f) + f[s[s.len() - 1]] }
    }
}

#[logic]
#[ensures(fsum(a.concat(b), f) == fsum(a, f) + fsum(b, f))]
#[variant(b.len())]
pub fn fsum_concat(a: Seq<Real>, b: Seq<Real>, f: Mapping<Real, Real>) {
    pearlite! {
        if b.len() > 0 {
            proof_assert!(a.concat(b).subsequence(0, a.len() + b.len() - 1)
                == a.concat(b.subsequence(0, b.len() - 1)));
            fsum_concat(a, b.subsequence(0, b.len() - 1), f)
        } else {
            proof_assert!(a.concat(b).ext_eq(a));
        }
    }
}

#[logic]
#[requires(0 <= j && j < t.len())]
#[ensures(fsum(t, f) == fsum(t.removed(j), f) + f[t[j]])]
#[variant(t.len())]
pub fn fsum_removed(t: Seq<Real>, j: Int, f: Mapping<Real, Real>) {
    pearlite! {
        if j < t.len() - 1 {
            let init = t.subsequence(0, t.len() - 1);
            proof_assert!(t.removed(j).subsequence(0, t.len() - 2) == init.removed(j));
            proof_assert!(t.removed(j)[t.len() - 2] == t[t.len() - 1]);
            fsum_removed(init, j, f)
        } else {
            proof_assert!(t.removed(j) == t.subsequence(0, t.len() - 1));
        }
    }
}

/// Multiset-equal sequences have the same sum of `f`.
#[logic]
#[requires(same(s, t))]
#[ensures(fsum(s, f) == fsum(t, f))]
#[variant(s.len())]
pub fn same_fsum(s: Seq<Real>, t: Seq<Real>, f: Mapping<Real, Real>) {
    pearlite! {
        same_sum(s, t);
        if s.len() > 0 {
            let x = s[s.len() - 1];
            let s0 = s.subsequence(0, s.len() - 1);
            count_nonneg(s0, x);
            proof_assert!(count(t, x) > 0);
            count_pos(t, x);
            let j = such_that(|j: Int| 0 <= j && j < t.len() && t[j] == x);
            removed(t, j);
            fsum_removed(t, j, f);
            proof_assert!(same(s0, t.removed(j)));
            same_fsum(s0, t.removed(j), f)
        }
    }
}

/// Bounds on `f` over the elements give bounds on the sum of `f`.
#[logic]
#[requires(forall<i> 0 <= i && i < a.len() ==> lo <= f[a[i]] && f[a[i]] <= hi)]
#[ensures(lo * Real::from_int(a.len()) <= fsum(a, f) && fsum(a, f) <= hi * Real::from_int(a.len()))]
#[variant(a.len())]
pub fn fsum_bounds(a: Seq<Real>, f: Mapping<Real, Real>, lo: Real, hi: Real) {
    pearlite! { if a.len() > 0 { fsum_bounds(a.subsequence(0, a.len() - 1), f, lo, hi) } }
}

/// The negative part of a real.
#[logic(open)]
pub fn neg_part(v: Real) -> Real {
    pearlite! { if v <= Real::from_int(0) { v } else { Real::from_int(0) } }
}

/// The positive part of a real.
#[logic(open)]
pub fn pos_part(v: Real) -> Real {
    pearlite! { if v >= Real::from_int(0) { v } else { Real::from_int(0) } }
}

/// The sums of the negative and positive parts of datasets within symmetric distance `d`
/// differ by at most `d * mag` in total.
#[logic]
#[requires(sym_close(x, y, d))]
#[requires(d >= 0)]
#[requires(forall<i> 0 <= i && i < x.len() ==> lo <= x[i] && x[i] <= hi)]
#[requires(forall<i> 0 <= i && i < y.len() ==> lo <= y[i] && y[i] <= hi)]
#[requires(mag >= -lo && mag >= hi && lo <= hi)]
#[ensures(real_abs(fsum(x, |v| neg_part(v)) - fsum(y, |v| neg_part(v)))
    + real_abs(fsum(x, |v| pos_part(v)) - fsum(y, |v| pos_part(v))) <= Real::from_int(d) * mag)]
pub fn unsized_split_sensitivity(
    x: Seq<Real>,
    y: Seq<Real>,
    d: Int,
    lo: Real,
    hi: Real,
    mag: Real,
) {
    pearlite! {
        let n: Mapping<Real, Real> = |v| neg_part(v);
        let p: Mapping<Real, Real> = |v| pos_part(v);
        let (c, a, b) = decompose(x, y, d);
        same_fsum(x, c.concat(a), n);
        same_fsum(y, c.concat(b), n);
        same_fsum(x, c.concat(a), p);
        same_fsum(y, c.concat(b), p);
        fsum_concat(c, a, n);
        fsum_concat(c, b, n);
        fsum_concat(c, a, p);
        fsum_concat(c, b, p);
        sub_bounded_upto(x, c, a, lo, hi, a.len());
        sub_bounded_upto(y, c, b, lo, hi, b.len());
        // the negative and positive parts of an element sum to at most `mag` in magnitude
        abs_parts_bound(a, mag);
        abs_parts_bound(b, mag);
        proof_assert!(Real::from_int(a.len()) + Real::from_int(b.len()) <= Real::from_int(d));
        proof_assert!((Real::from_int(a.len()) + Real::from_int(b.len())) * mag <= Real::from_int(d) * mag)
    }
}

/// `-fsum(neg_part) + fsum(pos_part)` is at most `len * mag` when every element is within `mag`.
#[logic]
#[requires(forall<i> 0 <= i && i < a.len() ==> -mag <= a[i] && a[i] <= mag)]
#[ensures(fsum(a, |v| neg_part(v)) <= Real::from_int(0) && fsum(a, |v| pos_part(v)) >= Real::from_int(0))]
#[ensures(fsum(a, |v| pos_part(v)) - fsum(a, |v| neg_part(v)) <= Real::from_int(a.len()) * mag)]
#[variant(a.len())]
pub fn abs_parts_bound(a: Seq<Real>, mag: Real) {
    pearlite! { if a.len() > 0 { abs_parts_bound(a.subsequence(0, a.len() - 1), mag) } }
}

/// With datasets of equal size, the sums of the negative and positive parts
/// differ by at most `(d / 2) * (hi - lo)` in total.
#[logic]
#[requires(sym_close(x, y, d))]
#[requires(d >= 0)]
#[requires(x.len() == y.len())]
#[requires(lo <= hi)]
#[requires(forall<i> 0 <= i && i < x.len() ==> lo <= x[i] && x[i] <= hi)]
#[requires(forall<i> 0 <= i && i < y.len() ==> lo <= y[i] && y[i] <= hi)]
#[ensures(real_abs(fsum(x, |v| neg_part(v)) - fsum(y, |v| neg_part(v)))
    + real_abs(fsum(x, |v| pos_part(v)) - fsum(y, |v| pos_part(v))) <= Real::from_int(d / 2) * (hi - lo))]
pub fn sized_split_sensitivity(x: Seq<Real>, y: Seq<Real>, d: Int, lo: Real, hi: Real) {
    pearlite! {
        let n: Mapping<Real, Real> = |v| neg_part(v);
        let p: Mapping<Real, Real> = |v| pos_part(v);
        let (c, a, b) = decompose(x, y, d);
        same_sum(x, c.concat(a));
        same_sum(y, c.concat(b));
        same_fsum(x, c.concat(a), n);
        same_fsum(y, c.concat(b), n);
        same_fsum(x, c.concat(a), p);
        same_fsum(y, c.concat(b), p);
        fsum_concat(c, a, n);
        fsum_concat(c, b, n);
        fsum_concat(c, a, p);
        fsum_concat(c, b, p);
        sub_bounded_upto(x, c, a, lo, hi, a.len());
        sub_bounded_upto(y, c, b, lo, hi, b.len());
        // each part of an element lies within the corresponding part of the bounds
        fsum_bounds(a, n, neg_part(lo), neg_part(hi));
        fsum_bounds(b, n, neg_part(lo), neg_part(hi));
        fsum_bounds(a, p, pos_part(lo), pos_part(hi));
        fsum_bounds(b, p, pos_part(lo), pos_part(hi));
        proof_assert!(x.len() == c.len() + a.len() && y.len() == c.len() + b.len());
        proof_assert!(a.len() == b.len() && a.len() <= d / 2);
        let k = Real::from_int(a.len());
        proof_assert!(neg_part(hi) - neg_part(lo) + pos_part(hi) - pos_part(lo) == hi - lo);
        proof_assert!(k * (neg_part(hi) - neg_part(lo)) + k * (pos_part(hi) - pos_part(lo)) == k * (hi - lo));
        proof_assert!(k <= Real::from_int(d / 2));
        proof_assert!(k * (hi - lo) <= Real::from_int(d / 2) * (hi - lo))
    }
}
