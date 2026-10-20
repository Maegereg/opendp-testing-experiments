//! Datasets as multisets of reals, and the symmetric distance between them.
//!
//! A dataset `x: Vec<T>` is modeled by the sequence of the real values of its elements.
//! Two datasets are within symmetric distance `d` (`sym_close`) when they share a common
//! sub-multiset `c` and differ only by extra elements `a` and `b` with `|a| + |b| <= d`.
//! This is equivalent to the definition of [`SymmetricDistance`](crate::metrics::SymmetricDistance):
//! the size of the symmetric difference of the two multisets is at most `d`.
use creusot_std::{
    logic::{real::Real, such_that},
    prelude::*,
};

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
        let (c, a, b) = such_that(|t: (Seq<Real>, Seq<Real>, Seq<Real>)|
            same(x, t.0.concat(t.1)) && same(y, t.0.concat(t.2)) && t.1.len() + t.2.len() <= d);
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
