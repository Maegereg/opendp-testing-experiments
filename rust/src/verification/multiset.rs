//! Datasets of arbitrary values as multisets, and the symmetric distance between them.
//!
//! The generic counterpart of [`dataset`](super::dataset), which models datasets by real values.
//! Here a dataset is a sequence of values of any type `T` (typically the deep models of the
//! elements), compared by logical equality.
use creusot_std::{
    logic::{Int, such_that},
    prelude::*,
};

/// Number of occurrences of `v` in `s`.
#[logic(open)]
#[variant(s.len())]
pub fn count<T>(s: Seq<T>, v: T) -> Int {
    pearlite! {
        if s.len() == 0 { 0 } else {
            count(s.subsequence(0, s.len() - 1), v) + if s[s.len() - 1] == v { 1 } else { 0 }
        }
    }
}

/// `a` and `b` are equal as multisets.
#[logic(open)]
pub fn same<T>(a: Seq<T>, b: Seq<T>) -> bool {
    pearlite! { forall<v: T> count(a, v) == count(b, v) }
}

/// `x` and `y` are within symmetric distance `d`: they share a common core `c`,
/// and differ only by the extra elements `a` (in `x`) and `b` (in `y`).
/// This is equivalent to |multiset(x) Δ multiset(y)| <= d.
#[logic(open)]
pub fn sym_close<T>(x: Seq<T>, y: Seq<T>, d: Int) -> bool {
    pearlite! {
        exists<c: Seq<T>, a: Seq<T>, b: Seq<T>>
            same(x, c.concat(a)) && same(y, c.concat(b)) && a.len() + b.len() <= d
    }
}

/// A witness that `x` and `y` are within symmetric distance `d`.
#[logic]
#[requires(sym_close(x, y, d))]
#[ensures(same(x, result.0.concat(result.1)) && same(y, result.0.concat(result.2)))]
#[ensures(result.1.len() + result.2.len() <= d)]
pub fn decompose<T>(x: Seq<T>, y: Seq<T>, d: Int) -> (Seq<T>, Seq<T>, Seq<T>) {
    pearlite! {
        such_that(|t: (Seq<T>, Seq<T>, Seq<T>)|
            same(x, t.0.concat(t.1)) && same(y, t.0.concat(t.2)) && t.1.len() + t.2.len() <= d)
    }
}

/// Counts are between zero and the length.
#[logic]
#[ensures(0 <= count(s, v) && count(s, v) <= s.len())]
#[variant(s.len())]
pub fn count_bounds<T>(s: Seq<T>, v: T) {
    pearlite! { if s.len() > 0 { count_bounds(s.subsequence(0, s.len() - 1), v) } }
}

/// Counts in a concatenation add up.
#[logic]
#[ensures(forall<v: T> count(a.concat(b), v) == count(a, v) + count(b, v))]
#[variant(b.len())]
pub fn count_concat<T>(a: Seq<T>, b: Seq<T>) {
    pearlite! {
        if b.len() > 0 {
            proof_assert!(a.concat(b).subsequence(0, a.len() + b.len() - 1)
                == a.concat(b.subsequence(0, b.len() - 1)));
            count_concat(a, b.subsequence(0, b.len() - 1))
        } else {
            proof_assert!(a.concat(b).ext_eq(a));
        }
    }
}

/// The elements of `k` are pairwise distinct.
#[logic(open)]
pub fn distinct<T>(k: Seq<T>) -> bool {
    pearlite! { forall<i, j> 0 <= i && i < j && j < k.len() ==> k[i] != k[j] }
}

/// The total count in `s` of the keys `k`: `sum_{v in k} count(s, v)`.
#[logic(open)]
#[variant(k.len())]
pub fn kcount<T>(k: Seq<T>, s: Seq<T>) -> Int {
    pearlite! {
        if k.len() == 0 { 0 } else { kcount(k.subsequence(0, k.len() - 1), s) + count(s, k[k.len() - 1]) }
    }
}

/// Appending `e` to `s` adds the number of occurrences of `e` in `k` to `kcount(k, s)`.
#[logic]
#[ensures(kcount(k, s.push_back(e)) == kcount(k, s) + count(k, e))]
#[variant(k.len())]
pub fn kcount_push<T>(k: Seq<T>, s: Seq<T>, e: T) {
    pearlite! {
        proof_assert!(s.push_back(e).subsequence(0, s.len()) == s);
        if k.len() > 0 { kcount_push(k.subsequence(0, k.len() - 1), s, e) }
    }
}

/// A distinct sequence contains each value at most once.
#[logic]
#[requires(distinct(k))]
#[ensures(count(k, e) <= 1)]
#[ensures(forall<i> 0 <= i && i < k.len() && k[i] == e ==> count(k, e) == 1)]
#[ensures((forall<i> 0 <= i && i < k.len() ==> k[i] != e) ==> count(k, e) == 0)]
#[variant(k.len())]
pub fn count_distinct<T>(k: Seq<T>, e: T) {
    pearlite! {
        if k.len() > 0 {
            let ki = k.subsequence(0, k.len() - 1);
            count_distinct(ki, e);
            proof_assert!(distinct(ki));
            proof_assert!(k[k.len() - 1] == e ==> forall<i> 0 <= i && i < ki.len() ==> ki[i] != e)
        }
    }
}

/// For distinct keys, the total count is at most the length of the dataset.
#[logic]
#[requires(distinct(k))]
#[ensures(result && 0 <= kcount(k, s) && kcount(k, s) <= s.len())]
#[variant(s.len())]
pub fn kcount_le_len<T>(k: Seq<T>, s: Seq<T>) -> bool {
    pearlite! {
        if s.len() > 0 {
            let si = s.subsequence(0, s.len() - 1);
            kcount_le_len(k, si);
            proof_assert!(si.push_back(s[s.len() - 1]) == s);
            kcount_push(k, si, s[s.len() - 1]);
            count_distinct(k, s[s.len() - 1]);
            count_bounds(k, s[s.len() - 1]);
            true
        } else {
            kcount_empty(k, s);
            true
        }
    }
}

/// Every count is between zero and the length.
#[logic]
#[ensures(forall<v: T> 0 <= count(s, v) && count(s, v) <= s.len())]
#[variant(s.len())]
pub fn count_range<T>(s: Seq<T>) {
    pearlite! { if s.len() > 0 { count_range(s.subsequence(0, s.len() - 1)) } }
}

/// Nothing is counted in an empty dataset.
#[logic]
#[requires(s.len() == 0)]
#[ensures(kcount(k, s) == 0)]
#[variant(k.len())]
pub fn kcount_empty<T>(k: Seq<T>, s: Seq<T>) {
    pearlite! { if k.len() > 0 { kcount_empty(k.subsequence(0, k.len() - 1), s) } }
}

/// Multiset-equal sequences have the same length.
#[logic]
#[requires(same(a, b))]
#[ensures(a.len() == b.len())]
#[variant(a.len())]
pub fn same_len<T>(a: Seq<T>, b: Seq<T>) {
    pearlite! {
        if a.len() == 0 {
            if b.len() > 0 {
                count_bounds(b.subsequence(0, b.len() - 1), b[b.len() - 1]);
                proof_assert!(count(b, b[b.len() - 1]) > 0);
            }
        } else {
            let e = a[a.len() - 1];
            let ai = a.subsequence(0, a.len() - 1);
            count_bounds(ai, e);
            let j = super::rows::index_of(b, e);
            super::rows::count_removed(b, j);
            same_len(ai, b.removed(j))
        }
    }
}

/// Appending an element adds one occurrence.
#[logic]
#[ensures(forall<w: T> count(s.push_back(v), w) == count(s, w) + if v == w { 1 } else { 0 })]
#[ensures(s.push_back(v).subsequence(0, s.len()) == s)]
pub fn count_push<T>(s: Seq<T>, v: T) {
    pearlite! { proof_assert!(s.push_back(v).subsequence(0, s.len()).ext_eq(s)) }
}
