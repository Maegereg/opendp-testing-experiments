//! Event-level dataset distances, and their stability under row-by-row maps.
//!
//! Each [`EventLevelMetric`](crate::metrics::EventLevelMetric) relates datasets (sequences of rows)
//! by `EventModel::close`. Applying the same function to every row of two `d`-close datasets gives
//! two `d`-close datasets (`EventModel::close_map`), which is the stability of
//! [`make_row_by_row`](crate::transformations::make_row_by_row) with the map `d -> d`.
use creusot_std::{
    logic::{Int, Mapping, such_that},
    prelude::*,
};

use super::multiset::{count, count_bounds, decompose, same, sym_close};
use crate::metrics::{ChangeOneDistance, HammingDistance, InsertDeleteDistance, SymmetricDistance};

/// The ghost model of an event-level metric: when two datasets are within distance `d`.
pub trait EventModel {
    /// `x` and `y` are within distance `d`.
    #[logic]
    fn close<T>(x: Seq<T>, y: Seq<T>, d: Int) -> bool;

    /// Closeness is monotone in `d`.
    #[logic]
    #[requires(Self::close(x, y, d) && d <= e)]
    #[ensures(result && Self::close(x, y, e))]
    fn close_mono<T>(x: Seq<T>, y: Seq<T>, d: Int, e: Int) -> bool;

    /// Mapping every row by the same function preserves closeness.
    #[logic]
    #[requires(Self::close(x, y, d))]
    #[ensures(result && Self::close(x.map(f), y.map(f), d))]
    fn close_map<T, U>(x: Seq<T>, y: Seq<T>, d: Int, f: Mapping<T, U>) -> bool;
}

/// Mapping commutes with dropping the last element.
#[logic]
#[requires(s.len() > 0)]
#[ensures(s.map(f).subsequence(0, s.len() - 1) == s.subsequence(0, s.len() - 1).map(f))]
#[ensures(s.map(f)[s.len() - 1] == f[s[s.len() - 1]])]
pub fn map_init<T, U>(s: Seq<T>, f: Mapping<T, U>) {
    pearlite! { proof_assert!(s.map(f).subsequence(0, s.len() - 1).ext_eq(s.subsequence(0, s.len() - 1).map(f))) }
}

/// Removing the element at `j` takes one occurrence of `t[j]` out of the counts.
#[logic]
#[requires(0 <= j && j < t.len())]
#[ensures(forall<v: T> count(t, v) == count(t.removed(j), v) + if t[j] == v { 1 } else { 0 })]
#[ensures(t.removed(j).len() == t.len() - 1)]
#[variant(t.len())]
pub fn count_removed<T>(t: Seq<T>, j: Int) {
    pearlite! {
        if j < t.len() - 1 {
            let init = t.subsequence(0, t.len() - 1);
            proof_assert!(t.removed(j).subsequence(0, t.len() - 2) == init.removed(j));
            proof_assert!(t.removed(j)[t.len() - 2] == t[t.len() - 1]);
            count_removed(init, j)
        } else {
            proof_assert!(t.removed(j) == t.subsequence(0, t.len() - 1));
        }
    }
}

/// A value with a positive count occurs at some index.
#[logic]
#[requires(count(t, v) > 0)]
#[ensures(0 <= result && result < t.len() && t[result] == v)]
pub fn index_of<T>(t: Seq<T>, v: T) -> Int {
    pearlite! {
        count_occurs(t, v);
        such_that(|j: Int| 0 <= j && j < t.len() && t[j] == v)
    }
}

#[logic]
#[requires(count(t, v) > 0)]
#[ensures(exists<j> 0 <= j && j < t.len() && t[j] == v)]
#[variant(t.len())]
fn count_occurs<T>(t: Seq<T>, v: T) {
    pearlite! {
        if t[t.len() - 1] != v { count_occurs(t.subsequence(0, t.len() - 1), v) }
    }
}

/// Multiset-equal sequences stay multiset-equal when every element is mapped by `f`.
#[logic]
#[requires(same(a, b))]
#[ensures(same(a.map(f), b.map(f)))]
#[variant(a.len())]
pub fn same_map<T, U>(a: Seq<T>, b: Seq<T>, f: Mapping<T, U>) {
    pearlite! {
        if a.len() == 0 {
            if b.len() > 0 {
                count_bounds(b.subsequence(0, b.len() - 1), b[b.len() - 1]);
                proof_assert!(count(b, b[b.len() - 1]) > 0);
            }
            proof_assert!(b.len() == 0);
            proof_assert!(a.map(f).ext_eq(b.map(f)));
        } else {
            let n = a.len();
            let e = a[n - 1];
            let ai = a.subsequence(0, n - 1);
            count_bounds(ai, e);
            let j = index_of(b, e);
            count_removed(b, j);
            proof_assert!(same(ai, b.removed(j)));
            same_map(ai, b.removed(j), f);
            proof_assert!(b.removed(j).map(f).ext_eq(b.map(f).removed(j)));
            count_removed(b.map(f), j);
            map_init(a, f);
        }
    }
}

/// Mapping distributes over concatenation.
#[logic]
#[ensures(a.concat(b).map(f) == a.map(f).concat(b.map(f)))]
pub fn map_concat<T, U>(a: Seq<T>, b: Seq<T>, f: Mapping<T, U>) {
    pearlite! { proof_assert!(a.concat(b).map(f).ext_eq(a.map(f).concat(b.map(f)))) }
}

/// Symmetric neighbours stay neighbours when every element is mapped by `f`.
#[logic]
#[requires(sym_close(x, y, d))]
#[ensures(sym_close(x.map(f), y.map(f), d))]
pub fn sym_close_map<T, U>(x: Seq<T>, y: Seq<T>, d: Int, f: Mapping<T, U>) {
    pearlite! {
        let (c, a, b) = decompose(x, y, d);
        same_map(x, c.concat(a), f);
        same_map(y, c.concat(b), f);
        map_concat(c, a, f);
        map_concat(c, b, f);
        proof_assert!(same(x.map(f), c.map(f).concat(a.map(f))));
        proof_assert!(same(y.map(f), c.map(f).concat(b.map(f))));
    }
}

/// `z` is a subsequence of `x`, and `dx` is the sequence of the other elements of `x`.
#[logic(open)]
#[variant(x.len())]
pub fn sub<T>(z: Seq<T>, x: Seq<T>, dx: Seq<T>) -> bool {
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

/// `x` and `y` are within insert-delete distance `d`: deleting `d` elements in all from `x` and
/// `y` leaves the same sequence `z`.
#[logic(open)]
pub fn id_close<T>(x: Seq<T>, y: Seq<T>, d: Int) -> bool {
    pearlite! {
        exists<z: Seq<T>, dx: Seq<T>, dy: Seq<T>> sub(z, x, dx) && sub(z, y, dy) && dx.len() + dy.len() <= d
    }
}

/// Subsequences stay subsequences when every element is mapped by `f`.
#[logic]
#[requires(sub(z, x, dx))]
#[ensures(sub(z.map(f), x.map(f), dx.map(f)))]
#[variant(x.len())]
pub fn sub_map<T, U>(z: Seq<T>, x: Seq<T>, dx: Seq<T>, f: Mapping<T, U>) {
    pearlite! {
        if x.len() > 0 {
            let xi = x.subsequence(0, x.len() - 1);
            map_init(x, f);
            if dx.len() > 0 && dx[dx.len() - 1] == x[x.len() - 1]
                && sub(z, xi, dx.subsequence(0, dx.len() - 1)) {
                map_init(dx, f);
                sub_map(z, xi, dx.subsequence(0, dx.len() - 1), f)
            } else {
                map_init(z, f);
                sub_map(z.subsequence(0, z.len() - 1), xi, dx, f)
            }
        } else {
            proof_assert!(z.map(f).len() == 0 && dx.map(f).len() == 0);
        }
    }
}

/// The number of positions at which `x` and `y` differ (`x` and `y` have the same length).
#[logic(open)]
#[variant(x.len())]
pub fn hamming<T>(x: Seq<T>, y: Seq<T>) -> Int {
    pearlite! {
        if x.len() == 0 { 0 } else {
            hamming(x.subsequence(0, x.len() - 1), y.subsequence(0, x.len() - 1))
                + if x[x.len() - 1] != y[x.len() - 1] { 1 } else { 0 }
        }
    }
}

/// Mapping every element can only remove differences.
#[logic]
#[requires(x.len() == y.len())]
#[ensures(hamming(x.map(f), y.map(f)) <= hamming(x, y))]
#[variant(x.len())]
pub fn hamming_map<T, U>(x: Seq<T>, y: Seq<T>, f: Mapping<T, U>) {
    pearlite! {
        if x.len() > 0 {
            map_init(x, f);
            map_init(y, f);
            hamming_map(x.subsequence(0, x.len() - 1), y.subsequence(0, x.len() - 1), f)
        }
    }
}

impl EventModel for SymmetricDistance {
    #[logic(open)]
    fn close<T>(x: Seq<T>, y: Seq<T>, d: Int) -> bool {
        sym_close(x, y, d)
    }

    #[logic]
    #[requires(Self::close(x, y, d) && d <= e)]
    #[ensures(result && Self::close(x, y, e))]
    fn close_mono<T>(x: Seq<T>, y: Seq<T>, d: Int, e: Int) -> bool {
        true
    }

    #[logic]
    #[requires(Self::close(x, y, d))]
    #[ensures(result && Self::close(x.map(f), y.map(f), d))]
    fn close_map<T, U>(x: Seq<T>, y: Seq<T>, d: Int, f: Mapping<T, U>) -> bool {
        sym_close_map(x, y, d, f);
        true
    }
}

impl EventModel for InsertDeleteDistance {
    #[logic(open)]
    fn close<T>(x: Seq<T>, y: Seq<T>, d: Int) -> bool {
        id_close(x, y, d)
    }

    #[logic]
    #[requires(Self::close(x, y, d) && d <= e)]
    #[ensures(result && Self::close(x, y, e))]
    fn close_mono<T>(x: Seq<T>, y: Seq<T>, d: Int, e: Int) -> bool {
        true
    }

    #[logic]
    #[requires(Self::close(x, y, d))]
    #[ensures(result && Self::close(x.map(f), y.map(f), d))]
    fn close_map<T, U>(x: Seq<T>, y: Seq<T>, d: Int, f: Mapping<T, U>) -> bool {
        pearlite! {
            let (z, dx, dy) = such_that(|w: (Seq<T>, Seq<T>, Seq<T>)|
                sub(w.0, x, w.1) && sub(w.0, y, w.2) && w.1.len() + w.2.len() <= d);
            sub_map(z, x, dx, f);
            sub_map(z, y, dy, f);
            true
        }
    }
}

/// The change-one distance: datasets of the same size, whose symmetric distance is at most `2 d`.
impl EventModel for ChangeOneDistance {
    #[logic(open)]
    fn close<T>(x: Seq<T>, y: Seq<T>, d: Int) -> bool {
        pearlite! { x.len() == y.len() && sym_close(x, y, 2 * d) }
    }

    #[logic]
    #[requires(Self::close(x, y, d) && d <= e)]
    #[ensures(result && Self::close(x, y, e))]
    fn close_mono<T>(x: Seq<T>, y: Seq<T>, d: Int, e: Int) -> bool {
        true
    }

    #[logic]
    #[requires(Self::close(x, y, d))]
    #[ensures(result && Self::close(x.map(f), y.map(f), d))]
    fn close_map<T, U>(x: Seq<T>, y: Seq<T>, d: Int, f: Mapping<T, U>) -> bool {
        sym_close_map(x, y, 2 * d, f);
        true
    }
}

/// The Hamming distance: datasets of the same size, differing in at most `d` positions.
impl EventModel for HammingDistance {
    #[logic(open)]
    fn close<T>(x: Seq<T>, y: Seq<T>, d: Int) -> bool {
        pearlite! { x.len() == y.len() && hamming(x, y) <= d }
    }

    #[logic]
    #[requires(Self::close(x, y, d) && d <= e)]
    #[ensures(result && Self::close(x, y, e))]
    fn close_mono<T>(x: Seq<T>, y: Seq<T>, d: Int, e: Int) -> bool {
        true
    }

    #[logic]
    #[requires(Self::close(x, y, d))]
    #[ensures(result && Self::close(x.map(f), y.map(f), d))]
    fn close_map<T, U>(x: Seq<T>, y: Seq<T>, d: Int, f: Mapping<T, U>) -> bool {
        hamming_map(x, y, f);
        true
    }
}
