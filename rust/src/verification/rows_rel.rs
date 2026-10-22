//! Event-level distances under a row-by-row *relation*, such as a random row function.
//!
//! A random row function relates each input row to its possible outputs (`r`). If `x` and `y`
//! are `d`-close, then for any outputs `fx` related row by row to `x`, there are outputs related to
//! `y` that are `d`-close to `fx`: the rows that `x` and `y` share keep their outputs, and the
//! other rows of `y` take any related output (`g`). This matching is the coupling that gives
//! shared rows the same randomness.
//!
//! Each lemma pairs every row with its output, lifts the witness of closeness from rows to pairs,
//! and projects the pairs onto the outputs (`EventModel::close_map`).
use creusot_std::{
    logic::{Int, Mapping},
    prelude::*,
};

use super::{
    multiset::{
        count, count_bounds, count_concat, count_push, decompose, same, same_len, sym_close,
    },
    rows::{count_removed, hamming, id_close, index_of, map_concat, sub},
};

/// The first component of a pair.
#[logic(open)]
pub fn fst<T, U>() -> Mapping<(T, U), T> {
    pearlite! { |p: (T, U)| p.0 }
}

/// The second component of a pair.
#[logic(open)]
pub fn snd<T, U>() -> Mapping<(T, U), U> {
    pearlite! { |p: (T, U)| p.1 }
}

/// The pairs of the elements of `x` and `y`, position by position.
#[logic(open)]
pub fn zip<T, U>(x: Seq<T>, y: Seq<U>) -> Seq<(T, U)> {
    pearlite! { Seq::create(x.len(), |i| (x[i], y[i])) }
}

/// Every pair in `p` is related by `r`.
#[logic(open)]
pub fn related<T, U>(p: Seq<(T, U)>, r: Mapping<(T, U), bool>) -> bool {
    pearlite! { forall<i> 0 <= i && i < p.len() ==> r[p[i]] }
}

/// The pair of `v` and `g(v)`.
#[logic(open)]
pub fn with<T, U>(g: Mapping<T, U>) -> Mapping<T, (T, U)> {
    pearlite! { |v: T| (v, g[v]) }
}

/// Mapping commutes with appending an element.
#[logic]
#[ensures(s.push_back(e).map(f) == s.map(f).push_back(f[e]))]
pub fn map_push<T, U>(s: Seq<T>, e: T, f: Mapping<T, U>) {
    pearlite! { proof_assert!(s.push_back(e).map(f).ext_eq(s.map(f).push_back(f[e]))) }
}

/// Mapping commutes with taking a prefix.
#[logic]
#[requires(0 <= n && n <= s.len())]
#[ensures(s.subsequence(0, n).map(f) == s.map(f).subsequence(0, n))]
pub fn map_prefix<T, U>(s: Seq<T>, n: Int, f: Mapping<T, U>) {
    pearlite! { proof_assert!(s.subsequence(0, n).map(f).ext_eq(s.map(f).subsequence(0, n))) }
}

/// An element at some position occurs.
#[logic]
#[requires(0 <= i && i < s.len())]
#[ensures(count(s, s[i]) > 0)]
#[variant(s.len())]
pub fn count_index<T>(s: Seq<T>, i: Int) {
    pearlite! {
        let si = s.subsequence(0, s.len() - 1);
        count_bounds(si, s[i]);
        if i < s.len() - 1 {
            count_index(si, i)
        }
    }
}

/// Multiset-equal sequences have the same elements, so if all of one are related, so are all of
/// the other.
#[logic]
#[requires(same(a, b) && related(b, r))]
#[ensures(related(a, r))]
pub fn same_related<T, U>(a: Seq<(T, U)>, b: Seq<(T, U)>, r: Mapping<(T, U), bool>) {
    pearlite! {
        proof_assert!(forall<i> 0 <= i && i < a.len() ==> same_related_at(a, b, r, i) && r[a[i]]);
    }
}

/// One element of `same_related`.
#[logic]
#[requires(same(a, b) && related(b, r) && 0 <= i && i < a.len())]
#[ensures(result && r[a[i]])]
pub fn same_related_at<T, U>(
    a: Seq<(T, U)>,
    b: Seq<(T, U)>,
    r: Mapping<(T, U), bool>,
    i: Int,
) -> bool {
    pearlite! {
        count_index(a, i);
        let j = index_of(b, a[i]);
        true
    }
}

// ---------------------------------------------------------------------------------------------
// Symmetric distance
// ---------------------------------------------------------------------------------------------

/// If the first components of `p` make up `c` and `a`, then `p` splits into pairs over `c` and
/// pairs over `a`.
#[logic]
#[requires(p.map(fst()) == x && same(x, c.concat(a)))]
#[ensures(same(p, result.0.concat(result.1)))]
#[ensures(same(result.0.map(fst()), c) && same(result.1.map(fst()), a))]
#[variant(p.len())]
pub fn lift_split<T, U>(
    p: Seq<(T, U)>,
    x: Seq<T>,
    c: Seq<T>,
    a: Seq<T>,
) -> (Seq<(T, U)>, Seq<(T, U)>) {
    pearlite! {
        if p.len() == 0 {
            same_len(x, c.concat(a));
            proof_assert!(Seq::<(T, U)>::empty().map(fst()).ext_eq(Seq::empty()));
            proof_assert!(c.ext_eq(Seq::empty()) && a.ext_eq(Seq::empty()));
            (Seq::empty(), Seq::empty())
        } else {
            let n = p.len();
            let e = p[n - 1];
            let v = e.0;
            let pi = p.subsequence(0, n - 1);
            let xi = x.subsequence(0, n - 1);
            map_prefix(p, n - 1, fst());
            proof_assert!(x[n - 1] == v);
            count_push(xi, v);
            proof_assert!(x == xi.push_back(v));
            count_push(pi, e);
            proof_assert!(p == pi.push_back(e));
            count_bounds(xi, v);
            count_concat(c, a);
            if count(c, v) > 0 {
                let j = index_of(c, v);
                let c2 = c.removed(j);
                count_removed(c, j);
                count_concat(c2, a);
                let (pc, pa) = lift_split(pi, xi, c2, a);
                count_push(pc, e);
                count_concat(pc.push_back(e), pa);
                count_concat(pc, pa);
                map_push(pc, e, fst());
                count_push(pc.map(fst()), v);
                (pc.push_back(e), pa)
            } else {
                let j = index_of(a, v);
                let a2 = a.removed(j);
                count_removed(a, j);
                count_concat(c, a2);
                let (pc, pa) = lift_split(pi, xi, c, a2);
                count_push(pa, e);
                count_concat(pc, pa.push_back(e));
                count_concat(pc, pa);
                map_push(pa, e, fst());
                count_push(pa.map(fst()), v);
                (pc, pa.push_back(e))
            }
        }
    }
}

/// Reorder `q` so that its first components are `y`.
#[logic]
#[requires(same(q.map(fst()), y))]
#[ensures(same(result, q) && result.map(fst()) == y)]
#[variant(y.len())]
pub fn align<T, U>(q: Seq<(T, U)>, y: Seq<T>) -> Seq<(T, U)> {
    pearlite! {
        same_len(q.map(fst()), y);
        if y.len() == 0 {
            proof_assert!(q.ext_eq(Seq::empty()));
            proof_assert!(Seq::<(T, U)>::empty().map(fst()).ext_eq(y));
            Seq::empty()
        } else {
            let n = y.len();
            let v = y[n - 1];
            let yi = y.subsequence(0, n - 1);
            count_push(yi, v);
            proof_assert!(y == yi.push_back(v));
            count_bounds(yi, v);
            let fq = q.map(fst());
            let k = index_of(fq, v);
            let qr = q.removed(k);
            proof_assert!(qr.map(fst()).ext_eq(fq.removed(k)));
            count_removed(fq, k);
            let q2 = align(qr, yi);
            count_removed(q, k);
            count_push(q2, q[k]);
            map_push(q2, q[k], fst());
            q2.push_back(q[k])
        }
    }
}

/// Lifting a symmetric-distance neighbour: if the first components of `p` are `x` and `x`, `y`
/// are within symmetric distance `d`, then pairs over `y`, taking the pairs of `p` for the rows
/// that `x` and `y` share and `g` for the others, are within symmetric distance `d` of `p`.
#[logic]
#[requires(sym_close(x, y, d) && p.map(fst()) == x)]
#[requires(related(p, r) && forall<v: T> r[(v, g[v])])]
#[ensures(result.map(fst()) == y && sym_close(p, result, d) && related(result, r))]
pub fn lift_sym<T, U>(
    x: Seq<T>,
    y: Seq<T>,
    d: Int,
    p: Seq<(T, U)>,
    r: Mapping<(T, U), bool>,
    g: Mapping<T, U>,
) -> Seq<(T, U)> {
    pearlite! {
        let (c, a, b) = decompose(x, y, d);
        let (pc, pa) = lift_split(p, x, c, a);
        let pb = b.map(with(g));
        proof_assert!(pb.map(fst()).ext_eq(b));
        let q = pc.concat(pb);
        map_concat(pc, pb, fst());
        count_concat(pc.map(fst()), b);
        count_concat(c, b);
        proof_assert!(q.map(fst()) == pc.map(fst()).concat(b));
        proof_assert!(same(q.map(fst()), y));
        same_len(pa.map(fst()), a);
        proof_assert!(pa.len() == a.len() && pb.len() == b.len());
        same_related(pc.concat(pa), p, r);
        proof_assert!(forall<i> 0 <= i && i < pc.len() ==> pc[i] == pc.concat(pa)[i]);
        proof_assert!(related(pc, r));
        proof_assert!(forall<i> 0 <= i && i < pb.len() ==> pb[i] == (b[i], g[b[i]]));
        proof_assert!(related(pb, r));
        proof_assert!(forall<i> 0 <= i && i < q.len() ==> q[i] == if i < pc.len() { pc[i] } else { pb[i - pc.len()] });
        proof_assert!(related(q, r));
        let q2 = align(q, y);
        same_related(q2, q, r);
        proof_assert!(same(q2, pc.concat(pb)));
        q2
    }
}

// ---------------------------------------------------------------------------------------------
// Insert-delete distance
// ---------------------------------------------------------------------------------------------

/// A subsequence `z` of the first components of `p` lifts to a subsequence of `p`.
#[logic]
#[requires(sub(z, x, dx) && p.map(fst()) == x && related(p, r))]
#[ensures(sub(result.0, p, result.1) && result.0.map(fst()) == z && result.1.len() == dx.len())]
#[ensures(related(result.0, r))]
#[variant(x.len())]
pub fn lift_sub<T, U>(
    z: Seq<T>,
    x: Seq<T>,
    dx: Seq<T>,
    p: Seq<(T, U)>,
    r: Mapping<(T, U), bool>,
) -> (Seq<(T, U)>, Seq<(T, U)>) {
    pearlite! {
        if x.len() == 0 {
            proof_assert!(p.len() == 0 && z.len() == 0);
            proof_assert!(Seq::<(T, U)>::empty().map(fst()).ext_eq(z));
            (Seq::empty(), Seq::empty())
        } else {
            let n = x.len();
            let xi = x.subsequence(0, n - 1);
            let pi = p.subsequence(0, n - 1);
            let e = p[n - 1];
            map_prefix(p, n - 1, fst());
            count_push(pi, e);
            proof_assert!(p == pi.push_back(e));
            if dx.len() > 0 && dx[dx.len() - 1] == x[n - 1]
                && sub(z, xi, dx.subsequence(0, dx.len() - 1)) {
                let (pz, pd) = lift_sub(z, xi, dx.subsequence(0, dx.len() - 1), pi, r);
                count_push(pd, e);
                (pz, pd.push_back(e))
            } else {
                let zi = z.subsequence(0, z.len() - 1);
                let (pz, pd) = lift_sub(zi, xi, dx, pi, r);
                count_push(pz, e);
                map_push(pz, e, fst());
                count_push(zi, z[z.len() - 1]);
                proof_assert!(z == zi.push_back(z[z.len() - 1]));
                (pz.push_back(e), pd)
            }
        }
    }
}

/// Pairs over `y` that contain `pz`, lifting `z`, as a subsequence: the pairs of `pz` for the rows
/// of `z`, and `g` for the inserted rows.
#[logic]
#[requires(sub(z, y, dy) && pz.map(fst()) == z && related(pz, r) && forall<v: T> r[(v, g[v])])]
#[ensures(result.0.map(fst()) == y && sub(pz, result.0, result.1) && result.1.len() == dy.len())]
#[ensures(related(result.0, r))]
#[variant(y.len())]
pub fn build_sub<T, U>(
    z: Seq<T>,
    y: Seq<T>,
    dy: Seq<T>,
    pz: Seq<(T, U)>,
    r: Mapping<(T, U), bool>,
    g: Mapping<T, U>,
) -> (Seq<(T, U)>, Seq<(T, U)>) {
    pearlite! {
        if y.len() == 0 {
            proof_assert!(z.len() == 0 && pz.len() == 0);
            proof_assert!(Seq::<(T, U)>::empty().map(fst()).ext_eq(y));
            (Seq::empty(), Seq::empty())
        } else {
            let n = y.len();
            let yi = y.subsequence(0, n - 1);
            count_push(yi, y[n - 1]);
            proof_assert!(y == yi.push_back(y[n - 1]));
            if dy.len() > 0 && dy[dy.len() - 1] == y[n - 1]
                && sub(z, yi, dy.subsequence(0, dy.len() - 1)) {
                let (py, pd) = build_sub(z, yi, dy.subsequence(0, dy.len() - 1), pz, r, g);
                let e = (y[n - 1], g[y[n - 1]]);
                count_push(py, e);
                count_push(pd, e);
                map_push(py, e, fst());
                (py.push_back(e), pd.push_back(e))
            } else {
                let m = z.len();
                let zi = z.subsequence(0, m - 1);
                let pzi = pz.subsequence(0, m - 1);
                map_prefix(pz, m - 1, fst());
                let e = pz[m - 1];
                let (py, pd) = build_sub(zi, yi, dy, pzi, r, g);
                count_push(py, e);
                count_push(pzi, e);
                proof_assert!(pz == pzi.push_back(e));
                map_push(py, e, fst());
                (py.push_back(e), pd)
            }
        }
    }
}

/// Lifting an insert-delete neighbour: the common subsequence keeps its pairs, and inserted rows
/// take `g`.
#[logic]
#[requires(id_close(x, y, d) && p.map(fst()) == x)]
#[requires(related(p, r) && forall<v: T> r[(v, g[v])])]
#[ensures(result.map(fst()) == y && id_close(p, result, d) && related(result, r))]
pub fn lift_id<T, U>(
    x: Seq<T>,
    y: Seq<T>,
    d: Int,
    p: Seq<(T, U)>,
    r: Mapping<(T, U), bool>,
    g: Mapping<T, U>,
) -> Seq<(T, U)> {
    pearlite! {
        let (z, dx, dy) = super::rows::id_witness(x, y, d);
        let (pz, pdx) = lift_sub(z, x, dx, p, r);
        let (py, pdy) = build_sub(z, y, dy, pz, r, g);
        py
    }
}

// ---------------------------------------------------------------------------------------------
// Hamming distance
// ---------------------------------------------------------------------------------------------

/// Lifting a Hamming neighbour: equal rows keep their pairs, and the others take `g`.
#[logic]
#[requires(x.len() == y.len() && p.map(fst()) == x)]
#[requires(related(p, r) && forall<v: T> r[(v, g[v])])]
#[ensures(result.map(fst()) == y && hamming(p, result) <= hamming(x, y) && related(result, r))]
#[variant(x.len())]
pub fn lift_hamming<T, U>(
    x: Seq<T>,
    y: Seq<T>,
    p: Seq<(T, U)>,
    r: Mapping<(T, U), bool>,
    g: Mapping<T, U>,
) -> Seq<(T, U)> {
    pearlite! {
        if x.len() == 0 {
            proof_assert!(Seq::<(T, U)>::empty().map(fst()).ext_eq(y));
            Seq::empty()
        } else {
            let n = x.len();
            let yi = y.subsequence(0, n - 1);
            let pi = p.subsequence(0, n - 1);
            map_prefix(p, n - 1, fst());
            let q = lift_hamming(x.subsequence(0, n - 1), yi, pi, r, g);
            let e = if y[n - 1] == x[n - 1] { p[n - 1] } else { (y[n - 1], g[y[n - 1]]) };
            count_push(q, e);
            count_push(yi, y[n - 1]);
            proof_assert!(y == yi.push_back(y[n - 1]));
            map_push(q, e, fst());
            q.push_back(e)
        }
    }
}

// ---------------------------------------------------------------------------------------------
// From pairs to outputs
// ---------------------------------------------------------------------------------------------

/// The pairs of `x` and its related outputs `fx`.
#[logic]
#[requires(fx.len() == x.len() && forall<i> 0 <= i && i < x.len() ==> r[(x[i], fx[i])])]
#[ensures(result.map(fst()) == x && result.map(snd()) == fx && related(result, r))]
pub fn pairs<T, U>(x: Seq<T>, fx: Seq<U>, r: Mapping<(T, U), bool>) -> Seq<(T, U)> {
    pearlite! {
        let p = zip(x, fx);
        proof_assert!(p.map(fst()).ext_eq(x) && p.map(snd()).ext_eq(fx));
        p
    }
}

/// The outputs of related pairs over `y` are related to `y`.
#[logic]
#[requires(q.map(fst()) == y && related(q, r))]
#[ensures(result && forall<j> 0 <= j && j < y.len() ==> r[(y[j], q.map(snd())[j])])]
pub fn outputs<T, U>(q: Seq<(T, U)>, y: Seq<T>, r: Mapping<(T, U), bool>) -> bool {
    pearlite! {
        proof_assert!(forall<j> 0 <= j && j < y.len() ==> q[j] == (y[j], q.map(snd())[j]));
        true
    }
}
