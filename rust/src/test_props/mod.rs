//! Shared helpers for property-based tests.
//!
//! Component test suites (for example `transformations::sum::test_props`)
//! build their strategies and checks out of these pieces:
//! * plumbing to report `Fallible` errors as test failures
//! * neighboring-dataset construction and exact dataset distances
//! * exact `IBig`/`RBig` references for integer and float atoms
//! * value and bounds generators biased towards the edges of each type
//! * macros to instantiate a generic check across every integer or float type
//!
//! References are always computed in `IBig`/`RBig`, never in the atomic type,
//! so that overflow or rounding in the atomic type can't hide a failure.

use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

use dashu::integer::IBig;
use dashu::rational::RBig;
use proptest::prelude::*;
use proptest::sample::Index;

use crate::error::Fallible;
use crate::metrics::{
    ChangeOneDistance, EventLevelMetric, HammingDistance, InsertDeleteDistance, IntDistance,
    SymmetricDistance,
};
use crate::traits::{Float, Integer};

pub(crate) type TestResult = Result<(), TestCaseError>;

/// Converts a library error into a test failure.
pub(crate) fn ok<T>(r: Fallible<T>) -> Result<T, TestCaseError> {
    r.map_err(|e| TestCaseError::fail(format!("{e:?}")))
}

// ---------------------------------------------------------------------------------------------
// Datasets, neighbors and distances
// ---------------------------------------------------------------------------------------------

/// An edit to apply to a dataset: (alternate op, position, second position, in-domain value).
/// See [`neighbor`].
pub(crate) type Edit<T> = (bool, Index, Index, T);

/// Up to four edits, each inserting or substituting a value drawn from `value`.
pub(crate) fn edits<T: Debug>(
    value: impl Strategy<Value = T>,
) -> impl Strategy<Value = Vec<Edit<T>>> {
    prop::collection::vec((any::<bool>(), any::<Index>(), any::<Index>(), value), 0..5)
}

/// Applies `edits` to `x`, returning the neighbor and an upper bound on its distance from `x`.
///
/// Sized datasets only receive changes that preserve length:
/// a substitution, or (when `ordered` and the alternate op is set)
/// a deletion at one position and insertion at another.
/// Each costs 2 under both `SymmetricDistance` and `InsertDeleteDistance`.
/// Unsized datasets receive single insertions or (with the alternate op) deletions, costing 1 each.
pub(crate) fn neighbor<T: Clone>(
    x: &[T],
    edits: &[Edit<T>],
    sized: bool,
    ordered: bool,
) -> (Vec<T>, IntDistance) {
    let mut x2 = x.to_vec();
    let mut k = 0;
    for (alt, i, j, value) in edits {
        if sized {
            if x2.is_empty() {
                continue;
            }
            let i = i.index(x2.len());
            if ordered && *alt {
                x2.remove(i);
                x2.insert(j.index(x2.len() + 1), value.clone());
            } else {
                x2[i] = value.clone();
            }
            k += 2;
        } else if !alt || x2.is_empty() {
            x2.insert(i.index(x2.len() + 1), value.clone());
            k += 1;
        } else {
            x2.remove(i.index(x2.len()));
            k += 1;
        }
    }
    (x2, k)
}

/// A dataset drawn from `data`, paired with a random permutation of it.
pub(crate) fn with_permutation<T: Clone + Debug>(
    data: impl Strategy<Value = Vec<T>>,
) -> impl Strategy<Value = (Vec<T>, Vec<T>)> {
    data.prop_flat_map(|x| (Just(x.clone()), Just(x).prop_shuffle()))
}

/// Ordered bounds, with both endpoints drawn from `value()`.
pub(crate) fn bounds<T: PartialOrd + Debug, S: Strategy<Value = T>>(
    value: impl Fn() -> S,
) -> impl Strategy<Value = (T, T)> {
    (value(), value()).prop_map(|(a, b)| if a <= b { (a, b) } else { (b, a) })
}

/// The number of occurrences of each distinct value in `x`.
pub(crate) fn multiplicities<T: Hash + Eq>(x: &[T]) -> HashMap<&T, usize> {
    let mut counts = HashMap::new();
    x.iter().for_each(|v| *counts.entry(v).or_insert(0) += 1);
    counts
}

/// The exact symmetric distance between `x` and `x2`, viewed as multisets.
pub(crate) fn symmetric_distance<T: Hash + Eq>(x: &[T], x2: &[T]) -> usize {
    let (m, m2) = (multiplicities(x), multiplicities(x2));
    let keys = m
        .keys()
        .chain(m2.keys())
        .collect::<std::collections::HashSet<_>>();
    keys.into_iter()
        .map(|k| {
            let (a, b) = (
                m.get(k).copied().unwrap_or(0),
                m2.get(k).copied().unwrap_or(0),
            );
            a.abs_diff(b)
        })
        .sum()
}

/// Values with an exact notion of identity, used to compare records across datasets.
///
/// Floats are identified by their bits, so `-0.0` and `0.0` are distinct records.
/// Any deterministic row function respects this identity.
pub(crate) trait ExactKey {
    type Key: Hash + Eq + Debug;
    fn key(&self) -> Self::Key;
}

macro_rules! impl_exact_key_self {
    ($($ty:ty)+) => {$(
        impl ExactKey for $ty {
            type Key = Self;
            fn key(&self) -> Self {
                self.clone()
            }
        }
    )+};
}
impl_exact_key_self!(u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize bool char String);

impl ExactKey for f32 {
    type Key = u32;
    fn key(&self) -> u32 {
        self.to_bits()
    }
}

impl ExactKey for f64 {
    type Key = u64;
    fn key(&self) -> u64 {
        self.to_bits()
    }
}

impl<A: ExactKey, B: ExactKey> ExactKey for (A, B) {
    type Key = (A::Key, B::Key);
    fn key(&self) -> Self::Key {
        (self.0.key(), self.1.key())
    }
}

/// The exact identity of each record in `x`.
pub(crate) fn keys<T: ExactKey>(x: &[T]) -> Vec<T::Key> {
    x.iter().map(ExactKey::key).collect()
}

/// The exact symmetric distance between `x` and `x2`, comparing records by [`ExactKey`].
pub(crate) fn symmetric_distance_by_key<T: ExactKey>(x: &[T], x2: &[T]) -> usize {
    symmetric_distance(&keys(x), &keys(x2))
}

/// The exact insert-delete distance between `x` and `x2`:
/// `|x| + |x2| - 2 LCS(x, x2)`, comparing records by [`ExactKey`].
pub(crate) fn insert_delete_distance<T: ExactKey>(x: &[T], x2: &[T]) -> usize {
    let (a, b) = (keys(x), keys(x2));
    // prev[j] is the length of the longest common subsequence of the rows of `a` seen so far and b[..j]
    let mut prev = vec![0usize; b.len() + 1];
    for ai in &a {
        let mut cur = vec![0usize; b.len() + 1];
        for (j, bj) in b.iter().enumerate() {
            cur[j + 1] = if ai == bj {
                prev[j] + 1
            } else {
                cur[j].max(prev[j + 1])
            };
        }
        prev = cur;
    }
    a.len() + b.len() - 2 * prev[b.len()]
}

/// The number of positions at which `x` and `x2` differ, or `None` if their lengths differ.
pub(crate) fn hamming_distance<T: ExactKey>(x: &[T], x2: &[T]) -> Option<usize> {
    (x.len() == x2.len()).then(|| x.iter().zip(x2).filter(|(a, b)| a.key() != b.key()).count())
}

/// The smallest number of changes to make `x` and `x2` equal as multisets,
/// or `None` if their lengths differ.
pub(crate) fn change_one_distance<T: ExactKey>(x: &[T], x2: &[T]) -> Option<usize> {
    (x.len() == x2.len()).then(|| symmetric_distance_by_key(x, x2) / 2)
}

/// Dataset metrics with an exact distance, for testing dataset-to-dataset transformations.
/// Whether a metric requires a known size is given by [`crate::metrics::MicrodataMetric::SIZED`].
pub(crate) trait PropDatasetMetric: EventLevelMetric {
    /// The exact distance between `x` and `x2`,
    /// or `None` if the metric doesn't relate them (lengths differ under a bounded metric).
    fn exact_distance<T: ExactKey>(x: &[T], x2: &[T]) -> Option<usize>;

    /// Applies `edits` to `x` (see [`neighbor`]),
    /// returning the neighbor and an upper bound on its distance from `x` under this metric.
    fn neighbor<T: Clone>(x: &[T], edits: &[Edit<T>], sized: bool) -> (Vec<T>, IntDistance);
}

impl PropDatasetMetric for SymmetricDistance {
    fn exact_distance<T: ExactKey>(x: &[T], x2: &[T]) -> Option<usize> {
        Some(symmetric_distance_by_key(x, x2))
    }
    fn neighbor<T: Clone>(x: &[T], edits: &[Edit<T>], sized: bool) -> (Vec<T>, IntDistance) {
        neighbor(x, edits, sized, false)
    }
}

impl PropDatasetMetric for InsertDeleteDistance {
    fn exact_distance<T: ExactKey>(x: &[T], x2: &[T]) -> Option<usize> {
        Some(insert_delete_distance(x, x2))
    }
    fn neighbor<T: Clone>(x: &[T], edits: &[Edit<T>], sized: bool) -> (Vec<T>, IntDistance) {
        neighbor(x, edits, sized, true)
    }
}

impl PropDatasetMetric for ChangeOneDistance {
    fn exact_distance<T: ExactKey>(x: &[T], x2: &[T]) -> Option<usize> {
        change_one_distance(x, x2)
    }
    fn neighbor<T: Clone>(x: &[T], edits: &[Edit<T>], _sized: bool) -> (Vec<T>, IntDistance) {
        // each substitution costs 2 under the symmetric distance, so 1 change
        let (x2, k) = neighbor(x, edits, true, false);
        (x2, k / 2)
    }
}

impl PropDatasetMetric for HammingDistance {
    fn exact_distance<T: ExactKey>(x: &[T], x2: &[T]) -> Option<usize> {
        hamming_distance(x, x2)
    }
    fn neighbor<T: Clone>(x: &[T], edits: &[Edit<T>], _sized: bool) -> (Vec<T>, IntDistance) {
        // substitutions in place, each changing at most one position
        let (x2, k) = neighbor(x, edits, true, false);
        (x2, k / 2)
    }
}

/// Input distances to probe a stability or privacy map with:
/// small values, arbitrary values, and the extremes of the distance type.
pub(crate) fn distance() -> impl Strategy<Value = IntDistance> {
    prop_oneof![0u32..8, any::<u32>(), Just(u32::MAX), Just(u32::MAX - 1)]
}

/// Up to three extra input distances. See [`distance`].
pub(crate) fn distances() -> impl Strategy<Value = Vec<IntDistance>> {
    prop::collection::vec(distance(), 0..4)
}

/// The exact `(L0, L1, L∞)` distance between two maps, over the union of their keys.
/// A key missing from one map is treated as the additive identity.
pub(crate) fn map_distance_l01inf<K: Hash + Eq, V: PropInt>(
    a: &HashMap<K, V>,
    b: &HashMap<K, V>,
) -> (usize, IBig, IBig) {
    let zero = || from_big::<V>(IBig::ZERO).unwrap();
    let diffs = a
        .keys()
        .chain(b.keys())
        .collect::<std::collections::HashSet<_>>()
        .into_iter()
        .map(|k| {
            let (va, vb) = (
                a.get(k).copied().unwrap_or_else(zero),
                b.get(k).copied().unwrap_or_else(zero),
            );
            abs_big(big(va) - big(vb))
        })
        .filter(|d| *d > IBig::ZERO)
        .collect::<Vec<_>>();
    let l1 = diffs.iter().fold(IBig::ZERO, |s, d| s + d);
    let linf = diffs.iter().cloned().max().unwrap_or(IBig::ZERO);
    (diffs.len(), l1, linf)
}

// ---------------------------------------------------------------------------------------------
// Keys
// ---------------------------------------------------------------------------------------------

/// Short strings over a two-letter alphabet, including the empty string, so that keys collide.
pub(crate) fn small_string() -> impl Strategy<Value = String> {
    "[ab]{0,2}"
}

/// Characters from a three-letter alphabet, so that keys collide.
pub(crate) fn small_char() -> impl Strategy<Value = char> {
    prop::char::range('a', 'c')
}

// ---------------------------------------------------------------------------------------------
// Integers
// ---------------------------------------------------------------------------------------------

/// Integer atoms that can be generated and converted exactly to and from `IBig`.
pub(crate) trait PropInt:
    Integer + Arbitrary + num::Bounded + Into<IBig> + TryFrom<IBig>
{
    /// Uniformly distributed values in `[l, u]`.
    fn range(l: Self, u: Self) -> BoxedStrategy<Self>;
}

macro_rules! impl_prop_int {
    ($($ty:ty)+) => {$(
        impl PropInt for $ty {
            fn range(l: Self, u: Self) -> BoxedStrategy<Self> {
                // proptest 1.11 computes `end - 1` for signed ranges, which overflows for `MIN..=MIN`
                if l == u {
                    return Just(l).boxed();
                }
                (l..=u).boxed()
            }
        }
    )+};
}
impl_prop_int!(u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize);

pub(crate) fn big<T: PropInt>(v: T) -> IBig {
    v.into()
}

pub(crate) fn from_big<T: PropInt>(v: IBig) -> Option<T> {
    <T as TryFrom<IBig>>::try_from(v).ok()
}

pub(crate) fn int_min<T: PropInt>() -> IBig {
    big(<T as num::Bounded>::min_value())
}

pub(crate) fn int_max<T: PropInt>() -> IBig {
    big(<T as num::Bounded>::max_value())
}

/// Clamps `v` to the range of `T`, the reference for saturating arithmetic.
pub(crate) fn clamp_big<T: PropInt>(v: IBig) -> IBig {
    v.clamp(int_min::<T>(), int_max::<T>())
}

pub(crate) fn abs_big(v: IBig) -> IBig {
    if v < IBig::ZERO { -v } else { v }
}

/// Arbitrary values, biased towards the edges of the type and towards small magnitudes.
pub(crate) fn int_value<T: PropInt>() -> impl Strategy<Value = T> {
    let int = |v: IBig| from_big::<T>(clamp_big::<T>(v)).unwrap();
    let edges = [
        int_min::<T>(),
        int_min::<T>() + IBig::ONE,
        IBig::ZERO,
        int_max::<T>() - IBig::ONE,
        int_max::<T>(),
    ]
    .map(int)
    .to_vec();
    let small = T::range(int(IBig::from(-32)), int(IBig::from(32)));
    prop_oneof![5 => prop::sample::select(edges), 2 => small, 1 => any::<T>()]
}

/// Values in `[l, u]`, biased towards the endpoints.
pub(crate) fn int_value_in<T: PropInt>((l, u): (T, T)) -> impl Strategy<Value = T> {
    prop_oneof![Just(l), Just(u), T::range(l, u)]
}

/// Bounds whose magnitude sits within one of `T::MAX / n`,
/// so that datasets of size near `n` straddle the overflow threshold.
pub(crate) fn int_boundary_bounds<T: PropInt>(n: usize, delta: u8, shape: u8) -> (T, T) {
    let mag = clamp_big::<T>(int_max::<T>() / IBig::from(n) + IBig::from(delta) - IBig::ONE);
    let (l, u) = match shape % 4 {
        0 => (IBig::ZERO, mag.clone()),
        1 => (-mag.clone(), IBig::ZERO),
        2 => (-mag.clone(), mag.clone()),
        _ => (IBig::from(-1), mag.clone()),
    };
    match (from_big(l), from_big(u)) {
        (Some(l), Some(u)) => (l, u),
        // unsigned types can't represent negative bounds
        _ => (from_big(IBig::ZERO).unwrap(), from_big(mag).unwrap()),
    }
}

// ---------------------------------------------------------------------------------------------
// Floats
// ---------------------------------------------------------------------------------------------

/// Float atoms. Exact values are obtained with [`rat`].
pub(crate) trait PropFloat: Float {
    /// Arbitrary finite or infinite values (not NaN), spread over every exponent.
    fn any_float() -> BoxedStrategy<Self>;
}

macro_rules! impl_prop_float {
    ($($ty:ident)+) => {$(
        impl PropFloat for $ty {
            fn any_float() -> BoxedStrategy<Self> {
                use prop::num::$ty::*;
                (POSITIVE | NEGATIVE | NORMAL | SUBNORMAL | ZERO | INFINITE).boxed()
            }
        }
    )+};
}
impl_prop_float!(f32 f64);

/// The exact value of `v`, or `None` if `v` is not finite.
pub(crate) fn rat<T: PropFloat>(v: T) -> Option<RBig> {
    v.into_rational().ok()
}

pub(crate) fn abs_rat(v: RBig) -> RBig {
    if v < RBig::ZERO { -v } else { v }
}

/// Arbitrary values, biased towards the edges of the type and towards moderate magnitudes.
pub(crate) fn float_value<T: PropFloat>() -> impl Strategy<Value = T> {
    let max = <T as num::Float>::max_value();
    let min_pos = <T as num::Float>::min_positive_value();
    let one = <T as num::One>::one();
    let edges = [
        <T as num::Zero>::zero(),
        one,
        max,
        min_pos,
        min_pos * <T as num::Float>::epsilon(), // smallest subnormal
        <T as num::Float>::infinity(),
    ];
    let edges = edges.iter().flat_map(|&v| [v, -v]).collect::<Vec<_>>();
    prop_oneof![
        prop::sample::select(edges),
        T::any_float(),
        (-1000f64..1000.).prop_map(|v| <T as num::NumCast>::from(v).unwrap()),
    ]
}

/// The value a fraction `frac` of the way from `l` to `u`, rounded to the nearest float.
/// Falls back to `l` if either bound is not finite.
fn lerp<T: PropFloat>((l, u): (T, T), frac: f64) -> T {
    match (rat(l), rat(u)) {
        (Some(lr), Some(ur)) => {
            let frac = RBig::try_from(frac).unwrap();
            // nearest rounding of a value in [l, u] stays in [l, u]
            num::clamp(T::from_rational(lr.clone() + frac * (ur - lr)), l, u)
        }
        _ => l,
    }
}

/// Values in `[l, u]`, biased towards the endpoints and tiny magnitudes.
///
/// Interpolates exactly rather than using a float range,
/// because `u - l` may overflow when the bounds are huge.
pub(crate) fn float_value_in<T: PropFloat>((l, u): (T, T)) -> impl Strategy<Value = T> + Clone {
    let tiny = <T as num::Float>::min_positive_value() * <T as num::Float>::epsilon();
    prop_oneof![
        1 => Just(l),
        1 => Just(u),
        1 => Just(num::clamp(tiny, l, u)),
        1 => Just(num::clamp(-tiny, l, u)),
        2 => (0.0f64..=1.0).prop_map(move |f| lerp((l, u), f)),
    ]
}

// ---------------------------------------------------------------------------------------------
// Instantiation
// ---------------------------------------------------------------------------------------------

/// Declares a module `$mod` with one proptest per integer type `T`,
/// each drawing `case` from `$strategy::<T>()` and running `$check::<T>(case)`.
/// Both must be in scope of the calling module.
macro_rules! for_each_int {
    ($mod:ident, $strategy:ident, $check:ident) => {
        mod $mod {
            use super::*;
            $crate::test_props::for_each_int!(@tests $strategy, $check,
                prop_u8: u8, prop_u16: u16, prop_u32: u32,
                prop_u64: u64, prop_u128: u128, prop_usize: usize,
                prop_i8: i8, prop_i16: i16, prop_i32: i32,
                prop_i64: i64, prop_i128: i128, prop_isize: isize);
        }
    };
    (@tests $strategy:ident, $check:ident, $($name:ident: $ty:ty),+) => {
        proptest::proptest! {
            $(#[test]
            fn $name(case in $strategy::<$ty>()) {
                $check::<$ty>(case)?;
            })+
        }
    };
}
pub(crate) use for_each_int;

/// Like [`for_each_int`], over `f32` and `f64`.
macro_rules! for_each_float {
    ($mod:ident, $strategy:ident, $check:ident) => {
        mod $mod {
            use super::*;
            $crate::test_props::for_each_int!(@tests $strategy, $check,
                prop_f32: f32, prop_f64: f64);
        }
    };
}
pub(crate) use for_each_float;

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_symmetric_distance() {
        assert_eq!(symmetric_distance(&[1, 1, 2], &[1, 2, 2, 3]), 3);
        assert_eq!(symmetric_distance::<i32>(&[], &[]), 0);
        assert_eq!(symmetric_distance(&[1, 2], &[2, 1]), 0);
    }

    #[test]
    fn test_dataset_distances() {
        // LCS of [1, 2, 3, 4] and [2, 4, 3] has length 2, e.g. [2, 3]
        assert_eq!(insert_delete_distance(&[1, 2, 3, 4], &[2, 4, 3]), 3);
        assert_eq!(insert_delete_distance::<i32>(&[], &[1, 2]), 2);
        assert_eq!(insert_delete_distance(&[1, 2], &[2, 1]), 2);
        assert_eq!(hamming_distance(&[1, 2, 3], &[1, 3, 2]), Some(2));
        assert_eq!(hamming_distance(&[1], &[1, 2]), None);
        assert_eq!(change_one_distance(&[1, 2, 3], &[3, 2, 1]), Some(0));
        assert_eq!(change_one_distance(&[1, 2, 3], &[1, 2, 4]), Some(1));

        // floats are compared by bits
        assert_eq!(symmetric_distance_by_key(&[-0.0f64], &[0.0]), 2);
        assert_eq!(
            insert_delete_distance(&[f64::INFINITY], &[f64::INFINITY]),
            0
        );
    }

    #[test]
    fn test_map_distance_l01inf() {
        let a = HashMap::from([("a", 3i32), ("b", 1)]);
        let b = HashMap::from([("a", 1i32), ("c", 4)]);
        let (l0, l1, linf) = map_distance_l01inf(&a, &b);
        assert_eq!((l0, l1, linf), (3, IBig::from(7), IBig::from(4)));
    }
}
