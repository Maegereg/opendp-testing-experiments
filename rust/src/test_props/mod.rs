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
use std::hash::Hash;

use dashu::integer::IBig;
use dashu::rational::RBig;
use proptest::prelude::*;

use crate::error::Fallible;
use crate::metrics::IntDistance;
use crate::traits::{Float, Integer};

pub(crate) type TestResult = Result<(), TestCaseError>;

/// Converts a library error into a test failure.
pub(crate) fn ok<T>(r: Fallible<T>) -> Result<T, TestCaseError> {
    r.map_err(|e| TestCaseError::fail(format!("{e:?}")))
}

// ---------------------------------------------------------------------------------------------
// Datasets, neighbors and distances
// ---------------------------------------------------------------------------------------------

/// An edit to apply to a dataset: (op, position, in-domain value). See [`neighbor`].
pub(crate) type Edit<T> = (u8, u16, T);

/// Up to four edits, each inserting or substituting a value drawn from `value`.
pub(crate) fn edits<T: std::fmt::Debug>(
    value: impl Strategy<Value = T>,
) -> impl Strategy<Value = Vec<Edit<T>>> {
    prop::collection::vec((any::<u8>(), any::<u16>(), value), 0..5)
}

/// Applies `edits` to `x`, returning the neighbor and an upper bound on its distance from `x`.
///
/// Sized datasets only receive changes that preserve length:
/// a substitution, or (when `ordered`) a deletion at one position and insertion at another.
/// Each costs 2 under both `SymmetricDistance` and `InsertDeleteDistance`.
/// Unsized datasets receive single insertions or deletions, costing 1 each.
pub(crate) fn neighbor<T: Clone>(
    x: &[T],
    edits: &[Edit<T>],
    sized: bool,
    ordered: bool,
) -> (Vec<T>, IntDistance) {
    let mut x2 = x.to_vec();
    let mut k = 0;
    for (op, pos, value) in edits {
        let pos = *pos as usize;
        if sized {
            if x2.is_empty() {
                continue;
            }
            let i = pos % x2.len();
            if ordered && op % 2 == 1 {
                x2.remove(i);
                let j = (pos / 7) % (x2.len() + 1);
                x2.insert(j, value.clone());
            } else {
                x2[i] = value.clone();
            }
            k += 2;
        } else if op % 2 == 0 || x2.is_empty() {
            x2.insert(pos % (x2.len() + 1), value.clone());
            k += 1;
        } else {
            x2.remove(pos % x2.len());
            k += 1;
        }
    }
    (x2, k)
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
}
impl<T> PropInt for T where T: Integer + Arbitrary + num::Bounded + Into<IBig> + TryFrom<IBig> {}

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

/// An arbitrary value, biased towards the edges of the type.
pub(crate) fn pick_int<T: PropInt>(sel: u8, raw: T) -> T {
    let v = match sel % 8 {
        0 => return raw,
        1 => int_min::<T>(),
        2 => int_max::<T>(),
        3 => int_min::<T>() + IBig::ONE,
        4 => int_max::<T>() - IBig::ONE,
        5 => IBig::ZERO,
        _ => big(raw) % IBig::from(33),
    };
    from_big(clamp_big::<T>(v)).unwrap()
}

/// A value in `[l, u]`, biased towards the endpoints.
pub(crate) fn int_in_range<T: PropInt>(sel: u8, raw: T, (l, u): (T, T)) -> T {
    match sel % 4 {
        0 => l,
        1 => u,
        _ => {
            let span = big(u) - big(l) + IBig::ONE;
            let offset = (big(raw) - int_min::<T>()) % span;
            from_big(big(l) + offset).unwrap()
        }
    }
}

/// Values in `[l, u]`. See [`int_in_range`].
pub(crate) fn int_value_in<T: PropInt>(bounds: (T, T)) -> impl Strategy<Value = T> {
    (any::<u8>(), any::<T>()).prop_map(move |(s, r)| int_in_range(s, r, bounds))
}

/// Ordered bounds whose endpoints are biased towards the edges of the type.
pub(crate) fn int_bounds<T: PropInt>() -> impl Strategy<Value = (T, T)> {
    any::<(u8, T, u8, T)>().prop_map(|(sa, a, sb, b)| {
        let (a, b) = (pick_int(sa, a), pick_int(sb, b));
        if a <= b { (a, b) } else { (b, a) }
    })
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
pub(crate) trait PropFloat: Float {}
impl<T: Float> PropFloat for T {}

/// The exact value of `v`, or `None` if `v` is not finite.
pub(crate) fn rat<T: PropFloat>(v: T) -> Option<RBig> {
    v.into_rational().ok()
}

pub(crate) fn abs_rat(v: RBig) -> RBig {
    if v < RBig::ZERO { -v } else { v }
}

/// An arbitrary value, biased towards the edges of the type
/// and towards `MAX / 2^j`, where overflow thresholds of size-`2^j` aggregates sit.
pub(crate) fn pick_float<T: PropFloat>(sel: u8, j: i32, frac: f64, neg: bool) -> T {
    let cast = |v: f64| <T as num::NumCast>::from(v).unwrap();
    let one = <T as num::One>::one();
    let two = one + one;
    let max = <T as num::Float>::max_value();
    let min_pos = <T as num::Float>::min_positive_value();
    let v = match sel % 10 {
        0 => <T as num::Zero>::zero(),
        1 => max,
        2 => min_pos,
        3 => min_pos * <T as num::Float>::epsilon(), // smallest subnormal
        4 => <T as num::Float>::infinity(),
        5 => one,
        6 | 7 => max / num::Float::powi(two, j) * cast(frac),
        8 => cast(frac * 1000.0),
        _ => cast(frac),
    };
    if neg { -v } else { v }
}

/// Values for [`pick_float`].
pub(crate) fn float_value<T: PropFloat>() -> impl Strategy<Value = T> {
    // small powers j put MAX / 2^j near the overflow threshold of datasets of size ~2^j
    (
        any::<u8>(),
        prop_oneof![1i32..8, 0i32..64],
        0.5f64..1.0,
        any::<bool>(),
    )
        .prop_map(|(s, j, f, n)| pick_float::<T>(s, j, f, n))
}

/// Ordered bounds whose endpoints are biased towards the edges of the type. May be infinite.
pub(crate) fn float_bounds<T: PropFloat>() -> impl Strategy<Value = (T, T)> {
    (float_value::<T>(), float_value::<T>()).prop_map(|(a, b)| if a <= b { (a, b) } else { (b, a) })
}

/// A value in `[l, u]`, biased towards the endpoints and tiny magnitudes.
pub(crate) fn float_in_range<T: PropFloat>(sel: u8, frac: f64, (l, u): (T, T)) -> T {
    let clamp = |v: T| {
        if v < l {
            l
        } else if v > u {
            u
        } else {
            v
        }
    };
    let tiny = <T as num::Float>::min_positive_value() * <T as num::Float>::epsilon();
    match sel % 6 {
        0 => l,
        1 => u,
        2 => clamp(tiny),
        3 => clamp(-tiny),
        _ => match (rat(l), rat(u)) {
            (Some(lr), Some(ur)) => {
                let frac = RBig::try_from(frac).unwrap();
                clamp(T::from_rational(lr.clone() + frac * (ur - lr)))
            }
            _ => l,
        },
    }
}

/// Values in `[l, u]`. See [`float_in_range`].
pub(crate) fn float_value_in<T: PropFloat>(bounds: (T, T)) -> impl Strategy<Value = T> + Clone {
    (any::<u8>(), 0.0f64..=1.0).prop_map(move |(s, f)| float_in_range(s, f, bounds))
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
    fn test_map_distance_l01inf() {
        let a = HashMap::from([("a", 3i32), ("b", 1)]);
        let b = HashMap::from([("a", 1i32), ("c", 4)]);
        let (l0, l1, linf) = map_distance_l01inf(&a, &b);
        assert_eq!((l0, l1, linf), (3, IBig::from(7), IBig::from(4)));
    }
}
