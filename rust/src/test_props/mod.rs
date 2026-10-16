//! Shared helpers for property-based tests.
//!
//! Component test suites (for example `transformations::sum::test_props`)
//! build their strategies and checks out of these pieces:
//! * plumbing to report `Fallible` errors as test failures
//! * neighboring-dataset construction and exact dataset distances
//! * exact `IBig`/`RBig` references for integer and float atoms
//! * value and bounds generators biased towards the edges of each type
//! * macros to instantiate a generic check across every integer or float type
//! * ([`noise`]) references and generators for noise-adding measurements
//!
//! References are always computed in `IBig`/`RBig`, never in the atomic type,
//! so that overflow or rounding in the atomic type can't hide a failure.
//!
//! Statistical tests (labelled D in the suites) run on fixed parameter grids, not on proptest
//! cases, and use the library's `check_chi_square` at significance 1e-6, as its sampler tests do.
//! The noise can't be seeded, so each such check fails spuriously with probability 1e-6.
//!
//! Proptest saves failing seeds under `proptest-regressions/` and replays them for every test
//! in that file. Commit a regression file when it records a real failure; delete files left
//! behind by experiments such as mutation runs, which would fail on unrelated tests.

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
use crate::traits::{CastInternalRational, Float, Integer};

pub(crate) mod noise;

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

/// The number of occurrences of each record in `x`, comparing records by [`ExactKey`].
pub(crate) fn multiset_of<T: ExactKey>(x: &[T]) -> HashMap<T::Key, usize> {
    let mut counts = HashMap::new();
    x.iter()
        .for_each(|v| *counts.entry(v.key()).or_insert(0) += 1);
    counts
}

/// Whether every record of `a` occurs at least as often in `b`.
pub(crate) fn is_sub_multiset<T: ExactKey>(a: &[T], b: &[T]) -> bool {
    let b = multiset_of(b);
    multiset_of(a)
        .iter()
        .all(|(k, n)| b.get(k).is_some_and(|m| n <= m))
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

/// Dataset lengths near `target` (within 2 either side), plus empty and small arbitrary lengths,
/// so that transformations with a size parameter see each side of it.
pub(crate) fn lengths(target: usize) -> impl Strategy<Value = usize> {
    prop_oneof![
        3 => target.saturating_sub(2)..=target.saturating_add(2),
        1 => Just(0usize),
        1 => 0usize..40,
    ]
}

/// Uniform probabilities over `n` categories, for chi-square tests of uniformity.
pub(crate) fn uniform_probs(n: usize) -> Vec<f64> {
    vec![1.0 / n as f64; n]
}

/// A dataset of length `len` with values from `value`.
/// Long datasets repeat a short random pattern, to keep generation cheap.
pub(crate) fn dataset<T: Clone + Debug + 'static>(
    value: BoxedStrategy<T>,
    len: usize,
) -> BoxedStrategy<Vec<T>> {
    if len <= 64 {
        return prop::collection::vec(value, len).boxed();
    }
    prop::collection::vec(value, 1..16)
        .prop_map(move |pattern| pattern.iter().cycle().take(len).cloned().collect())
        .boxed()
}

/// Checks that a row-by-row transformation kept one output row per input row,
/// and that `row(&x[i], &out[i])` holds for every row.
pub(crate) fn check_row_wise<T, U>(
    x: &[T],
    out: &[U],
    row: impl Fn(&T, &U) -> Result<(), String>,
) -> TestResult {
    prop_assert_eq!(x.len(), out.len(), "the number of rows changed");
    for (i, (v, o)) in x.iter().zip(out).enumerate() {
        row(v, o).map_err(|e| TestCaseError::fail(format!("row {i}: {e}")))?;
    }
    Ok(())
}

/// Set in the child processes started by [`run_ignored_test`].
const PROBE_CHILD_ENV: &str = "OPENDP_PROBE_CHILD";

/// Whether this process is a child started by [`run_ignored_test`].
///
/// Probes that abort or hang the process return early unless this holds,
/// so that running ignored tests directly (`cargo test -- --ignored`) is still safe.
pub(crate) fn in_probe_child() -> bool {
    std::env::var_os(PROBE_CHILD_ENV).is_some()
}

/// Runs the ignored test `name` (its full path) in a child process of this test binary.
/// Returns its exit status and stderr, or `None` if it was still running after `timeout`,
/// in which case it is killed.
///
/// For probes that abort or hang the process, which can't be observed in-process.
/// The probe should return early unless [`in_probe_child`] holds.
pub(crate) fn run_ignored_test(
    name: &str,
    timeout: std::time::Duration,
) -> Option<(std::process::ExitStatus, String)> {
    let mut child = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--ignored", "--exact", name])
        .env(PROBE_CHILD_ENV, "1")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    let start = std::time::Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if start.elapsed() > timeout {
            child.kill().unwrap();
            child.wait().unwrap();
            return None;
        }
        std::thread::sleep(std::time::Duration::from_millis(100));
    };
    let mut stderr = String::new();
    std::io::Read::read_to_string(&mut child.stderr.take().unwrap(), &mut stderr).unwrap();
    Some((status, stderr))
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

/// Like [`map_distance_l01inf`], for any values with an exact rational value (including floats),
/// or `None` if a value isn't finite.
pub(crate) fn map_distance_exact<K: Hash + Eq, V: ExactRat>(
    a: &HashMap<K, V>,
    b: &HashMap<K, V>,
) -> Option<(usize, RBig, RBig)> {
    let value = |m: &HashMap<K, V>, k: &K| m.get(k).map_or(Some(RBig::ZERO), ExactRat::exact);
    let mut diffs = vec![];
    for k in a.keys().chain(b.keys().filter(|k| !a.contains_key(k))) {
        let d = abs_rat(value(a, k)? - value(b, k)?);
        if d > RBig::ZERO {
            diffs.push(d);
        }
    }
    let l1 = diffs.iter().fold(RBig::ZERO, |s, d| s + d);
    let linf = diffs.iter().cloned().max().unwrap_or(RBig::ZERO);
    Some((diffs.len(), l1, linf))
}

/// A map with up to `max_keys` keys, and a neighbor formed by up to four edits:
/// removing a key, adding a key, or changing a value, with values drawn from `value`.
pub(crate) fn map_neighbors<V: Clone + Debug + 'static>(
    value: BoxedStrategy<V>,
    max_keys: usize,
) -> impl Strategy<Value = (HashMap<u32, V>, HashMap<u32, V>)> {
    let key_range = 2 * max_keys.max(1) as u32;
    (
        prop::collection::hash_map(0..key_range, value.clone(), 0..=max_keys),
        prop::collection::vec((0u8..3, 0..key_range, value), 0..5),
    )
        .prop_map(|(x, edits)| {
            let mut x2 = x.clone();
            for (op, key, v) in edits {
                match op {
                    0 => {
                        x2.remove(&key);
                    }
                    _ => {
                        x2.insert(key, v);
                    }
                }
            }
            (x, x2)
        })
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
                // proptest (1.11, the locked version) computes `end - 1` for signed ranges,
                // which overflows for `MIN..=MIN`
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
    /// The exponent `k` where `2^k` is the smallest positive subnormal.
    const K_MIN: i32;
    /// Arbitrary finite or infinite values (not NaN), spread over every exponent.
    fn any_float() -> BoxedStrategy<Self>;
    /// The next representable value towards positive infinity.
    fn next_up(self) -> Self;
    /// The next representable value towards negative infinity.
    fn next_down(self) -> Self;
}

macro_rules! impl_prop_float {
    ($($ty:ident)+) => {$(
        impl PropFloat for $ty {
            const K_MIN: i32 = $ty::MIN_EXP - $ty::MANTISSA_DIGITS as i32;
            fn any_float() -> BoxedStrategy<Self> {
                use prop::num::$ty::*;
                (POSITIVE | NEGATIVE | NORMAL | SUBNORMAL | ZERO | INFINITE).boxed()
            }
            fn next_up(self) -> Self {
                $ty::next_up(self)
            }
            fn next_down(self) -> Self {
                $ty::next_down(self)
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

/// Percentages of NaN for [`nan_heavy_float`]: none, some, half, mostly, or all.
pub(crate) fn nan_percent() -> impl Strategy<Value = u32> {
    prop::sample::select(vec![0, 10, 50, 90, 100])
}

/// Values from [`float_value`] (including ±0, ±inf and subnormals), NaN `nan_percent`% of the time.
pub(crate) fn nan_heavy_float<T: PropFloat>(nan_percent: u32) -> BoxedStrategy<T> {
    let nan = <T as num::Float>::nan();
    match nan_percent {
        0 => float_value::<T>().boxed(),
        100.. => Just(nan).boxed(),
        p => prop_oneof![p => Just(nan), 100 - p => float_value::<T>()].boxed(),
    }
}

/// The number of `samples` in each of `k` equal-width bins over `[lower, upper)`.
/// Bin edges are exact, so the bins are correct even when `upper - lower` overflows.
///
/// # Panics
/// If a sample is not in `[lower, upper)`.
pub(crate) fn bin_counts<T: PropFloat>(
    samples: &[T],
    (lower, upper): (T, T),
    k: usize,
) -> Vec<u64> {
    let (l, u) = (rat(lower).unwrap(), rat(upper).unwrap());
    let scale = RBig::from(k) / (u - l.clone());
    let mut counts = vec![0u64; k];
    for &s in samples {
        let bin = rat(s)
            .map(|s| ((s - l.clone()) * scale.clone()).floor())
            .and_then(|i| usize::try_from(i).ok())
            .filter(|&i| i < k)
            .unwrap_or_else(|| panic!("{s:?} is outside [{lower:?}, {upper:?})"));
        counts[bin] += 1;
    }
    counts
}

// ---------------------------------------------------------------------------------------------
// Exact values, rounding and distances
// ---------------------------------------------------------------------------------------------

/// Values with an exact rational value.
pub(crate) trait ExactRat {
    /// The exact value of `self`, or `None` if `self` is not finite.
    fn exact(&self) -> Option<RBig>;
}

macro_rules! impl_exact_rat_int {
    ($($ty:ty)+) => {$(
        impl ExactRat for $ty {
            fn exact(&self) -> Option<RBig> {
                Some(RBig::from(IBig::from(*self)))
            }
        }
    )+};
}
impl_exact_rat_int!(u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize);

impl ExactRat for f32 {
    fn exact(&self) -> Option<RBig> {
        rat(*self)
    }
}

impl ExactRat for f64 {
    fn exact(&self) -> Option<RBig> {
        rat(*self)
    }
}

impl ExactRat for IBig {
    fn exact(&self) -> Option<RBig> {
        Some(RBig::from(self.clone()))
    }
}

impl ExactRat for RBig {
    fn exact(&self) -> Option<RBig> {
        Some(self.clone())
    }
}

/// The exact L1 distance between `x` and `x2`,
/// or `None` if their lengths differ or any value is not finite.
pub(crate) fn l1_exact<T: ExactRat>(x: &[T], x2: &[T]) -> Option<RBig> {
    if x.len() != x2.len() {
        return None;
    }
    x.iter().zip(x2).try_fold(RBig::ZERO, |s, (a, b)| {
        Some(s + abs_rat(a.exact()? - b.exact()?))
    })
}

/// `2^k`, exactly.
pub(crate) fn pow2(k: i32) -> RBig {
    let p = RBig::from(IBig::ONE << k.unsigned_abs() as usize);
    if k < 0 { RBig::ONE / p } else { p }
}

/// `x * 2^k`, exactly.
pub(crate) fn mul_2k(x: &RBig, k: i32) -> RBig {
    x * pow2(k)
}

/// The index `i` of the multiple `i * 2^k` nearest to `x`, with ties rounding towards positive infinity.
pub(crate) fn round_to_2k(x: &RBig, k: i32) -> IBig {
    (mul_2k(x, -k) + RBig::from_parts(IBig::ONE, 2u8.into())).floor()
}

/// Whether `out` is `exact` rounded up: the smallest `f64` (or infinity) at or above `exact`.
pub(crate) fn is_rounded_up(out: f64, exact: &RBig) -> bool {
    match rat(out) {
        Some(o) => o >= *exact && rat(out.next_down()).is_none_or(|below| below < *exact),
        None => out == f64::INFINITY && rat(f64::MAX).unwrap() < *exact,
    }
}

/// Whether `out` is at least `exact`, where `None` stands for positive infinity.
pub(crate) fn at_least(out: f64, exact: &Option<RBig>) -> bool {
    match (rat(out), exact) {
        (_, _) if out == f64::INFINITY => true,
        (Some(o), Some(e)) => o >= *e,
        _ => false,
    }
}

/// Distance types of metrics on numbers, such as the `Q` in `AbsoluteDistance<Q>`.
pub(crate) trait PropDistance: ExactRat + Clone + Debug + 'static {
    /// The smallest value at or above `r`, or `None` if no finite value is.
    fn round_up(r: &RBig) -> Option<Self>;
    /// Arbitrary values, including negative and non-finite ones where the type has them.
    fn value() -> BoxedStrategy<Self>;
}

macro_rules! impl_prop_distance_int {
    ($($ty:ty)+) => {$(
        impl PropDistance for $ty {
            fn round_up(r: &RBig) -> Option<Self> {
                from_big(r.ceil())
            }
            fn value() -> BoxedStrategy<Self> {
                int_value::<$ty>().boxed()
            }
        }
    )+};
}
impl_prop_distance_int!(u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize);

macro_rules! impl_prop_distance_float {
    ($($ty:ty)+) => {$(
        impl PropDistance for $ty {
            fn round_up(r: &RBig) -> Option<Self> {
                let v = <$ty>::from_rational(r.clone());
                let v = if rat(v).is_some_and(|e| e < *r) { v.next_up() } else { v };
                v.is_finite().then_some(v)
            }
            fn value() -> BoxedStrategy<Self> {
                prop_oneof![9 => float_value::<$ty>(), 1 => Just(<$ty>::NAN)].boxed()
            }
        }
    )+};
}
impl_prop_distance_float!(f32 f64);

impl PropDistance for RBig {
    fn round_up(r: &RBig) -> Option<Self> {
        Some(r.clone())
    }
    fn value() -> BoxedStrategy<Self> {
        (any::<i64>(), 1u16..1000)
            .prop_map(|(n, d)| RBig::from_parts(n.into(), d.into()))
            .boxed()
    }
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
    fn test_multisets() {
        let m = multiset_of(&[1.0f64, -0.0, 0.0, 1.0]);
        assert_eq!(m.len(), 3);
        assert_eq!(m[&1.0f64.to_bits()], 2);
        assert!(is_sub_multiset(&[1, 1], &[1, 2, 1]));
        assert!(!is_sub_multiset(&[1, 1], &[1, 2]));
        assert!(is_sub_multiset::<i32>(&[], &[]));
        assert!(!is_sub_multiset(&[f64::NAN], &[f64::NAN.copysign(-1.0)]));
    }

    #[test]
    fn test_row_wise() {
        let same = |a: &i32, b: &i32| (a == b).then_some(()).ok_or(format!("{a} != {b}"));
        assert!(check_row_wise(&[1, 2], &[1, 2], same).is_ok());
        assert!(check_row_wise(&[1, 2], &[1, 3], same).is_err());
        assert!(check_row_wise(&[1, 2], &[1], same).is_err());
    }

    #[test]
    fn test_bin_counts() {
        assert_eq!(
            bin_counts(&[0.0, 0.25, 0.5, 0.999], (0.0f64, 1.0), 4),
            [1, 1, 1, 1]
        );
        // the width overflows, but the bins are still exact
        let max = f64::MAX;
        assert_eq!(
            bin_counts(&[-max, -1.0, 0.0, max / 2.0], (-max, max), 2),
            [2, 2]
        );
        assert_eq!(bin_counts(&[-0.0f32], (-1.0, 1.0), 2), [0, 1]);
    }

    #[test]
    #[should_panic(expected = "outside")]
    fn test_bin_counts_rejects_upper() {
        bin_counts(&[1.0], (0.0f64, 1.0), 4);
    }

    #[test]
    fn test_map_distance_l01inf() {
        let a = HashMap::from([("a", 3i32), ("b", 1)]);
        let b = HashMap::from([("a", 1i32), ("c", 4)]);
        let (l0, l1, linf) = map_distance_l01inf(&a, &b);
        assert_eq!((l0, l1, linf), (3, IBig::from(7), IBig::from(4)));
    }

    #[test]
    fn test_exact_rounding() {
        let r = |n: i64, d: u64| RBig::from_parts(n.into(), d.into());
        // ties round up, including for negative values
        assert_eq!(round_to_2k(&r(1, 2), 0), IBig::ONE);
        assert_eq!(round_to_2k(&r(-1, 2), 0), IBig::ZERO);
        assert_eq!(round_to_2k(&r(-3, 2), 0), IBig::from(-1));
        assert_eq!(round_to_2k(&r(5, 1), 2), IBig::ONE);
        assert_eq!(round_to_2k(&r(6, 1), 2), IBig::from(2));
        assert_eq!(round_to_2k(&r(3, 8), -2), IBig::from(2));
        assert_eq!(mul_2k(&r(3, 1), -2), r(3, 4));

        assert!(is_rounded_up(0.0, &RBig::ZERO));
        assert!(is_rounded_up(0.5, &r(1, 2)));
        assert!(!is_rounded_up(1.0, &r(1, 2)));
        // half of the smallest subnormal rounds up to it
        let half_sub = rat(f64::from_bits(1)).unwrap() / RBig::from(2);
        assert!(is_rounded_up(f64::from_bits(1), &half_sub));
        assert!(!is_rounded_up(0.0, &half_sub));
        assert!(is_rounded_up(
            f64::INFINITY,
            &(rat(f64::MAX).unwrap() + RBig::ONE)
        ));
        assert!(!is_rounded_up(f64::INFINITY, &rat(f64::MAX).unwrap()));

        let third = <f64 as PropDistance>::round_up(&r(1, 3)).unwrap();
        assert!(is_rounded_up(third, &r(1, 3)));
        assert_eq!(<f64 as PropDistance>::round_up(&r(1, 2)), Some(0.5));
        assert_eq!(
            <f32 as PropDistance>::round_up(&rat(f64::MAX).unwrap()),
            None
        );
        assert_eq!(<u8 as PropDistance>::round_up(&r(509, 2)), Some(255));
        assert_eq!(<u8 as PropDistance>::round_up(&r(511, 2)), None);
        assert_eq!(<f64 as PropFloat>::K_MIN, -1074);
        assert_eq!(<f32 as PropFloat>::K_MIN, -149);
    }

    #[test]
    fn test_l1_exact() {
        assert_eq!(l1_exact(&[1i8, -128], &[-1, 127]), Some(RBig::from(257)));
        assert_eq!(l1_exact(&[0.5f64], &[f64::INFINITY]), None);
        assert_eq!(l1_exact(&[0.5f64], &[]), None);
    }
}
