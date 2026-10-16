//! Property-based tests for `make_resize`.
//!
//! Records are compared by exact identity (floats by bits), and dataset distances are exact.
//!
//! The function shuffles in two branches: before truncating under an unordered input metric,
//! and after imputing under an ordered output metric. The shuffles draw from system entropy,
//! so in those branches stability rests on the proof's coupling of the two shuffles,
//! which a black-box test can't reproduce. Those branches are checked by their support
//! (every possible output has exactly the right records) and by statistical tests of uniformity.
//! Every other branch is deterministic, and its stability is checked exactly.
//!
//! Properties (labels match the comments below):
//! * A: constructor succeeds exactly when its inputs are valid, and builds the expected output space
//! * B: the function always returns `size` records: the input plus copies of the constant,
//!   or a sub-multiset of the input, in input order in the deterministic branches
//! * C: the map is `d -> 2d`, and is sound and tight in the deterministic branches
//! * D: the shuffles are uniform, and don't depend on the order of unordered input (statistical)
//! * E: large datasets and sizes, including sizes too large to allocate
//!
//! Known issue: imputing to a size that can't be allocated panics or aborts the process,
//! instead of returning an error. Its tests of the correct behavior are marked
//! `#[should_panic(expected = "known issue: unallocatable size")]`.
//! When it's fixed, they fail: remove their `should_panic`.

use std::fmt::Debug;

use proptest::prelude::*;

use super::*;
use crate::metrics::{InsertDeleteDistance, IntDistance, MicrodataMetric, SymmetricDistance};
use crate::test_props::*;
use crate::traits::samplers::test::check_chi_square_from_probs;

/// Atoms that can be resized and compared exactly.
trait ResizeAtom: 'static + Clone + CheckAtom + ExactKey + Debug + PartialOrd {
    /// Whether the value is NaN.
    fn nan(&self) -> bool {
        false
    }
}
macro_rules! impl_resize_atom {
    ($($ty:ty)+) => {$(impl ResizeAtom for $ty {})+};
}
impl_resize_atom!(u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize bool String);
impl ResizeAtom for f32 {
    fn nan(&self) -> bool {
        self.is_nan()
    }
}
impl ResizeAtom for f64 {
    fn nan(&self) -> bool {
        self.is_nan()
    }
}

/// An input domain, a target size, a constant to impute with, and datasets to compare.
#[derive(Debug, Clone)]
struct Case<T: CheckAtom> {
    /// element bounds, if any
    bounds: Option<(T, T)>,
    /// whether the element domain may contain NaN
    nan: bool,
    /// whether the input domain records the length of `data`
    sized: bool,
    size: usize,
    /// possibly outside the element domain
    constant: T,
    data: Vec<T>,
    /// a random permutation of `data`
    permuted: Vec<T>,
    edits: Vec<Edit<T>>,
    /// an arbitrary dataset in the same domain, with the same length if sized
    other: Vec<T>,
    /// extra input distances to probe the stability map with
    distances: Vec<IntDistance>,
}

impl<T: ResizeAtom> Case<T> {
    fn element_domain(&self) -> AtomDomain<T> {
        match &self.bounds {
            Some(b) => AtomDomain::new_closed(b.clone()).unwrap(),
            None if self.nan => AtomDomain::default(),
            None => AtomDomain::new(None, None),
        }
    }

    fn input_domain(&self) -> VectorDomain<AtomDomain<T>> {
        let domain = VectorDomain::new(self.element_domain());
        if self.sized {
            domain.with_size(self.data.len())
        } else {
            domain
        }
    }

    /// The reference for membership of the constant in the element domain.
    fn constant_ok(&self) -> bool {
        let c = &self.constant;
        if c.nan() {
            return self.nan && self.bounds.is_none();
        }
        self.bounds.as_ref().is_none_or(|(l, u)| l <= c && c <= u)
    }
}

/// Target sizes: mostly small, sometimes zero (invalid), occasionally large.
fn size() -> impl Strategy<Value = usize> {
    prop_oneof![
        36 => 1usize..20,
        3 => Just(0usize),
        1 => 10_000usize..200_000,
    ]
}

/// Datasets with values from `value`, a constant from `constant`, and lengths near the target size.
fn case<T: ResizeAtom>(
    bounds: Option<(T, T)>,
    nan: bool,
    value: BoxedStrategy<T>,
    constant: BoxedStrategy<T>,
) -> impl Strategy<Value = Case<T>> {
    (size(), any::<bool>()).prop_flat_map(move |(size, sized)| {
        let len = prop_oneof![
            39 => lengths(size),
            // a large dataset, far above or around the target size
            1 => prop_oneof![10_000usize..200_000, Just(size.saturating_add(10_000))],
        ];
        let (bounds, value, constant) = (bounds.clone(), value.clone(), constant.clone());
        len.prop_flat_map(move |len| {
            (
                with_permutation(dataset(value.clone(), len)),
                edits(value.clone()),
                dataset(value.clone(), len.min(40)),
                constant.clone(),
                distances(),
            )
                .prop_map({
                    let bounds = bounds.clone();
                    move |((data, permuted), edits, mut other, constant, distances)| {
                        if sized {
                            // the second dataset must also have the known length
                            other.truncate(data.len());
                            other.extend_from_slice(&data[other.len()..]);
                        }
                        Case {
                            bounds: bounds.clone(),
                            nan,
                            sized,
                            size,
                            constant,
                            data,
                            permuted,
                            edits,
                            other,
                            distances,
                        }
                    }
                })
        })
    })
}

fn int_case<T: PropInt + ResizeAtom>() -> impl Strategy<Value = Case<T>> {
    let bounded = bounds(int_value::<T>).prop_flat_map(|b| {
        // the constant is usually in bounds, so it may collide with the data
        let constant = prop_oneof![9 => int_value_in(b), 1 => int_value::<T>()];
        case(Some(b), false, int_value_in(b).boxed(), constant.boxed())
    });
    prop_oneof![
        case(
            None,
            false,
            int_value::<T>().boxed(),
            int_value::<T>().boxed()
        ),
        bounded,
    ]
}

fn float_case<T: PropFloat + ResizeAtom>() -> impl Strategy<Value = Case<T>> {
    let nan = <T as num::Float>::nan();
    let maybe_nan = move || prop_oneof![9 => float_value::<T>(), 1 => Just(nan)].boxed();
    let bounded = bounds(float_value::<T>).prop_flat_map(move |b| {
        let constant = prop_oneof![8 => float_value_in(b), 1 => float_value::<T>(), 1 => Just(nan)];
        case(Some(b), false, float_value_in(b).boxed(), constant.boxed())
    });
    prop_oneof![
        // NaN is in the domain, so NaN data and constants are valid
        case(None, true, maybe_nan(), maybe_nan()),
        // NaN is not in the domain, so a NaN constant is invalid
        case(None, false, float_value::<T>().boxed(), maybe_nan()),
        bounded,
    ]
}

fn check_all<T: ResizeAtom>(case: Case<T>) -> TestResult {
    check::<T, SymmetricDistance, SymmetricDistance>(&case)?;
    check::<T, SymmetricDistance, InsertDeleteDistance>(&case)?;
    check::<T, InsertDeleteDistance, SymmetricDistance>(&case)?;
    check::<T, InsertDeleteDistance, InsertDeleteDistance>(&case)
}

/// Whether resizing a dataset of length `len` takes a branch that doesn't shuffle.
fn deterministic<MI: MicrodataMetric, MO: MicrodataMetric>(len: usize, size: usize) -> bool {
    if len <= size {
        !MO::ORDERED
    } else {
        MI::ORDERED
    }
}

fn check<T, MI, MO>(case: &Case<T>) -> TestResult
where
    T: ResizeAtom,
    MI: IsMetricOrdered<Distance = IntDistance> + PropDatasetMetric,
    MO: IsMetricOrdered<Distance = IntDistance> + PropDatasetMetric,
    (VectorDomain<AtomDomain<T>>, MI): MetricSpace,
    (VectorDomain<AtomDomain<T>>, MO): MetricSpace,
{
    let input_domain = case.input_domain();
    let size = case.size;

    // A: construction succeeds exactly when the size is positive and the constant is in the domain
    let t = make_resize::<T, MI, MO>(
        input_domain.clone(),
        MI::default(),
        size,
        case.constant.clone(),
    );
    let valid = size > 0 && case.constant_ok();
    prop_assert_eq!(t.is_ok(), valid, "construction: {:?}", t.as_ref().err());
    let Ok(t) = t else {
        return Ok(());
    };

    // A: the output domain is the input domain with the new size, replacing any input size
    prop_assert!(t.input_domain == input_domain);
    prop_assert!(t.input_metric == MI::default());
    prop_assert!(t.output_domain == input_domain.clone().with_size(size));
    prop_assert!(t.output_metric == MO::default());

    // C: the map is d -> 2d, or an error when that doesn't fit
    let probes = [0, 1, u32::MAX / 2, u32::MAX / 2 + 1, u32::MAX];
    for d in probes.iter().chain(&case.distances) {
        match d.checked_mul(2) {
            Some(expected) => prop_assert_eq!(ok(t.map(d))?, expected, "map({})", d),
            None => prop_assert!(t.map(d).is_err(), "map({}) should overflow", d),
        }
    }

    let resize = |x: &Vec<T>| -> Result<Vec<T>, TestCaseError> {
        let out = ok(t.invoke(x))?;
        let len = x.len();

        // B: always exactly `size` records, in the output domain
        prop_assert_eq!(out.len(), size);
        prop_assert!(ok(t.output_domain.member(&out))?);

        if len <= size {
            // B: the input plus `size - len` copies of the constant, nothing else
            let mut expected = multiset_of(x);
            if len < size {
                *expected.entry(case.constant.key()).or_insert(0) += size - len;
            }
            prop_assert!(
                multiset_of(&out) == expected,
                "imputation lost or added records"
            );
        } else {
            // B: a sub-multiset of the input
            prop_assert!(is_sub_multiset(&out, x), "truncation invented records");
        }

        // B: the deterministic branches keep the input order
        if len <= size && !<MO as MicrodataMetric>::ORDERED {
            let mut expected = keys(x);
            expected.extend((len..size).map(|_| case.constant.key()));
            prop_assert!(keys(&out) == expected, "imputation reordered records");
        }
        if len > size && <MI as MicrodataMetric>::ORDERED {
            prop_assert!(
                keys(&out) == keys(&x[..size]),
                "truncation didn't keep the prefix"
            );
        }
        Ok(out)
    };

    let out = resize(&case.data)?;

    // B: the input's order doesn't change which records are output, wherever that is determined
    let out_permuted = resize(&case.permuted)?;
    if case.data.len() <= size {
        prop_assert!(multiset_of(&out_permuted) == multiset_of(&out));
    }

    // C: in deterministic branches, outputs are no further apart than the map allows.
    // The exact insert-delete distance takes quadratic time, so it's skipped for large datasets.
    let deterministic = |x: &Vec<T>| deterministic::<MI, MO>(x.len(), size);
    let ordered = <MI as MicrodataMetric>::ORDERED || <MO as MicrodataMetric>::ORDERED;
    let affordable = |x: &Vec<T>| !ordered || x.len().max(size) <= 2_000;
    let (neighbor, _) = MI::neighbor(&case.data, &case.edits, case.sized);
    for other in [neighbor, case.permuted.clone(), case.other.clone()] {
        let out_other = resize(&other)?;
        if !(deterministic(&case.data) && deterministic(&other))
            || !(affordable(&case.data) && affordable(&other))
        {
            continue;
        }
        let Some(d_in) = MI::exact_distance(&case.data, &other) else {
            continue;
        };
        let d_out = MO::exact_distance(&out, &out_other).unwrap();
        prop_assert!(
            d_out <= 2 * d_in,
            "stability violated: inputs at distance {} gave outputs at distance {}",
            d_in,
            d_out
        );
    }
    Ok(())
}

for_each_int!(ints, int_case, check_all);
for_each_float!(floats, float_case, check_all);

proptest! {
    #[test]
    fn prop_string(case in case(None, false, small_string().boxed(), small_string().boxed())) {
        check_all(case)?;
    }

    #[test]
    fn prop_bool(case in case(None, false, any::<bool>().boxed(), any::<bool>().boxed())) {
        check_all(case)?;
    }
}

// ---------------------------------------------------------------------------------------------
// Tightness of the stability map
// ---------------------------------------------------------------------------------------------

fn tightness<MI, MO>() -> Fallible<()>
where
    MI: IsMetricOrdered<Distance = IntDistance> + PropDatasetMetric,
    MO: IsMetricOrdered<Distance = IntDistance> + PropDatasetMetric,
    (VectorDomain<AtomDomain<i32>>, MI): MetricSpace,
    (VectorDomain<AtomDomain<i32>>, MO): MetricSpace,
{
    // C: an empty dataset and a neighbor with one record resize to [c] and [v], at distance 2
    let t = make_resize::<i32, MI, MO>(VectorDomain::default(), MI::default(), 1, 0)?;
    let (x, x2) = (vec![], vec![7]);
    let d_in = MI::exact_distance(&x, &x2).unwrap() as u32;
    let d_out = MO::exact_distance(&t.invoke(&x)?, &t.invoke(&x2)?).unwrap() as u32;
    assert_eq!(d_in, 1);
    assert_eq!(d_out, t.map(&d_in)?);
    Ok(())
}

#[test]
fn test_resize_map_is_tight() -> Fallible<()> {
    tightness::<SymmetricDistance, SymmetricDistance>()?;
    tightness::<SymmetricDistance, InsertDeleteDistance>()?;
    tightness::<InsertDeleteDistance, SymmetricDistance>()?;
    tightness::<InsertDeleteDistance, InsertDeleteDistance>()
}

// ---------------------------------------------------------------------------------------------
// Randomness (statistical)
// ---------------------------------------------------------------------------------------------

/// The number of samples per statistical test. Each check fails spuriously with probability at most 1e-6.
const SAMPLES: usize = 20_000;

/// Chi-square test that `draw` returns each of `categories` uniformly at random.
fn check_uniform<K: Eq + std::hash::Hash + Debug>(
    categories: Vec<K>,
    mut draw: impl FnMut() -> Fallible<K>,
) -> Fallible<()> {
    let index = categories
        .iter()
        .enumerate()
        .map(|(i, k)| (k, i))
        .collect::<std::collections::HashMap<_, _>>();
    let mut counts = vec![0u64; categories.len()];
    for _ in 0..SAMPLES {
        let k = draw()?;
        let i = *index
            .get(&k)
            .unwrap_or_else(|| panic!("draw {k:?} is not a category"));
        counts[i] += 1;
    }
    check_chi_square_from_probs(&counts, &uniform_probs(categories.len()))
}

/// Every subset of `0..n` with `k` elements, sorted.
fn subsets(n: i32, k: usize) -> Vec<Vec<i32>> {
    if k == 0 {
        return vec![vec![]];
    }
    (0..n)
        .flat_map(|first| {
            subsets(n, k - 1)
                .into_iter()
                .filter(move |rest| rest.first().is_none_or(|&r| r > first))
                .map(move |mut rest| {
                    rest.insert(0, first);
                    rest
                })
        })
        .collect()
}

// D: truncating unordered input keeps a uniformly random subset, whatever the input order
#[test]
fn test_resize_truncation_is_uniform() -> Fallible<()> {
    let t = make_resize::<i32, SymmetricDistance, SymmetricDistance>(
        VectorDomain::default(),
        SymmetricDistance,
        3,
        0,
    )?;
    for x in [(0..8).collect::<Vec<_>>(), (0..8).rev().collect()] {
        check_uniform(subsets(8, 3), || {
            let mut out = t.invoke(&x)?;
            out.sort();
            Ok(out)
        })?;
    }
    Ok(())
}

// D: imputing under an ordered output metric places the input records uniformly
#[test]
fn test_resize_imputation_placement_is_uniform() -> Fallible<()> {
    let t = make_resize::<i32, SymmetricDistance, InsertDeleteDistance>(
        VectorDomain::default(),
        SymmetricDistance,
        5,
        0,
    )?;
    let placements = (0..5)
        .flat_map(|i| (0..5).filter(move |&j| j != i).map(move |j| (i, j)))
        .collect();
    check_uniform(placements, || {
        let out = t.invoke(&vec![1, 2])?;
        let position = |v| out.iter().position(|&o| o == v).unwrap();
        Ok((position(1), position(2)))
    })
}

// ---------------------------------------------------------------------------------------------
// E. Large sizes and datasets
// ---------------------------------------------------------------------------------------------

fn resize_i32(
    size: usize,
) -> Fallible<
    Transformation<
        VectorDomain<AtomDomain<i32>>,
        SymmetricDistance,
        VectorDomain<AtomDomain<i32>>,
        SymmetricDistance,
    >,
> {
    make_resize(VectorDomain::default(), SymmetricDistance, size, 0)
}

// E: huge sizes construct, the output domain records them exactly, and the map ignores them
#[test]
fn test_resize_huge_sizes_construct() -> Fallible<()> {
    for size in [
        u32::MAX as usize,
        u32::MAX as usize + 1,
        isize::MAX as usize,
        usize::MAX,
    ] {
        let t = resize_i32(size)?;
        assert_eq!(t.output_domain.size, Some(size));
        assert_eq!(t.map(&1)?, 2);
        assert!(t.map(&(u32::MAX / 2 + 1)).is_err());
    }
    Ok(())
}

// E: a large dataset truncated to one record keeps one of its records
#[test]
fn test_resize_large_dataset_to_one() -> Fallible<()> {
    let x = (0..1_000_000).collect::<Vec<i32>>();
    let start = std::time::Instant::now();
    let out = resize_i32(1)?.invoke(&x)?;
    assert_eq!(out.len(), 1);
    assert!((0..1_000_000).contains(&out[0]));
    // shuffling the whole input to take one record is linear in the input length
    assert!(start.elapsed() < std::time::Duration::from_secs(30));
    Ok(())
}

// E: a large imputation and a large truncation, in each deterministic branch
#[test]
fn test_resize_large_deterministic() -> Fallible<()> {
    let t = make_resize::<i32, InsertDeleteDistance, SymmetricDistance>(
        VectorDomain::default(),
        InsertDeleteDistance,
        500_000,
        -1,
    )?;
    let x = (0..1_000_000).collect::<Vec<i32>>();
    assert_eq!(t.invoke(&x)?, x[..500_000]);
    let x = (0..1_000).collect::<Vec<i32>>();
    let out = t.invoke(&x)?;
    assert_eq!(out[..1_000], x);
    assert!(out[1_000..].iter().all(|&v| v == -1));
    Ok(())
}

// E: imputing to a size whose buffer can't be described returns an error.
// Fails for the known issue: it panics with a capacity overflow. Construction accepts any positive size.
#[test]
#[should_panic(expected = "known issue: unallocatable size")]
fn test_resize_unallocatable_size_errors() {
    let t = resize_i32(usize::MAX).unwrap();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| t.invoke(&vec![1])));
    match result {
        Ok(result) => assert!(result.is_err(), "resized to usize::MAX records"),
        Err(_) => panic!("known issue: unallocatable size: imputing to usize::MAX panics"),
    }
}

/// Imputes to 2^45 records: 2^48 bytes of references, which passes the capacity check
/// but exceeds a 48-bit address space, so the allocation fails.
/// Ignored, because a failed allocation aborts the process. Run by [`test_resize_unallocatable_size_doesnt_abort`].
#[cfg(target_pointer_width = "64")]
#[test]
#[ignore]
fn probe_resize_allocation_failure() {
    if !in_probe_child() {
        return;
    }
    // returns, with an error, once the known issue is fixed
    let _ = resize_i32(1 << 45).unwrap().invoke(&vec![1]);
}

// E: imputing to a size that passes the capacity check but can't be allocated returns an error.
// Fails for the known issue: the failed allocation aborts the whole process.
// The probe runs in a child process, since the abort can't be caught. It assumes a 64-bit
// target with at most 48 bits of address space, where the allocation fails immediately.
#[cfg(target_pointer_width = "64")]
#[test]
#[should_panic(expected = "known issue: unallocatable size")]
fn test_resize_unallocatable_size_doesnt_abort() {
    let (status, stderr) = run_ignored_test(
        "transformations::resize::test_props::probe_resize_allocation_failure",
        std::time::Duration::from_secs(60),
    )
    .expect("the allocation probe didn't finish within 60 seconds");
    if !status.success() && stderr.contains("memory allocation") {
        panic!("known issue: unallocatable size: the probe aborted: {status:?}");
    }
    assert!(status.success(), "the probe failed: {stderr}");
}
