//! Property-based tests for `make_count_by`.
//!
//! Counts and distances are checked against exact `usize`/`IBig` references,
//! never computed in the count type `TV`.
//!
//! Properties (labels match the comments below):
//! * A: constructor succeeds and builds the expected output space
//! * B: the function counts each distinct key exactly, saturating at `TV::MAX`
//! * C: the stability map is sound for every component of the `(L0, L1, L∞)` distance,
//!   and is exactly `(d, d, d)` whenever `d` is representable in `TV`

use dashu::integer::IBig;
use proptest::prelude::*;

use super::*;
use crate::core::Domain;
use crate::metrics::IntDistance;
use crate::test_props::*;

/// A dataset, edits to derive a neighbor, and a second arbitrary dataset in the same domain.
#[derive(Debug, Clone)]
struct Case<K: Hashable> {
    domain: VectorDomain<AtomDomain<K>>,
    data: Vec<K>,
    edits: Vec<Edit<K>>,
    other: Vec<K>,
    /// extra input distances to probe the stability map with
    distances: Vec<IntDistance>,
}

/// Datasets over `element_domain`, with keys drawn from `key()`, optionally of known size.
fn case<K: Hashable, S: Strategy<Value = K>>(
    element_domain: AtomDomain<K>,
    key: impl Fn() -> S,
) -> impl Strategy<Value = Case<K>> {
    (
        any::<bool>(),
        prop::collection::vec(key(), 0..40),
        edits(key()),
        prop::collection::vec(key(), 0..40),
        distances(),
    )
        .prop_map(move |(sized, data, edits, mut other, distances)| {
            let mut domain = VectorDomain::new(element_domain.clone());
            if sized {
                domain.size = Some(data.len());
                // the second dataset must also have the known size
                other.truncate(data.len());
                other.extend_from_slice(&data[other.len()..]);
            }
            Case {
                domain,
                data,
                edits,
                other,
                distances,
            }
        })
}

/// One key repeated about `V::MAX` times, so that its count straddles saturation.
/// For count types too wide to saturate in memory, the key is repeated about 1000 times.
fn heavy_case<V: PropInt>() -> impl Strategy<Value = Case<u8>> {
    let max = int_max::<V>();
    let center = if max <= IBig::from(u16::MAX) {
        from_big::<usize>(max).unwrap()
    } else {
        1000
    };
    (
        any::<u8>(),
        0usize..5,
        0usize..5,
        prop::collection::vec(any::<u8>(), 0..4),
        any::<bool>(),
        distances(),
    )
        .prop_flat_map(move |(k, dn, dn_other, extra, sized, distances)| {
            let mut data = vec![k; center + dn - 2];
            data.extend(&extra);
            let mut other = vec![k; center + dn_other - 2];
            other.extend(&extra);
            let mut domain = VectorDomain::new(AtomDomain::default());
            if sized {
                domain.size = Some(data.len());
                other.truncate(data.len());
                other.extend_from_slice(&data[other.len()..]);
            }
            // edits mostly add or remove the saturated key
            edits(prop_oneof![3 => Just(k), 1 => any::<u8>()]).prop_map(move |edits| Case {
                domain: domain.clone(),
                data: data.clone(),
                edits,
                other: other.clone(),
                distances: distances.clone(),
            })
        })
}

/// `u8` keys, in bounded, unbounded and saturating datasets.
fn u8_key_case<V: PropInt>() -> impl Strategy<Value = Case<u8>> {
    let bounded = int_bounds::<u8>()
        .prop_flat_map(|b| case(AtomDomain::new_closed(b).unwrap(), move || int_value_in(b)));
    prop_oneof![
        bounded,
        case(AtomDomain::default(), any::<u8>),
        heavy_case::<V>()
    ]
}

fn check_u8_key<V: PropInt>(case: Case<u8>) -> TestResult {
    check::<u8, V>(case)
}

fn check<K: Hashable, V: PropInt>(case: Case<K>) -> TestResult {
    // A1: construction succeeds for any input domain
    let t = ok(make_count_by::<K, V>(
        case.domain.clone(),
        SymmetricDistance,
    ))?;

    // A2: input space is preserved, and keys of the output carry the input bounds
    prop_assert!(t.input_domain == case.domain);
    prop_assert!(t.input_metric == SymmetricDistance);
    prop_assert!(
        t.output_domain
            == MapDomain::new(
                case.domain.element_domain.clone(),
                AtomDomain::new_non_nan()
            )
    );
    prop_assert!(t.output_metric == L01InfDistance::default());

    let max = int_max::<V>();
    let out = ok(t.invoke(&case.data))?;
    let mult = multiplicities(&case.data);

    // B1/B2: exactly the distinct keys, each counted exactly, saturating at V::MAX
    prop_assert_eq!(out.len(), mult.len());
    for (k, n) in &mult {
        let Some(v) = out.get(*k) else {
            return Err(TestCaseError::fail(format!("key {k:?} is missing")));
        };
        prop_assert_eq!(big(*v), IBig::from(*n).min(max.clone()), "count of {:?}", k);
    }

    // B4/B5: output is in the output domain, and empty input gives an empty map
    prop_assert!(ok(t.output_domain.member(&out))?);
    if case.data.is_empty() {
        prop_assert!(out.is_empty());
    }

    // B3: the input metric is unordered, so the result can't depend on order
    let mut reordered = case.data.clone();
    reordered.reverse();
    prop_assert!(ok(t.invoke(&reordered))? == out);
    let mid = reordered.len() / 2;
    reordered.rotate_left(mid);
    prop_assert!(ok(t.invoke(&reordered))? == out);

    // B6: adding a record increments only its key, unless saturated
    if case.domain.size.is_none()
        && let Some((_, _, key)) = case.edits.first()
    {
        let mut added = case.data.clone();
        added.push(key.clone());
        let mut expected = out.clone();
        let count = expected
            .entry(key.clone())
            .or_insert(from_big(IBig::ZERO).unwrap());
        *count = from_big(clamp_big::<V>(big(*count) + IBig::ONE)).unwrap();
        prop_assert!(ok(t.invoke(&added))? == expected);
    }

    // B7: with no saturation, counts add up to the number of records
    if mult.values().all(|n| IBig::from(*n) <= max) {
        let total = out.values().fold(IBig::ZERO, |s, v| s + big(*v));
        prop_assert_eq!(total, IBig::from(case.data.len()));
    }

    // C2/C3: the map is exactly (d, d, d), or fails because d isn't representable in V
    let (x2, k) = neighbor(&case.data, &case.edits, case.domain.size.is_some(), false);
    let d_other = u32::try_from(symmetric_distance(&case.data, &case.other)).unwrap();
    let near_max = [
        max.clone() - IBig::ONE,
        max.clone(),
        max.clone() + IBig::ONE,
    ]
    .into_iter()
    .filter_map(|d| u32::try_from(d).ok());
    let probes = [0, 1, 2, k, d_other, u32::MAX]
        .into_iter()
        .chain(near_max)
        .chain(case.distances.iter().copied());
    for d in probes {
        match t.map(&d) {
            Ok((d0, d1, d2)) => {
                prop_assert_eq!(d0, d, "L0 component of map({})", d);
                prop_assert_eq!(big(d1), IBig::from(d), "L1 component of map({})", d);
                prop_assert_eq!(big(d2), IBig::from(d), "L∞ component of map({})", d);
            }
            Err(_) => prop_assert!(IBig::from(d) > max, "map({}) failed spuriously", d),
        }
    }

    // C1: stability, both for an edited neighbor and for an arbitrary dataset at its exact distance
    for (x2, d) in [(x2, k), (case.other.clone(), d_other)] {
        let out2 = ok(t.invoke(&x2))?;
        let (l0, l1, linf) = map_distance_l01inf(&out, &out2);
        let d_big = IBig::from(d);
        // each component of the distance is at most d, even when d isn't representable in V
        prop_assert!(
            IBig::from(l0) <= d_big && l1 <= d_big && linf <= d_big,
            "counts moved by ({}, {}, {}) between datasets at distance {}",
            l0,
            l1,
            linf,
            d
        );
        if let Ok((d0, d1, d2)) = t.map(&d) {
            prop_assert!(
                l0 <= d0 as usize && l1 <= big(d1) && linf <= big(d2),
                "stability violated: distance ({}, {}, {}) exceeds map({}) = ({}, {:?}, {:?})",
                l0,
                l1,
                linf,
                d,
                d0,
                d1,
                d2
            );
        }
    }
    Ok(())
}

for_each_int!(u8_keys, u8_key_case, check_u8_key);

proptest! {
    #[test]
    fn prop_bool_keys(case in case(AtomDomain::default(), any::<bool>)) {
        check::<bool, u8>(case)?;
    }

    #[test]
    fn prop_i8_keys(case in case(AtomDomain::default(), any::<i8>)) {
        check::<i8, i8>(case)?;
    }

    #[test]
    fn prop_i32_keys(case in prop_oneof![
        case(AtomDomain::default(), || -4i32..4),
        case(AtomDomain::new_closed((-4, 4)).unwrap(), || -4i32..=4),
    ]) {
        check::<i32, u128>(case)?;
    }

    #[test]
    fn prop_u64_keys(case in case(AtomDomain::default(), || prop_oneof![0u64..4, any::<u64>()])) {
        check::<u64, i64>(case)?;
    }

    #[test]
    fn prop_string_keys(case in case(AtomDomain::default(), small_string)) {
        check::<String, i8>(case)?;
    }

    #[test]
    fn prop_char_keys(case in case(AtomDomain::default(), small_char)) {
        check::<char, u16>(case)?;
    }
}

// ---------------------------------------------------------------------------------------------
// Deterministic regression cases
// ---------------------------------------------------------------------------------------------

#[test]
fn test_count_by_saturation() -> Fallible<()> {
    let t = make_count_by::<u8, u8>(VectorDomain::new(AtomDomain::default()), SymmetricDistance)?;
    let saturated = t.invoke(&vec![7; 300])?;
    assert_eq!(saturated, HashMap::from([(7, 255)]));

    // C4: removing or adding a record to a saturated count can't move it by more than one
    assert_eq!(t.invoke(&vec![7; 299])?, saturated);
    assert_eq!(t.invoke(&vec![7; 255])?, saturated);
    assert_eq!(t.invoke(&vec![7; 254])?, HashMap::from([(7, 254)]));
    Ok(())
}

#[test]
fn test_count_by_map_limits() -> Fallible<()> {
    let t = make_count_by::<bool, i8>(VectorDomain::new(AtomDomain::default()), SymmetricDistance)?;
    assert_eq!(t.map(&0)?, (0, 0, 0));
    assert_eq!(t.map(&127)?, (127, 127, 127));
    assert!(t.map(&128).is_err());
    assert!(t.map(&u32::MAX).is_err());
    Ok(())
}

#[test]
fn test_count_by_key_disappears() -> Fallible<()> {
    let t =
        make_count_by::<String, i32>(VectorDomain::new(AtomDomain::default()), SymmetricDistance)?;
    let with_key = t.invoke(&vec!["a".to_string()])?;
    let without_key = t.invoke(&vec![])?;
    assert_eq!(
        map_distance_l01inf(&with_key, &without_key),
        (1, IBig::ONE, IBig::ONE)
    );
    assert_eq!(t.map(&1)?, (1, 1, 1));
    Ok(())
}

#[test]
fn test_count_by_bounded_keys() -> Fallible<()> {
    let element_domain = AtomDomain::new_closed((0i32, 3))?;
    let t =
        make_count_by::<i32, u32>(VectorDomain::new(element_domain.clone()), SymmetricDistance)?;
    assert!(t.output_domain.key_domain == element_domain);
    assert_eq!(t.invoke(&vec![0, 3, 3])?, HashMap::from([(0, 1), (3, 2)]));
    Ok(())
}
