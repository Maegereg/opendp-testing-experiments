use super::*;
use crate::domains::AtomDomain;

#[test]
fn test() -> Fallible<()> {
    let (input_domain, input_metric) =
        (VectorDomain::new(AtomDomain::default()), SymmetricDistance);
    let trans =
        make_resize::<_, SymmetricDistance, SymmetricDistance>(input_domain, input_metric, 3, "x")?;
    assert_eq!(trans.invoke(&vec!["A"; 2])?, vec!["A", "A", "x"]);
    assert_eq!(trans.invoke(&vec!["A"; 3])?, vec!["A"; 3]);
    assert_eq!(trans.invoke(&vec!["A"; 4])?, vec!["A", "A", "A"]);

    assert!(trans.check(&1, &2)?);
    assert!(!trans.check(&1, &1)?);
    Ok(())
}

/// The insert-delete distance between two sequences: `|a| + |b| - 2 LCS(a, b)`.
fn insert_delete_distance<T: PartialEq>(a: &[T], b: &[T]) -> usize {
    let mut lcs = vec![vec![0usize; b.len() + 1]; a.len() + 1];
    for i in 0..a.len() {
        for j in 0..b.len() {
            lcs[i + 1][j + 1] = if a[i] == b[j] {
                lcs[i][j] + 1
            } else {
                lcs[i][j + 1].max(lcs[i + 1][j])
            };
        }
    }
    a.len() + b.len() - 2 * lcs[a.len()][b.len()]
}

/// FINDINGS.md F4: under `InsertDeleteDistance` to `InsertDeleteDistance`, a dataset of exactly
/// `size` rows is shuffled while its neighbour with one more row is truncated without a shuffle,
/// so the outputs can be at distance 4 > `map(1)` = 2 (`resize_id_id_unstable` in `proof.rs`).
#[test]
#[ignore = "F4: make_resize is not stable from InsertDeleteDistance to InsertDeleteDistance"]
fn test_insert_delete_boundary_stability() -> Fallible<()> {
    let trans = make_resize::<_, InsertDeleteDistance, InsertDeleteDistance>(
        VectorDomain::new(AtomDomain::default()),
        InsertDeleteDistance,
        3,
        0i32,
    )?;
    let x = vec![1, 2, 3];
    let y = vec![1, 2, 3, 1];
    assert_eq!(insert_delete_distance(&x, &y), 1);
    let d_out = trans.map(&1)? as usize;
    let fy = trans.invoke(&y)?;
    for _ in 0..200 {
        let fx = trans.invoke(&x)?;
        assert!(
            insert_delete_distance(&fx, &fy) <= d_out,
            "{fx:?} and {fy:?} are farther apart than {d_out}"
        );
    }
    Ok(())
}
