use super::*;

#[test]
fn test_make_sum() -> Fallible<()> {
    macro_rules! test_sum {
        ($bounds:expr, $data:expr, $expected:expr, $metric:expr) => {{
            let input_space = (
                VectorDomain::new(AtomDomain::new_closed($bounds)?),
                SymmetricDistance,
            );
            let transformation = (input_space >> then_sum())?;
            let ret = transformation.invoke(&$data)?;
            assert_eq!(ret, $expected);
        }};
    }
    test_sum!((0, 10), vec![1, 2, 3, 4, 5], 15, SymmetricDistance);
    test_sum!((0, 10), vec![1, 2, 3, 4, 5], 15, InsertDeleteDistance);
    test_sum!((0., 10.), vec![1., 2., 3., 4., 5.], 15., SymmetricDistance);
    test_sum!(
        (0., 10.),
        vec![1., 2., 3., 4., 5.],
        15.,
        InsertDeleteDistance
    );
    Ok(())
}

/// Regression test for the unstable pairwise saturating sum (verification/FINDINGS.md, F2).
/// Deleting the last element regroups the pairwise sum, which changed the output by twice the map.
#[test]
fn test_make_sum_float_saturating_is_stable() -> Fallible<()> {
    let k = f64::MAX / 4.001;
    let input_domain = VectorDomain::new(AtomDomain::new_closed((-k, k))?);
    let t = make_sum(input_domain, InsertDeleteDistance)?;

    let x: Vec<f64> = [
        -1, -1, -1, 0, -1, -1, 0, 1, 1, -1, -1, 1, 0, 1, 1, -1, 1, 1, 0, 1, 1, 1, 1, 1, 0, -1, -1,
        1, -1, 0, -1, -1,
    ]
    .into_iter()
    .map(|v| v as f64 * k)
    .collect();
    let y = x[..x.len() - 1].to_vec();

    let (fx, fy) = (t.invoke(&x)?, t.invoke(&y)?);
    // compare halves, as the difference itself can exceed f64::MAX
    assert!((fx / 2. - fy / 2.).abs() <= t.map(&1)? / 2.);
    Ok(())
}
