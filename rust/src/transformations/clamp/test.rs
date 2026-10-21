use crate::{error::Fallible, metrics::SymmetricDistance, transformations::then_clamp};

use super::*;

#[test]
fn test_make_clamp() -> Fallible<()> {
    let input_space = (VectorDomain::new(AtomDomain::default()), SymmetricDistance);
    let transformation = (input_space >> then_clamp((0, 10)))?;
    let arg = vec![-10, -5, 0, 5, 10, 20];
    let ret = transformation.invoke(&arg)?;
    let expected = vec![0, 0, 0, 5, 10, 10];
    assert_eq!(ret, expected);
    Ok(())
}

#[test]
fn test_make_clamp_rejects_unordered_pair_bounds() -> Fallible<()> {
    // (0, 10) < (1, 0) lexicographically, so `Bounds` accepts them,
    // but they are not ordered componentwise, so no row could be clamped.
    let input_space = (
        VectorDomain::new(AtomDomain::<(f64, f64)>::new(None, None)),
        SymmetricDistance,
    );
    assert!((input_space >> then_clamp(((0.0, 10.0), (1.0, 0.0)))).is_err());
    Ok(())
}
