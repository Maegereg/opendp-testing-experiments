use crate::{
    domains::{AtomDomain, LazyFrameDomain, Margin, OptionDomain, SeriesDomain},
    metrics::SymmetricDistance,
    transformations::make_stable_lazyframe,
};

use super::*;

#[test]
fn test_filter() -> Fallible<()> {
    let lf = df!("chunk_2_null" => [Some(1i64), None])?.lazy();

    let lf_domain = LazyFrameDomain::new(vec![SeriesDomain::new(
        "chunk_2_null",
        OptionDomain::new(AtomDomain::<i64>::default()),
    )])?
    .with_margin(Margin::by(["chunk_2_null"]).with_invariant_keys())?;

    let t_filter = make_stable_lazyframe(
        lf_domain.clone(),
        FrameDistance(SymmetricDistance),
        lf.clone().filter(col("chunk_2_null").is_not_null()),
    )?;

    let actual = t_filter.invoke(&lf)?.collect()?;
    assert_eq!(actual, df!("chunk_2_null" => [Some(1)])?);

    assert!(
        t_filter
            .output_domain
            .margins
            .iter()
            .all(|m| { m.invariant.is_none() })
    );

    Ok(())
}

#[test]
fn test_filter_fail_with_non_bool_predicate() -> Fallible<()> {
    let lf = df!("chunk_2_null" => [Some(1i64), None])?.lazy();

    let lf_domain = LazyFrameDomain::new(vec![SeriesDomain::new(
        "chunk_2_null",
        OptionDomain::new(AtomDomain::<i64>::default()),
    )])?
    .with_margin(Margin::by(["chunk_2_null"]).with_invariant_keys())?;

    let variant = make_stable_lazyframe(
        lf_domain.clone(),
        FrameDistance(SymmetricDistance),
        lf.clone().filter(col("chunk_2_null").fill_nan(0)),
    )
    .map(|_| ())
    .unwrap_err()
    .variant;

    assert_eq!(variant, ErrorVariant::MakeTransformation);

    Ok(())
}

// Conformance tests for the Lean model of `filter` (`verification/lean/OpenDPVerification/Filter.lean`):
// Polars keeps the rows whose predicate is `true` (not `false` or null), in order (`filt`), and the
// output is in the output domain.

/// Predicates the model covers: columns, comparisons with NaN and nulls, Kleene logic, literals.
fn predicates() -> Vec<Expr> {
    vec![
        col("b"),
        col("x").gt(lit(0.0)),
        col("x").is_null(),
        col("b").and(col("x").lt_eq(lit(1.0))),
        col("b").or(col("x").is_nan()),
        lit(true),
        lit(false),
    ]
}

/// `df` is in `domain`: each column in its series domain, and each margin's `max_length` and
/// `max_groups` hold. (`FrameDomain::member` cannot group by no columns.)
fn check_frame_domain(domain: &LazyFrameDomain, df: &DataFrame) -> Fallible<()> {
    use crate::core::Domain;
    for (series_domain, column) in domain.series_domains.iter().zip(df.get_columns()) {
        assert!(series_domain.member(column.as_materialized_series())?);
    }
    for margin in &domain.margins {
        let by: Vec<Expr> = margin.by.iter().cloned().collect();
        let lengths: Vec<u32> = if by.is_empty() {
            vec![df.height() as u32]
        } else {
            let groups = df.clone().lazy().group_by(by).agg([len()]).collect()?;
            groups.column("len")?.u32()?.into_no_null_iter().collect()
        };
        assert!(
            lengths
                .iter()
                .all(|&l| l <= margin.max_length.unwrap_or(u32::MAX))
        );
        assert!(lengths.len() as u32 <= margin.max_groups.unwrap_or(u32::MAX));
    }
    Ok(())
}

#[test]
fn test_filter_model() -> Fallible<()> {
    use crate::metrics::InsertDeleteDistance;
    use crate::transformations::make_stable_expr::test_helper::{
        filter_test_data, row_values, same_f64,
    };
    let n = 300;
    let (lf_domain, lf, k, x, b) = filter_test_data(3, n)?;

    for pred in predicates() {
        let keep = row_values(&lf, pred.clone(), n)?;
        let keep: Vec<Option<bool>> = keep.bool()?.into_iter().collect();
        let rows: Vec<usize> = (0..n).filter(|&i| keep[i] == Some(true)).collect();

        let t_sym = make_stable_lazyframe(
            lf_domain.clone(),
            FrameDistance(SymmetricDistance),
            lf.clone().filter(pred.clone()),
        )?;
        let t_id = make_stable_lazyframe(
            lf_domain.clone(),
            FrameDistance(InsertDeleteDistance),
            lf.clone().filter(pred.clone()),
        )?;
        for (out_lf, out_domain) in [
            (t_sym.invoke(&lf)?, &t_sym.output_domain),
            (t_id.invoke(&lf)?, &t_id.output_domain),
        ] {
            let out = out_lf.clone().collect()?;
            let out_k: Vec<Option<u32>> = out.column("k")?.u32()?.into_iter().collect();
            let out_x: Vec<Option<f64>> = out.column("x")?.f64()?.into_iter().collect();
            let out_b: Vec<Option<bool>> = out.column("b")?.bool()?.into_iter().collect();
            assert_eq!(out_k, rows.iter().map(|&i| Some(k[i])).collect::<Vec<_>>());
            assert_eq!(out_x.len(), rows.len());
            assert!(rows.iter().zip(&out_x).all(|(&i, &v)| same_f64(v, x[i])));
            assert_eq!(out_b, rows.iter().map(|&i| b[i]).collect::<Vec<_>>());

            check_frame_domain(out_domain, &out)?;
            assert!(out_domain.margins.iter().all(|m| m.invariant.is_none()));
        }
    }
    Ok(())
}
