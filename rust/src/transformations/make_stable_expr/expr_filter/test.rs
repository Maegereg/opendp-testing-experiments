use polars::df;
use polars::prelude::{IntoLazy, NamedFrom, col, lit};
use polars::series::Series;

use crate::domains::{AtomDomain, LazyFrameDomain, OptionDomain, SeriesDomain};
use crate::measurements::make_private_lazyframe;
use crate::measures::MaxDivergence;
use crate::metrics::{FrameDistance, SymmetricDistance};
use crate::polars::PrivacyNamespace;

use super::*;

#[test]
fn make_expr_filter_standard() -> Fallible<()> {
    let a_domain = SeriesDomain::new("a", AtomDomain::<i32>::default());
    let b_domain = SeriesDomain::new("b", AtomDomain::<i32>::default());
    let lf_domain = LazyFrameDomain::new(vec![a_domain, b_domain])?;
    let lf = df!("a" => &[1, 2, 3], "b" => &[10, 20, 30])?.lazy();

    let lf_filter = lf
        .clone()
        .select([col("a").filter(col("b").gt(15)).dp().count(None, false)]);

    let t_obs = make_private_lazyframe(
        lf_domain,
        FrameDistance(SymmetricDistance),
        MaxDivergence,
        lf_filter,
        Some(0.0),
        None,
    )?;
    let df_observed = t_obs.invoke(&lf)?.collect()?;
    assert_eq!(
        df_observed.column("a")?.as_materialized_series(),
        &Series::new("a".into(), [2])
    );
    Ok(())
}

#[test]
fn make_expr_filter_impute() -> Fallible<()> {
    let series_domain = SeriesDomain::new("", OptionDomain::new(AtomDomain::<i32>::default()));
    let lf_domain = LazyFrameDomain::new(vec![series_domain])?
        .with_margin(Margin::select().with_max_length(5))?;
    let lf = df!("" => &[Some(1), Some(2), Some(3), None])?.lazy();

    let lf_filter = lf.clone().select([col("")
        .filter(col("").is_not_null())
        .fill_null(lit(0))
        .dp()
        .sum((lit(1), lit(3)), None)]);

    let t_obs = make_private_lazyframe(
        lf_domain,
        FrameDistance(SymmetricDistance),
        MaxDivergence,
        lf_filter,
        Some(0.0),
        None,
    )?;
    let df_observed = t_obs.invoke(&lf)?.collect()?;
    assert_eq!(
        df_observed.column("")?.as_materialized_series(),
        &Series::new("".into(), [6])
    );
    Ok(())
}

// Conformance tests for the Lean model of `expr.filter(by)` (`verification/lean/OpenDPVerification/Filter.lean`):
// on each group, Polars keeps the values of `expr` on the rows where `by` is `true`, in order
// (`filtMap`), and every group of the input stays in the output (the keys invariant).

#[test]
fn test_expr_filter_model() -> Fallible<()> {
    use crate::core::Domain;
    use crate::domains::Invariant;
    use crate::transformations::make_stable_expr::test_helper::{
        filter_test_data, row_values, same_f64,
    };
    let n = 300;
    let (lf_domain, lf, k, _, _) = filter_test_data(4, n)?;
    let mut keys: Vec<u32> = vec![];
    for &v in &k {
        if !keys.contains(&v) {
            keys.push(v);
        }
    }

    let cases = [
        (col("x"), col("b")),
        (col("x"), col("x").gt(lit(0.0))),
        (col("x"), col("b").and(col("x").lt_eq(lit(1.0)))),
        (lit(1.5), col("b")),
        (col("x"), lit(true)),
        (col("x"), lit(false)),
    ];
    for (input, by) in cases {
        let value: Vec<Option<f64>> = row_values(&lf, input.clone(), n)?
            .f64()?
            .into_iter()
            .collect();
        let keep: Vec<Option<bool>> = row_values(&lf, by.clone(), n)?
            .bool()?
            .into_iter()
            .collect();
        let expected = |group: Option<u32>| -> Vec<Option<f64>> {
            (0..n)
                .filter(|&i| group.is_none_or(|g| k[i] == g) && keep[i] == Some(true))
                .map(|i| value[i])
                .collect()
        };
        let expr = input.clone().filter(by.clone());

        // select context: the whole frame is one group
        let t = expr
            .clone()
            .make_stable(lf_domain.clone().select(), FrameDistance(SymmetricDistance))?;
        let out = (lf.clone())
            .select([t.invoke(&lf.logical_plan)?.expr])
            .collect()?;
        let series = out.get_columns()[0].as_materialized_series().clone();
        let actual: Vec<Option<f64>> = series.f64()?.into_iter().collect();
        let exp = expected(None);
        assert_eq!(actual.len(), exp.len(), "{input:?} {by:?}");
        assert!(actual.iter().zip(&exp).all(|(a, e)| same_f64(*a, *e)));
        assert!(t.output_domain.column.member(&series)?);

        // aggregation context: each group on its own, all groups kept
        let t = expr.make_stable(
            lf_domain.clone().aggregate(["k"]),
            FrameDistance(SymmetricDistance),
        )?;
        let out = (lf.clone())
            .group_by_stable([col("k")])
            .agg([t.invoke(&lf.logical_plan)?.expr])
            .collect()?;
        let out_keys: Vec<u32> = out.column("k")?.u32()?.into_no_null_iter().collect();
        assert_eq!(out_keys, keys);
        let Context::Aggregation { margin } = &t.output_domain.context else {
            panic!("expected an aggregation context");
        };
        assert_eq!(margin.invariant, Some(Invariant::Keys));
        assert!(out_keys.len() as u32 <= margin.max_groups.unwrap_or(u32::MAX));
        let lists = out.get_columns()[1].list()?.clone();
        for (key, list) in out_keys.iter().zip(lists.into_iter()) {
            let list = list.unwrap();
            let actual: Vec<Option<f64>> = list.f64()?.into_iter().collect();
            let exp = expected(Some(*key));
            assert_eq!(actual.len(), exp.len());
            assert!(actual.iter().zip(&exp).all(|(a, e)| same_f64(*a, *e)));
            assert!(list.len() as u32 <= margin.max_length.unwrap_or(u32::MAX));
            // list elements are unnamed; the domain names the column
            let list = list.with_name(series.name().clone());
            assert!(t.output_domain.column.member(&list)?);
        }
    }
    Ok(())
}
