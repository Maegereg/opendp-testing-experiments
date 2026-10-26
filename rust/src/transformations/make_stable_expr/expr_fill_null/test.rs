use polars::df;
use polars::lazy::frame::IntoLazy;
use polars::prelude::{NamedFrom, col, lit};
use polars::series::Series;

use crate::domains::{AtomDomain, LazyFrameDomain, OptionDomain, SeriesDomain};
use crate::metrics::{FrameDistance, SymmetricDistance};

use super::*;

#[test]
fn test_make_expr_fill_null() -> Fallible<()> {
    let lf_domain = LazyFrameDomain::new(vec![SeriesDomain::new(
        "i32",
        OptionDomain::new(AtomDomain::<i32>::default()),
    )])?;

    let lf = df!("i32" => [None, Some(1)])?.lazy();

    let t_fill_null = col("i32").fill_null(0).make_stable(
        lf_domain.clone().row_by_row(),
        FrameDistance(SymmetricDistance),
    )?;
    let expr_fill_null = t_fill_null.invoke(&lf.logical_plan)?.expr;
    println!("{:?}", expr_fill_null);
    let actual = lf.with_column(expr_fill_null).collect()?;

    assert_eq!(actual, df!("i32" => [0, 1])?);

    assert!(!t_fill_null.output_domain.column.nullable);

    Ok(())
}

#[test]
fn test_make_expr_fill_null_expr() -> Fallible<()> {
    let f64_null = SeriesDomain::new("f64_null", OptionDomain::new(AtomDomain::<f64>::default()));
    let f64_nonnull = SeriesDomain::new("f64_nonnull", AtomDomain::<f64>::default());
    let lf_domain = LazyFrameDomain::new(vec![f64_null, f64_nonnull])?;

    let lf = df!(
        "f64_null" => [None, Some(1.), Some(f64::NAN)],
        "f64_nonnull" => [0f64; 3]
    )?
    .lazy();

    let t_fill_null = col("f64_null").fill_null(col("f64_nonnull")).make_stable(
        lf_domain.clone().row_by_row(),
        FrameDistance(SymmetricDistance),
    )?;

    let expr_fill_null = t_fill_null.invoke(&lf.logical_plan)?.expr;
    let actual = lf.with_column(expr_fill_null).collect()?;
    let actual_f64_null = actual.column("f64_null")?.as_materialized_series();

    assert_eq!(
        actual_f64_null,
        &Series::new("f64_null".into(), [Some(0.), Some(1.), Some(f64::NAN)])
    );

    assert!(!t_fill_null.output_domain.column.nullable);

    Ok(())
}

#[test]
fn test_make_expr_fill_null_expr_filter_fail() -> Fallible<()> {
    let f64_null = SeriesDomain::new("f64_null", OptionDomain::new(AtomDomain::<f64>::default()));
    let f64_nonnull = SeriesDomain::new("f64_nonnull", AtomDomain::<f64>::default());
    let lf_domain = LazyFrameDomain::new(vec![f64_null, f64_nonnull])?;

    let err = col("f64_null")
        .fill_null(lit(0.0).filter(col("f64_nonnull").gt_eq(0.0)))
        .make_stable(
            lf_domain.clone().row_by_row(),
            FrameDistance(SymmetricDistance),
        )
        .unwrap_err();

    assert_eq!(
        err.message,
        Some("filter is not allowed in a row-by-row context".to_string())
    );
    Ok(())
}

// Conformance tests for the Lean model of `fill_null` (`verification/lean/OpenDPVerification/FillNull.lean`):
// Polars' `fill_null` is the per-row model `fillRow` (the data value, or the fill value if the data
// is null), in each context, and keeps the data's type when the fill has it.

/// Deterministic pseudo-random values (a linear congruential generator).
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }
    fn f64(&mut self) -> f64 {
        match self.next() % 10 {
            0 => f64::NAN,
            1 => f64::INFINITY,
            2 => f64::NEG_INFINITY,
            3 => -0.0,
            _ => (self.next() as f64 - 2f64.powi(30)) * 2f64.powi((self.next() % 80) as i32 - 40),
        }
    }
}

const N: usize = 200;

/// Evaluates the expression built by `make_stable` for `expr` on `lf`, in a row-by-row context
/// (`with_column`), and checks the output is in the output domain.
fn eval_row_by_row(
    lf_domain: &LazyFrameDomain,
    lf: &polars::prelude::LazyFrame,
    expr: Expr,
) -> Fallible<Series> {
    use crate::core::Domain;
    let t = expr.make_stable(
        lf_domain.clone().row_by_row(),
        FrameDistance(SymmetricDistance),
    )?;
    let out_expr = t.invoke(&lf.logical_plan)?.expr;
    let out = lf.clone().select([out_expr]).collect()?;
    let series = out.get_columns()[0].as_materialized_series().clone();
    assert_eq!(series.dtype(), &t.output_domain.column.dtype());
    assert!(t.output_domain.column.member(&series)?);
    Ok(series)
}

fn same_f64(a: Option<f64>, b: Option<f64>) -> bool {
    match (a, b) {
        (Some(a), Some(b)) => a.to_bits() == b.to_bits(),
        (a, b) => a.is_none() && b.is_none(),
    }
}

#[test]
fn test_fill_null_model_f64() -> Fallible<()> {
    let mut rng = Lcg(1);
    let x: Vec<Option<f64>> = (0..N)
        .map(|_| (rng.next() % 3 != 0).then(|| rng.f64()))
        .collect();
    let f: Vec<f64> = (0..N).map(|_| rng.f64()).collect();
    let k: Vec<u32> = (0..N).map(|_| (rng.next() % 4) as u32).collect();
    let lf_domain = LazyFrameDomain::new(vec![
        SeriesDomain::new("x", OptionDomain::new(AtomDomain::<f64>::default())),
        SeriesDomain::new("f", AtomDomain::<f64>::default()),
        SeriesDomain::new("k", AtomDomain::<u32>::default()),
    ])?;
    let lf = df!("x" => &x, "f" => &f, "k" => &k)?.lazy();

    // column fill
    let out = eval_row_by_row(&lf_domain, &lf, col("x").fill_null(col("f")))?;
    for (i, v) in out.f64()?.into_iter().enumerate() {
        assert!(same_f64(v, Some(x[i].unwrap_or(f[i]))), "row {i}");
    }

    // scalar fill
    for c in [0.5, f64::NAN, f64::INFINITY] {
        let out = eval_row_by_row(&lf_domain, &lf, col("x").fill_null(lit(c)))?;
        for (i, v) in out.f64()?.into_iter().enumerate() {
            assert!(same_f64(v, Some(x[i].unwrap_or(c))), "row {i}");
        }
    }

    // aggregation context: per row, within each group
    let t = col("x").fill_null(lit(0.5)).make_stable(
        lf_domain.clone().aggregate(["k"]),
        FrameDistance(SymmetricDistance),
    )?;
    let out_expr = t.invoke(&lf.logical_plan)?.expr;
    let out = lf
        .clone()
        .group_by_stable([col("k")])
        .agg([out_expr])
        .collect()?;
    let keys = out.column("k")?.u32()?.clone();
    let lists = out.column("x")?.list()?.clone();
    for (key, list) in keys.into_iter().zip(lists.into_iter()) {
        let (key, list) = (key.unwrap(), list.unwrap());
        let expected: Vec<Option<f64>> = (0..N)
            .filter(|&i| k[i] == key)
            .map(|i| Some(x[i].unwrap_or(0.5)))
            .collect();
        let actual: Vec<Option<f64>> = list.f64()?.into_iter().collect();
        assert_eq!(actual.len(), expected.len());
        assert!(actual.iter().zip(&expected).all(|(a, e)| same_f64(*a, *e)));
    }
    Ok(())
}

#[test]
fn test_fill_null_model_i32_string() -> Fallible<()> {
    let mut rng = Lcg(2);
    let x: Vec<Option<i32>> = (0..N)
        .map(|_| (rng.next() % 3 != 0).then(|| rng.next() as i32))
        .collect();
    let f: Vec<i32> = (0..N).map(|_| rng.next() as i32).collect();
    let s: Vec<Option<String>> = (0..N)
        .map(|_| (rng.next() % 3 != 0).then(|| format!("s{}", rng.next() % 7)))
        .collect();
    let lf_domain = LazyFrameDomain::new(vec![
        SeriesDomain::new("x", OptionDomain::new(AtomDomain::<i32>::default())),
        SeriesDomain::new("f", AtomDomain::<i32>::default()),
        SeriesDomain::new("s", OptionDomain::new(AtomDomain::<String>::default())),
    ])?;
    let lf = df!("x" => &x, "f" => &f, "s" => &s)?.lazy();

    let out = eval_row_by_row(&lf_domain, &lf, col("x").fill_null(col("f")))?;
    let expected: Vec<Option<i32>> = (0..N).map(|i| Some(x[i].unwrap_or(f[i]))).collect();
    assert_eq!(out.i32()?.into_iter().collect::<Vec<_>>(), expected);

    let out = eval_row_by_row(&lf_domain, &lf, col("x").fill_null(lit(7i32)))?;
    let expected: Vec<Option<i32>> = (0..N).map(|i| Some(x[i].unwrap_or(7))).collect();
    assert_eq!(out.i32()?.into_iter().collect::<Vec<_>>(), expected);

    let out = eval_row_by_row(&lf_domain, &lf, col("s").fill_null(lit("fill")))?;
    let expected: Vec<Option<&str>> = (0..N)
        .map(|i| Some(s[i].as_deref().unwrap_or("fill")))
        .collect();
    assert_eq!(out.str()?.into_iter().collect::<Vec<_>>(), expected);
    Ok(())
}

/// The constructor either rejects `expr`, or its output is in the output domain.
fn check_claim(
    lf_domain: &LazyFrameDomain,
    lf: &polars::prelude::LazyFrame,
    expr: Expr,
) -> Fallible<()> {
    use crate::core::Domain;
    let Ok(t) = expr.make_stable(
        lf_domain.clone().row_by_row(),
        FrameDistance(SymmetricDistance),
    ) else {
        return Ok(());
    };
    let out_expr = t.invoke(&lf.logical_plan)?.expr;
    let out = lf.clone().select([out_expr]).collect()?;
    let series = out.get_columns()[0].as_materialized_series().clone();
    assert_eq!(series.dtype(), &t.output_domain.column.dtype());
    assert!(t.output_domain.column.member(&series)?);
    Ok(())
}

#[test]
#[ignore = "F19 (verification/FINDINGS.md): open"]
fn test_fill_null_keeps_dtype() -> Fallible<()> {
    // Polars casts to the supertype of the data and the fill; the output domain keeps the data's type
    let lf_domain = LazyFrameDomain::new(vec![
        SeriesDomain::new("i32", OptionDomain::new(AtomDomain::<i32>::default())),
        SeriesDomain::new("f64", AtomDomain::<f64>::default()),
    ])?;
    let lf = df!("i32" => [None, Some(1)], "f64" => [2.5, 3.5])?.lazy();
    check_claim(&lf_domain, &lf, col("i32").fill_null(lit(1.5)))?;
    check_claim(&lf_domain, &lf, col("i32").fill_null(lit(1i64 << 40)))?;
    check_claim(&lf_domain, &lf, col("i32").fill_null(lit("a")))?;
    check_claim(&lf_domain, &lf, col("i32").fill_null(col("f64")))
}

#[test]
#[ignore = "F20 (verification/FINDINGS.md): open"]
fn test_fill_null_nan() -> Fallible<()> {
    // the output domain keeps the data's NaN flag, whatever the fill
    let lf_domain = LazyFrameDomain::new(vec![
        SeriesDomain::new("x", OptionDomain::new(AtomDomain::<f64>::new(None, None))),
        SeriesDomain::new("f", AtomDomain::<f64>::default()),
    ])?;
    let lf = df!("x" => [None, Some(1.0)], "f" => [f64::NAN, 2.0])?.lazy();
    check_claim(&lf_domain, &lf, col("x").fill_null(lit(f64::NAN)))?;
    check_claim(&lf_domain, &lf, col("x").fill_null(col("f")))
}
