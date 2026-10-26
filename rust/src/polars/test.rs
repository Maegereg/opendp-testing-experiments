use polars::{
    df,
    prelude::{IntoLazy, NamedFrom, col},
};

use crate::{
    domains::{AtomDomain, LazyFrameDomain, Margin, SeriesDomain},
    measurements::make_private_lazyframe,
    measures::MaxDivergence,
    metrics::SymmetricDistance,
};

use super::*;

#[test]
fn test_dp_quantile() -> Fallible<()> {
    let lf_domain = LazyFrameDomain::new(vec![SeriesDomain::new(
        "A",
        AtomDomain::<f64>::new_non_nan(),
    )])?
    .with_margin(Margin::select().with_max_length(100))?;

    let lf = df!("A" => [50f64; 100])?.lazy();

    let candidates = Series::new(
        "".into(),
        [0., 10., 20., 30., 40., 50., 60., 70., 80., 90., 100.],
    );

    let m_quant = make_private_lazyframe(
        lf_domain,
        SymmetricDistance,
        MaxDivergence,
        lf.clone().select([col("A").dp().median(candidates, None)]),
        Some(1.),
        None,
    )?;

    let observed = m_quant
        .invoke(&lf)?
        .collect()?
        .column("A")?
        .f64()?
        .get(0)
        .unwrap();

    let expected = 50.;
    assert_eq!(observed, expected);
    Ok(())
}

#[test]
fn test_dp_quantile_int_even_candidates() -> Fallible<()> {
    // nulls are filled with the candidates' median (1.5 here), converted to the data's type: fill_null
    // requires a fill of the data's type (F19, verification/FINDINGS.md)
    let lf_domain = LazyFrameDomain::new(vec![SeriesDomain::new(
        "A",
        crate::domains::OptionDomain::new(AtomDomain::<i64>::default()),
    )])?
    .with_margin(Margin::select().with_max_length(100))?;

    let lf = df!("A" => [Some(2i64); 100])?.lazy();
    let candidates = Series::new("".into(), [0i64, 1, 2, 3]);

    let m_quant = make_private_lazyframe(
        lf_domain,
        SymmetricDistance,
        MaxDivergence,
        lf.clone().select([col("A").dp().median(candidates, None)]),
        Some(1.),
        None,
    )?;
    let observed = m_quant.invoke(&lf)?.collect()?;
    assert_eq!(observed.column("A")?.i64()?.get(0), Some(2));
    Ok(())
}
