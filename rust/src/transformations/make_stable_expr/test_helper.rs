use crate::domains::{AtomDomain, LazyFrameDomain, Margin, SeriesDomain};
use crate::error::*;
use polars::prelude::*;

pub fn get_test_data() -> Fallible<(LazyFrameDomain, LazyFrame)> {
    let lf_domain = LazyFrameDomain::new(vec![
        SeriesDomain::new("chunk_2_bool", AtomDomain::<bool>::default()),
        SeriesDomain::new("cycle_5_alpha", AtomDomain::<String>::default()),
        SeriesDomain::new("const_1f64", AtomDomain::<f64>::new_non_nan()),
        SeriesDomain::new("chunk_(..10u32)", AtomDomain::<u32>::default()),
        SeriesDomain::new("cycle_(..100i32)", AtomDomain::<i32>::default()),
    ])?
    .with_margin(
        Margin::select()
            .with_invariant_lengths()
            .with_max_length(1000),
    )?
    .with_margin(
        Margin::by(["chunk_2_bool"])
            .with_invariant_lengths()
            .with_max_length(500)
            .with_max_groups(2),
    )?
    .with_margin(
        Margin::by(["chunk_2_bool", "cycle_5_alpha"])
            .with_invariant_keys()
            .with_max_length(200),
    )?
    .with_margin(
        Margin::by(["cycle_(..100i32)"])
            .with_invariant_keys()
            .with_max_length(100),
    )?;

    let lf = df!(
        "chunk_2_bool" => [[false; 500], [true; 500]].concat(),
        "cycle_5_alpha" => ["A", "B", "C", "D", "E"].repeat(200),
        "const_1f64" => [1.0; 1000],
        "chunk_(..10u32)" => (0..10u32).flat_map(|i| [i; 100].into_iter()).collect::<Vec<_>>(),
        "cycle_(..100i32)" => (0..100i32).cycle().take(1000).collect::<Vec<_>>()
    )?
    .lazy();

    Ok((lf_domain, lf))
}

/// Deterministic pseudo-random values (a linear congruential generator), for the conformance tests
/// of the Lean models (`verification/lean/OpenDPVerification`).
pub struct Lcg(pub u64);

impl Lcg {
    pub fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }
    /// A float that is often NaN, infinite or -0.0, and otherwise of any magnitude.
    pub fn f64(&mut self) -> f64 {
        match self.next() % 10 {
            0 => f64::NAN,
            1 => f64::INFINITY,
            2 => f64::NEG_INFINITY,
            3 => -0.0,
            _ => (self.next() as f64 - 2f64.powi(30)) * 2f64.powi((self.next() % 80) as i32 - 40),
        }
    }
}

/// Random data for the `filter` conformance tests (`verification/lean/OpenDPVerification/Filter.lean`):
/// a group column `k`, a value column `x` (NaN, infinities, nulls) and a predicate column `b` (nulls).
/// The domain has a margin on `k` (with keys invariant) and a `select` margin.
pub fn filter_test_data(
    seed: u64,
    n: usize,
) -> Fallible<(
    LazyFrameDomain,
    LazyFrame,
    Vec<u32>,
    Vec<Option<f64>>,
    Vec<Option<bool>>,
)> {
    use crate::domains::OptionDomain;
    let mut rng = Lcg(seed);
    let k: Vec<u32> = (0..n).map(|_| (rng.next() % 5) as u32).collect();
    let x: Vec<Option<f64>> = (0..n)
        .map(|_| (rng.next() % 4 != 0).then(|| rng.f64()))
        .collect();
    let b: Vec<Option<bool>> = (0..n)
        .map(|_| match rng.next() % 3 {
            0 => None,
            v => Some(v == 1),
        })
        .collect();
    let lf_domain = LazyFrameDomain::new(vec![
        SeriesDomain::new("k", AtomDomain::<u32>::default()),
        SeriesDomain::new("x", OptionDomain::new(AtomDomain::<f64>::default())),
        SeriesDomain::new("b", OptionDomain::new(AtomDomain::<bool>::default())),
    ])?
    .with_margin(
        Margin::by(["k"])
            .with_max_length(n as u32)
            .with_max_groups(5)
            .with_invariant_keys(),
    )?
    .with_margin(Margin::select().with_max_length(n as u32))?;
    let lf = df!("k" => &k, "x" => &x, "b" => &b)?.lazy();
    Ok((lf_domain, lf, k, x, b))
}

/// The values of a row-by-row expression on each of `n` rows (a scalar is broadcast).
pub fn row_values(lf: &LazyFrame, expr: Expr, n: usize) -> Fallible<Series> {
    let out = lf.clone().select([expr.alias("v")]).collect()?;
    let s = out.column("v")?.as_materialized_series().clone();
    Ok(if s.len() == 1 {
        s.new_from_index(0, n)
    } else {
        s
    })
}

/// Whether two optional floats are the same, bit for bit.
pub fn same_f64(a: Option<f64>, b: Option<f64>) -> bool {
    match (a, b) {
        (Some(a), Some(b)) => a.to_bits() == b.to_bits(),
        (a, b) => a.is_none() && b.is_none(),
    }
}
