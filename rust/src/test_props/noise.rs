//! Shared helpers for property tests of noise-adding measurements,
//! such as `make_laplace` and `make_gaussian`.
//!
//! Every such mechanism maps each input value `x` to an integer index `z`
//! (the multiple `z * 2^k` of the granularity `2^k` nearest to `x`, or `x` itself for integers),
//! adds integer noise to `z`, and maps the result back into the atomic type.
//! [`NoiseAtom`] gives exact references for each of these steps.

use std::fmt::Debug;

use dashu::integer::IBig;
use dashu::rational::RBig;

use super::*;
use crate::domains::AtomDomain;
use crate::traits::CheckAtom;

/// Noise scales: mostly valid (including `±0.0`, the smallest subnormal and `f64::MAX`),
/// sometimes invalid (negative, NaN or infinite).
pub(crate) fn scale() -> impl Strategy<Value = f64> {
    prop_oneof![
        3 => prop::sample::select(vec![0.0, -0.0, f64::from_bits(1), 1.0, f64::MAX]),
        6 => (-10f64..20.).prop_map(|e| e.exp2()),
        1 => prop::sample::select(vec![
            -1.0,
            -f64::from_bits(1),
            f64::NAN,
            f64::INFINITY,
            f64::NEG_INFINITY
        ]),
    ]
}

/// Granularity exponents `k` for float atoms whose smallest granularity is `2^k_min`:
/// the default, values at and just below `k_min`, moderate values,
/// values large enough that rounding `MAX` overflows, and `i32::MIN`.
pub(crate) fn granularity(k_min: i32) -> impl Strategy<Value = Option<i32>> {
    prop_oneof![
        3 => Just(None),
        3 => (k_min..k_min + 3).prop_map(Some),
        1 => (k_min - 3..k_min).prop_map(Some),
        2 => (-60..60).prop_map(Some),
        1 => (900..1100).prop_map(Some),
        1 => Just(Some(i32::MIN)),
    ]
}

/// Floats at or one step either side of a midpoint `(m + 1/2) 2^k` between multiples of `2^k`,
/// where rounding to the granularity moves values the furthest.
/// Falls back to [`float_value`] when `k` is outside `[T::K_MIN, 1100]`.
pub(crate) fn tie_value<T: PropFloat>(k: i32) -> BoxedStrategy<T> {
    if !(T::K_MIN..=1100).contains(&k) {
        return float_value::<T>().boxed();
    }
    (
        prop_oneof![-8i64..8, any::<i32>().prop_map(i64::from)],
        // just below a tie is the worst case: it rounds down, while the tie rounds up
        prop_oneof![2 => Just(-1i8), 1 => Just(0), 1 => Just(1)],
    )
        .prop_map(move |(m, step)| {
            let tie = mul_2k(
                &(RBig::from(m) + RBig::from_parts(IBig::ONE, 2u8.into())),
                k,
            );
            let v = T::from_rational(tie);
            match step {
                -1 => v.next_down(),
                1 => v.next_up(),
                _ => v,
            }
        })
        .boxed()
}

/// Atomic types that noise can be added to, with exact references for each step of the mechanism.
pub(crate) trait NoiseAtom: CheckAtom + ExactRat + Clone + Debug + 'static {
    /// Whether the type has NaN, so that domains may contain it.
    const HAS_NAN: bool;

    /// Whether the mechanism accepts the granularity `k`, given whether the input size is known.
    fn k_ok(k: Option<i32>, known_size: bool) -> bool;
    /// The granularity exponent the mechanism uses when given `k`. Integers always use `0`.
    fn k_eff(k: Option<i32>) -> i32;
    /// The smallest granularity exponent the type supports. Integers use `0`.
    fn k_min() -> i32;
    /// Granularities to construct mechanisms with, valid or not.
    fn granularity() -> BoxedStrategy<Option<i32>>;

    /// The element domain, which may contain NaN only when `nan` is set and the type has NaN.
    fn element_domain(nan: bool) -> AtomDomain<Self>;
    /// Arbitrary values in the non-NaN domain, biased towards rounding ties at granularity `2^k`.
    fn value(k: i32) -> BoxedStrategy<Self>;
    /// Values at or next to rounding ties at granularity `2^k`, where they exist.
    fn near_tie(k: i32) -> BoxedStrategy<Self> {
        Self::value(k)
    }
    /// The adjacent value above (`up`) or below `self`, saturating at the edges of the type.
    fn nudge(&self, up: bool) -> Self;
    /// The smallest value that rounds to the next multiple of `2^k` above the one `self` rounds to,
    /// so that rounding moves the two values apart by nearly `2^k` more than they differ.
    fn across_tie(&self, k: i32) -> Self {
        let _ = k;
        self.nudge(true)
    }

    /// The index `z` of the multiple `z * 2^k` the mechanism adds noise to.
    fn shift(&self, k: i32) -> IBig;
    /// The release when the noise is zero, for index `z`.
    fn release(z: &IBig, k: i32) -> Self;
    /// Whether `self` is within `bound` of `center`, allowing for rounding into the type.
    fn near(&self, center: &RBig, bound: &RBig) -> bool;
    /// Exact equality, distinguishing `-0.0` from `0.0`.
    fn same(&self, other: &Self) -> bool;
    /// Whether `self` is NaN.
    fn is_nan(&self) -> bool;
}

macro_rules! impl_noise_atom_int {
    ($($ty:ty)+) => {$(
        impl NoiseAtom for $ty {
            const HAS_NAN: bool = false;
            fn k_ok(k: Option<i32>, _known_size: bool) -> bool {
                k.unwrap_or(0) == 0
            }
            fn k_eff(_k: Option<i32>) -> i32 {
                0
            }
            fn k_min() -> i32 {
                0
            }
            fn granularity() -> BoxedStrategy<Option<i32>> {
                prop_oneof![
                    3 => Just(None),
                    2 => Just(Some(0)),
                    1 => (-3..=3).prop_map(Some),
                    1 => Just(Some(i32::MIN)),
                ]
                .boxed()
            }
            fn element_domain(_nan: bool) -> AtomDomain<Self> {
                AtomDomain::default()
            }
            fn value(_k: i32) -> BoxedStrategy<Self> {
                int_value::<$ty>().boxed()
            }
            fn nudge(&self, up: bool) -> Self {
                if up { self.saturating_add(1) } else { self.saturating_sub(1) }
            }
            fn shift(&self, _k: i32) -> IBig {
                big(*self)
            }
            fn release(z: &IBig, _k: i32) -> Self {
                from_big(clamp_big::<$ty>(z.clone())).unwrap()
            }
            fn near(&self, center: &RBig, bound: &RBig) -> bool {
                abs_rat(self.exact().unwrap() - center) <= *bound
            }
            fn same(&self, other: &Self) -> bool {
                self == other
            }
            fn is_nan(&self) -> bool {
                false
            }
        }
    )+};
}
impl_noise_atom_int!(u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize);

impl NoiseAtom for IBig {
    const HAS_NAN: bool = false;
    fn k_ok(k: Option<i32>, _known_size: bool) -> bool {
        k.unwrap_or(0) == 0
    }
    fn k_eff(_k: Option<i32>) -> i32 {
        0
    }
    fn k_min() -> i32 {
        0
    }
    fn granularity() -> BoxedStrategy<Option<i32>> {
        <i8 as NoiseAtom>::granularity()
    }
    fn element_domain(_nan: bool) -> AtomDomain<Self> {
        AtomDomain::default()
    }
    fn value(_k: i32) -> BoxedStrategy<Self> {
        prop_oneof![
            int_value::<i64>().prop_map(IBig::from),
            // beyond the range of every primitive integer
            (any::<i128>(), any::<i128>()).prop_map(|(a, b)| IBig::from(a) * IBig::from(b)),
        ]
        .boxed()
    }
    fn nudge(&self, up: bool) -> Self {
        if up {
            self + IBig::ONE
        } else {
            self - IBig::ONE
        }
    }
    fn shift(&self, _k: i32) -> IBig {
        self.clone()
    }
    fn release(z: &IBig, _k: i32) -> Self {
        z.clone()
    }
    fn near(&self, center: &RBig, bound: &RBig) -> bool {
        abs_rat(RBig::from(self.clone()) - center) <= *bound
    }
    fn same(&self, other: &Self) -> bool {
        self == other
    }
    fn is_nan(&self) -> bool {
        false
    }
}

macro_rules! impl_noise_atom_float {
    ($($ty:ty)+) => {$(
        impl NoiseAtom for $ty {
            const HAS_NAN: bool = true;
            fn k_ok(k: Option<i32>, known_size: bool) -> bool {
                let k_min = <$ty as PropFloat>::K_MIN;
                match k {
                    None => true,
                    Some(k) => k != i32::MIN && k >= k_min && (k == k_min || known_size),
                }
            }
            fn k_eff(k: Option<i32>) -> i32 {
                k.unwrap_or(<$ty as PropFloat>::K_MIN)
            }
            fn k_min() -> i32 {
                <$ty as PropFloat>::K_MIN
            }
            fn granularity() -> BoxedStrategy<Option<i32>> {
                granularity(<$ty as PropFloat>::K_MIN).boxed()
            }
            fn element_domain(nan: bool) -> AtomDomain<Self> {
                if nan { AtomDomain::default() } else { AtomDomain::new_non_nan() }
            }
            fn value(k: i32) -> BoxedStrategy<Self> {
                prop_oneof![float_value::<$ty>(), tie_value::<$ty>(k)].boxed()
            }
            fn nudge(&self, up: bool) -> Self {
                // `next_up(MAX)` is infinite, which is still in the domain
                if up { PropFloat::next_up(*self) } else { PropFloat::next_down(*self) }
            }
            fn near_tie(k: i32) -> BoxedStrategy<Self> {
                tie_value::<$ty>(k)
            }
            fn across_tie(&self, k: i32) -> Self {
                if !(<$ty as PropFloat>::K_MIN..=1100).contains(&k) {
                    return self.nudge(true);
                }
                // ties round up, so the tie itself rounds to the next multiple
                let tie = mul_2k(&(RBig::from(self.shift(k)) + RBig::from_parts(IBig::ONE, 2u8.into())), k);
                let v = <$ty>::from_rational(tie.clone());
                if rat(v).is_some_and(|e| e < tie) { PropFloat::next_up(v) } else { v }
            }
            fn shift(&self, k: i32) -> IBig {
                // infinities are clamped to the largest finite values
                let x = self.clamp(<$ty>::MIN, <$ty>::MAX);
                round_to_2k(&rat(x).unwrap(), k)
            }
            fn release(z: &IBig, k: i32) -> Self {
                <$ty>::from_rational(mul_2k(&RBig::from(z.clone()), k))
            }
            fn near(&self, center: &RBig, bound: &RBig) -> bool {
                match rat(*self) {
                    // nearest rounding moves a value by at most epsilon of its magnitude
                    Some(e) => {
                        let slack = abs_rat(e.clone()) * rat(<$ty>::EPSILON).unwrap();
                        abs_rat(e - center) <= bound.clone() + slack
                    }
                    // saturating to infinity requires a value of at least half of MAX
                    None => {
                        let center = if *self > 0.0 { center.clone() } else { -center.clone() };
                        center + bound >= rat(<$ty>::MAX).unwrap() / RBig::from(2)
                    }
                }
            }
            fn same(&self, other: &Self) -> bool {
                self.to_bits() == other.to_bits()
            }
            fn is_nan(&self) -> bool {
                <$ty>::is_nan(*self)
            }
        }
    )+};
}
impl_noise_atom_float!(f32 f64);

/// Bins for a chi-square test of discrete Laplace noise with the given `scale`,
/// over `n` samples: returns `w` and the probabilities of noise in
/// `(-∞, -w], -w + 1, ..., w - 1, [w, ∞)`, as wide as keeps every expected count at least 5.
/// See [`histogram`].
pub(crate) fn discrete_laplace_probs(scale: f64, n: usize) -> (i64, Vec<f64>) {
    let a = (-1.0 / scale).exp();
    let pmf = |z: i64| (1.0 - a) / (1.0 + a) * a.powi(z.abs() as i32);
    // P(Z >= w) for w >= 1
    let tail = |w: i64| a.powi(w as i32) / (1.0 + a);
    let enough = |p: f64| p * n as f64 >= 5.0;
    let mut w = 1;
    while enough(pmf(w)) && enough(tail(w + 1)) {
        w += 1;
    }
    let probs = (-w..=w)
        .map(|z| if z.abs() == w { tail(w) } else { pmf(z) })
        .collect();
    (w, probs)
}

/// Counts of `noise` in the bins of [`discrete_laplace_probs`].
pub(crate) fn histogram(noise: &[IBig], w: i64) -> Vec<u64> {
    let mut counts = vec![0u64; 2 * w as usize + 1];
    for z in noise {
        let z = i64::try_from(z.clone()).unwrap_or(i64::MAX).clamp(-w, w);
        counts[(z + w) as usize] += 1;
    }
    counts
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_noise_atom_references() {
        // ties round up, and infinities are clamped first
        assert_eq!(0.5f64.shift(0), IBig::ONE);
        assert_eq!((-0.5f64).shift(0), IBig::ZERO);
        assert_eq!(
            f64::INFINITY.shift(f64::K_MIN),
            round_to_2k(&rat(f64::MAX).unwrap(), f64::K_MIN)
        );
        assert!(f64::release(&IBig::ONE, f64::K_MIN).same(&f64::from_bits(1)));
        assert_eq!(f64::release(&IBig::ONE, 1024), f64::INFINITY);
        assert_eq!(u8::release(&IBig::from(-3), 0), 0);
        assert_eq!(i8::release(&IBig::from(300), 0), 127);

        assert_eq!(0.4f64.across_tie(0), 0.5);
        assert_eq!(1.75f64.across_tie(-1), 2.25);
        assert_eq!(3i32.across_tie(0), 4);
        assert!(f64::K_MIN == <f64 as NoiseAtom>::k_eff(None));
        assert!(<f32 as NoiseAtom>::k_ok(Some(-149), false));
        assert!(!<f32 as NoiseAtom>::k_ok(Some(-148), false));
        assert!(<f32 as NoiseAtom>::k_ok(Some(-148), true));
        assert!(!<i32 as NoiseAtom>::k_ok(Some(1), true));
    }

    #[test]
    fn test_discrete_laplace_probs() {
        let (w, probs) = discrete_laplace_probs(1.0, 10_000);
        assert_eq!(probs.len(), 2 * w as usize + 1);
        assert!((probs.iter().sum::<f64>() - 1.0).abs() < 1e-12);
        assert!(probs.iter().all(|p| p * 10_000.0 >= 5.0));
        assert_eq!(
            histogram(&[IBig::from(-100), IBig::ZERO, IBig::from(100)], w),
            [
                vec![1],
                vec![0; w as usize - 1],
                vec![1],
                vec![0; w as usize - 1],
                vec![1]
            ]
            .concat()
        );
    }
}
