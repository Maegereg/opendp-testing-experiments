use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::Debug;
use std::ops::{BitAnd, BitOr, Shl, Shr, Sub};

use dashu::integer::IBig;
use dashu::rational::RBig;
use num::{One, Zero};

use crate::domains::Bounds;
use crate::error::Fallible;
#[cfg(feature = "contrib")]
use crate::interactive::Queryable;
use crate::verification::RealModel;
#[cfg(creusot)]
use creusot_std::{
    macros::{ensures, logic, proof_assert, requires, trusted},
    model::DeepModel,
};

use super::ExactIntCast;

/// Returns the length of self, where self is a collection.
///
/// Self is commonly a `Vec` or `HashMap`.
pub trait CollectionSize {
    /// # Proof Definition
    /// For any `value` of type `Self`, returns the size of the collection.
    fn size(&self) -> usize;
}

pub trait CheckAtom: CheckNull + Sized + Clone + PartialEq + Debug + Send + Sync {
    fn is_bounded(&self, _bounds: Bounds<Self>) -> Fallible<bool> {
        fallible!(FailedFunction, "bounds check is not implemented")
    }
    fn check_member(&self, bounds: Option<Bounds<Self>>, nan: bool) -> Fallible<bool> {
        if let Some(bounds) = bounds {
            if !self.is_bounded(bounds)? {
                return Ok(false);
            }
        }
        if !nan && self.is_null() {
            return Ok(false);
        }
        Ok(true)
    }
}

/// Checks if a value is null.
///
/// Since [`crate::domains::AtomDomain`] may or may not contain null values,
/// this trait is necessary for its member check.
pub trait CheckNull {
    /// # Proof Definition
    /// A constant that is true if the type can represent null values.
    const NULLABLE: bool;

    /// # Proof Definition
    /// For any `self` of type `Self`, returns true if null.
    fn is_null(&self) -> bool {
        Self::NULLABLE
    }
}

/// Defines an example NaN value inherent to `Self`.
pub trait HasNull: CheckNull {
    /// # Proof Definition
    /// NULL is a constant such that `Self::is_null(Self::NULL)` is true.
    const NULL: Self;
}

/// ProductOrd is well-defined on types that are Ord on their non-null values.
///
/// The framework provides a way to ensure values are non-null at runtime.
/// This trait should only be used when the framework can rely on these assurances.
/// ProductOrd shares the same interface as Ord, but with a total_ prefix on methods
pub trait ProductOrd: Sized + RealModel {
    /// Ghost model: the order compared by `total_cmp`.
    #[cfg(creusot)]
    #[logic]
    fn ple(self, other: Self) -> bool;

    /// Ghost model: `self` is non-null.
    #[cfg(creusot)]
    #[logic]
    fn non_null(self) -> bool;

    /// Ghost model: any two non-null values are comparable.
    /// `false` for pairs, which are ordered componentwise.
    #[cfg(creusot)]
    #[logic]
    fn total() -> bool;

    /// Lemma: only non-null values are ordered, and each of them is ordered with itself.
    #[cfg(creusot)]
    #[logic]
    #[requires(a.ple(b))]
    #[ensures(result && a.non_null() && b.non_null() && a.ple(a) && b.ple(b))]
    fn ple_refl(a: Self, b: Self) -> bool;

    /// # Proof Definition
    /// For any two values `self` and `other` of type `Self`, returns `Ok(out)` or `Err(e)`.
    /// The implementation returns `Err(e)` if either `self` or `other` are null.
    /// Otherwise `out` is the [`Ordering`] of `self` and `other` as defined by [`PartialOrd`].
    #[cfg_attr(creusot, ensures(match result {
        Ok(Ordering::Less) => self.ple(*other) && !other.ple(*self),
        Ok(Ordering::Equal) => self.ple(*other) && other.ple(*self),
        Ok(Ordering::Greater) => other.ple(*self) && !self.ple(*other),
        Err(_) => true,
    }))]
    #[cfg_attr(creusot, ensures(Self::total() && self.non_null() && other.non_null() ==>
        exists<o: Ordering> result == Ok(o)))]
    fn total_cmp(&self, other: &Self) -> Fallible<Ordering>;

    /// # Proof Definition
    /// For any two values `self` and `other` of type `Self`, returns `Ok(out)` or `Err(e)`.
    /// The implementation returns `Err(e)` if either `self` or `other` are null.
    /// Otherwise returns `Some(out)` where `out` is the greater of `self` and `other` as defined by [`PartialOrd`].
    #[cfg_attr(creusot, ensures(forall<out: Self> result == Ok(out) ==>
        (out == self || out == other) && self.real() <= out.real() && other.real() <= out.real()))]
    // Trusted: `max_by` takes the comparator as a generic `FnOnce`, which has no specification.
    #[cfg_attr(creusot, trusted)]
    fn total_max(self, other: Self) -> Fallible<Self> {
        max_by(self, other, ProductOrd::total_cmp)
    }

    /// # Proof Definition
    /// For any two values `self` and `other` of type `Self`, returns `Ok(out)` or `Err(e)`.
    /// The implementation returns `Err(e)` if either `self` or `other` are null.
    /// Otherwise returns `Some(out)` where `out` is the lesser of `self` and `other` as defined by [`PartialOrd`].
    #[cfg_attr(creusot, trusted)]
    fn total_min(self, other: Self) -> Fallible<Self> {
        min_by(self, other, ProductOrd::total_cmp)
    }

    /// # Proof Definition
    /// For any three values `self`, `min` and `max` of type `Self`, returns `Ok(out)` or `Err(e)`.
    /// The implementation returns `Err(e)` if any of `self`, `min` or `max` are null.
    /// Otherwise returns `Some(out)` where `out` is `min` if $self \lt min$, `max` if $self \gt max$, or else `self`.
    #[cfg_attr(creusot, ensures(forall<out: Self> result == Ok(out) ==>
        out == clamp_log(self, min, max) && min.ple(out) && out.ple(max)))]
    #[cfg_attr(creusot, ensures(
        Self::total() && self.non_null() && min.ple(max) ==> exists<out: Self> result == Ok(out)))]
    fn total_clamp(self, min: Self, max: Self) -> Fallible<Self> {
        #[cfg(creusot)]
        proof_assert!(min.ple(max) ==> Self::ple_refl(min, max));
        if min.total_gt(&max)? {
            return fallible!(FailedFunction, "min cannot be greater than max");
        }
        Ok(if let Ordering::Less = self.total_cmp(&min)? {
            min
        } else if let Ordering::Greater = self.total_cmp(&max)? {
            max
        } else {
            self
        })
    }

    /// # Proof Definition
    /// For any two values `self` and `other` of type `Self`, returns `Ok(out)` or `Err(e)`.
    /// The implementation returns `Err(e)` if either `self` or `other` are null.
    /// Otherwise returns `Ok(out)` where `out` is true if $self \lt other$.
    fn total_lt(&self, other: &Self) -> Fallible<bool> {
        Ok(self.total_cmp(other)?.is_lt())
    }

    /// # Proof Definition
    /// For any two values `self` and `other` of type `Self`, returns `Ok(out)` or `Err(e)`.
    /// The implementation returns `Err(e)` if either `self` or `other` are null.
    /// Otherwise returns `Ok(out)` where `out` is true if $self \le other$.
    fn total_le(&self, other: &Self) -> Fallible<bool> {
        Ok(self.total_cmp(other)?.is_le())
    }

    /// # Proof Definition
    /// For any two values `self` and `other` of type `Self`, returns `Ok(out)` or `Err(e)`.
    /// The implementation returns `Err(e)` if either `self` or `other` are null.
    /// Otherwise returns `Ok(out)` where `out` is true if $self \gt other$.
    #[cfg_attr(creusot, ensures(match result {
        Ok(true) => other.ple(*self) && !self.ple(*other),
        Ok(false) => self.ple(*other),
        Err(_) => true,
    }))]
    #[cfg_attr(creusot, ensures(Self::total() && self.non_null() && other.non_null() ==>
        exists<b: bool> result == Ok(b)))]
    fn total_gt(&self, other: &Self) -> Fallible<bool> {
        Ok(self.total_cmp(other)?.is_gt())
    }

    /// # Proof Definition
    /// For any two values `self` and `other` of type `Self`, returns `Ok(out)` or `Err(e)`.
    /// The implementation returns `Err(e)` if either `self` or `other` are null.
    /// Otherwise returns `Ok(out)` where `out` is true if $self \ge other$.
    fn total_ge(&self, other: &Self) -> Fallible<bool> {
        Ok(self.total_cmp(other)?.is_ge())
    }
}

/// Ghost model of [`ProductOrd::total_clamp`]: `min` if `v` is below `min`, `max` if `v` is above `max`,
/// and otherwise `v`.
#[cfg(creusot)]
#[logic(open)]
pub fn clamp_log<T: ProductOrd>(v: T, min: T, max: T) -> T {
    pearlite! {
        if v.ple(min) && !min.ple(v) { min } else if max.ple(v) && !v.ple(max) { max } else { v }
    }
}

/// Bitwise consts and decompositions for float types.
pub trait FloatBits: Copy + Sized + ExactIntCast<Self::Bits> {
    /// # Proof Definition
    /// An associated type that captures the bit representation of Self.
    type Bits: Copy
        + RealModel
        + One
        + Zero
        + Eq
        + Shr<Output = Self::Bits>
        + Shl<Output = Self::Bits>
        + BitAnd<Output = Self::Bits>
        + BitOr<Output = Self::Bits>
        + Sub<Output = Self::Bits>
        + From<bool>
        + Into<IBig>
        + PartialOrd;
    /// # Proof Definition
    /// A constant equal to the number of bits in exponent.
    const EXPONENT_BITS: Self::Bits;
    /// # Proof Definition
    /// A constant equal to the number of bits in mantissa.
    ///
    /// # Note
    /// This should be equal to Self::MANTISSA_DIGITS - 1, because of the implied leading bit.
    const MANTISSA_BITS: Self::Bits;

    /// # Proof Definition
    /// A constant equal to the bias correction of the exponent.
    const EXPONENT_BIAS: Self::Bits;

    /// # Proof Definition
    /// For any `self` of type `Self`, returns true if `self` is positive, otherwise false.
    #[cfg_attr(creusot, trusted)]
    fn sign(self) -> bool {
        !(self.to_bits() & (Self::Bits::one() << (Self::EXPONENT_BITS + Self::MANTISSA_BITS)))
            .is_zero()
    }

    /// # Proof Definition
    /// For any `self` of type `Self`, returns the bits representing the exponent, without bias correction.
    #[cfg_attr(creusot, trusted)]
    fn raw_exponent(self) -> Self::Bits {
        // (shift the exponent to the rightmost bits) & (mask away everything but the trailing EXPONENT_BITS)
        (self.to_bits() >> Self::MANTISSA_BITS)
            & ((Self::Bits::one() << Self::EXPONENT_BITS) - Self::Bits::one())
    }

    /// # Proof Definition
    /// For any `self` of type `Self`, returns the bits representing the mantissa.
    #[cfg_attr(creusot, trusted)]
    fn mantissa(self) -> Self::Bits {
        // (bits) & (mask away everything but the trailing MANTISSA_BITS)
        self.to_bits() & ((Self::Bits::one() << Self::MANTISSA_BITS) - Self::Bits::one())
    }

    /// # Proof Definition
    /// For any set of arguments, returns the corresponding floating-point number according to IEEE-754.
    ///
    /// # Notes
    /// Assumes that the bits to the left of the bit range of the raw_exponent and mantissa are not set.
    #[cfg_attr(creusot, trusted)]
    fn from_raw_components(sign: bool, raw_exponent: Self::Bits, mantissa: Self::Bits) -> Self {
        // shift the sign to the leading bit
        let sign = Self::Bits::from(sign) << (Self::EXPONENT_BITS + Self::MANTISSA_BITS);
        // shift the exponent to the next EXPONENT_BITS
        let raw_exponent = raw_exponent << Self::MANTISSA_BITS;

        // mantissa is already in place, bit-or them together
        Self::from_bits(sign | raw_exponent | mantissa)
    }

    /// # Proof Definition
    /// For any `self` of type `Self`, decomposes the type into the sign, raw exponent and mantissa.
    fn to_raw_components(self) -> (bool, Self::Bits, Self::Bits) {
        (self.sign(), self.raw_exponent(), self.mantissa())
    }

    /// # Proof Definition
    /// For any `self` of type `Self`, retrieves the corresponding bit representation.
    fn to_bits(self) -> Self::Bits;

    /// # Proof Definition
    /// For any `bits` of the associated `Bits` type, returns the floating-point number corresponding to `bits`.
    fn from_bits(bits: Self::Bits) -> Self;
}

impl<T> CollectionSize for Vec<T> {
    fn size(&self) -> usize {
        self.len()
    }
}

impl<K, V> CollectionSize for HashMap<K, V> {
    #[cfg_attr(creusot, trusted)]
    fn size(&self) -> usize {
        self.len()
    }
}

macro_rules! impl_CheckAtom_number {
    ($($ty:ty)+) => ($(impl CheckAtom for $ty {
        fn is_bounded(&self, bounds: Bounds<Self>) -> Fallible<bool> {
            bounds.member(self)
        }
    })+)
}

impl_CheckAtom_number!(f32 f64 i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize);

#[cfg(feature = "polars")]
impl_CheckAtom_number!(chrono::NaiveDate);
#[cfg(feature = "polars")]
impl_CheckAtom_number!(chrono::NaiveTime);

impl CheckAtom for (f32, f32) {
    fn is_bounded(&self, bounds: Bounds<Self>) -> Fallible<bool> {
        bounds.member(self)
    }
}
impl CheckAtom for (f64, f64) {
    fn is_bounded(&self, bounds: Bounds<Self>) -> Fallible<bool> {
        bounds.member(self)
    }
}
impl_CheckAtom_number!(RBig IBig);

macro_rules! impl_CheckAtom_simple {
    ($($ty:ty)+) => ($(impl CheckAtom for $ty {})+)
}
impl_CheckAtom_simple!(bool String char &str);

macro_rules! impl_CheckNull_for_non_null_able {
    ($($ty:ty),+) => {
        $(impl CheckNull for $ty {
            const NULLABLE: bool = false;
        })+
    }
}
impl_CheckNull_for_non_null_able!(
    u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, bool, String, &str, char, usize, isize
);

#[cfg(feature = "polars")]
impl_CheckNull_for_non_null_able!(chrono::NaiveDate);
#[cfg(feature = "polars")]
impl_CheckNull_for_non_null_able!(chrono::NaiveTime);

impl<T1: CheckNull, T2: CheckNull> CheckNull for (T1, T2) {
    const NULLABLE: bool = T1::NULLABLE || T2::NULLABLE;
    fn is_null(&self) -> bool {
        self.0.is_null() || self.1.is_null()
    }
}
impl<T: CheckNull> CheckNull for Option<T> {
    const NULLABLE: bool = true;

    #[inline]
    fn is_null(&self) -> bool {
        if let Some(v) = self {
            v.is_null()
        } else {
            true
        }
    }
}
macro_rules! impl_CheckNull_for_float {
    ($($ty:ty),+) => {
        $(impl CheckNull for $ty {
            const NULLABLE: bool = true;

            #[inline]
            #[cfg_attr(creusot, creusot_std::macros::trusted)]
            fn is_null(&self) -> bool {<$ty>::is_nan(*self)}
        })+
    }
}
impl_CheckNull_for_float!(f64, f32);
impl CheckNull for RBig {
    const NULLABLE: bool = false;
}
impl CheckNull for IBig {
    const NULLABLE: bool = false;
}
#[cfg(feature = "contrib")]
impl<Q, A> CheckNull for Queryable<Q, A> {
    const NULLABLE: bool = false;
}

// TRAIT HasNull
macro_rules! impl_HasNull_float {
    ($($ty:ty),+) => ($(impl HasNull for $ty {
        const NULL: Self = Self::NAN;
    })+)
}
impl_HasNull_float!(f64, f32);

// TRAIT ProductOrd
macro_rules! impl_ProductOrd_for_ord {
    ($($ty:ty),*) => {$(impl ProductOrd for $ty {
        #[cfg(creusot)]
        #[logic(open)]
        fn ple(self, other: Self) -> bool {
            pearlite! { self.deep_model() <= other.deep_model() }
        }
        #[cfg(creusot)]
        #[logic(open)]
        fn non_null(self) -> bool {
            true
        }
        #[cfg(creusot)]
        #[logic(open)]
        fn total() -> bool {
            true
        }
        #[cfg(creusot)]
        #[logic]
        #[requires(a.ple(b))]
        #[ensures(result && a.non_null() && b.non_null() && a.ple(a) && b.ple(b))]
        fn ple_refl(a: Self, b: Self) -> bool {
            true
        }

        #[cfg_attr(creusot, ensures(match result {
            Ok(Ordering::Less) => self.ple(*other) && !other.ple(*self),
            Ok(Ordering::Equal) => self.ple(*other) && other.ple(*self),
            Ok(Ordering::Greater) => other.ple(*self) && !self.ple(*other),
            Err(_) => true,
        }))]
        #[cfg_attr(creusot, ensures(Self::total() && self.non_null() && other.non_null() ==>
            exists<o: Ordering> result == Ok(o)))]
        fn total_cmp(&self, other: &Self) -> Fallible<Ordering> {Ok(Ord::cmp(self, other))}
    })*}
}
impl_ProductOrd_for_ord!(
    u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
);

impl_ProductOrd_for_ord!(RBig, IBig);

#[cfg(feature = "polars")]
impl_ProductOrd_for_ord!(chrono::NaiveDate);
#[cfg(feature = "polars")]
impl_ProductOrd_for_ord!(chrono::NaiveTime);

macro_rules! impl_total_ord_for_float {
    ($($ty:ty),*) => {
        $(impl ProductOrd for $ty {
            // `<=` on floats: NaN is null, and is not ordered with anything.
            #[cfg(creusot)]
            #[logic(opaque)]
            fn ple(self, _other: Self) -> bool {
                dead
            }
            #[cfg(creusot)]
            #[logic(opaque)]
            fn non_null(self) -> bool {
                dead
            }
            #[cfg(creusot)]
            #[logic(open)]
            fn total() -> bool {
                true
            }
            // Trusted: `ple` is uninterpreted (IEEE `<=` is reflexive except on NaN, which it never orders).
            #[cfg(creusot)]
            #[trusted]
            #[logic(opaque)]
            #[requires(a.ple(b))]
            #[ensures(result && a.non_null() && b.non_null() && a.ple(a) && b.ple(b))]
            fn ple_refl(a: Self, b: Self) -> bool {
                dead
            }

            // Trusted: floats have no sound `DeepModel` (IEEE equality is not logical equality).
            #[cfg_attr(creusot, creusot_std::macros::trusted)]
            #[cfg_attr(creusot, ensures(match result {
                Ok(Ordering::Less) => self.ple(*other) && !other.ple(*self),
                Ok(Ordering::Equal) => self.ple(*other) && other.ple(*self),
                Ok(Ordering::Greater) => other.ple(*self) && !self.ple(*other),
                Err(_) => true,
            }))]
            #[cfg_attr(creusot, ensures(Self::total() && self.non_null() && other.non_null() ==>
                exists<o: Ordering> result == Ok(o)))]
            fn total_cmp(&self, other: &Self) -> Fallible<Ordering> {
                PartialOrd::partial_cmp(self, other)
                    .ok_or_else(|| err!(FailedFunction, concat!(stringify!($ty), " cannot not be null when clamping.")))
            }
        })*
    }
}
impl_total_ord_for_float!(f64, f32);

#[cfg_attr(creusot, trusted)]
fn max_by<T, F: FnOnce(&T, &T) -> Fallible<Ordering>>(v1: T, v2: T, compare: F) -> Fallible<T> {
    compare(&v1, &v2).map(|cmp| match cmp {
        Ordering::Less | Ordering::Equal => v2,
        Ordering::Greater => v1,
    })
}

#[cfg_attr(creusot, trusted)]
fn min_by<T, F: FnOnce(&T, &T) -> Fallible<Ordering>>(v1: T, v2: T, compare: F) -> Fallible<T> {
    compare(&v1, &v2).map(|cmp| match cmp {
        Ordering::Less | Ordering::Equal => v1,
        Ordering::Greater => v2,
    })
}

impl<T1: ProductOrd + Debug, T2: ProductOrd + Debug> ProductOrd for (T1, T2) {
    #[cfg(creusot)]
    #[logic(open)]
    fn ple(self, other: Self) -> bool {
        pearlite! { self.0.ple(other.0) && self.1.ple(other.1) }
    }
    #[cfg(creusot)]
    #[logic(open)]
    fn non_null(self) -> bool {
        pearlite! { self.0.non_null() && self.1.non_null() }
    }
    #[cfg(creusot)]
    #[logic(open)]
    fn total() -> bool {
        false
    }
    #[cfg(creusot)]
    #[logic]
    #[requires(a.ple(b))]
    #[ensures(result && a.non_null() && b.non_null() && a.ple(a) && b.ple(b))]
    fn ple_refl(a: Self, b: Self) -> bool {
        T1::ple_refl(a.0, b.0) && T2::ple_refl(a.1, b.1)
    }

    #[cfg_attr(creusot, ensures(match result {
        Ok(Ordering::Less) => self.ple(*other) && !other.ple(*self),
        Ok(Ordering::Equal) => self.ple(*other) && other.ple(*self),
        Ok(Ordering::Greater) => other.ple(*self) && !self.ple(*other),
        Err(_) => true,
    }))]
    #[cfg_attr(creusot, ensures(Self::total() && self.non_null() && other.non_null() ==>
        exists<o: Ordering> result == Ok(o)))]
    fn total_cmp(&self, other: &Self) -> Fallible<Ordering> {
        use Ordering::*;
        Ok(
            match (self.0.total_cmp(&other.0)?, self.1.total_cmp(&other.1)?) {
                (Equal, Equal) => Equal,
                (Less | Equal, Less | Equal) => Less,
                (Greater | Equal, Greater | Equal) => Greater,
                _ => {
                    return fallible!(
                        FailedFunction,
                        "unknown ordering between {:?} and {:?}",
                        self,
                        other
                    );
                }
            },
        )
    }
}

// TRAIT FloatBits
impl FloatBits for f64 {
    type Bits = u64;
    const EXPONENT_BITS: u64 = 11;
    const MANTISSA_BITS: u64 = 52;
    const EXPONENT_BIAS: u64 = 1023;

    #[cfg_attr(creusot, trusted)]
    fn to_bits(self) -> Self::Bits {
        self.to_bits()
    }
    #[cfg_attr(creusot, trusted)]
    fn from_bits(bits: Self::Bits) -> Self {
        Self::from_bits(bits)
    }
}

impl FloatBits for f32 {
    type Bits = u32;
    const EXPONENT_BITS: u32 = 8;
    const MANTISSA_BITS: u32 = 23;
    const EXPONENT_BIAS: u32 = 127;

    #[cfg_attr(creusot, trusted)]
    fn to_bits(self) -> Self::Bits {
        self.to_bits()
    }
    #[cfg_attr(creusot, trusted)]
    fn from_bits(bits: Self::Bits) -> Self {
        Self::from_bits(bits)
    }
}

#[allow(dead_code)]
#[cfg_attr(creusot, trusted)]
/// # Proof Definition
/// Return the minimum of `a` and `b` if both are `Some`,
/// or the `Some` value if only one is `Some`.
pub(crate) fn option_min<T: PartialOrd>(a: Option<T>, b: Option<T>) -> Option<T> {
    match (a, b) {
        (Some(a), Some(b)) => match a.partial_cmp(&b) {
            None => None,
            Some(std::cmp::Ordering::Greater) => Some(b),
            _ => Some(a),
        },
        (Some(x), _) | (_, Some(x)) => Some(x),
        _ => None,
    }
}
