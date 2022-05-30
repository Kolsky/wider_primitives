use core::cmp::Ordering;
use core::fmt;
use core::iter;
use crate::ParseIntError;
use crate::Repr;
use crate::array_pair_to_u128;
use crate::uint::*;

#[cfg_attr(stable, path = "../stable_ops/u256.rs")]
#[cfg_attr(unstable, path = "../unstable_ops/u256.rs")]
#[cfg_attr(hide_internal, doc(hidden))]
pub mod impl_ops;

impl iter::Sum for u256 {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |a, b| a + b)
    }
}

impl<'a> iter::Sum<&'a u256> for u256 {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |a, b| a + b)
    }
}

impl iter::Product for u256 {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ONE, |a, b| a * b)
    }
}

impl<'a> iter::Product<&'a u256> for u256 {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::ONE, |a, b| a * b)
    }
}

const N: usize = 4;

macro_rules! typename {
    () => {
        stringify!(u256)
    };
}

macro_rules! typesize {
    () => {
        256
    };
}

macro_rules! min_value {
    () => {
        "0"
    };
}

macro_rules! max_value {
    () => {
        "115792089237316195423570985008687907853269984665640564039457584007913129639935"
    };
}

macro_rules! op_in {
    (rotate_left) => { stringify!([2, 3, 0, 1]) };
    (rotate_right) => { stringify!([2, 4, 6, 0]) };
    (swap_words) => { stringify!([1, 2, 3, 4]) };
    (swap_bytes) => { stringify!("0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20") };
    (reverse_bits) => { stringify!("1234567890123456789012345678901234567890123456789012345678901234") };
}

macro_rules! op_out {
    (rotate_left) => { stringify!([2, 4, 6, 0]) };
    (rotate_right) => { stringify!([2, 3, 0, 1]) };
    (swap_words) => { stringify!([4, 3, 2, 1]) };
    (swap_bytes) => { stringify!("201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201") };
    (reverse_bits) => { stringify!("2c48091e6a2c48091e6a2c48091e6a2c48091e6a2c48091e6a2c48091e6a2c48") };
}

#[allow(non_camel_case_types)]
#[repr(transparent)]
#[derive(Clone, Copy, Hash)]
#[cfg_attr(stable, derive(PartialEq, Eq))]
#[doc = concat!("The ", typesize!(), "-bit unsigned integer type.")]
/// 
/// ## Table of contents
/// 
/// 1. [C3 (Constants, Constructors, Casts)](#impl)
/// 2. [Equality and comparison](#impl-1)
/// 3. [Basic arithmetic operations](#impl-2)
/// 4. [Extended arithmetic operations](#impl-3)
/// 5. [Bit manipulation](#impl-4)
pub struct u256 {
    pub(crate) inner: Repr<N>,
}

impl fmt::Debug for u256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        crate::debug_fmt(&self.inner, typename!(), f, |val, f| val.fmt(f))
    }
}

impl fmt::Display for u256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        crate::fmt_unsigned(&self.inner, f)
    }
}

impl fmt::Binary for u256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        crate::fmt_binary(&self.inner, f)
    }
}

impl fmt::Octal for u256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        crate::fmt_octal(&self.inner, f)
    }
}

impl fmt::LowerHex for u256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        crate::fmt_lower_hex(&self.inner, f)
    }
}

impl fmt::UpperHex for u256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        crate::fmt_upper_hex(&self.inner, f)
    }
}

/// # C3 (Constants, Constructors, Casts)
impl u256 {
    /// The size of this integer type in bits.
    /// 
    /// # Examples
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert_eq!(", typename!(), "::BITS, ", typesize!(), ");")]
    /// ```
    pub const BITS: u32 = Repr::<N>::BITS;

    /// The additive identity.
    /// 
    /// # Examples
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("# let x = ", typename!(), "::from_u64(2479);")]
    #[doc = concat!("assert_eq!(x.add(", typename!(), "::ZERO), x);")]
    #[doc = concat!("assert_eq!(", typename!(), "::ZERO.add(x), x);")]
    /// ```
    pub const ZERO: Self = Self { inner: Repr::ZERO };
    
    /// The multiplicative identity.
    /// 
    /// # Examples
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("# let x = ", typename!(), "::from_u64(2479);")]
    #[doc = concat!("assert_eq!(x.mul(", typename!(), "::ONE), x);")]
    #[doc = concat!("assert_eq!(", typename!(), "::ONE.mul(x), x);")]
    /// ```
    pub const ONE: Self = Self { inner: Repr::ONE };
    
    /// The smallest value that can be represented by this integer type.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let min = ", typename!(), "::from_str_or_panic(\"", min_value!(), "\");")]
    #[doc = concat!("assert_eq!(", typename!(), "::MIN, min);")]
    /// ```
    pub const MIN: Self = Self { inner: Repr::MIN_UNSIGNED };
    
    /// The largest value that can be represented by this integer type,
    #[doc = concat!("2<sup>", typesize!(), "</sup> &minus; 1.")]
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let max = ", typename!(), "::from_str_or_panic(\"", max_value!(), "\");")]
    #[doc = concat!("assert_eq!(", typename!(), "::MAX, max);")]
    /// ```
    pub const MAX: Self = Self { inner: Repr::MAX_UNSIGNED };

    /// Constructs an integer from its inner representation,
    /// which is a low-ordered array of words. The first element
    /// of the array corresponds to the lowest 64 bits, the second
    /// to bits 64..128, and so on.
    /// 
    /// If a word (u64) is little endian, then the type's endianess
    /// would also be the same, but it doesn't hold in general case.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert!(",
        typename!(), "::from_inner(", op_in!(swap_words), 
        ").gt(",
        typename!(), "::from_inner(", op_out!(swap_words),
    ")));")]
    /// ```
    pub const fn from_inner(inner: [u64; N]) -> Self {
        Self { inner: Repr::from_inner(inner) }
    }

    /// Returns inner representation of `self`.
    /// 
    /// This function is an inverse of [`from_inner`](Self::from_inner).
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let swapped = ", typename!(), "::from_inner(", op_in!(swap_words), ").swap_words();")]
    #[doc = concat!("assert_eq!(swapped.into_inner(), ", op_out!(swap_words), ");")]
    /// ```
    pub const fn into_inner(self) -> [u64; N] {
        self.inner.into_inner()
    }

    #[doc = concat!("Constructs [`", typename!(), "`] from [`u8`], without the loss of precision.")]
    ///
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert!(", typename!(), "::from_u8(u8::MAX).lt(", typename!(), "::MAX));")]
    /// ```
    pub const fn from_u8(n: u8) -> Self {
        Self::from_u64(n as u64)
    }

    #[doc = concat!("Constructs [`", typename!(), "`] from [`u16`], without the loss of precision.")]
    ///
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert!(", typename!(), "::from_u16(u16::MAX).lt(", typename!(), "::MAX));")]
    /// ```
    pub const fn from_u16(n: u16) -> Self {
        Self::from_u64(n as u64)
    }

    #[doc = concat!("Constructs [`", typename!(), "`] from [`u32`], without the loss of precision.")]
    ///
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert!(", typename!(), "::from_u32(u32::MAX).lt(", typename!(), "::MAX));")]
    /// ```
    pub const fn from_u32(n: u32) -> Self {
        Self::from_u64(n as u64)
    }

    #[doc = concat!("Constructs [`", typename!(), "`] from [`u64`], without the loss of precision.")]
    ///
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert!(", typename!(), "::from_u64(u64::MAX).lt(", typename!(), "::MAX));")]
    /// ```
    pub const fn from_u64(n: u64) -> Self {
        Self { inner: Repr::from_u64(n) }
    }

    #[doc = concat!("Constructs [`", typename!(), "`] from [`u128`], without the loss of precision.")]
    ///
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert!(", typename!(), "::from_u128(u128::MAX).lt(", typename!(), "::MAX));")]
    /// ```
    pub const fn from_u128(n: u128) -> Self {
        Self { inner: Repr::from_u128(n) }
    }

    /// Converts `self` to [`u384`](crate::u384), without the loss of precision.
    ///
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert!(", typename!(), "::MAX.into_u384().lt(u384::MAX));")]
    /// ```
    pub const fn into_u384(self) -> u384 {
        u384::from_inner(self.inner.as_cast_unsigned().into_inner())
    }
    
    /// Converts `self` to [`u512`](crate::u512), without the loss of precision.
    ///
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert!(", typename!(), "::MAX.into_u512().lt(u512::MAX));")]
    /// ```
    pub const fn into_u512(self) -> u512 {
        u512::from_inner(self.inner.as_cast_unsigned().into_inner())
    }

    /// Casts `self` to [`u8`] based on semantics explained in [The Rust Reference][numeric_cast].
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.as_u8(), u8::MAX);")]
    /// ```
    /// [numeric_cast]: <https://doc.rust-lang.org/reference/expressions/operator-expr.html#numeric-cast>
    pub const fn as_u8(self) -> u8 {
        self.inner.as_u64() as u8
    }

    /// Casts `self` to [`u16`] based on semantics explained in [The Rust Reference][numeric_cast].
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.as_u16(), u16::MAX);")]
    /// ```
    /// [numeric_cast]: <https://doc.rust-lang.org/reference/expressions/operator-expr.html#numeric-cast>
    pub const fn as_u16(self) -> u16 {
        self.inner.as_u64() as u16
    }

    /// Casts `self` to [`u32`] based on semantics explained in [The Rust Reference][numeric_cast].
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.as_u32(), u32::MAX);")]
    /// ```
    /// [numeric_cast]: <https://doc.rust-lang.org/reference/expressions/operator-expr.html#numeric-cast>
    pub const fn as_u32(self) -> u32 {
        self.inner.as_u64() as u32
    }

    /// Casts `self` to [`u64`] based on semantics explained in [The Rust Reference][numeric_cast].
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.as_u64(), u64::MAX);")]
    /// ```
    /// [numeric_cast]: <https://doc.rust-lang.org/reference/expressions/operator-expr.html#numeric-cast>
    pub const fn as_u64(self) -> u64 {
        self.inner.as_u64()
    }

    /// Casts `self` to [`u128`] based on semantics explained in [The Rust Reference][numeric_cast].
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.as_u128(), u128::MAX);")]
    /// ```
    /// [numeric_cast]: <https://doc.rust-lang.org/reference/expressions/operator-expr.html#numeric-cast>
    pub const fn as_u128(self) -> u128 {
        array_pair_to_u128(self.inner.as_cast_unsigned().into_inner())
    }

    /// Casts `self` to [`u256`](crate::u256) based on semantics explained in [The Rust Reference][numeric_cast].
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.as_u256(), u256::MAX);")]
    /// ```
    /// [numeric_cast]: <https://doc.rust-lang.org/reference/expressions/operator-expr.html#numeric-cast>
    pub const fn as_u256(self) -> u256 {
        self
    }

    /// Casts `self` to [`u384`](crate::u384) based on semantics explained in [The Rust Reference][numeric_cast].
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert!(", typename!(), "::MAX.as_u384().lt(u384::MAX));")]
    /// ```
    /// [numeric_cast]: <https://doc.rust-lang.org/reference/expressions/operator-expr.html#numeric-cast>
    pub const fn as_u384(self) -> u384 {
        self.into_u384()
    }

    /// Casts `self` to [`u512`](crate::u512) based on semantics explained in [The Rust Reference][numeric_cast].
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert!(", typename!(), "::MAX.as_u512().lt(u512::MAX));")]
    /// ```
    /// [numeric_cast]: <https://doc.rust-lang.org/reference/expressions/operator-expr.html#numeric-cast>
    pub const fn as_u512(self) -> u512 {
        self.into_u512()
    }

    /// Converts a string slice in a given base to an integer.
    /// 
    /// The string is expected to be an optional `+` sign
    /// followed by digits.
    /// Leading and trailing whitespace represent an error.
    /// Digits are a subset of these characters, depending on `radix`:
    /// 
    /// * `0-9`
    /// * `a-z`
    /// * `A-Z`
    /// 
    /// # Panics
    /// 
    /// This function panics if `radix` is not in the range from 2 to 36.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert_eq!(", typename!(), "::from_str_radix(\"A\", 16), Ok(", typename!(), "::from_u64(10)));")]
    /// ```
    pub const fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntError> {
        match Repr::from_str_radix_unsigned(src, radix) {
            Ok(inner) => Ok(Self { inner }),
            Err(e) => Err(e),
        }
    }
    /// Converts a string slice in a given base to an integer.
    /// 
    /// This is the panicking variant of [`from_str_radix`](Self::from_str_radix).
    /// 
    /// # Panics
    /// 
    /// This function panics if `radix` is not in the range from 2 to 36,
    /// or in case of a parse error due to malformed input.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert_eq!(", typename!(), "::from_str_radix_or_panic(\"A\", 16), ", typename!(), "::from_u64(10));")]
    /// ```
    /// ```should_panic
    /// # use wider_primitives::*;
    #[doc = concat!("let _ = ", typename!(), "::from_str_radix_or_panic(\"-B\", 16);")]
    /// ```
    pub const fn from_str_radix_or_panic(src: &str, radix: u32) -> Self {
        Self { inner: Repr::from_str_radix_or_panic_unsigned(src, radix) }
    }
    
    /// Converts a string slice in a base 10 to an integer.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert_eq!(", typename!(), "::from_str(\"98765432109876543210\"), Ok(", typename!(), "::from_u128(98765432109876543210)));")]
    /// ```
    pub const fn from_str(src: &str) -> Result<Self, ParseIntError> {
        match Repr::from_str_signed(src) {
            Ok(inner) => Ok(Self { inner }),
            Err(e) => Err(e),
        }
    }

    /// Converts a string slice in a base 10 to an integer.
    /// 
    /// # Panics
    /// 
    #[doc = concat!("This function panics whenever [`", typename!(), "::from_str`] would have returned an Err.")]
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert_eq!(", typename!(), "::from_str_or_panic(\"98765432109876543210\"), ", typename!(), "::from_u128(98765432109876543210));")]
    /// ```
    /// ```should_panic
    /// # use wider_primitives::*;
    #[doc = concat!("let _ = ", typename!(), "::from_str_or_panic(\"a\");")]
    /// ```
    pub const fn from_str_or_panic(src: &str) -> Self {
        Self { inner: Repr::from_str_or_panic_unsigned(src) }
    }

    /// Converts a string slice in a base 16 to an integer.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert_eq!(", typename!(), "::from_hex_str(\"98765432109876543210\"), Ok(", typename!(), "::from_u128(0x98765432109876543210)));")]
    /// ```
    pub const fn from_hex_str(src: &str) -> Result<Self, ParseIntError> {
        match Repr::from_hex_str_unsigned(src) {
            Ok(inner) => Ok(Self { inner }),
            Err(e) => Err(e),
        }
    }

    /// Converts a string slice in a base 16 to an integer.
    /// 
    /// # Panics
    /// 
    #[doc = concat!("This function panics whenever [`", typename!(), "::from_hex_str`] would have returned an Err.")]
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert_eq!(", typename!(), "::from_hex_str_or_panic(\"98765432109876543210\"), ", typename!(), "::from_u128(0x98765432109876543210));")]
    /// ```
    /// ```should_panic
    /// # use wider_primitives::*;
    #[doc = concat!("let _ = ", typename!(), "::from_hex_str_or_panic(\"\");")]
    /// ```
    pub const fn from_hex_str_or_panic(src: &str) -> Self {
        Self { inner: Repr::from_hex_str_or_panic_unsigned(src) }
    }
}

/// # Equality and comparison
impl u256 {
    /// Tests if `self == other`.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let (x, y) = (", typename!(), "::ZERO, ", typename!(), "::ONE);")]
    /// 
    /// assert!(x.equals(x));
    /// assert!(!x.equals(y));
    /// ```
    pub const fn equals(self, other: Self) -> bool {
        self.inner.equals(&other.inner)
    }

    /// Returns an [`Ordering`](core::cmp::Ordering)
    /// between `self` and `other`.
    /// 
    /// An implementation of a total comparison 
    /// otherwise known as [`Ord`](core::cmp::Ord).
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// ```
    /// # use wider_primitives::*;
    /// use core::cmp::Ordering;
    #[doc = concat!("let (x, y) = (", typename!(), "::ZERO, ", typename!(), "::ONE);")]
    /// 
    /// assert_eq!(x.compare(y), Ordering::Less);
    /// assert_eq!(y.compare(y), Ordering::Equal);
    /// assert_eq!(y.compare(x), Ordering::Greater);
    /// ```
    pub const fn compare(self, other: Self) -> Ordering {
        self.inner.compare_unsigned(&other.inner)
    }

    /// Shorthand for `self.compare(other).is_lt()`.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let (x, y) = (", typename!(), "::ZERO, ", typename!(), "::ONE);")]
    /// 
    /// assert!(x.lt(y));
    /// ```
    pub const fn lt(self, other: Self) -> bool {
        self.compare(other).is_lt()
    }

    /// Shorthand for `self.compare(other).is_gt()`.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let (x, y) = (", typename!(), "::ZERO, ", typename!(), "::ONE);")]
    /// 
    /// assert!(y.gt(x));
    /// ```
    pub const fn gt(self, other: Self) -> bool {
        self.compare(other).is_gt()
    }

    /// Shorthand for `self.compare(other).is_le()`.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let (x, y) = (", typename!(), "::ZERO, ", typename!(), "::ONE);")]
    /// 
    /// assert!(x.le(y));
    /// assert!(y.le(y));
    /// assert!(!y.le(x));
    /// ```
    pub const fn le(self, other: Self) -> bool {
        self.compare(other).is_le()
    }

    /// Shorthand for `self.compare(other).is_ge()`.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let (x, y) = (", typename!(), "::ZERO, ", typename!(), "::ONE);")]
    /// 
    /// assert!(!x.ge(y));
    /// assert!(y.ge(y));
    /// assert!(y.ge(x));
    /// ```
    pub const fn ge(self, other: Self) -> bool {
        self.compare(other).is_ge()
    }
}

/// # Basic arithmetic operations
impl u256 {
    /// Calculates `self + rhs`.
    /// 
    /// Returns a tuple of the addition along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would
    /// have occurred then the wrapped value is returned.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// assert_eq!(uint(5).overflowing_add(uint(2)), (uint(7), false));
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.overflowing_add(uint(1)), (uint(0), true));")]
    /// ```
    pub const fn overflowing_add(self, rhs: Self) -> (Self, bool) {
        let (inner, overflows) = self.inner.overflowing_add_unsigned(rhs.inner);
        (Self { inner }, overflows)
    }

    /// Checked integer addition. Computes `self + rhs`, returning `None`
    /// if overflow occurred.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    #[doc = concat!(
        "assert_eq!(", typename!(), "::MAX.sub(uint(2)).checked_add(uint(1)), ",
        "Some(", typename!(), "::MAX.sub(uint(1))));"
    )]
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.sub(uint(2)).checked_add(uint(3)), None);")]
    /// ```
    pub const fn checked_add(self, rhs: Self) -> Option<Self> {
        match self.inner.checked_add_unsigned(rhs.inner) {
            Some(inner) => Some(Self { inner }),
            None => None,
        }
    }

    /// Saturating integer addition. Computes `self + rhs`, saturating at
    /// the numeric bounds instead of overflowing.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// assert_eq!(uint(100).saturating_add(uint(1)), uint(101));
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.saturating_add(uint(127)), ", typename!(), "::MAX);")]
    /// ```
    pub const fn saturating_add(self, rhs: Self) -> Self {
        Self { inner: self.inner.saturating_add_unsigned(rhs.inner) }
    }

    /// Wrapping (modular) addition. Computes `self + rhs`,
    /// wrapping around at the boundary of the type.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// assert_eq!(uint(200).wrapping_add(uint(55)), uint(255));
    #[doc = concat!("assert_eq!(uint(200).wrapping_add(", typename!(), "::MAX), uint(199));")]
    /// ```
    pub const fn wrapping_add(self, rhs: Self) -> Self {
        Self { inner: self.inner.wrapping_add(rhs.inner) }
    }

    /// Calculates `self + rhs`.
    /// 
    /// # Overflow behavior
    /// 
    /// This function panics on overflow in debug mode
    /// and wraps around the type boundary in release mode. 
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// assert_eq!(uint(1).add(uint(1)), uint(2));
    pub const fn add(self, rhs: Self) -> Self {
        Self { inner: self.inner.add_unsigned(rhs.inner) }
    }

    /// Calculates `self - rhs`.
    /// 
    /// Returns a tuple of the subtraction along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would
    /// have occurred then the wrapped value is returned.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// assert_eq!(uint(5).overflowing_sub(uint(2)), (uint(3), false));
    #[doc = concat!("assert_eq!(uint(0).overflowing_sub(uint(1)), (", typename!(), "::MAX, true));")]
    /// ```
    pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
        let (inner, overflows) = self.inner.overflowing_sub_unsigned(rhs.inner);
        (Self { inner }, overflows)
    }

    /// Checked integer subtraction. Computes `self - rhs`, returning
    /// `None` if overflow occurred.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// assert_eq!(uint(1).checked_sub(uint(1)), Some(uint(0)));
    /// assert_eq!(uint(0).checked_sub(uint(1)), None);
    /// ```
    pub const fn checked_sub(self, rhs: Self) -> Option<Self> {
        match self.inner.checked_sub_unsigned(rhs.inner) {
            Some(inner) => Some(Self { inner }),
            None => None,
        }
    }

    /// Saturating integer subtraction. Computes `self - rhs`, saturating
    /// at the numeric bounds instead of overflowing.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// assert_eq!(uint(100).saturating_sub(uint(27)), uint(73));
    /// assert_eq!(uint(13).saturating_sub(uint(127)), uint(0));
    /// ```
    pub const fn saturating_sub(self, rhs: Self) -> Self {
        Self { inner: self.inner.saturating_sub_unsigned(rhs.inner) }
    }

    /// Wrapping (modular) subtraction. Computes `self - rhs`,
    /// wrapping around at the boundary of the type.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// assert_eq!(uint(100).wrapping_sub(uint(100)), uint(0));
    #[doc = concat!("assert_eq!(uint(100).wrapping_sub(", typename!(), "::MAX), uint(101));")]
    /// ```
    pub const fn wrapping_sub(self, rhs: Self) -> Self {
        Self { inner: self.inner.wrapping_sub(rhs.inner) }
    }

    /// Calculates `self - rhs`.
    /// 
    /// # Overflow behavior
    /// 
    /// This function panics on overflow in debug mode
    /// and wraps around the type boundary in release mode. 
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// assert_eq!(uint(629).saturating_sub(uint(81)), uint(548));
    /// ```
    pub const fn sub(self, rhs: Self) -> Self {
        Self { inner: self.inner.sub_unsigned(rhs.inner) }
    }

    /// Calculates the multiplication of `self` and `rhs`.
    /// 
    /// Returns a tuple of the multiplication along with u64
    /// containing the high-order (overflowing) bits. If an
    /// overflow would have occurred then the high-order bits
    /// would contain a value not equal to 0 and the wrapped value is returned.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// assert_eq!(uint(5).overflowing_short_mul(2), (uint(10), 0));
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.overflowing_short_mul(10), (", typename!(), "::MAX.sub(uint(9)), 9));")]
    /// ```
    pub const fn overflowing_short_mul(self, rhs: u64) -> (Self, u64) {
        let (inner, overflows) = self.inner.overflowing_short_mul_unsigned(rhs);
        (Self { inner }, overflows)
    }

    /// Checked integer multiplication. Computes `self * rhs`, returning
    /// `None` if overflow occurred.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// assert_eq!(uint(5).checked_short_mul(1), Some(uint(5)));
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.checked_short_mul(2), None);")]
    /// ```
    pub const fn checked_short_mul(self, rhs: u64) -> Option<Self> {
        match self.inner.checked_short_mul_unsigned(rhs) {
            Some(inner) => Some(Self { inner }),
            None => None,
        }
    }

    /// Saturating integer multiplication. Computes `self * rhs`,
    /// saturating at the numeric bounds instead of overflowing.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// assert_eq!(uint(2).saturating_short_mul(10), uint(20));
    #[doc = concat!("assert_eq!((", typename!(), "::MAX).saturating_short_mul(10), ", typename!(), "::MAX);")]
    /// ```
    pub const fn saturating_short_mul(self, rhs: u64) -> Self {
        Self { inner: self.inner.saturating_short_mul_unsigned(rhs) }
    }

    /// Wrapping (modular) multiplication. Computes `self *
    /// rhs`, wrapping around at the boundary of the type.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// assert_eq!(uint(5).wrapping_short_mul(5), uint(25));
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.wrapping_short_mul(2), ", typename!(), "::MAX.sub(uint(1)));")]
    /// ```
    pub const fn wrapping_short_mul(self, rhs: u64) -> Self {
        Self { inner: self.inner.wrapping_short_mul_unsigned(rhs) }
    }

    /// Calculates the multiplication of `self` and `rhs`.
    /// 
    /// # Overflow behavior
    /// 
    /// This function panics on overflow in debug mode
    /// and wraps around the type boundary in release mode. 
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// assert_eq!(uint(91).short_mul(10_000_000), uint(910_000_000));
    /// ```
    pub const fn short_mul(self, rhs: u64) -> Self {
        Self { inner: self.inner.short_mul_unsigned(rhs) }
    }

    /// Calculates the multiplication of `self` and `rhs`.
    /// 
    /// Returns a tuple of the multiplication along with a boolean
    /// indicating whether an arithmetic overflow would occur. If an
    /// overflow would have occurred then the wrapped value is returned.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// assert_eq!(uint(5).overflowing_mul(uint(2)), (uint(10), false));
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.overflowing_mul(uint(10)), (", typename!(), "::MAX.sub(uint(9)), true));")]
    /// ```
    pub const fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
        let (inner, overflows) = self.inner.overflowing_mul_unsigned(rhs.inner);
        (Self { inner }, overflows)
    }

    /// Checked integer multiplication. Computes `self * rhs`, returning
    /// `None` if overflow occurred.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// assert_eq!(uint(5).checked_mul(uint(1)), Some(uint(5)));
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.checked_mul(uint(2)), None);")]
    /// ```
    pub const fn checked_mul(self, rhs: Self) -> Option<Self> {
        match self.inner.checked_mul_unsigned(rhs.inner) {
            Some(inner) => Some(Self { inner }),
            None => None,
        }
    }

    /// Saturating integer multiplication. Computes `self * rhs`,
    /// saturating at the numeric bounds instead of overflowing.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// assert_eq!(uint(2).saturating_mul(uint(10)), uint(20));
    #[doc = concat!("assert_eq!((", typename!(), "::MAX).saturating_mul(uint(10)), ", typename!(), "::MAX);")]
    /// ```
    pub const fn saturating_mul(self, rhs: Self) -> Self {
        Self { inner: self.inner.saturating_mul_unsigned(rhs.inner) }
    }

    /// Wrapping (modular) multiplication. Computes `self *
    /// rhs`, wrapping around at the boundary of the type.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// assert_eq!(uint(5).wrapping_mul(uint(5)), uint(25));
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.wrapping_mul(", typename!(), "::MAX), uint(1));")]
    /// ```
    pub const fn wrapping_mul(self, rhs: Self) -> Self {
        Self { inner: self.inner.wrapping_mul(rhs.inner) }
    }

    /// Calculates the multiplication of `self` and `rhs`.
    /// 
    /// # Overflow behavior
    /// 
    /// This function panics on overflow in debug mode
    /// and wraps around the type boundary in release mode. 
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// assert_eq!(uint(91).mul(uint(10_000_000)), uint(910_000_000));
    /// ```
    pub const fn mul(self, rhs: Self) -> Self {
        Self { inner: self.inner.mul_unsigned(rhs.inner) }
    }

    /// Checked integer division. Computes `self / rhs`, returning `None`
    /// if `rhs == 0`.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(128).checked_short_div(2), Some(uint(64)));
    /// assert_eq!(uint(1).checked_short_div(0), None);
    /// ```
    pub const fn checked_short_div(self, rhs: u64) -> Option<Self> {
        match self.inner.checked_short_div_unsigned(rhs) {
            Some(inner) => Some(Self { inner }),
            None => None,
        }
    }

    /// Calculates the division of `self` and `rhs`.
    /// 
    /// # Panics
    /// 
    /// This function will panic if `rhs` is 0.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(128).short_div(2), uint(64));
    /// ```
    /// ```should_panic
    /// # use wider_primitives::*;
    #[doc = concat!("let _ = ", typename!(), "::ONE.short_div(0);")]
    /// ```
    pub const fn short_div(self, rhs: u64) -> Self {
        Self { inner: self.inner.short_div_unsigned(rhs) }
    }

    /// Checked integer division. Computes `self / rhs`, returning `None`
    /// if `rhs == 0`.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    #[doc = concat!("let y = ", typename!(), "::MAX;")]
    #[doc = concat!("let x = y.clear_bit(", typename!(), "::BITS - 1);")]
    /// 
    /// assert_eq!(y.checked_div(x), Some(uint(2)));
    /// assert_eq!(y.checked_div(uint(0)), None);
    /// ```
    pub const fn checked_div(self, rhs: Self) -> Option<Self> {
        match self.inner.checked_div_unsigned(rhs.inner) {
            Some(inner) => Some(Self { inner }),
            None => None,
        }
    }

    /// Calculates the division of `self` and `rhs`.
    /// 
    /// # Panics
    /// 
    /// This function will panic if `rhs` is 0.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(8).div(uint(3)), uint(2));
    /// ```
    /// ```should_panic
    /// # use wider_primitives::*;
    #[doc = concat!("let _ = ", typename!(), "::ONE.div(", typename!(), "::ZERO);")]
    /// ```
    pub const fn div(self, rhs: Self) -> Self {
        Self { inner: self.inner.div_unsigned(rhs.inner) }
    }

    /// Checked integer remainder. Computes `self % rhs`, returning `None`
    /// if `rhs == 0`.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(128).checked_short_rem(2), Some(0));
    /// assert_eq!(uint(1).checked_short_rem(0), None);
    /// ```
    pub const fn checked_short_rem(self, rhs: u64) -> Option<u64> {
        self.inner.checked_short_rem_unsigned(rhs)
    }

    /// Calculates the remainder of `self` and `rhs`.
    /// 
    /// # Panics
    /// 
    /// This function will panic if `rhs` is 0.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(128).short_rem(2), 0);
    /// ```
    /// ```should_panic
    /// # use wider_primitives::*;
    #[doc = concat!("let _ = ", typename!(), "::ONE.short_rem(0);")]
    /// ```
    pub const fn short_rem(self, rhs: u64) -> u64 {
        self.inner.short_rem_unsigned(rhs)
    }

    /// Checked integer remainder. Computes `self % rhs`, returning `None`
    /// if `rhs == 0`.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    #[doc = concat!("let y = ", typename!(), "::MAX;")]
    #[doc = concat!("let x = y.clear_bit(", typename!(), "::BITS - 1);")]
    /// 
    /// assert_eq!(y.checked_rem(x), Some(uint(1)));
    /// assert_eq!(y.checked_rem(uint(0)), None);
    /// ```
    pub const fn checked_rem(self, rhs: Self) -> Option<Self> {
        match self.inner.checked_rem_unsigned(rhs.inner) {
            Some(inner) => Some(Self { inner }),
            None => None,
        }
    }

    /// Calculates the remainder of `self` and `rhs`.
    /// 
    /// # Panics
    /// 
    /// This function will panic if `rhs` is 0.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(8).rem(uint(3)), uint(2));
    /// ```
    /// ```should_panic
    /// # use wider_primitives::*;
    #[doc = concat!("let _ = ", typename!(), "::ONE.rem(", typename!(), "::ZERO);")]
    /// ```
    pub const fn rem(self, rhs: Self) -> Self {
        Self { inner: self.inner.rem_unsigned(rhs.inner) }
    }
}

/// # Extended arithmetic operations
impl u256 {
    /// Negates self in an overflowing fashion.
    ///
    /// Returns `!self + 1` using wrapping operations to return the value
    /// that represents the negation of this unsigned value. Note that for
    /// positive unsigned values overflow always occurs, but negating 0 does
    /// not overflow.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(0).overflowing_neg(), (uint(0), false));
    /// assert_eq!(uint(2).overflowing_neg(), (uint(2).not().add(uint(1)), true));
    /// ```
    pub const fn overflowing_neg(self) -> (Self, bool) {
        let (inner, overflows) = self.inner.overflowing_neg_unsigned();
        (Self { inner }, overflows)
    }

    /// Checked negation. Computes `-self`, returning `None` unless `self ==
    /// 0`.
    ///
    /// Note that negating any positive integer will overflow.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(0).checked_neg(), Some(uint(0)));
    /// assert_eq!(uint(1).checked_neg(), None);
    /// ```
    pub const fn checked_neg(self) -> Option<Self> {
        match self.inner.checked_neg_unsigned() {
            Some(inner) => Some(Self { inner }),
            None => None,
        }
    }

    /// Wrapping (modular) negation. Computes `-self`,
    /// wrapping around at the boundary of the type.
    ///
    /// Since unsigned types do not have negative equivalents,
    /// all applications of this function will wrap (except for `-0`).
    /// 
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(0).wrapping_neg(), uint(0));
    /// assert_eq!(uint(2).wrapping_neg(), uint(0).wrapping_sub(uint(2)));
    /// ```
    pub const fn wrapping_neg(self) -> Self {
        Self { inner: self.inner.wrapping_neg() }
    }

    /// Computes the absolute difference between `self` and `other`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(100).abs_diff(uint(80)), uint(20));
    /// assert_eq!(uint(100).abs_diff(uint(110)), uint(10));
    /// ```
    pub const fn abs_diff(self, rhs: Self) -> Self {
        Self{ inner: self.inner.abs_diff_unsigned(rhs.inner) }
    }

    /// Calculates the complete product `self * rhs`
    /// without the possibility to overflow.
    /// 
    /// This returns the low-order (wrapping) bits 
    /// and the high-order (overflow) bits of the result 
    /// as two separate values, in that order.
    ///
    /// # Examples
    /// 
    /// Basic usage:
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert_eq!(",
        typename!(), "::MAX.full_mul(", typename!(), "::MAX), \
        (", typename!(), "::ONE, ", typename!(), "::MAX.sub(", typename!(), "::ONE))\
    );")]
    /// ```
    pub const fn full_mul(mut self, mut rhs: Self) -> (Self, Self) {
        (self.inner, rhs.inner) = self.inner.full_mul_unsigned(rhs.inner);
        (self, rhs)
    }

    /// Checked integer division and remainder. Computes `self.short_divrem(rhs)`,
    /// returning `None` if `rhs == 0`.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(128).checked_short_divrem(2), Some((uint(64), 0)));
    /// assert_eq!(uint(1).checked_short_divrem(0), None);
    /// ```
    pub const fn checked_short_divrem(self, rhs: u64) -> Option<(Self, u64)> {
        match self.inner.checked_short_divrem_unsigned(rhs) {
            Some((quot, rem)) => Some((Self { inner: quot }, rem)),
            None => None,
        }
    }

    /// Calculates the division and remainder of `self` and `rhs`.
    /// Slightly more efficient variant of `(self.div(rhs), self.rem(rhs))`
    /// provided for convenience.
    /// 
    /// # Panics
    /// 
    /// This function will panic if `rhs` is 0.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(128).short_divrem(2), (uint(64), 0));
    /// ```
    /// ```should_panic
    /// # use wider_primitives::*;
    #[doc = concat!("let _ = ", typename!(), "::ONE.short_divrem(0);")]
    /// ```
    pub const fn short_divrem(self, rhs: u64) -> (Self, u64) {
        let (quot, rem) = self.inner.short_divrem_unsigned(rhs);
        (Self { inner: quot }, rem)
    }

    /// Checked integer division and remainder. Computes `self.divrem(rhs)`,
    /// returning `None` if `rhs == 0`.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    #[doc = concat!("let y = ", typename!(), "::MAX;")]
    #[doc = concat!("let x = y.clear_bit(", typename!(), "::BITS - 1);")]
    /// 
    /// assert_eq!(y.checked_divrem(x), Some((uint(2), uint(1))));
    /// assert_eq!(y.checked_divrem(uint(0)), None);
    /// ```
    pub const fn checked_divrem(self, rhs: Self) -> Option<(Self, Self)> {
        match self.inner.checked_divrem_unsigned(rhs.inner) {
            Some((quot, rem)) => Some((Self { inner: quot }, Self { inner: rem })),
            None => None,
        }
    }

    /// Calculates the division and remainder of `self` and `rhs`.
    /// Slightly more efficient variant of `(self.div(rhs), self.rem(rhs))`
    /// provided for convenience.
    /// 
    /// # Panics
    /// 
    /// This function will panic if `rhs` is 0.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(8).divrem(uint(3)), (uint(2), uint(2)));
    /// ```
    /// ```should_panic
    /// # use wider_primitives::*;
    #[doc = concat!("let _ = ", typename!(), "::ONE.divrem(", typename!(), "::ZERO);")]
    /// ```
    pub const fn divrem(self, rhs: Self) -> (Self, Self) {
        let (quot, rem) = self.inner.divrem_unsigned(rhs.inner);
        (Self { inner: quot }, Self { inner: rem })
    }

    /// Raises self to the power of `exp`, using exponentiation by squaring.
    ///
    /// Returns a tuple of the exponentiation along with a bool indicating
    /// whether an overflow happened.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(3).overflowing_pow(5), (uint(243), false));
    /// assert_eq!(uint(2).overflowing_pow(512), (uint(0), true));
    /// ```
    pub const fn overflowing_pow(self, rhs: u32) -> (Self, bool) {
        let (inner, overflows) = self.inner.overflowing_pow_unsigned(rhs);
        (Self { inner }, overflows)
    }

    /// Checked exponentiation. Computes `self.pow(exp)`, returning `None` if
    /// overflow occurred.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(2).checked_pow(5), Some(uint(32)));
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.checked_pow(2), None);")]
    /// ```
    pub const fn checked_pow(self, rhs: u32) -> Option<Self> {
        match self.inner.checked_pow_unsigned(rhs) {
            Some(inner) => Some(Self { inner }),
            None => None,
        }
    }

    /// Saturating integer exponentiation. Computes `self.pow(exp)`,
    /// saturating at the numeric bounds instead of overflowing.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(4).saturating_pow(3), uint(64));
    #[doc = concat!("assert_eq!(uint(3).saturating_pow(324), ", typename!(), "::MAX);")]
    /// ```
    pub const fn saturating_pow(self, rhs: u32) -> Self {
        Self { inner: self.inner.saturating_pow_unsigned(rhs) }
    }

    /// Wrapping (modular) exponentiation. Computes `self.pow(exp)`,
    /// wrapping around at the boundary of the type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(3).wrapping_pow(5), uint(243));
    /// assert_eq!(uint(2).wrapping_pow(512), uint(0));
    /// ```
    pub const fn wrapping_pow(self, rhs: u32) -> Self {
        Self { inner: self.inner.wrapping_pow_unsigned(rhs) }
    }

    /// Raises self to the power of `exp`, using exponentiation by squaring.
    /// 
    /// # Overflow behavior
    /// 
    /// This function panics on overflow in debug mode
    /// and wraps around the type boundary in release mode.
    /// 
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(9).pow(9), uint(387_420_489));
    /// ```
    pub const fn pow(self, rhs: u32) -> Self {
        Self { inner: self.inner.pow_unsigned(rhs) }
    }

    /// Returns the tuple pair of smallest power of two greater than or equal
    /// to `self` along with a bool indicating whether an overflow happened.
    /// If the next power of two is greater than the type's maximum value,
    /// the return value is wrapped to `0`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    ///
    /// assert_eq!(uint(2).overflowing_next_power_of_two(), (uint(2), false));
    /// assert_eq!(uint(3).overflowing_next_power_of_two(), (uint(4), false));
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.overflowing_next_power_of_two(), (uint(0), true));")]
    /// ```
    pub const fn overflowing_next_power_of_two(self) -> (Self, bool) {
        let (inner, overflows) = self.inner.overflowing_next_power_of_two();
        (Self { inner }, overflows)
    }

    /// Returns the smallest power of two greater than or equal to `self`.
    /// If the next power of two is greater than the type's maximum value,
    /// `None` is returned, otherwise the power of two is wrapped in `Some`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    ///
    /// assert_eq!(uint(2).checked_next_power_of_two(), Some(uint(2)));
    /// assert_eq!(uint(3).checked_next_power_of_two(), Some(uint(4)));
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.checked_next_power_of_two(), None);")]
    /// ```
    pub const fn checked_next_power_of_two(self) -> Option<Self> {
        match self.inner.checked_next_power_of_two() {
            Some(inner) => Some(Self { inner }),
            None => None,
        }
    }

    /// Returns the smallest power of two greater than or equal to `self`.
    /// If the next power of two is greater than the type's maximum value,
    /// the return value is wrapped to `0`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    ///
    /// assert_eq!(uint(2).wrapping_next_power_of_two(), uint(2));
    /// assert_eq!(uint(3).wrapping_next_power_of_two(), uint(4));
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.wrapping_next_power_of_two(), uint(0));")]
    /// ```
    pub const fn wrapping_next_power_of_two(self) -> Self {
        Self { inner: self.inner.wrapping_next_power_of_two() }
    }

    /// Returns the smallest power of two greater than or equal to `self`.
    /// 
    /// When return value overflows (i.e., `self > (1 << (N-1))` for type
    /// `uN`), it panics in debug mode and the return value is wrapped to 0 in
    /// release mode (the only situation in which method can return 0).
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    ///
    /// assert_eq!(uint(0).next_power_of_two(), uint(1));
    /// assert_eq!(uint(1).next_power_of_two(), uint(1));
    /// assert_eq!(uint(2).next_power_of_two(), uint(2));
    /// assert_eq!(uint(3).next_power_of_two(), uint(4));
    /// ```
    pub const fn next_power_of_two(self) -> Self {
        Self { inner: self.inner.next_power_of_two() }
    }
}

/// # Bit manipulation
impl u256 {
    /// Returns the state of `i`th bit.
    /// 
    /// # Panics
    /// 
    #[doc = concat!("This function panics if <code>bit &gt;= <a href=\"struct.", typename!(), ".html#associatedconstant.BITS\" title=\"Self::BITS\">Self::BITS</a></code>.")]
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    ///
    /// assert_eq!(uint(0b011001).bit(4), true);
    /// assert_eq!(uint(0b011001).bit(5), false);
    /// ```
    pub const fn bit(self, bit: u32) -> bool {
        self.inner.bit(bit)
    }

    /// Returns the integer based of off `self` but with the `i`th bit set to 0.
    /// 
    /// # Panics
    /// 
    #[doc = concat!("This function panics if <code>bit &gt;= <a href=\"struct.", typename!(), ".html#associatedconstant.BITS\" title=\"Self::BITS\">Self::BITS</a></code>.")]
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    ///
    /// assert_eq!(uint(0b011001).clear_bit(4), uint(0b001001));
    /// assert_eq!(uint(0b011001).clear_bit(5), uint(0b011001));
    /// ```
    pub const fn clear_bit(self, bit: u32) -> Self {
        Self { inner: self.inner.clear_bit(bit) }
    }

    /// Flips the `i`th bit of `self`.
    /// 
    /// # Panics
    /// 
    #[doc = concat!("This function panics if <code>bit &gt;= <a href=\"struct.", typename!(), ".html#associatedconstant.BITS\" title=\"Self::BITS\">Self::BITS</a></code>.")]
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    ///
    /// assert_eq!(uint(0b011001).toggle_bit(4), uint(0b001001));
    /// assert_eq!(uint(0b011001).toggle_bit(5), uint(0b111001));
    /// ```
    pub const fn toggle_bit(self, bit: u32) -> Self {
        Self { inner: self.inner.toggle_bit(bit) }
    }

    /// Returns the integer based of off `self` but with the `i`th bit set to 1.
    /// 
    /// # Panics
    /// 
    #[doc = concat!("This function panics if <code>bit &gt;= <a href=\"struct.", typename!(), ".html#associatedconstant.BITS\" title=\"Self::BITS\">Self::BITS</a></code>.")]
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    ///
    /// assert_eq!(uint(0b011001).set_bit(4), uint(0b011001));
    /// assert_eq!(uint(0b011001).set_bit(5), uint(0b111001));
    /// ```
    pub const fn set_bit(self, bit: u32) -> Self {
        Self { inner: self.inner.set_bit(bit) }
    }

    /// Flips each bit of `self`.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let x = ", typename!(), "::from_u64(0b011001).not();")]
    ///
    /// assert!(!x.bit(0) && !x.bit(3) && !x.bit(4));
    #[doc = concat!("assert!(x.bit(1) && x.bit(2) && (5..", typename!(), "::BITS).all(|i| x.bit(i)));")]
    /// ```
    pub const fn not(self) -> Self {
        Self { inner: self.inner.not() }
    }

    /// Computes bitwise `and` between `self` and `rhs`.
    ///
    /// # Examples
    /// 
    /// Basic usage:
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(0b011001).bitand(uint(0b110011)), uint(0b010001));
    /// ```
    pub const fn bitand(self, rhs: Self) -> Self {
        Self { inner: self.inner.bitand(rhs.inner) }
    }

    /// Computes bitwise `or` between `self` and `rhs`.
    ///
    /// # Examples
    /// 
    /// Basic usage:
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(0b011001).bitor(uint(0b110011)), uint(0b111011));
    /// ```
    pub const fn bitor(self, rhs: Self) -> Self {
        Self { inner: self.inner.bitor(rhs.inner) }
    }

    /// Computes bitwise `exclusive or` between `self` and `rhs`.
    ///
    /// # Examples
    /// 
    /// Basic usage:
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(0b011001).bitxor(uint(0b110011)), uint(0b101010));
    /// ```
    pub const fn bitxor(self, rhs: Self) -> Self {
        Self { inner: self.inner.bitxor(rhs.inner) }
    }

    /// Shifts `self` left by `rhs` bits.
    ///
    /// Returns a tuple of the shifted version of `self` along with a boolean
    /// indicating whether the shift value was larger than or equal to the
    /// number of bits. If the shift value is too large, then value is
    /// masked (N-1) where N is the number of bits, and this value is then
    /// used to perform the shift.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(0x1).overflowing_shl(4), (uint(0x10), false));
    /// assert_eq!(uint(0x1).overflowing_shl(1540), (uint(0x10), true));
    /// ```
    pub const fn overflowing_shl(self, rhs: u32) -> (Self, bool) {
        let (inner, overflows) = self.inner.overflowing_shl(rhs);
        (Self { inner }, overflows)
    }

    /// Checked shift left. Computes `self << rhs`, returning `None`
    /// if `rhs` is larger than or equal to the number of bits in `self`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(0x1).checked_shl(4), Some(uint(0x10)));
    #[doc = concat!("assert_eq!(uint(0x1).checked_shl(", typesize!(), "), None);")]
    /// ```
    pub const fn checked_shl(self, rhs: u32) -> Option<Self> {
        match self.inner.checked_shl(rhs) {
            Some(inner) => Some(Self { inner }),
            None => None,
        }
    }

    /// Saturating shift left. Computes `self << rhs`, returning `0`
    /// if `rhs` is larger than or equal to the number of bits in `self`.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(0x1).saturating_shl(4), uint(0x10));
    #[doc = concat!("assert_eq!(uint(0x1).saturating_shl(", typesize!(), "), uint(0));")]
    /// ```
    pub const fn saturating_shl(self, rhs: u32) -> Self {
        Self { inner: self.inner.saturating_shl(rhs) }
    }

    /// Panic-free bitwise shift-left; yields `self << mask(rhs)`,
    /// where `mask` removes any high-order bits of `rhs` that
    /// would cause the shift to exceed the bitwidth of the type.
    ///
    /// Note that this is *not* the same as a rotate-left; the
    /// RHS of a wrapping shift-left is restricted to the range
    /// of the type, rather than the bits shifted out of the LHS
    /// being returned to the other end. The wider integer
    /// types all implement a [`rotate_left`](Self::rotate_left) function,
    /// which may be what you want instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(1).wrapping_shl(7), uint(128));
    /// assert_eq!(uint(1).wrapping_shl(1536), uint(1));
    /// ```
    pub const fn wrapping_shl(self, rhs: u32) -> Self {
        Self { inner: self.inner.wrapping_shl(rhs) }
    }

    /// Shifts `self` left by `rhs` bits.
    /// 
    /// # Overflow behavior
    /// 
    /// This function panics on overflow in debug mode
    /// and wraps around the type boundary in release mode.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(0x1).shl(4), uint(0x10));
    /// ```
    pub const fn shl(self, rhs: u32) -> Self {
        Self { inner: self.inner.shl(rhs) }
    }


    /// Shifts `self` right by `rhs` bits.
    ///
    /// Returns a tuple of the shifted version of `self` along with a boolean
    /// indicating whether the shift value was larger than or equal to the
    /// number of bits. If the shift value is too large, then value is
    /// masked (N-1) where N is the number of bits, and this value is then
    /// used to perform the shift.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(0x10).overflowing_shr(4), (uint(0x1), false));
    /// assert_eq!(uint(0x10).overflowing_shr(1540), (uint(0x1), true));
    /// ```
    pub const fn overflowing_shr(self, rhs: u32) -> (Self, bool) {
        let (inner, overflows) = self.inner.overflowing_shr_unsigned(rhs);
        (Self { inner }, overflows)
    }

    /// Checked shift right. Computes `self >> rhs`, returning `None`
    /// if `rhs` is larger than or equal to the number of bits in `self`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(0x10).checked_shr(4), Some(uint(0x1)));
    #[doc = concat!("assert_eq!(uint(0x10).checked_shr(", typesize!(), "), None);")]
    /// ```
    pub const fn checked_shr(self, rhs: u32) -> Option<Self> {
        match self.inner.checked_shr_unsigned(rhs) {
            Some(inner) => Some(Self { inner }),
            None => None,
        }
    }

    /// Saturating shift right. Computes `self >> rhs`, returning `0`
    /// if `rhs` is larger than or equal to the number of bits in `self`.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(0x10).saturating_shr(4), uint(0x1));
    #[doc = concat!("assert_eq!(uint(0x10).saturating_shl(", typesize!(), "), uint(0));")]
    /// ```
    pub const fn saturating_shr(self, rhs: u32) -> Self {
        Self { inner: self.inner.saturating_shr_unsigned(rhs) }
    }

    /// Panic-free bitwise shift-right; yields `self >> mask(rhs)`,
    /// where `mask` removes any high-order bits of `rhs` that
    /// would cause the shift to exceed the bitwidth of the type.
    ///
    /// Note that this is *not* the same as a rotate-right; the
    /// RHS of a wrapping shift-right is restricted to the range
    /// of the type, rather than the bits shifted out of the LHS
    /// being returned to the other end. The wider integer
    /// types all implement a [`rotate_right`](Self::rotate_right) function,
    /// which may be what you want instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(128).wrapping_shr(7), uint(1));
    /// assert_eq!(uint(128).wrapping_shr(1536), uint(128));
    /// ```
    pub const fn wrapping_shr(self, rhs: u32) -> Self {
        Self { inner: self.inner.wrapping_shr_unsigned(rhs) }
    }

    /// Shifts `self` right by `rhs` bits.
    /// 
    /// # Overflow behavior
    /// 
    /// This function panics on overflow in debug mode
    /// and wraps around the type boundary in release mode.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let uint = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(uint(0x10).shr(4), uint(0x1));
    /// ```
    pub const fn shr(self, rhs: u32) -> Self {
        Self { inner: self.inner.shr_unsigned(rhs) }
    }

    /// Returns the number of ones in the binary representation of `self`.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let n = ", typename!(), "::from_u64(0b01001100);")]
    /// 
    /// assert_eq!(n.count_ones(), 3);
    /// ```
    #[doc(alias = "popcount")]
    #[doc(alias = "popcnt")]
    pub const fn count_ones(self) -> u32 {
        self.inner.count_ones()
    }

    /// Returns the number of zeros in the binary representation of `self`.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.count_zeros(), 0);")]
    /// ```
    pub const fn count_zeros(self) -> u32 {
        self.inner.count_zeros()
    }

    /// Returns the number of leading ones in the binary representation of `self`.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let n = ", typename!(), "::MAX.shr(2).not();")]
    /// 
    /// assert_eq!(n.leading_ones(), 2);
    /// ```
    pub const fn leading_ones(self) -> u32 {
        self.inner.leading_ones()
    }

    /// Returns the number of leading zeros in the binary representation of `self`.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let n = ", typename!(), "::MAX.shr(2);")]
    /// 
    /// assert_eq!(n.leading_zeros(), 2);
    /// ```
    pub const fn leading_zeros(self) -> u32 {
        self.inner.leading_zeros()
    }

    /// Returns the number of trailing ones in the binary representation
    /// of `self`.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let n = ", typename!(), "::from_u64(0b1010111);")]
    /// 
    /// assert_eq!(n.trailing_ones(), 3);
    /// ```
    pub const fn trailing_ones(self) -> u32 {
        self.inner.trailing_ones()
    }

    /// Returns the number of trailing zeros in the binary representation
    /// of `self`.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let n = ", typename!(), "::from_u64(0b0101000);")]
    /// 
    /// assert_eq!(n.trailing_zeros(), 3);
    /// ```
    pub const fn trailing_zeros(self) -> u32 {
        self.inner.trailing_zeros()
    }

    /// Shifts the bits to the left by a specified amount, `n`,
    /// wrapping the truncated bits to the end of the resulting integer.
    /// 
    /// Please note this isn't the same operation as the `<<` shifting operator!
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let n = ", typename!(), "::from_inner(", op_in!(rotate_left), ");")]
    #[doc = concat!("let m = ", typename!(), "::from_inner(", op_out!(rotate_left), ");")]
    /// 
    #[doc = concat!("assert_eq!(n.rotate_left(", 65, "), m);")]
    /// ```
    pub const fn rotate_left(self, rhs: u32) -> Self {
        Self { inner: self.inner.rotate_left(rhs) }
    }

    /// Shifts the bits to the right by a specified amount, `n`,
    /// wrapping the truncated bits to the beginning of the resulting
    /// integer.
    /// 
    /// Please note this isn't the same operation as the `>>` shifting operator!
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let n = ", typename!(), "::from_inner(", op_in!(rotate_right), ");")]
    #[doc = concat!("let m = ", typename!(), "::from_inner(", op_out!(rotate_right), ");")]
    /// 
    #[doc = concat!("assert_eq!(n.rotate_right(", 65, "), m);")]
    /// ```
    pub const fn rotate_right(self, rhs: u32) -> Self {
        Self { inner: self.inner.rotate_right(rhs) }
    }

    /// Reverses the word order of the integer.
    /// Here ‘word’ means an underlying primitive integer type
    /// that the current implementation relies upon. It effectively
    /// reverses the array of words returned by [`into_inner`](Self::into_inner).
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let n = ", typename!(), "::from_inner(", op_in!(swap_words), ");")]
    #[doc = concat!("let m = ", typename!(), "::from_inner(", op_out!(swap_words), ");")]
    /// 
    /// assert_eq!(n.swap_words(), m);
    /// ```
    pub const fn swap_words(self) -> Self {
        Self { inner: self.inner.swap_words() }
    }

    /// Reverses the byte order of the integer.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let n = ", typename!(), "::from_hex_str_or_panic(", op_in!(swap_bytes), ");")]
    #[doc = concat!("let m = ", typename!(), "::from_hex_str_or_panic(", op_out!(swap_bytes), ");")]
    /// 
    /// assert_eq!(n.swap_bytes(), m);
    /// ```
    pub const fn swap_bytes(self) -> Self {
        Self { inner: self.inner.swap_bytes() }
    }

    /// Reverses the order of bits in the integer. The least significant bit becomes the most significant bit,
    ///                 second least-significant bit becomes second most-significant bit, etc.
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("let n = ", typename!(), "::from_hex_str_or_panic(", op_in!(reverse_bits), ");")]
    #[doc = concat!("let m = ", typename!(), "::from_hex_str_or_panic(", op_out!(reverse_bits), ");")]
    /// 
    /// assert_eq!(n.reverse_bits(), m);
    /// ```
    pub const fn reverse_bits(self) -> Self {
        Self { inner: self.inner.reverse_bits() }
    }
}