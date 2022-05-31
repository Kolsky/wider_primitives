use core::cmp::Ordering;
use core::fmt;
// use core::iter;
use crate::ParseIntError;
use crate::Repr;
use crate::array_pair_to_u128;
use crate::int::*;
use crate::uint::u256;

// #[cfg_attr(stable, path = "../stable_ops/i256.rs")]
// #[cfg_attr(unstable, path = "../unstable_ops/i256.rs")]
// #[cfg_attr(hide_internal, doc(hidden))]
// pub mod impl_ops;

// impl iter::Sum for i256 {
//     fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
//         iter.fold(Self::ZERO, |a, b| a + b)
//     }
// }

// impl<'a> iter::Sum<&'a i256> for i256 {
//     fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
//         iter.fold(Self::ZERO, |a, b| a + b)
//     }
// }

// impl iter::Product for i256 {
//     fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
//         iter.fold(Self::ONE, |a, b| a * b)
//     }
// }

// impl<'a> iter::Product<&'a i256> for i256 {
//     fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
//         iter.fold(Self::ONE, |a, b| a * b)
//     }
// }

const N: usize = 4;

macro_rules! typename {
    () => {
        stringify!(i256)
    };
}

macro_rules! utypename {
    () => {
        stringify!(u256)
    };
}

macro_rules! typesize {
    () => {
        256
    };
}

macro_rules! sign_bit {
    () => {
        255
    };
}

macro_rules! min_value {
    () => {
        "-57896044618658097711785492504343953926634992332820282019728792003956564819968"
    };
}

macro_rules! max_value {
    () => {
        "57896044618658097711785492504343953926634992332820282019728792003956564819967"
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
#[cfg_attr(stable, derive(PartialEq, Eq, Default))]
#[doc = concat!("The ", typesize!(), "-bit signed integer type.")]
/// 
/// ## Table of contents
/// 
/// 1. [C3 (Constants, Constructors, Casts)](#impl)
/// 2. [Equality and comparison](#impl-1)
/// 3. [Basic arithmetic operations](#impl-2)
/// 4. [Extended arithmetic operations](#impl-3)
/// 5. [Bit manipulation](#impl-4)
pub struct i256 {
    pub(crate) inner: Repr<N>,
}

impl fmt::Debug for i256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        crate::debug_fmt(&self.inner, typename!(), f, |val, f| val.fmt(f))
    }
}

impl fmt::Display for i256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        crate::fmt_signed(&self.inner, f)
    }
}

impl fmt::Binary for i256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        crate::fmt_binary(&self.inner, f)
    }
}

impl fmt::Octal for i256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        crate::fmt_octal(&self.inner, f)
    }
}

impl fmt::LowerHex for i256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        crate::fmt_lower_hex(&self.inner, f)
    }
}

impl fmt::UpperHex for i256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        crate::fmt_upper_hex(&self.inner, f)
    }
}

/// # C3 (Constants, Constructors, Casts)
impl i256 {
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
    
    /// The additive inverse of [`ONE`](Self::ONE).
    /// 
    /// # Examples
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert_eq!(", typename!(), "::ONE.add(", typename!(), "::MINUS_ONE), ", typename!(), "::ZERO);")]
    /// ```
    pub const MINUS_ONE: Self = Self { inner: Repr::MINUS_ONE };
    
    /// The smallest value that can be represented by this integer type,
    #[doc = concat!("&minus;2<sup>", sign_bit!(), "</sup>.")]
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
    pub const MIN: Self = Self { inner: Repr::MIN_SIGNED };
    
    /// The largest value that can be represented by this integer type,
    #[doc = concat!("2<sup>", sign_bit!(), "</sup> &minus; 1.")]
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
    pub const MAX: Self = Self { inner: Repr::MAX_SIGNED };

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

    #[doc = concat!("Constructs [`", typename!(), "`] from [`i8`], without the loss of precision.")]
    ///
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert!(", typename!(), "::from_i8(i8::MAX).lt(", typename!(), "::MAX));")]
    #[doc = concat!("assert!(", typename!(), "::from_i8(i8::MIN).gt(", typename!(), "::MIN));")]
    /// ```
    pub const fn from_i8(n: i8) -> Self {
        Self::from_i64(n as i64)
    }

    #[doc = concat!("Constructs [`", typename!(), "`] from [`i16`], without the loss of precision.")]
    ///
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert!(", typename!(), "::from_i16(i16::MAX).lt(", typename!(), "::MAX));")]
    #[doc = concat!("assert!(", typename!(), "::from_i16(i16::MIN).gt(", typename!(), "::MIN));")]
    /// ```
    pub const fn from_i16(n: i16) -> Self {
        Self::from_i64(n as i64)
    }

    #[doc = concat!("Constructs [`", typename!(), "`] from [`i32`], without the loss of precision.")]
    ///
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert!(", typename!(), "::from_i32(i32::MAX).lt(", typename!(), "::MAX));")]
    #[doc = concat!("assert!(", typename!(), "::from_i32(i32::MIN).gt(", typename!(), "::MIN));")]
    /// ```
    pub const fn from_i32(n: i32) -> Self {
        Self::from_i64(n as i64)
    }

    #[doc = concat!("Constructs [`", typename!(), "`] from [`i64`], without the loss of precision.")]
    ///
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert!(", typename!(), "::from_i64(i64::MAX).lt(", typename!(), "::MAX));")]
    #[doc = concat!("assert!(", typename!(), "::from_i64(i64::MIN).gt(", typename!(), "::MIN));")]
    /// ```
    pub const fn from_i64(n: i64) -> Self {
        Self { inner: Repr::from_i64(n) }
    }

    #[doc = concat!("Constructs [`", typename!(), "`] from [`i128`], without the loss of precision.")]
    ///
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert!(", typename!(), "::from_i128(i128::MAX).lt(", typename!(), "::MAX));")]
    #[doc = concat!("assert!(", typename!(), "::from_i128(i128::MIN).gt(", typename!(), "::MIN));")]
    /// ```
    pub const fn from_i128(n: i128) -> Self {
        Self { inner: Repr::from_i128(n) }
    }
    
    /// Converts `self` to [`i384`](crate::i384), without the loss of precision.
    ///
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert!(", typename!(), "::MAX.into_i384().lt(i384::MAX));")]
    #[doc = concat!("assert!(", typename!(), "::MIN.into_i384().gt(i384::MIN));")]
    /// ```
    pub const fn into_i384(self) -> i384 {
        i384::from_inner(self.inner.as_cast_signed().into_inner())
    }
    
    /// Converts `self` to [`i512`](crate::i512), without the loss of precision.
    ///
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert!(", typename!(), "::MAX.into_i512().lt(i512::MAX));")]
    #[doc = concat!("assert!(", typename!(), "::MIN.into_i512().gt(i512::MIN));")]
    /// ```
    pub const fn into_i512(self) -> i512 {
        i512::from_inner(self.inner.as_cast_signed().into_inner())
    }

    /// Casts `self` to [`u256`] based on semantics explained in [The Rust Reference][numeric_cast].
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert_eq!(", typename!(), "::MINUS_ONE.as_u256(), u256::MAX);")]
    /// ```
    /// [numeric_cast]: <https://doc.rust-lang.org/reference/expressions/operator-expr.html#numeric-cast>
    pub const fn as_u256(self) -> u256 {
        u256 { inner: self.inner }
    }

    /// Casts `self` to [`i8`] based on semantics explained in [The Rust Reference][numeric_cast].
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.as_i8(), -1);")]
    /// ```
    /// [numeric_cast]: <https://doc.rust-lang.org/reference/expressions/operator-expr.html#numeric-cast>
    pub const fn as_i8(self) -> i8 {
        self.inner.as_i64() as i8
    }

    /// Casts `self` to [`i16`] based on semantics explained in [The Rust Reference][numeric_cast].
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.as_i16(), -1);")]
    /// ```
    /// [numeric_cast]: <https://doc.rust-lang.org/reference/expressions/operator-expr.html#numeric-cast>
    pub const fn as_i16(self) -> i16 {
        self.inner.as_i64() as i16
    }

    /// Casts `self` to [`i32`] based on semantics explained in [The Rust Reference][numeric_cast].
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.as_i32(), -1);")]
    /// ```
    /// [numeric_cast]: <https://doc.rust-lang.org/reference/expressions/operator-expr.html#numeric-cast>
    pub const fn as_i32(self) -> i32 {
        self.inner.as_i64() as i32
    }

    /// Casts `self` to [`i64`] based on semantics explained in [The Rust Reference][numeric_cast].
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.as_i64(), -1);")]
    /// ```
    /// [numeric_cast]: <https://doc.rust-lang.org/reference/expressions/operator-expr.html#numeric-cast>
    pub const fn as_i64(self) -> i64 {
        self.inner.as_i64()
    }

    /// Casts `self` to [`i128`] based on semantics explained in [The Rust Reference][numeric_cast].
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.as_i128(), -1);")]
    /// ```
    /// [numeric_cast]: <https://doc.rust-lang.org/reference/expressions/operator-expr.html#numeric-cast>
    pub const fn as_i128(self) -> i128 {
        array_pair_to_u128(self.inner.as_cast_signed().into_inner()) as i128
    }

    /// Casts `self` to [`i256`](crate::i256) based on semantics explained in [The Rust Reference][numeric_cast].
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.as_i256(), i256::MAX);")]
    /// ```
    /// [numeric_cast]: <https://doc.rust-lang.org/reference/expressions/operator-expr.html#numeric-cast>
    pub const fn as_i256(self) -> i256 {
        self
    }

    /// Casts `self` to [`i384`](crate::i384) based on semantics explained in [The Rust Reference][numeric_cast].
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert!(", typename!(), "::MAX.as_i384().lt(i384::MAX));")]
    #[doc = concat!("assert!(", typename!(), "::MIN.as_i384().gt(i384::MIN));")]
    /// ```
    /// [numeric_cast]: <https://doc.rust-lang.org/reference/expressions/operator-expr.html#numeric-cast>
    pub const fn as_i384(self) -> i384 {
        self.into_i384()
    }

    /// Casts `self` to [`i512`](crate::i512) based on semantics explained in [The Rust Reference][numeric_cast].
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert!(", typename!(), "::MAX.as_i512().lt(i512::MAX));")]
    #[doc = concat!("assert!(", typename!(), "::MIN.as_i512().gt(i512::MIN));")]
    /// ```
    /// [numeric_cast]: <https://doc.rust-lang.org/reference/expressions/operator-expr.html#numeric-cast>
    pub const fn as_i512(self) -> i512 {
        self.into_i512()
    }

    /// Converts a string slice in a given base to an integer.
    /// 
    /// The string is expected to be an optional `+` or `-` sign
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
    #[doc = concat!("assert_eq!(", typename!(), "::from_str_radix(\"-A\", 16), Ok(", typename!(), "::from_i64(-10)));")]
    /// ```
    pub const fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntError> {
        match Repr::from_str_radix_signed(src, radix) {
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
    #[doc = concat!("assert_eq!(", typename!(), "::from_str_radix_or_panic(\"-A\", 16), ", typename!(), "::from_i64(-10));")]
    /// ```
    /// ```should_panic
    /// # use wider_primitives::*;
    #[doc = concat!("let _ = ", typename!(), "::from_str_radix_or_panic(\"--B\", 16);")]
    /// ```
    pub const fn from_str_radix_or_panic(src: &str, radix: u32) -> Self {
        Self { inner: Repr::from_str_radix_or_panic_signed(src, radix) }
    }
    
    /// Converts a string slice in a base 10 to an integer.
    /// 
    /// # Examples
    /// 
    /// Basic usage:
    /// 
    /// ```
    /// # use wider_primitives::*;
    #[doc = concat!("assert_eq!(", typename!(), "::from_str(\"-98765432109876543210\"), Ok(", typename!(), "::from_i128(-98765432109876543210)));")]
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
    #[doc = concat!("assert_eq!(", typename!(), "::from_str_or_panic(\"-98765432109876543210\"), ", typename!(), "::from_i128(-98765432109876543210));")]
    /// ```
    /// ```should_panic
    /// # use wider_primitives::*;
    #[doc = concat!("let _ = ", typename!(), "::from_str_or_panic(\"a\");")]
    /// ```
    pub const fn from_str_or_panic(src: &str) -> Self {
        Self { inner: Repr::from_str_or_panic_signed(src) }
    }
}

/// # Equality and comparison
impl i256 {
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
        self.inner.compare_signed(&other.inner)
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

impl i256 {
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
    #[doc = concat!("let int = ", typename!(), "::from_u64;")]
    /// assert_eq!(int(5).overflowing_add(int(2)), (int(7), false));
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.overflowing_add(int(1)), (", typename!(), "::MIN, true));")]
    /// ```
    pub const fn overflowing_add(self, rhs: Self) -> (Self, bool) {
        let (inner, overflows) = self.inner.overflowing_add_signed(rhs.inner);
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
    #[doc = concat!("let int = ", typename!(), "::from_u64;")]
    #[doc = concat!(
        "assert_eq!(", typename!(), "::MAX.sub(int(2)).checked_add(int(1)), ",
        "Some(", typename!(), "::MAX.sub(int(1))));"
    )]
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.sub(int(2)).checked_add(int(3)), None);")]
    /// ```
    pub const fn checked_add(self, rhs: Self) -> Option<Self> {
        match self.inner.checked_add_signed(rhs.inner) {
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
    #[doc = concat!("let int = ", typename!(), "::from_i64;")]
    /// assert_eq!(int(100).saturating_add(int(1)), int(101));
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.saturating_add(int(127)), ", typename!(), "::MAX);")]
    #[doc = concat!("assert_eq!(", typename!(), "::MIN.saturating_add(int(-12)), ", typename!(), "::MIN);")]
    /// ```
    pub const fn saturating_add(self, rhs: Self) -> Self {
        Self { inner: self.inner.saturating_add_signed(rhs.inner) }
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
    #[doc = concat!("let int = ", typename!(), "::from_u64;")]
    /// assert_eq!(int(200).wrapping_add(int(55)), int(255));
    #[doc = concat!("assert_eq!(int(200).wrapping_add(", typename!(), "::MAX), int(199).add(", typename!(), "::MIN));")]
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
    #[doc = concat!("let int = ", typename!(), "::from_u64;")]
    /// assert_eq!(int(1).add(int(1)), int(2));
    pub const fn add(self, rhs: Self) -> Self {
        Self { inner: self.inner.add_signed(rhs.inner) }
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
    #[doc = concat!("let int = ", typename!(), "::from_u64;")]
    /// assert_eq!(int(5).overflowing_sub(int(2)), (int(3), false));
    #[doc = concat!("assert_eq!(", typename!(), "::MIN.overflowing_sub(int(1)), (", typename!(), "::MAX, true));")]
    /// ```
    pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
        let (inner, overflows) = self.inner.overflowing_sub_signed(rhs.inner);
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
    #[doc = concat!("let int = ", typename!(), "::from_u64;")]
    /// assert_eq!(int(1).checked_sub(int(1)), Some(int(0)));
    #[doc = concat!("assert_eq!(", typename!(), "::MIN.checked_sub(int(1)), None);")]
    /// ```
    pub const fn checked_sub(self, rhs: Self) -> Option<Self> {
        match self.inner.checked_sub_signed(rhs.inner) {
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
    #[doc = concat!("let int = ", typename!(), "::from_i64;")]
    #[doc = concat!("let min = ", typename!(), "::MIN;")]
    #[doc = concat!("let max = ", typename!(), "::MAX;")]
    /// 
    /// assert_eq!(int(100).saturating_sub(int(27)), int(73));
    /// assert_eq!(min.add(int(13)).saturating_sub(int(127)), min);
    /// assert_eq!(max.saturating_sub(int(-127)), max);
    /// ```
    pub const fn saturating_sub(self, rhs: Self) -> Self {
        Self { inner: self.inner.saturating_sub_signed(rhs.inner) }
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
    #[doc = concat!("let int = ", typename!(), "::from_u64;")]
    /// assert_eq!(int(100).wrapping_sub(int(100)), int(0));
    #[doc = concat!("assert_eq!(int(100).wrapping_sub(", typename!(), "::MAX), int(101).add(", typename!(), "::MIN));")]
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
    #[doc = concat!("let int = ", typename!(), "::from_u64;")]
    /// assert_eq!(int(629).sub(int(81)), int(548));
    /// ```
    pub const fn sub(self, rhs: Self) -> Self {
        Self { inner: self.inner.sub_signed(rhs.inner) }
    }
}

impl i256 {}

/// # Bit manipulation
impl i256 {
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
    #[doc = concat!("let int = ", typename!(), "::from_u64;")]
    ///
    /// assert_eq!(int(0b011001).bit(4), true);
    /// assert_eq!(int(0b011001).bit(5), false);
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
    #[doc = concat!("let int = ", typename!(), "::from_u64;")]
    ///
    /// assert_eq!(int(0b011001).clear_bit(4), int(0b001001));
    /// assert_eq!(int(0b011001).clear_bit(5), int(0b011001));
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
    #[doc = concat!("let int = ", typename!(), "::from_u64;")]
    ///
    /// assert_eq!(int(0b011001).toggle_bit(4), int(0b001001));
    /// assert_eq!(int(0b011001).toggle_bit(5), int(0b111001));
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
    #[doc = concat!("let int = ", typename!(), "::from_u64;")]
    ///
    /// assert_eq!(int(0b011001).set_bit(4), int(0b011001));
    /// assert_eq!(int(0b011001).set_bit(5), int(0b111001));
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
    #[doc = concat!("let int = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(int(0b011001).bitand(int(0b110011)), int(0b010001));
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
    #[doc = concat!("let int = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(int(0b011001).bitor(int(0b110011)), int(0b111011));
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
    #[doc = concat!("let int = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(int(0b011001).bitxor(int(0b110011)), int(0b101010));
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
    #[doc = concat!("let int = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(int(0x1).overflowing_shl(4), (int(0x10), false));
    /// assert_eq!(int(0x1).overflowing_shl(1540), (int(0x10), true));
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
    #[doc = concat!("let int = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(int(0x1).checked_shl(4), Some(int(0x10)));
    #[doc = concat!("assert_eq!(int(0x1).checked_shl(", typesize!(), "), None);")]
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
    #[doc = concat!("let int = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(int(0x1).saturating_shl(4), int(0x10));
    #[doc = concat!("assert_eq!(int(0x1).saturating_shl(", typesize!(), "), int(0));")]
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
    #[doc = concat!("let int = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(int(1).wrapping_shl(7), int(128));
    /// assert_eq!(int(1).wrapping_shl(1536), int(1));
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
    #[doc = concat!("let int = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(int(0x1).shl(4), int(0x10));
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
    #[doc = concat!("let int = ", typename!(), "::from_i64;")]
    /// 
    /// assert_eq!(int(-0x10).overflowing_shr(4), (int(-0x1), false));
    /// assert_eq!(int(-0x10).overflowing_shr(1540), (int(-0x1), true));
    /// ```
    pub const fn overflowing_shr(self, rhs: u32) -> (Self, bool) {
        let (inner, overflows) = self.inner.overflowing_shr_signed(rhs);
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
    #[doc = concat!("let int = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(int(0x10).checked_shr(4), Some(int(0x1)));
    #[doc = concat!("assert_eq!(int(0x10).checked_shr(", typesize!(), "), None);")]
    /// ```
    pub const fn checked_shr(self, rhs: u32) -> Option<Self> {
        match self.inner.checked_shr_signed(rhs) {
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
    #[doc = concat!("let int = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(int(0x10).saturating_shr(4), int(0x1));
    #[doc = concat!("assert_eq!(int(0x10).saturating_shl(", typesize!(), "), int(0));")]
    /// ```
    pub const fn saturating_shr(self, rhs: u32) -> Self {
        Self { inner: self.inner.saturating_shr_signed(rhs) }
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
    #[doc = concat!("let int = ", typename!(), "::from_u64;")]
    /// 
    /// assert_eq!(int(128).wrapping_shr(7), int(1));
    /// assert_eq!(int(128).wrapping_shr(1536), int(128));
    /// ```
    pub const fn wrapping_shr(self, rhs: u32) -> Self {
        Self { inner: self.inner.wrapping_shr_signed(rhs) }
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
    #[doc = concat!("let int = ", typename!(), "::from_i64;")]
    /// 
    /// assert_eq!(int(-0x10).shr(4), int(-0x1));
    /// ```
    pub const fn shr(self, rhs: u32) -> Self {
        Self { inner: self.inner.shr_signed(rhs) }
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
    #[doc = concat!("assert_eq!(", typename!(), "::MAX.count_zeros(), 1);")]
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
    /// assert_eq!(n.leading_ones(), 3);
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
    /// assert_eq!(n.leading_zeros(), 3);
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
    #[doc = concat!("let int = |x| ", utypename!(), "::from_hex_str_or_panic(x).as_", typename!(), "();")]
    #[doc = concat!("let n = int(", op_in!(swap_bytes), ");")]
    #[doc = concat!("let m = int(", op_out!(swap_bytes), ");")]
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
    #[doc = concat!("let int = |x| ", utypename!(), "::from_hex_str_or_panic(x).as_", typename!(), "();")]
    #[doc = concat!("let n = int(", op_in!(reverse_bits), ");")]
    #[doc = concat!("let m = int(", op_out!(reverse_bits), ");")]
    /// 
    /// assert_eq!(n.reverse_bits(), m);
    /// ```
    pub const fn reverse_bits(self) -> Self {
        Self { inner: self.inner.reverse_bits() }
    }
}
