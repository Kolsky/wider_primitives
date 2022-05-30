use core::cmp::Ordering;
use core::fmt;
// use core::iter;
use crate::ParseIntError;
use crate::Repr;
use crate::array_pair_to_u128;
use crate::int::*;

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
        i512::from_inner(self.inner.as_cast_unsigned().into_inner())
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

impl i256 {}

impl i256 {}

/// # Bit manipulation
impl i256 {}
