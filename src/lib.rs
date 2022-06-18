#![doc = include_str!("../README.md")]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(not(test), no_std)]
#![cfg_attr(unstable, feature(const_mut_refs))]
#![cfg_attr(unstable, feature(const_trait_impl))]
#![cfg_attr(unstable, feature(structural_match))]

use core::cmp::Ordering;
use core::fmt;
use core::num::IntErrorKind;

#[cfg_attr(hide_internal, doc(hidden))]
pub mod uint;

#[doc(inline)]
pub use uint::u256;

#[doc(inline)]
pub use uint::u384;

#[doc(inline)]
pub use uint::u512;

#[cfg_attr(hide_internal, doc(hidden))]
pub mod int;

#[doc(inline)]
pub use int::i256;

#[doc(inline)]
pub use int::i384;

#[doc(inline)]
pub use int::i512;

#[cfg(any(serde, docsrs))]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
pub mod serde;

enum UnaryBitOp {
    Clear = 0,
    #[allow(unused)]
    Preserve = 1,
    Toggle = 2,
    Set = 3,
}

impl UnaryBitOp {
    const UNARY_BIT_OPS_TABLE: [[u64; 2]; 4] = [
        [0_, 0_],
        [0_, !0],
        [!0, 0_],
        [!0, !0],
    ];

    const fn output(self, input: u64, state: u64) -> u64 {
        input & Self::UNARY_BIT_OPS_TABLE[self as usize][((input & state) != 0) as usize]
    }
}

/// An error which can be returned when parsing an integer.
///
/// This error is used as the error type for the `from_str_radix()` functions
/// on the library integer types, such as [`i256::from_str_radix`].
/// 
/// It also supports the conversion to a native [`num::ParseIntError`](core::num::ParseIntError)
/// type via the [`From`] trait. Note that, although strictly speaking,
/// the error conversion relies on implementation details of primitive
/// parse methods, thus the exact behavior is unspecified.
/// 
/// # Potential causes
/// 
/// Among other causes, `ParseIntError` can be thrown because of leading or trailing whitespace
/// in the string e.g., when it is obtained from the standard input.
/// Using the [`str::trim()`] method ensures that no whitespace remains before parsing.
/// 
/// # Example
/// 
/// ```
/// # use wider_primitives::*;
/// if let Err(e) = i256::from_str_radix("a12", 10) {
///     println!("Failed conversion to i256: {e}");
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseIntError {
    kind: IntErrorKind,
}

impl From<ParseIntError> for core::num::ParseIntError {
    fn from(pie: ParseIntError) -> Self {
        use IntErrorKind::*;
        let mimic_erroneous_str = match pie.kind {
            Empty => "",
            InvalidDigit => "+",
            PosOverflow => "128",
            NegOverflow => "-129",
            _ => unreachable!("kinds of errors not created from within this library"),
        };
        mimic_erroneous_str.parse::<i8>().unwrap_err()
    }
}

impl ParseIntError {
    /// Outputs the detailed cause of parsing an integer failing.
    pub const fn kind(&self) -> &IntErrorKind {
        &self.kind
    }

    const fn description(&self) -> &str {
        match self.kind {
            IntErrorKind::Empty => "cannot parse integer from empty string",
            IntErrorKind::InvalidDigit => "invalid digit found in string",
            IntErrorKind::PosOverflow => "number too large to fit in target type",
            IntErrorKind::NegOverflow => "number too small to fit in target type",
            IntErrorKind::Zero => "number would be zero for non-zero type",
            _ => "unknown error",
        }
    }
}

impl fmt::Display for ParseIntError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.description().fmt(f)
    }
}

#[cfg_attr(hide_internal, doc(hidden))]
#[repr(transparent)]
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct Repr<const N: usize> {
    inner: [u64; N],
}

impl<const N: usize> Default for Repr<N> {
    fn default() -> Self {
        Self::ZERO
    }
}

const fn carrying_add(lhs: u64, rhs: u64, carry: bool) -> (u64, bool) {
    let result = lhs as u128 + rhs as u128 + carry as u128;
    (result as u64, (result >> u64::BITS) == 1)
}

const fn carrying_mul(a: u64, b: u64, carry: u64) -> (u64, u64) {
    let result = a as u128 * b as u128 + carry as u128;
    (result as u64, (result >> 64) as u64)
}

const fn carrying_div(a: u64, b: u64, carry: u64) -> (u64, u64) {
    let result = (carry as u128) << u64::BITS | a as u128;
    ((result / b as u128) as u64, (result % b as u128) as u64)
}

const fn carrying_shl(a: u64, b: u32, carry: u64) -> (u64, u64) {
    ((a << b) | carry, a >> (u64::BITS - b))
}

const fn carrying_shr(a: u64, b: u32, carry: u64) -> (u64, u64) {
    ((a >> b) | carry, a << (u64::BITS - b))
}

// Taken from corelib
const fn to_digit(c: char, radix: u32) -> Option<u32> {
    assert!(radix <= 36, "to_digit: radix is too high (maximum 36)");
    
    let mut digit = (c as u32).wrapping_sub('0' as u32);
    if radix > 10 {
        if digit < 10 {
            return Some(digit);
        }
        digit = (c as u32 | 0b10_0000).wrapping_sub('a' as u32).saturating_add(10);
    }
    if digit < radix { Some(digit) } else { None }
}

#[cfg_attr(hide_internal, doc(hidden))]
pub const fn array_pair_to_u128([lo, hi]: [u64; 2]) -> u128 {
    ((hi as u128) << u64::BITS) | lo as u128
}

impl<const N: usize> Repr<N> {
    pub const BITS: u32 = u64::BITS * N as u32;
    pub const SIGN_BIT: u32 = Self::BITS - 1;
    
    pub const ZERO: Self = Self::from_inner([0; N]);
    pub const ONE: Self = Self::ZERO.set_bit(0);
    pub const MINUS_ONE: Self = Self::ONE.wrapping_neg();

    pub const MIN_UNSIGNED: Self = Self::ZERO;
    pub const MAX_UNSIGNED: Self = Self::from_inner([!0; N]);
    pub const MIN_SIGNED: Self = Self::MIN_UNSIGNED.set_bit(Self::SIGN_BIT);
    pub const MAX_SIGNED: Self = Self::MAX_UNSIGNED.clear_bit(Self::SIGN_BIT);

    pub const fn from_inner(inner: [u64; N]) -> Self {
        Self { inner }
    }

    pub const fn into_inner(self) -> [u64; N] {
        self.inner
    }

    pub const fn from_u64(n: u64) -> Self {
        Repr::from_inner([n]).as_cast_unsigned()
    }

    pub const fn from_u128(n: u128) -> Self {
        Repr::from_inner([n as u64, (n >> 64) as u64]).as_cast_unsigned()
    }

    pub const fn from_i64(n: i64) -> Self {
        Repr::from_inner([n as u64]).as_cast_signed()
    }

    pub const fn from_i128(n: i128) -> Self {
        Repr::from_inner([n as u64, (n >> 64) as u64]).as_cast_signed()
    }

    pub const fn as_u64(self) -> u64 {
        self.inner[0]
    }

    pub const fn as_i64(self) -> i64 {
        self.as_u64() as i64
    }

    pub const fn as_cast_unsigned<const M: usize>(self) -> Repr<M> {
        let mut ret = Repr::ZERO;
        let mut i = 0;
        while i < M && i < N {
            ret.inner[i] = self.inner[i];
            i += 1;
        }
        ret
    }

    pub const fn as_cast_signed<const M: usize>(self) -> Repr<M> {
        let mut ret = Repr::ZERO;
        let mut i = 0;
        let fill_rest = (self.inner[N - 1] as i64 >> (i64::BITS - 1)) as u64;
        while i < M && i < N {
            ret.inner[i] = self.inner[i];
            i += 1;
        }
        while i < M {
            ret.inner[i] = fill_rest;
            i += 1;
        }
        ret
    }

    // Taken from corelib
    const fn from_str_radix<const SIGNED: bool>(src: &str, radix: u32) -> Result<Self, ParseIntError> {
        use self::ParseIntError as PIE;
        use self::IntErrorKind::*;

        assert!(
            2 <= radix && radix <= 36,
            "from_str_radix_int: must lie in the range `[2, 36]`"
        );
        if src.is_empty() {
            return Err(PIE { kind: Empty });
        }

        let src = src.as_bytes();
    
        let (is_non_negative, mut digits) = match src {
            [b'+' | b'-'] => {
                return Err(PIE { kind: InvalidDigit });
            }
            [b'+', src @ ..] => (true, src),
            [b'-', src @ ..] if SIGNED => (false, src),
            _ => (true, src),
        };
        
        let mut result = Self::ZERO;
        let mut x = Self::ZERO;
        if is_non_negative {
            while let [c, d @ ..] = digits {
                digits = d;
                let carry = match to_digit(*c as char, radix) {
                    Some(digit) => digit as u64,
                    None => return Err(PIE { kind: InvalidDigit }),
                };
                match result.carrying_short_mul_unsigned(radix as u64, carry) {
                    (val, 0) => result = val,
                    _ => return Err(PIE { kind: PosOverflow }),
                };
            }
        }
        else {
            while let [c, d @ ..] = digits {
                digits = d;
                match to_digit(*c as char, radix) {
                    Some(digit) => x.inner[0] = digit as u64,
                    None => return Err(PIE { kind: InvalidDigit }),
                };
                (result, _) = result.carrying_short_mul_unsigned(radix as u64, 0);
                if !result.is_negative() && !result.equals(&Self::ZERO) {
                    return Err(PIE { kind: NegOverflow });
                };
                match result.overflowing_sub_signed(x) {
                    (val, false) => result = val,
                    _ => return Err(PIE { kind: NegOverflow }),
                };
            }
        }
        if is_non_negative && SIGNED && result.is_negative() {
            return Err(PIE { kind: PosOverflow });
        }
        Ok(result)
    }

    const fn from_str_radix_or_panic<const SIGNED: bool>(src: &str, radix: u32) -> Self {
        match Self::from_str_radix::<SIGNED>(src, radix) {
            Ok(val) => val,
            Err(pie) => panic!("{}", pie.description()),
        }
    }

    pub const fn from_str_radix_unsigned(src: &str, radix: u32) -> Result<Self, ParseIntError> {
        Self::from_str_radix::<false>(src, radix)
    }

    pub const fn from_str_radix_or_panic_unsigned(src: &str, radix: u32) -> Self {
        Self::from_str_radix_or_panic::<false>(src, radix)
    }

    pub const fn from_str_unsigned(src: &str) -> Result<Self, ParseIntError> {
        Self::from_str_radix::<false>(src, 10)
    }

    pub const fn from_str_or_panic_unsigned(src: &str) -> Self {
        Self::from_str_radix_or_panic::<false>(src, 10)
    }

    pub const fn from_hex_str_unsigned(src: &str) -> Result<Self, ParseIntError> {
        Self::from_str_radix::<false>(src, 16)
    }

    pub const fn from_hex_str_or_panic_unsigned(src: &str) -> Self {
        Self::from_str_radix_or_panic::<false>(src, 16)
    }

    pub const fn from_str_radix_signed(src: &str, radix: u32) -> Result<Self, ParseIntError> {
        Self::from_str_radix::<true>(src, radix)
    }

    pub const fn from_str_radix_or_panic_signed(src: &str, radix: u32) -> Self {
        Self::from_str_radix_or_panic::<true>(src, radix)
    }

    pub const fn from_str_signed(src: &str) -> Result<Self, ParseIntError> {
        Self::from_str_radix::<true>(src, 10)
    }

    pub const fn from_str_or_panic_signed(src: &str) -> Self {
        Self::from_str_radix_or_panic::<true>(src, 10)
    }

    pub const fn from_hex_str_signed(src: &str) -> Result<Self, ParseIntError> {
        Self::from_str_radix::<true>(src, 16)
    }

    pub const fn from_hex_str_or_panic_signed(src: &str) -> Self {
        Self::from_str_radix_or_panic::<true>(src, 16)
    }

    const fn change_bit(mut self, bit: u32, op: UnaryBitOp) -> Self {
        assert!(bit < Self::BITS, "attempt to change bit with overflow");
        let index = (bit / u64::BITS) as usize;
        let bit = bit % u64::BITS;
        let mask = 1u64 << bit;
        self.inner[index] = (self.inner[index] & !mask) | op.output(mask, self.inner[index]);
        self
    }

    pub const fn bit(&self, bit: u32) -> bool {
        assert!(bit < Self::BITS, "attempt to read bit with overflow");
        let index = (bit / u64::BITS) as usize;
        let bit = bit % u64::BITS;
        let mask = 1u64 << bit;
        (self.inner[index] & mask) != 0
    }

    pub const fn clear_bit(self, bit: u32) -> Self {
        self.change_bit(bit, UnaryBitOp::Clear)
    }

    pub const fn toggle_bit(self, bit: u32) -> Self {
        self.change_bit(bit, UnaryBitOp::Toggle)
    }

    pub const fn set_bit(self, bit: u32) -> Self {
        self.change_bit(bit, UnaryBitOp::Set)
    }

    pub const fn is_negative(&self) -> bool {
        self.bit(Self::SIGN_BIT)
    }

    pub const fn is_positive(&self) -> bool {
        !self.is_negative() && self.compare_unsigned(&Self::ZERO).is_gt()
    }

    pub const fn signum(self) -> Self {
        if self.is_negative() {
            Self::MINUS_ONE
        }
        else if self.is_positive() {
            Self::ONE
        }
        else {
            Self::ZERO
        }
    }

    pub const fn not(mut self) -> Self {
        let mut i = N;
        while i > 0 {
            i -= 1;
            self.inner[i] = !self.inner[i];
        }
        self
    }

    pub const fn bitand(mut self, rhs: Self) -> Self {
        let mut i = N;
        while i > 0 {
            i -= 1;
            self.inner[i] &= rhs.inner[i];
        }
        self
    }

    pub const fn bitor(mut self, rhs: Self) -> Self {
        let mut i = N;
        while i > 0 {
            i -= 1;
            self.inner[i] |= rhs.inner[i];
        }
        self
    }
    
    pub const fn bitxor(mut self, rhs: Self) -> Self {
        let mut i = N;
        while i > 0 {
            i -= 1;
            self.inner[i] ^= rhs.inner[i];
        }
        self
    }

    pub const fn equals(&self, other: &Self) -> bool {
        let mut i = N;
        while i > 0 {
            i -= 1;
            if self.inner[i] != other.inner[i] {
                return false;
            }
        }
        true
    }

    pub const fn compare_unsigned(&self, other: &Self) -> Ordering {
        let mut i = N;
        while i > 0 {
            i -= 1;
            if self.inner[i] < other.inner[i] {
                return Ordering::Less;
            }
            if self.inner[i] > other.inner[i] {
                return Ordering::Greater;
            }
        }
        Ordering::Equal
    }

    pub const fn compare_signed(&self, other: &Self) -> Ordering {
        self.toggle_bit(Self::SIGN_BIT).compare_unsigned(&other.toggle_bit(Self::SIGN_BIT))
    }

    pub const fn overflowing_neg_unsigned(self) -> (Self, bool) {
        (self.wrapping_neg(), !self.equals(&Self::ZERO))
    }

    pub const fn checked_neg_unsigned(self) -> Option<Self> {
        match self.overflowing_neg_unsigned() {
            (val, false) => Some(val),
            (_, true) => None,
        }
    }

    pub const fn wrapping_neg(self) -> Self {
        Self::ZERO.wrapping_sub(self)
    }

    pub const fn overflowing_neg_signed(self) -> (Self, bool) {
        let result = self.wrapping_neg();
        (result, self.is_negative() && result.is_negative())
    }

    pub const fn checked_neg_signed(self) -> Option<Self> {
        match self.overflowing_neg_signed() {
            (val, false) => Some(val),
            (_, true) => None,
        }
    }

    pub const fn saturating_neg_signed(self) -> Self {
        match self.overflowing_neg_signed() {
            (val, false) => val,
            (_, true) => Self::MAX_SIGNED,
        }
    }

    #[cfg(debug)]
    pub const fn neg_signed(self) -> Self {
        match self.overflowing_neg_signed() {
            (val, false) => val,
            (_, true) => panic!("attempt to negate with overflow"),
        }
    }

    #[cfg(release)]
    pub const fn neg_signed(self) -> Self {
        self.wrapping_neg()
    }

    pub const fn carrying_add_unsigned(self, rhs: Self, mut carry: bool) -> (Self, bool) {
        let mut inner = self.into_inner();
        let mut i = 0;
        while i < N {
            (inner[i], carry) = carrying_add(inner[i], rhs.inner[i], carry);
            i += 1;
        }
        (Self::from_inner(inner), carry)
    }

    pub const fn overflowing_add_unsigned(self, rhs: Self) -> (Self, bool) {
        self.carrying_add_unsigned(rhs, false)
    }

    pub const fn checked_add_unsigned(self, rhs: Self) -> Option<Self> {
        match self.overflowing_add_unsigned(rhs) {
            (val, false) => Some(val),
            (_, true) => None,
        }
    }

    pub const fn saturating_add_unsigned(self, rhs: Self) -> Self {
        match self.overflowing_add_unsigned(rhs) {
            (val, false) => val,
            (_, true) => Self::MAX_UNSIGNED,
        }
    }

    pub const fn wrapping_add(self, rhs: Self) -> Self {
        self.overflowing_add_unsigned(rhs).0
    }

    #[cfg(debug)]
    pub const fn add_unsigned(self, rhs: Self) -> Self {
        match self.overflowing_add_unsigned(rhs) {
            (val, false) => val,
            (_, true) => panic!("attempt to add with overflow"),
        }
    }

    #[cfg(release)]
    pub const fn add_unsigned(self, rhs: Self) -> Self {
        self.wrapping_add(rhs)
    }

    const fn sign_bit_test(&self, rhs: &Self, result: &Self) -> bool {
        (result.bit(Self::SIGN_BIT) ^ self.bit(Self::SIGN_BIT)) && (result.bit(Self::SIGN_BIT) ^ rhs.bit(Self::SIGN_BIT))
    }

    pub const fn overflowing_add_signed(self, rhs: Self) -> (Self, bool) {
        let result = self.wrapping_add(rhs);
        (result, self.sign_bit_test(&rhs, &result))
    }

    pub const fn checked_add_signed(self, rhs: Self) -> Option<Self> {
        match self.overflowing_add_signed(rhs) {
            (val, false) => Some(val),
            (_, true) => None,
        }
    }

    pub const fn saturating_add_signed(self, rhs: Self) -> Self {
        match self.overflowing_add_signed(rhs) {
            (val, false) => val,
            (val, true) if val.is_negative() => Self::MAX_SIGNED,
            (_, true) => Self::MIN_SIGNED,
        }
    }
    
    #[cfg(debug)]
    pub const fn add_signed(self, rhs: Self) -> Self {
        match self.overflowing_add_signed(rhs) {
            (val, false) => val,
            (_, true) => panic!("attempt to add with overflow"),
        }
    }
    
    #[cfg(release)]
    pub const fn add_signed(self, rhs: Self) -> Self {
        self.wrapping_add(rhs)
    }

    pub const fn overflowing_sub_unsigned(self, rhs: Self) -> (Self, bool) {
        let (result, carry) = self.carrying_add_unsigned(rhs.not(), true);
        (result, !carry)
    }

    pub const fn checked_sub_unsigned(self, rhs: Self) -> Option<Self> {
        match self.overflowing_sub_unsigned(rhs) {
            (val, false) => Some(val),
            (_, true) => None,
        }
    }

    pub const fn saturating_sub_unsigned(self, rhs: Self) -> Self {
        match self.overflowing_sub_unsigned(rhs) {
            (val, false) => val,
            (_, true) => Self::MIN_UNSIGNED,
        }
    }

    pub const fn wrapping_sub(self, rhs: Self) -> Self {
        self.overflowing_sub_unsigned(rhs).0
    }

    #[cfg(debug)]
    pub const fn sub_unsigned(self, rhs: Self) -> Self {
        match self.overflowing_sub_unsigned(rhs) {
            (val, false) => val,
            (_, true) => panic!("attempt to subtract with overflow"),
        }
    }

    #[cfg(release)]
    pub const fn sub_unsigned(self, rhs: Self) -> Self {
        self.wrapping_sub(rhs)
    }

    pub const fn abs_diff_unsigned(self, rhs: Self) -> Self {
        match self.compare_unsigned(&rhs) {
            Ordering::Less => rhs.wrapping_sub(self),
            _ => self.wrapping_sub(rhs),
        }
    }

    pub const fn overflowing_sub_signed(self, rhs: Self) -> (Self, bool) {
        let result = self.wrapping_sub(rhs);
        (result, result.sign_bit_test(&rhs, &self))
    }

    pub const fn checked_sub_signed(self, rhs: Self) -> Option<Self> {
        match self.overflowing_sub_signed(rhs) {
            (val, false) => Some(val),
            (_, true) => None,
        }
    }

    pub const fn saturating_sub_signed(self, rhs: Self) -> Self {
        match self.overflowing_sub_signed(rhs) {
            (val, false) => val,
            (val, true) if val.is_negative() => Self::MAX_SIGNED,
            (_, true) => Self::MIN_SIGNED,
        }
    }
    
    #[cfg(debug)]
    pub const fn sub_signed(self, rhs: Self) -> Self {
        match self.overflowing_sub_signed(rhs) {
            (val, false) => val,
            (_, true) => panic!("attempt to subtract with overflow"),
        }
    }
    
    #[cfg(release)]
    pub const fn sub_signed(self, rhs: Self) -> Self {
        self.wrapping_sub(rhs)
    }

    pub const fn abs_diff_signed(self, rhs: Self) -> Self {
        match self.compare_signed(&rhs) {
            Ordering::Less => rhs.wrapping_sub(self),
            _ => self.wrapping_sub(rhs),
        }
    }

    const fn carrying_short_mul_unsigned(mut self, rhs: u64, mut carry: u64) -> (Self, u64) {
        let mut i = 0;
        while i < N {
            (self.inner[i], carry) = carrying_mul(self.inner[i], rhs, carry);
            i += 1;
        }
        (self, carry)
    }

    pub const fn overflowing_short_mul_unsigned(self, rhs: u64) -> (Self, u64) {
        self.carrying_short_mul_unsigned(rhs, 0)
    }

    pub const fn checked_short_mul_unsigned(self, rhs: u64) -> Option<Self> {
        match self.overflowing_short_mul_unsigned(rhs) {
            (val, 0) => Some(val),
            _ => None,
        }
    }
    
    pub const fn saturating_short_mul_unsigned(self, rhs: u64) -> Self {
        match self.overflowing_short_mul_unsigned(rhs) {
            (val, 0) => val,
            _ => Self::MAX_UNSIGNED,
        }
    }

    pub const fn wrapping_short_mul_unsigned(self, rhs: u64) -> Self {
        self.overflowing_short_mul_unsigned(rhs).0
    }

    #[cfg(debug)]
    pub const fn short_mul_unsigned(self, rhs: u64) -> Self {
        match self.overflowing_short_mul_unsigned(rhs) {
            (val, 0) => val,
            _ => panic!("attempt to multiply with overflow"),
        }
    }

    #[cfg(release)]
    pub const fn short_mul_unsigned(self, rhs: u64) -> Self {
        self.wrapping_short_mul_unsigned(rhs)
    }
    
    pub const fn full_mul_unsigned(self, rhs: Self) -> (Self, Self) {
        let [mut lo, mut hi] = [[0; N]; 2];
        let mut i = 0;
        let mut carry = false;
        while i < N {
            let add;
            (Self { inner: add }, hi[i]) = self.carrying_short_mul_unsigned(rhs.inner[i], 0);
            
            let mut j = 0;
            while i + j < N {
                (lo[i + j], carry) = carrying_add(lo[i + j], add[j], carry);
                j += 1;
            }
            while j < N {
                (hi[i + j - N], carry) = carrying_add(hi[i + j - N], add[j], carry);
                j += 1;
            }
            while carry && i + j - N < N {
                (hi[i + j - N], carry) = carrying_add(hi[i + j - N], 0, carry);
            }

            i += 1;
        }
        (Self::from_inner(lo), Self::from_inner(hi))
    }

    pub const fn overflowing_mul_unsigned(self, rhs: Self) -> (Self, bool) {
        let (lo, hi) = self.full_mul_unsigned(rhs);
        (lo, !hi.equals(&Self::ZERO))
    }

    pub const fn checked_mul_unsigned(self, rhs: Self) -> Option<Self> {
        match self.overflowing_mul_unsigned(rhs) {
            (val, false) => Some(val),
            (_, true) => None,
        }
    }

    pub const fn saturating_mul_unsigned(self, rhs: Self) -> Self {
        match self.overflowing_mul_unsigned(rhs) {
            (val, false) => val,
            (_, true) => Self::MAX_UNSIGNED,
        }
    }

    pub const fn wrapping_mul(self, rhs: Self) -> Self {
        self.full_mul_unsigned(rhs).0
    }
    
    #[cfg(debug)]
    pub const fn mul_unsigned(self, rhs: Self) -> Self {
        match self.overflowing_mul_unsigned(rhs) {
            (val, false) => val,
            (_, true) => panic!("attempt to multiply with overflow"),
        }
    }
    
    #[cfg(release)]
    pub const fn mul_unsigned(self, rhs: Self) -> Self {
        self.wrapping_mul(rhs)
    }

    pub const fn overflowing_short_mul_signed(self, rhs: i64) -> (Self, i64) {
        let (mut lo, mut hi) = self.unsigned_abs().overflowing_short_mul_unsigned(rhs.unsigned_abs());
        if self.is_negative() ^ rhs.is_negative() {
            let carry;
            (lo, carry) = lo.not().carrying_add_unsigned(Self::ZERO, true);
            (hi, _) = carrying_add(!hi, 0, carry);
        }
        (lo, hi as i64)
    }

    pub const fn checked_short_mul_signed(self, rhs: i64) -> Option<Self> {
        match self.overflowing_short_mul_signed(rhs) {
            (val, -1) if val.is_negative() => Some(val),
            (val, 0) if !val.is_negative() => Some(val),
            _ => None,
        }
    }

    pub const fn saturating_short_mul_signed(self, rhs: i64) -> Self {
        match self.overflowing_short_mul_signed(rhs) {
            (val, -1) if val.is_negative() => val,
            (val, 0) if !val.is_negative() => val,
            _ if self.is_negative() ^ rhs.is_negative() => Self::MIN_SIGNED,
            _ => Self::MAX_SIGNED,
        }
    }

    pub const fn wrapping_short_mul_signed(self, rhs: i64) -> Self {
        self.overflowing_short_mul_signed(rhs).0
    }

    #[cfg(debug)]
    pub const fn short_mul_signed(self, rhs: i64) -> Self {
        match self.checked_short_mul_signed(rhs) {
            Some(val) => val,
            None => panic!("attempt to multiply with overflow"),
        }
    }

    #[cfg(release)]
    pub const fn short_mul_signed(self, rhs: i64) -> Self {
        self.wrapping_short_mul_signed(rhs)
    }

    pub const fn full_mul_signed(self, rhs: Self) -> (Self, Self) {
        let (lo, mut hi) = self.full_mul_unsigned(rhs);
        hi = match [self.is_negative(), rhs.is_negative()] {
            [false, false] => hi,
            [false, true] => hi.wrapping_sub(self),
            [true, false] => hi.wrapping_sub(rhs),
            [true, true] => hi.wrapping_sub(self).wrapping_sub(rhs),
        };
        (lo, hi)
    }
    
    pub const fn overflowing_mul_signed(self, rhs: Self) -> (Self, bool) {
        let (lo, hi) = self.full_mul_signed(rhs);
        let neg_inbounds = lo.is_negative() && hi.equals(&Self::MINUS_ONE);
        let pos_inbounds = !lo.is_negative() && hi.equals(&Self::ZERO);
        (lo, !(neg_inbounds || pos_inbounds))
    }

    pub const fn checked_mul_signed(self, rhs: Self) -> Option<Self> {
        match self.overflowing_mul_signed(rhs) {
            (val, false) => Some(val),
            (_, true) => None,
        }
    }
    
    pub const fn saturating_mul_signed(self, rhs: Self) -> Self {
        match self.overflowing_mul_signed(rhs) {
            (val, false) => val,
            (_, true) if self.is_negative() ^ rhs.is_negative() => Self::MIN_SIGNED,
            (_, true) => Self::MAX_SIGNED,
        }
    }
    
    #[cfg(debug)]
    pub const fn mul_signed(self, rhs: Self) -> Self {
        match self.overflowing_mul_signed(rhs) {
            (val, false) => val,
            (_, true) => panic!("attempt to multiply with overflow"),
        }
    }
    
    #[cfg(release)]
    pub const fn mul_signed(self, rhs: Self) -> Self {
        self.wrapping_mul(rhs)
    }

    pub const fn checked_short_divrem_unsigned(self, rhs: u64) -> Option<(Self, u64)> {
        match rhs {
            0 => None,
            _ => Some(self.short_divrem_unsigned(rhs)),
        }
    }
    
    pub const fn short_divrem_unsigned(mut self, rhs: u64) -> (Self, u64) {
        assert!(rhs != 0, "attempt to divide by zero");
        let mut rem = 0;
        let mut i = N;
        while i > 0 {
            i -= 1;
            (self.inner[i], rem) = carrying_div(self.inner[i], rhs, rem);
        }
        (self, rem)
    }

    pub const fn checked_divrem_unsigned(self, rhs: Self) -> Option<(Self, Self)> {
        if rhs.equals(&Self::ZERO) {
            return None;
        }
        Some(self.divrem_unsigned(rhs))
    }

    pub const fn divrem_unsigned(self, rhs: Self) -> (Self, Self) {
        let [mut quot, mut rem] = [Self::ZERO; 2];
        // D1
        let mut n = N - 1;
        let norm_shl = loop {
            match (rhs.inner[n] != 0, n) {
                (true, 0) => {
                    (quot, rem.inner[0]) = self.short_divrem_unsigned(rhs.inner[n]);
                    return (quot, rem);
                }
                (true, _) => break rhs.inner[n].leading_zeros(),
                (false, 0) => panic!("attempt to divide by zero"),
                (false, _) => n -= 1,
            }
        };
        let mut lhs_hi = self.inner[N - 1].rotate_left(norm_shl) % (1 << norm_shl);
        let mut lhs = self.wrapping_shl(norm_shl);
        let rhs = rhs.wrapping_shl(norm_shl);

        // D2
        let mut m = N - n;
        while m > 0 {
            // D7
            m -= 1;
            // D3
            let (mut q_hat, mut r_hat) = 
                Repr::from_inner([lhs.inner[m + n], lhs_hi]).short_divrem_unsigned(rhs.inner[n]);
            while q_hat.equals(&Repr::from_inner([0, 1]))
                || q_hat.wrapping_short_mul_unsigned(rhs.inner[n - 1]).compare_unsigned(&Repr::from_inner([lhs.inner[m + n - 1], r_hat])).is_gt() 
            {
                q_hat = q_hat.sub_unsigned(Repr::ONE);
                let overflow;
                (r_hat, overflow) = r_hat.overflowing_add(rhs.inner[n]);
                if overflow { break };
            }

            // D4
            let mut mul_carry = 0;
            let mut in_bounds = true;
            let mut i = 0;
            while i <= n {
                let qrhs ;
                (qrhs, mul_carry) = carrying_mul(rhs.inner[i], q_hat.inner[0], mul_carry);
                (lhs.inner[m + i], in_bounds) = carrying_add(lhs.inner[m + i], !qrhs, in_bounds);
                i += 1;
            }
            (lhs_hi, in_bounds) = carrying_add(lhs_hi, !mul_carry, in_bounds);

            // D5
            quot.inner[m] = q_hat.inner[0];
            if !in_bounds {
                // D6
                quot.inner[m] -= 1;
                let mut add_carry = false;
                let mut i = 0;
                while i <= n {
                    (lhs.inner[m + i], add_carry) = carrying_add(lhs.inner[m + i], rhs.inner[i], add_carry);
                    i += 1;
                }
                (lhs_hi, _) = carrying_add(lhs_hi, 0, add_carry);
            }
            if m + n + 1 < N {
                lhs.inner[m + n + 1] = lhs_hi;
            }
            lhs_hi = lhs.inner[m + n];
        }
        
        // D8
        rem = lhs.wrapping_shr_unsigned(norm_shl);
        (quot, rem)
    }

    pub const fn checked_short_div_unsigned(self, rhs: u64) -> Option<Self> {
        match self.checked_short_divrem_unsigned(rhs) {
            Some((quot, _)) => Some(quot),
            None => None,
        }
    }

    pub const fn short_div_unsigned(self, rhs: u64) -> Self {
        self.short_divrem_unsigned(rhs).0
    }

    pub const fn checked_div_unsigned(self, rhs: Self) -> Option<Self> {
        match self.checked_divrem_unsigned(rhs) {
            Some((quot, _)) => Some(quot),
            None => None,
        }
    }

    pub const fn div_unsigned(self, rhs: Self) -> Self {
        self.divrem_unsigned(rhs).0
    }

    pub const fn checked_short_rem_unsigned(self, rhs: u64) -> Option<u64> {
        match self.checked_short_divrem_unsigned(rhs) {
            Some((_, rem)) => Some(rem),
            None => None,
        }
    }

    pub const fn short_rem_unsigned(self, rhs: u64) -> u64 {
        self.short_divrem_unsigned(rhs).1
    }

    pub const fn checked_rem_unsigned(self, rhs: Self) -> Option<Self> {
        match self.checked_divrem_unsigned(rhs) {
            Some((_, rem)) => Some(rem),
            None => None,
        }
    }

    pub const fn rem_unsigned(self, rhs: Self) -> Self {
        self.divrem_unsigned(rhs).1
    }

    pub const fn checked_short_divrem_signed(self, rhs: u64) -> Option<(Self, i128)> {
        match rhs {
            0 => None,
            _ => Some(self.short_divrem_signed(rhs)),
        }
    }

    pub const fn short_divrem_signed(self, rhs: u64) -> (Self, i128) {
        let (mut quot, rem) = self.unsigned_abs().short_divrem_unsigned(rhs);
        let mut rem = rem as i128;
        if self.is_negative() {
            quot = quot.wrapping_neg();
        }
        if self.is_negative() {
            rem = rem.wrapping_neg();
        }
        (quot, rem)
    }

    pub const fn overflowing_short_idivrem_signed(self, rhs: i64) -> (Self, i64, bool) {
        let (mut quot, rem) = self.unsigned_abs().short_divrem_unsigned(rhs.unsigned_abs());
        let mut rem = rem as i64;
        if self.is_negative() ^ rhs.is_negative() {
            quot = quot.wrapping_neg();
        }
        if self.is_negative() {
            rem = rem.wrapping_neg();
        }
        (quot, rem, self.is_negative() && rhs.is_negative() && quot.is_negative())
    }

    pub const fn checked_short_idivrem_signed(self, rhs: i64) -> Option<(Self, i64)> {
        if rhs == 0 {
            return None;
        }
        match self.overflowing_short_idivrem_signed(rhs) {
            (quot, rem, false) => Some((quot, rem)),
            (_, _, true) => None,
        }
    }

    pub const fn saturating_short_idivrem_signed(self, rhs: i64) -> (Self, i64) {
        match self.overflowing_short_idivrem_signed(rhs) {
            (quot, rem, false) => (quot, rem),
            (_, _, true) => (Self::MAX_SIGNED, 0),
        }
    }

    pub const fn wrapping_short_idivrem_signed(self, rhs: i64) -> (Self, i64) {
        let (quot, rem, _) = self.overflowing_short_idivrem_signed(rhs);
        (quot, rem)
    }

    pub const fn short_idivrem_signed(self, rhs: i64) -> (Self, i64) {
        match self.overflowing_short_idivrem_signed(rhs) {
            (quot, rem, false) => (quot, rem),
            (_, _, true) => panic!("attempt to divide with overflow"),
        }
    }

    pub const fn overflowing_divrem_signed(self, rhs: Self) -> (Self, Self, bool) {
        let (mut quot, mut rem) = self.unsigned_abs().divrem_unsigned(rhs.unsigned_abs());
        if self.is_negative() ^ rhs.is_negative() {
            quot = quot.wrapping_neg();
        }
        if self.is_negative() {
            rem = rem.wrapping_neg();
        }
        (quot, rem, self.is_negative() && rhs.is_negative() && quot.is_negative())
    }

    pub const fn checked_divrem_signed(self, rhs: Self) -> Option<(Self, Self)> {
        if rhs.equals(&Self::ZERO) {
            return None;
        }
        match self.overflowing_divrem_signed(rhs) {
            (quot, rem, false) => Some((quot, rem)),
            (_, _, true) => None,
        }
    }

    pub const fn saturating_divrem_signed(self, rhs: Self) -> (Self, Self) {
        match self.overflowing_divrem_signed(rhs) {
            (quot, rem, false) => (quot, rem),
            (_, _, true) => (Self::MAX_SIGNED, Self::ZERO),
        }
    }

    pub const fn wrapping_divrem_signed(self, rhs: Self) -> (Self, Self) {
        let (quot, rem, _) = self.overflowing_divrem_signed(rhs);
        (quot, rem)
    }

    pub const fn divrem_signed(self, rhs: Self) -> (Self, Self) {
        match self.overflowing_divrem_signed(rhs) {
            (quot, rem, false) => (quot, rem),
            (_, _, true) => panic!("attempt to divide with overflow"),
        }
    }

    pub const fn checked_short_div_signed(self, rhs: u64) -> Option<Self> {
        match self.checked_short_divrem_signed(rhs) {
            Some((quot, _)) => Some(quot),
            None => None,
        }
    }

    pub const fn short_div_signed(self, rhs: u64) -> Self {
        self.short_divrem_signed(rhs).0
    }

    pub const fn overflowing_short_idiv_signed(self, rhs: i64) -> (Self, bool) {
        let (quot, _, overflows) = self.overflowing_short_idivrem_signed(rhs);
        (quot, overflows)
    }

    pub const fn checked_short_idiv_signed(self, rhs: i64) -> Option<Self> {
        match self.checked_short_idivrem_signed(rhs) {
            Some((quot, _)) => Some(quot),
            None => None,
        }
    }

    pub const fn saturating_short_idiv_signed(self, rhs: i64) -> Self {
        self.saturating_short_idivrem_signed(rhs).0
    }

    pub const fn wrapping_short_idiv_signed(self, rhs: i64) -> Self {
        self.wrapping_short_idivrem_signed(rhs).0
    }

    pub const fn short_idiv_signed(self, rhs: i64) -> Self {
        self.short_idivrem_signed(rhs).0
    }

    pub const fn overflowing_div_signed(self, rhs: Self) -> (Self, bool) {
        let (quot, _, overflows) = self.overflowing_divrem_signed(rhs);
        (quot, overflows)
    }

    pub const fn checked_div_signed(self, rhs: Self) -> Option<Self> {
        match self.checked_divrem_signed(rhs) {
            Some((quot, _)) => Some(quot),
            None => None,
        }
    }

    pub const fn saturating_div_signed(self, rhs: Self) -> Self {
        self.saturating_divrem_signed(rhs).0
    }

    pub const fn wrapping_div_signed(self, rhs: Self) -> Self {
        self.wrapping_divrem_signed(rhs).0
    }

    pub const fn div_signed(self, rhs: Self) -> Self {
        self.divrem_signed(rhs).0
    }

    pub const fn checked_short_rem_signed(self, rhs: u64) -> Option<i128> {
        match self.checked_short_divrem_signed(rhs) {
            Some((_, rem)) => Some(rem),
            None => None,
        }
    }

    pub const fn short_rem_signed(self, rhs: u64) -> i128 {
        self.short_divrem_signed(rhs).1
    }

    pub const fn overflowing_short_irem_signed(self, rhs: i64) -> (i64, bool) {
        let (_, rem, overflows) = self.overflowing_short_idivrem_signed(rhs);
        (rem, overflows)
    }

    pub const fn checked_short_irem_signed(self, rhs: i64) -> Option<i64> {
        match self.checked_short_idivrem_signed(rhs) {
            Some((_, rem)) => Some(rem),
            None => None,
        }
    }

    pub const fn saturating_short_irem_signed(self, rhs: i64) -> i64 {
        self.saturating_short_idivrem_signed(rhs).1
    }

    pub const fn wrapping_short_irem_signed(self, rhs: i64) -> i64 {
        self.wrapping_short_idivrem_signed(rhs).1
    }

    pub const fn short_irem_signed(self, rhs: i64) -> i64 {
        self.short_idivrem_signed(rhs).1
    }

    pub const fn overflowing_rem_signed(self, rhs: Self) -> (Self, bool) {
        let (_, rem, overflows) = self.overflowing_divrem_signed(rhs);
        (rem, overflows)
    }

    pub const fn checked_rem_signed(self, rhs: Self) -> Option<Self> {
        match self.checked_divrem_signed(rhs) {
            Some((_, rem)) => Some(rem),
            None => None,
        }
    }

    pub const fn saturating_rem_signed(self, rhs: Self) -> Self {
        self.saturating_divrem_signed(rhs).1
    }

    pub const fn wrapping_rem_signed(self, rhs: Self) -> Self {
        self.wrapping_divrem_signed(rhs).1
    }

    pub const fn rem_signed(self, rhs: Self) -> Self {
        self.divrem_signed(rhs).1
    }

    pub const fn overflowing_shl(self, rhs: u32) -> (Self, bool) {
        let mut result = Self::ZERO;
        let overflows = rhs >= Self::BITS;
        let rhs = rhs % Self::BITS;
        let bits = rhs % u64::BITS;
        let byte = (rhs / u64::BITS) as usize;
        let mut i = byte;
        let mut carry = 0;
        if bits > 0 {
            while i < N {
                (result.inner[i], carry) = carrying_shl(self.inner[i - byte], bits, carry);
                i += 1;
            }
        }
        else {
            while i < N {
                result.inner[i] = self.inner[i - byte];
                i += 1;
            }
        }
        (result, overflows)
    }

    pub const fn checked_shl(self, rhs: u32) -> Option<Self> {
        match self.overflowing_shl(rhs) {
            (val, false) => Some(val),
            (_, true) => None,
        }
    }

    pub const fn saturating_shl(self, rhs: u32) -> Self {
        if rhs < Self::BITS {
            self.wrapping_shl(rhs)
        }
        else {
            Self::ZERO
        }
    }

    pub const fn wrapping_shl(self, rhs: u32) -> Self {
        self.overflowing_shl(rhs).0
    }

    #[cfg(debug)]
    pub const fn shl(self, rhs: u32) -> Self {
        match self.overflowing_shl(rhs) {
            (val, false) => val,
            (_, true) => panic!("attempt to shift left with overflow"),
        }
    }

    #[cfg(release)]
    pub const fn shl(self, rhs: u32) -> Self {
        self.wrapping_shl(rhs)
    }

    pub const fn overflowing_shr_unsigned(self, rhs: u32) -> (Self, bool) {
        let mut result = Self::ZERO;
        let overflows = rhs >= Self::BITS;
        let rhs = rhs % Self::BITS;
        let bits = rhs % u64::BITS;
        let byte = (rhs / u64::BITS) as usize;
        let mut i = N - byte;
        let mut carry = 0;
        if bits > 0 {
            while i > 0 {
                i -= 1;
                (result.inner[i], carry) = carrying_shr(self.inner[i + byte], bits, carry);
            }
        }
        else {
            while i > 0 {
                i -= 1;
                result.inner[i] = self.inner[i + byte];
            }
        }
        (result, overflows)
    }

    pub const fn checked_shr_unsigned(self, rhs: u32) -> Option<Self> {
        match self.overflowing_shr_unsigned(rhs) {
            (val, false) => Some(val),
            (_, true) => None,
        }
    }

    pub const fn saturating_shr_unsigned(self, rhs: u32) -> Self {
        if rhs < Self::BITS {
            self.wrapping_shr_unsigned(rhs)
        }
        else {
            Self::ZERO
        }
    }

    pub const fn wrapping_shr_unsigned(self, rhs: u32) -> Self {
        self.overflowing_shr_unsigned(rhs).0
    }

    #[cfg(debug)]
    pub const fn shr_unsigned(self, rhs: u32) -> Self {
        match self.overflowing_shr_unsigned(rhs) {
            (val, false) => val,
            (_, true) => panic!("attempt to shift right with overflow"),
        }
    }

    #[cfg(release)]
    pub const fn shr_unsigned(self, rhs: u32) -> Self {
        self.wrapping_shr_unsigned(rhs)
    }

    pub const fn overflowing_shr_signed(self, rhs: u32) -> (Self, bool) {
        let (mut result, overflows) = self.overflowing_shr_unsigned(rhs);
        if self.is_negative() {
            let rhs = rhs % Self::BITS;
            let bits = rhs % u64::BITS;
            let byte = (rhs / u64::BITS) as usize;
            let mut i = N;
            while i > N - byte {
                i -= 1;
                result.inner[i] = !0;
            }
            if i > 0 {
                i -= 1;
                result.inner[i] |= !(!0 >> bits);
            }
        }
        (result, overflows)
    }

    pub const fn checked_shr_signed(self, rhs: u32) -> Option<Self> {
        match self.overflowing_shr_signed(rhs) {
            (val, false) => Some(val),
            (_, true) => None,
        }
    }

    pub const fn saturating_shr_signed(self, rhs: u32) -> Self {
        if rhs < Self::BITS {
            self.wrapping_shr_signed(rhs)
        }
        else if self.is_negative() {
            Self::MINUS_ONE
        }
        else {
            Self::ZERO
        }
    }

    pub const fn wrapping_shr_signed(self, rhs: u32) -> Self {
        self.overflowing_shr_signed(rhs).0
    }

    #[cfg(debug)]
    pub const fn shr_signed(self, rhs: u32) -> Self {
        match self.overflowing_shr_signed(rhs) {
            (val, false) => val,
            (_, true) => panic!("attempt to shift right with overflow"),
        }
    }

    #[cfg(release)]
    pub const fn shr_signed(self, rhs: u32) -> Self {
        self.wrapping_shr_signed(rhs)
    }

    pub const fn overflowing_pow_unsigned(mut self, mut exp: u32) -> (Self, bool) {
        if exp == 0 {
            return (Self::ONE, false);
        }
        let mut overflows @ mut o1 = false;
        let mut o2;
        let mut acc = Self::ONE;
        while exp > 1 {
            if exp % 2 != 0 {
                (acc, o1) = self.overflowing_mul_unsigned(acc);
            }
            (self, o2) = self.overflowing_mul_unsigned(self);
            overflows |= o1 || o2;
            exp /= 2;
        }
        (self, o1) = self.overflowing_mul_unsigned(acc);
        (self, overflows || o1)
    }

    pub const fn checked_pow_unsigned(self, exp: u32) -> Option<Self> {
        match self.overflowing_pow_unsigned(exp) {
            (val, false) => Some(val),
            (_, true) => None,
        }
    }

    pub const fn saturating_pow_unsigned(self, exp: u32) -> Self {
        match self.overflowing_pow_unsigned(exp) {
            (val, false) => val,
            (_, true) => Self::MAX_UNSIGNED,
        }
    }

    pub const fn wrapping_pow_unsigned(self, exp: u32) -> Self {
        self.overflowing_pow_unsigned(exp).0
    }

    #[cfg(debug)]
    pub const fn pow_unsigned(self, exp: u32) -> Self {
        match self.overflowing_pow_unsigned(exp) {
            (val, false) => val,
            (_, true) => panic!("attempt to pow with overflow"),
        }
    }

    #[cfg(release)]
    pub const fn pow_unsigned(self, exp: u32) -> Self {
        self.wrapping_pow_unsigned(exp)
    }

    pub const fn overflowing_pow_signed(mut self, mut exp: u32) -> (Self, bool) {
        if exp == 0 {
            return (Self::ONE, false);
        }
        let mut overflows @ mut o1 = false;
        let mut o2;
        let mut acc = Self::ONE;
        while exp > 1 {
            if exp % 2 != 0 {
                (acc, o1) = self.overflowing_mul_signed(acc);
            }
            (self, o2) = self.overflowing_mul_signed(self);
            overflows |= o1 || o2;
            exp /= 2;
        }
        (self, o1) = self.overflowing_mul_signed(acc);
        (self, overflows || o1)
    }

    pub const fn checked_pow_signed(self, exp: u32) -> Option<Self> {
        match self.overflowing_pow_signed(exp) {
            (val, false) => Some(val),
            (_, true) => None,
        }
    }

    pub const fn saturating_pow_signed(self, exp: u32) -> Self {
        match self.overflowing_pow_signed(exp) {
            (val, false) => val,
            (_, true) if self.is_negative() && exp % 2 != 0 =>
                Self::MIN_SIGNED,
            (_, true) => Self::MAX_SIGNED,
        }
    }

    pub const fn wrapping_pow_signed(self, exp: u32) -> Self {
        self.overflowing_pow_signed(exp).0
    }

    #[cfg(debug)]
    pub const fn pow_signed(self, exp: u32) -> Self {
        match self.overflowing_pow_signed(exp) {
            (val, false) => val,
            (_, true) => panic!("attempt to pow with overflow"),
        }
    }

    #[cfg(release)]
    pub const fn pow_signed(self, exp: u32) -> Self {
        self.wrapping_pow_signed(exp)
    }

    pub const fn overflowing_divrem_euclid(self, rhs: Self) -> (Self, Self, bool) {
        let (mut quot, mut rem, overflows) = self.overflowing_divrem_signed(rhs);
        if rem.is_negative() {
            if rhs.is_negative() {
                quot = quot.wrapping_add(Self::ONE);
                rem = rem.wrapping_sub(rhs);
            }
            else {
                quot = quot.wrapping_sub(Self::ONE);
                rem = rem.wrapping_add(rhs);
            }
        }
        (quot, rem, overflows)
    }

    pub const fn checked_divrem_euclid(self, rhs: Self) -> Option<(Self, Self)> {
        if rhs.equals(&Self::ZERO) {
            return None;
        }
        match self.overflowing_divrem_euclid(rhs) {
            (quot, rem, false) => Some((quot, rem)),
            (_, _, true) => None,
        }
    }

    pub const fn saturating_divrem_euclid(self, rhs: Self) -> (Self, Self) {
        match self.overflowing_divrem_euclid(rhs) {
            (quot, rem, false) => (quot, rem),
            (_, _, true) => (Self::MAX_SIGNED, Self::ZERO),
        }
    }

    pub const fn wrapping_divrem_euclid(self, rhs: Self) -> (Self, Self) {
        let (quot, rem, _) = self.overflowing_divrem_euclid(rhs);
        (quot, rem)
    }

    pub const fn divrem_euclid(self, rhs: Self) -> (Self, Self) {
        match self.overflowing_divrem_euclid(rhs) {
            (quot, rem, false) => (quot, rem),
            (_, _, true) => panic!("attempt to divide with overflow"),
        }
    }

    pub const fn overflowing_div_euclid(self, rhs: Self) -> (Self, bool) {
        let (quot, _, overflows) = self.overflowing_divrem_euclid(rhs);
        (quot, overflows)
    }

    pub const fn checked_div_euclid(self, rhs: Self) -> Option<Self> {
        match self.checked_divrem_euclid(rhs) {
            Some((quot, _)) => Some(quot),
            None => None,
        }
    }

    pub const fn saturating_div_euclid(self, rhs: Self) -> Self {
        self.saturating_divrem_euclid(rhs).0
    }

    pub const fn wrapping_div_euclid(self, rhs: Self) -> Self {
        self.wrapping_divrem_euclid(rhs).0
    }

    pub const fn div_euclid(self, rhs: Self) -> Self {
        self.divrem_euclid(rhs).0
    }

    pub const fn overflowing_rem_euclid(self, rhs: Self) -> (Self, bool) {
        let (_, rem, overflows) = self.overflowing_divrem_euclid(rhs);
        (rem, overflows)
    }

    pub const fn checked_rem_euclid(self, rhs: Self) -> Option<Self> {
        match self.checked_divrem_euclid(rhs) {
            Some((_, rem)) => Some(rem),
            None => None,
        }
    }

    pub const fn saturating_rem_euclid(self, rhs: Self) -> Self {
        self.saturating_divrem_euclid(rhs).1
    }

    pub const fn wrapping_rem_euclid(self, rhs: Self) -> Self {
        self.wrapping_divrem_euclid(rhs).1
    }

    pub const fn rem_euclid(self, rhs: Self) -> Self {
        self.divrem_euclid(rhs).1
    }

    pub const fn count_ones(self) -> u32 {
        let mut ones = 0;
        let mut i = N;
        while i > 0 {
            i -= 1;
            ones += self.inner[i].count_ones();
        }
        ones
    }

    pub const fn count_zeros(self) -> u32 {
        let mut zeros = 0;
        let mut i = N;
        while i > 0 {
            i -= 1;
            zeros += self.inner[i].count_zeros();
        }
        zeros
    }

    pub const fn leading_ones(self) -> u32 {
        let mut ones = 0;
        let mut i = N;
        while i > 0 && ones / u64::BITS == (N - i) as u32 {
            i -= 1;
            ones = self.inner[i].leading_ones();
        }
        ones
    }

    pub const fn leading_zeros(self) -> u32 {
        let mut zeros = 0;
        let mut i = N;
        while i > 0 && zeros / u64::BITS == (N - i) as u32 {
            i -= 1;
            zeros += self.inner[i].leading_zeros();
        }
        zeros
    }

    pub const fn trailing_ones(self) -> u32 {
        let mut ones = 0;
        let mut i = 0;
        while i < N && ones / u64::BITS == i as u32 {
            ones = self.inner[i].trailing_ones();
            i += 1;
        }
        ones
    }

    pub const fn trailing_zeros(self) -> u32 {
        let mut zeros = 0;
        let mut i = 0;
        while i < N && zeros / u64::BITS == i as u32 {
            zeros += self.inner[i].trailing_zeros();
            i += 1;
        }
        zeros
    }

    pub const fn rotate_left(self, n: u32) -> Self {
        let n = n % Self::BITS;
        self.wrapping_shl(n).bitor(self.wrapping_shr_unsigned(Self::BITS - n))
    }

    pub const fn rotate_right(self, n: u32) -> Self {
        let n = n % Self::BITS;
        self.wrapping_shr_unsigned(n).bitor(self.wrapping_shl(Self::BITS - n))
    }

    pub const fn swap_words(mut self) -> Self {
        let mut i = N / 2;
        let mut j = N - i;
        while i > 0 && j < N {
            i -= 1;
            (self.inner[i], self.inner[j]) = (self.inner[j], self.inner[i]);
            j += 1;
        }
        self
    }

    pub const fn swap_bytes(mut self) -> Self {
        let mut i = N;
        while i > 0 {
            i -= 1;
            self.inner[i] = self.inner[i].swap_bytes();
        }
        self.swap_words()
    }

    pub const fn reverse_bits(mut self) -> Self {
        let mut i = N;
        while i > 0 {
            i -= 1;
            self.inner[i] = self.inner[i].reverse_bits();
        }
        self.swap_words()
    }

    pub const fn is_power_of_two(self) -> bool {
        self.count_ones() == 1
    }

    const fn overflowing_next_power_of_two(self) -> (Self, bool) {
        let n = self.wrapping_sub(Self::ONE);
        if self.is_negative() && n.is_negative() {
            return (Self::ZERO, true);
        }
        else if n.is_negative() {
            return (Self::ONE, false);
        }
        (Self::MAX_UNSIGNED.saturating_shr_unsigned(n.leading_zeros()).wrapping_add(Self::ONE), false)
    }

    pub const fn checked_next_power_of_two(self) -> Option<Self> {
        match self.overflowing_next_power_of_two() {
            (val, false) => Some(val),
            (_, true) => None,
        }
    }

    pub const fn wrapping_next_power_of_two(self) -> Self {
        self.overflowing_next_power_of_two().0
    }

    #[cfg(debug)]
    pub const fn next_power_of_two(self) -> Self {
        match self.overflowing_next_power_of_two() {
            (val, false) => val,
            (_, true) => panic!("attempt to next power of two with overflow"),
        }
    }

    #[cfg(release)]
    pub const fn next_power_of_two(self) -> Self {
        self.wrapping_next_power_of_two()
    }

    pub const fn unsigned_abs(self) -> Self {
        match self.is_negative() {
            true => self.wrapping_neg(),
            false => self,
        }
    }

    pub const fn overflowing_abs(self) -> (Self, bool) {
        let result = self.wrapping_abs();
        (result, self.is_negative() && result.is_negative())
    }

    pub const fn checked_abs(self) -> Option<Self> {
        match self.overflowing_abs() {
            (val, false) => Some(val),
            (_, true) => None,
        }
    }

    pub const fn saturating_abs(self) -> Self {
        match self.overflowing_abs() {
            (val, false) => val,
            (_, true) => Self::MAX_SIGNED,
        }
    }

    pub const fn wrapping_abs(self) -> Self {
        self.unsigned_abs()
    }

    #[cfg(debug)]
    pub const fn abs(self) -> Self {
        match self.overflowing_abs() {
            (val, false) => val,
            (_, true) => panic!("attempt to abs with overflow"),
        }
    }

    #[cfg(release)]
    pub const fn abs(self) -> Self {
        self.wrapping_abs()
    }
}

fn repr_fmt<const N: usize>(
    this: &Repr<N>,
    f: &mut fmt::Formatter<'_>,
    val_fmt: impl Fn(&u64, &mut fmt::Formatter<'_>) -> fmt::Result,
) -> fmt::Result {
    debug_fmt(this, "Repr", f, val_fmt)
}

#[cfg_attr(hide_internal, doc(hidden))]
pub fn debug_fmt<const N: usize>(
    this: &Repr<N>,
    prefix: &str,
    f: &mut fmt::Formatter<'_>,
    val_fmt: impl Fn(&u64, &mut fmt::Formatter<'_>) -> fmt::Result,
) -> fmt::Result {
    f.write_str(prefix)?;
    f.write_str(" [")?;
    let mut inner = this.inner.iter();
    for val in inner.next() {
        val_fmt(val, f)?;
    }
    for val in inner {
        f.write_str(", ")?;
        val_fmt(val, f)?;
    }
    f.write_str("]")
}

fn segmented_fmt_next(
    past_zero: &mut bool,
    not_zero: bool,
    f: &mut fmt::Formatter<'_>,
    fmt_just_past_zero: impl FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result,
    fmt_past_zero: impl FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result,
) -> fmt::Result {
    if !*past_zero && !not_zero {
        return Ok(());
    }
    match core::mem::replace(past_zero, true) {
        false => fmt_just_past_zero(f),
        true => fmt_past_zero(f),
    }
}

fn segmented_fmt_end(f: &mut fmt::Formatter<'_>, past_zero: bool) -> fmt::Result {
    match past_zero {
        true => Ok(()),
        false => f.write_str("0"),
    }
}

#[cfg_attr(hide_internal, doc(hidden))]
pub fn fmt_unsigned<const N: usize>(this: &Repr<N>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut rems = [0; N];
    let mut this = *this;
    for i in (0..N).rev() {
        (this, rems[i]) = this.short_divrem_unsigned(10_000_000_000_000_000_000);
    }
    let mut last_rem = Some(this.inner[0]);
    if this.inner[1..].iter().any(|el| el != &0) {
        f.write_str("...")?;
        last_rem = None;
    }
    let mut past_zero = false;
    let fmt = |val| {
        segmented_fmt_next(
            &mut past_zero, val > 0, f,
            |f| fmt::Display::fmt(&val, f),
            |f| write!(f, "{val:019}"),
        )
    };
    last_rem.into_iter().chain(rems).try_for_each(fmt)?;
    segmented_fmt_end(f, past_zero)
}

#[cfg_attr(hide_internal, doc(hidden))]
pub fn fmt_signed<const N: usize>(this: &Repr<N>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if this.is_negative() {
        f.write_str("-")?;
    }
    fmt_unsigned(&this.unsigned_abs(), f)
}

#[cfg_attr(hide_internal, doc(hidden))]
pub fn fmt_binary<const N: usize>(this: &Repr<N>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut past_zero = false;
    let mut fmt = |val| {
        segmented_fmt_next(
            &mut past_zero, val > 0, f,
            |f| fmt::Binary::fmt(&val, f),
            |f| write!(f, "{val:064b}"),
        )
    };
    this.inner.iter().rev().try_for_each(|&val| fmt(val))?;
    segmented_fmt_end(f, past_zero)
}

#[cfg_attr(hide_internal, doc(hidden))]
pub fn fmt_lower_hex<const N: usize>(this: &Repr<N>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut past_zero = false;
    let mut fmt = |val| {
        segmented_fmt_next(
            &mut past_zero, val > 0, f,
            |f| fmt::LowerHex::fmt(&val, f),
            |f| write!(f, "{val:016x}"),
        )
    };
    this.inner.iter().rev().try_for_each(|&val| fmt(val))?;
    segmented_fmt_end(f, past_zero)
}

#[cfg_attr(hide_internal, doc(hidden))]
pub fn fmt_upper_hex<const N: usize>(this: &Repr<N>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut past_zero = false;
    let mut fmt = |val| {
        segmented_fmt_next(
            &mut past_zero, val > 0, f,
            |f| fmt::UpperHex::fmt(&val, f),
            |f| write!(f, "{val:016X}"),
        )
    };
    this.inner.iter().rev().try_for_each(|&val| fmt(val))?;
    segmented_fmt_end(f, past_zero)
}

#[cfg_attr(hide_internal, doc(hidden))]
pub fn fmt_octal<const N: usize>(this: &Repr<N>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let chunks_exact = this.inner.chunks_exact(3);
    let mut past_zero = false;
    let mut fmt = |&[x, y, z]: &[u64; 3]| {
        let lo = array_pair_to_u128([x, y]) & (u128::MAX >> 32);
        let hi = array_pair_to_u128([y, z]) >> 32;
        for val in [hi, lo] {    
            segmented_fmt_next(
                &mut past_zero, val > 0, f,
                |f| fmt::Octal::fmt(&val, f),
                |f| write!(f, "{val:032o}"),
            )?;
        }
        Ok(())
    };
    match chunks_exact.remainder() {
        [] => (),
        &[x] => fmt(&[x, 0, 0])?,
        &[x, y, ..] => fmt(&[x, y, 0])?,
    }
    chunks_exact.rev()
        .filter_map(|chunk| chunk.try_into().ok())
        .try_for_each(fmt)?;
    segmented_fmt_end(f, past_zero)
}

impl<const N: usize> fmt::Debug for Repr<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        repr_fmt(self, f, |val, f| val.fmt(f))
    }
}

impl<const N: usize> fmt::UpperHex for Repr<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        repr_fmt(self, f, |val, f| val.fmt(f))
    }
}

impl<const N: usize> fmt::LowerHex for Repr<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        repr_fmt(self, f, |val, f| val.fmt(f))
    }
}
