use core::cmp;
use core::marker::StructuralPartialEq;
use core::marker::StructuralEq;
use core::ops;
use core::str;
use crate::i256;
use crate::i384;
use crate::i512;

impl const Default for i512 {
    fn default() -> Self {
        Self::ZERO
    }
}

impl const cmp::PartialEq for i512 {
    fn eq(&self, other: &Self) -> bool {
        self.inner.equals(&other.inner)
    }
}

impl Eq for i512 {}

impl StructuralPartialEq for i512 {}

impl StructuralEq for i512 {}

impl const cmp::PartialOrd for i512 {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl const cmp::Ord for i512 {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.inner.compare_unsigned(&other.inner)
    }

    fn max(self, other: Self) -> Self {
        if self < other {
            other
        }
        else {
            self
        }
    }

    fn min(self, other: Self) -> Self {
        if self > other {
            other
        }
        else {
            self
        }
    }

    fn clamp(self, min: Self, max: Self) -> Self {
        assert!(min <= max);
        if self < min {
            min
        }
        else if self > max {
            max
        }
        else {
            self
        }
    }
}

impl ops::Neg for &i512 {
    type Output = i512;

    fn neg(self) -> Self::Output {
        (*self).neg()
    }
}

impl ops::Neg for i512 {
    type Output = Self;

    fn neg(self) -> Self::Output {
        self.neg()
    }
}

impl ops::Add for &i512 {
    type Output = i512;

    fn add(self, rhs: Self) -> Self::Output {
        (*self).add(*rhs)
    }
}

impl ops::Add<i512> for &i512 {
    type Output = i512;

    fn add(self, rhs: i512) -> Self::Output {
        (*self).add(rhs)
    }
}

impl ops::Add<&i512> for i512 {
    type Output = Self;

    fn add(self, rhs: &i512) -> Self::Output {
        self.add(*rhs)
    }
}

impl ops::Add for i512 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        self.add(rhs)
    }
}

impl ops::AddAssign for i512 {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl ops::AddAssign<&i512> for i512 {
    fn add_assign(&mut self, rhs: &i512) {
        *self = *self + *rhs;
    }
}

impl ops::Sub for &i512 {
    type Output = i512;

    fn sub(self, rhs: Self) -> Self::Output {
        (*self).sub(*rhs)
    }
}

impl ops::Sub<i512> for &i512 {
    type Output = i512;

    fn sub(self, rhs: i512) -> Self::Output {
        (*self).sub(rhs)
    }
}

impl ops::Sub<&i512> for i512 {
    type Output = Self;

    fn sub(self, rhs: &i512) -> Self::Output {
        self.sub(*rhs)
    }
}

impl ops::Sub for i512 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.sub(rhs)
    }
}

impl ops::SubAssign for i512 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl ops::SubAssign<&i512> for i512 {
    fn sub_assign(&mut self, rhs: &i512) {
        *self = *self - *rhs;
    }
}

impl ops::Mul<&i64> for &i512 {
    type Output = i512;

    fn mul(self, rhs: &i64) -> Self::Output {
        (*self).short_mul(*rhs)
    }
}

impl ops::Mul<i64> for &i512 {
    type Output = i512;

    fn mul(self, rhs: i64) -> Self::Output {
        (*self).short_mul(rhs)
    }
}

impl ops::Mul<&i64> for i512 {
    type Output = i512;

    fn mul(self, rhs: &i64) -> Self::Output {
        self.short_mul(*rhs)
    }
}

impl ops::Mul<i64> for i512 {
    type Output = i512;

    fn mul(self, rhs: i64) -> Self::Output {
        self.short_mul(rhs)
    }
}

impl ops::Mul for &i512 {
    type Output = i512;

    fn mul(self, rhs: Self) -> Self::Output {
        (*self).mul(*rhs)
    }
}

impl ops::Mul<i512> for &i512 {
    type Output = i512;

    fn mul(self, rhs: i512) -> Self::Output {
        (*self).mul(rhs)
    }
}

impl ops::Mul<&i512> for i512 {
    type Output = Self;

    fn mul(self, rhs: &i512) -> Self::Output {
        self.mul(*rhs)
    }
}

impl ops::Mul for i512 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        self.mul(rhs)
    }
}

impl ops::MulAssign for i512 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl ops::MulAssign<&i512> for i512 {
    fn mul_assign(&mut self, rhs: &i512) {
        *self = *self * *rhs;
    }
}

impl ops::MulAssign<i64> for i512 {
    fn mul_assign(&mut self, rhs: i64) {
        *self = *self * rhs;
    }
}

impl ops::MulAssign<&i64> for i512 {
    fn mul_assign(&mut self, rhs: &i64) {
        *self = *self * *rhs;
    }
}

impl ops::Div<&i64> for &i512 {
    type Output = i512;

    fn div(self, rhs: &i64) -> Self::Output {
        (*self).short_div(*rhs)
    }
}

impl ops::Div<i64> for &i512 {
    type Output = i512;

    fn div(self, rhs: i64) -> Self::Output {
        (*self).short_div(rhs)
    }
}

impl ops::Div<&i64> for i512 {
    type Output = i512;

    fn div(self, rhs: &i64) -> Self::Output {
        self.short_div(*rhs)
    }
}

impl ops::Div<i64> for i512 {
    type Output = i512;

    fn div(self, rhs: i64) -> Self::Output {
        self.short_div(rhs)
    }
}

impl ops::Div for &i512 {
    type Output = i512;

    fn div(self, rhs: Self) -> Self::Output {
        (*self).div(*rhs)
    }
}

impl ops::Div<i512> for &i512 {
    type Output = i512;

    fn div(self, rhs: i512) -> Self::Output {
        (*self).div(rhs)
    }
}

impl ops::Div<&i512> for i512 {
    type Output = Self;

    fn div(self, rhs: &i512) -> Self::Output {
        self.div(*rhs)
    }
}

impl ops::Div for i512 {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self.div(rhs)
    }
}

impl ops::DivAssign for i512 {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl ops::DivAssign<&i512> for i512 {
    fn div_assign(&mut self, rhs: &i512) {
        *self = *self / *rhs;
    }
}

impl ops::DivAssign<i64> for i512 {
    fn div_assign(&mut self, rhs: i64) {
        *self = *self / rhs;
    }
}

impl ops::DivAssign<&i64> for i512 {
    fn div_assign(&mut self, rhs: &i64) {
        *self = *self / *rhs;
    }
}

impl ops::Rem<&i64> for &i512 {
    type Output = i64;

    fn rem(self, rhs: &i64) -> Self::Output {
        (*self).short_rem(*rhs)
    }
}

impl ops::Rem<i64> for &i512 {
    type Output = i64;

    fn rem(self, rhs: i64) -> Self::Output {
        (*self).short_rem(rhs)
    }
}

impl ops::Rem<&i64> for i512 {
    type Output = i64;

    fn rem(self, rhs: &i64) -> Self::Output {
        self.short_rem(*rhs)
    }
}

impl ops::Rem<i64> for i512 {
    type Output = i64;

    fn rem(self, rhs: i64) -> Self::Output {
        self.short_rem(rhs)
    }
}

impl ops::Rem for &i512 {
    type Output = i512;

    fn rem(self, rhs: Self) -> Self::Output {
        (*self).rem(*rhs)
    }
}

impl ops::Rem<i512> for &i512 {
    type Output = i512;

    fn rem(self, rhs: i512) -> Self::Output {
        (*self).rem(rhs)
    }
}

impl ops::Rem<&i512> for i512 {
    type Output = Self;

    fn rem(self, rhs: &i512) -> Self::Output {
        self.rem(*rhs)
    }
}

impl ops::Rem for i512 {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        self.rem(rhs)
    }
}

impl ops::RemAssign for i512 {
    fn rem_assign(&mut self, rhs: Self) {
        *self = *self % rhs;
    }
}

impl ops::RemAssign<&i512> for i512 {
    fn rem_assign(&mut self, rhs: &i512) {
        *self = *self % *rhs;
    }
}

impl ops::RemAssign<i64> for i512 {
    fn rem_assign(&mut self, rhs: i64) {
        *self = Self::from_i64(*self % rhs);
    }
}

impl ops::RemAssign<&i64> for i512 {
    fn rem_assign(&mut self, rhs: &i64) {
        *self = Self::from_i64(*self % *rhs);
    }
}

impl ops::Not for i512 {
    type Output = Self;

    fn not(self) -> Self::Output {
        self.not()
    }
}

impl ops::Not for &i512 {
    type Output = i512;

    fn not(self) -> Self::Output {
        (*self).not()
    }
}

impl ops::BitAnd for &i512 {
    type Output = i512;

    fn bitand(self, rhs: Self) -> Self::Output {
        (*self).bitand(*rhs)
    }
}

impl ops::BitAnd<i512> for &i512 {
    type Output = i512;

    fn bitand(self, rhs: i512) -> Self::Output {
        (*self).bitand(rhs)
    }
}

impl ops::BitAnd<&i512> for i512 {
    type Output = Self;

    fn bitand(self, rhs: &i512) -> Self::Output {
        self.bitand(*rhs)
    }
}

impl ops::BitAnd for i512 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        self.bitand(rhs)
    }
}

impl ops::BitAndAssign for i512 {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

impl ops::BitAndAssign<&i512> for i512 {
    fn bitand_assign(&mut self, rhs: &Self) {
        *self = *self & *rhs;
    }
}

impl ops::BitOr for &i512 {
    type Output = i512;

    fn bitor(self, rhs: Self) -> Self::Output {
        (*self).bitor(*rhs)
    }
}

impl ops::BitOr<i512> for &i512 {
    type Output = i512;

    fn bitor(self, rhs: i512) -> Self::Output {
        (*self).bitor(rhs)
    }
}

impl ops::BitOr<&i512> for i512 {
    type Output = Self;

    fn bitor(self, rhs: &i512) -> Self::Output {
        self.bitor(*rhs)
    }
}

impl ops::BitOr for i512 {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        self.bitor(rhs)
    }
}

impl ops::BitOrAssign for i512 {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

impl ops::BitOrAssign<&i512> for i512 {
    fn bitor_assign(&mut self, rhs: &Self) {
        *self = *self | *rhs;
    }
}

impl ops::BitXor for &i512 {
    type Output = i512;

    fn bitxor(self, rhs: Self) -> Self::Output {
        (*self).bitxor(*rhs)
    }
}

impl ops::BitXor<i512> for &i512 {
    type Output = i512;

    fn bitxor(self, rhs: i512) -> Self::Output {
        (*self).bitxor(rhs)
    }
}

impl ops::BitXor<&i512> for i512 {
    type Output = Self;

    fn bitxor(self, rhs: &i512) -> Self::Output {
        self.bitxor(*rhs)
    }
}

impl ops::BitXor for i512 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        self.bitxor(rhs)
    }
}

impl ops::BitXorAssign for i512 {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs;
    }
}

impl ops::BitXorAssign<&i512> for i512 {
    fn bitxor_assign(&mut self, rhs: &Self) {
        *self = *self ^ *rhs;
    }
}

impl From<u8> for i512 {
    fn from(n: u8) -> Self {
        Self::from_u8(n)
    }
}

impl From<u16> for i512 {
    fn from(n: u16) -> Self {
        Self::from_u16(n)
    }
}

impl From<u32> for i512 {
    fn from(n: u32) -> Self {
        Self::from_u32(n)
    }
}

impl From<u64> for i512 {
    fn from(n: u64) -> Self {
        Self::from_u64(n)
    }
}

impl From<u128> for i512 {
    fn from(n: u128) -> Self {
        Self::from_u128(n)
    }
}
impl From<i8> for i512 {
    fn from(n: i8) -> Self {
        Self::from_i8(n)
    }
}

impl From<i16> for i512 {
    fn from(n: i16) -> Self {
        Self::from_i16(n)
    }
}

impl From<i32> for i512 {
    fn from(n: i32) -> Self {
        Self::from_i32(n)
    }
}

impl From<i64> for i512 {
    fn from(n: i64) -> Self {
        Self::from_i64(n)
    }
}

impl From<i128> for i512 {
    fn from(n: i128) -> Self {
        Self::from_i128(n)
    }
}

impl From<i256> for i512 {
    fn from(n: i256) -> Self {
        Self::from_i256(n)
    }
}

impl From<i384> for i512 {
    fn from(n: i384) -> Self {
        Self::from_i384(n)
    }
}

impl str::FromStr for i512 {
    type Err = crate::ParseIntError;

    fn from_str(src: &str) -> Result<Self, Self::Err> {
        Self::from_str(src)
    }
}

impl ops::Shl<&u32> for i512 {
    type Output = Self;

    fn shl(self, rhs: &u32) -> Self::Output {
        self.shl(*rhs)
    }
}

impl ops::Shl<u32> for i512 {
    type Output = Self;

    fn shl(self, rhs: u32) -> Self::Output {
        self.shl(rhs)
    }
}

impl ops::ShlAssign<&u32> for i512 {
    fn shl_assign(&mut self, rhs: &u32) {
        *self = *self << rhs;
    }
}

impl ops::ShlAssign<u32> for i512 {
    fn shl_assign(&mut self, rhs: u32) {
        *self = *self << rhs;
    }
}

impl ops::Shr<&u32> for i512 {
    type Output = Self;

    fn shr(self, rhs: &u32) -> Self::Output {
        self.shr(*rhs)
    }
}

impl ops::Shr<u32> for i512 {
    type Output = Self;

    fn shr(self, rhs: u32) -> Self::Output {
        self.shr(rhs)
    }
}

impl ops::ShrAssign<&u32> for i512 {
    fn shr_assign(&mut self, rhs: &u32) {
        *self = *self >> rhs;
    }
}

impl ops::ShrAssign<u32> for i512 {
    fn shr_assign(&mut self, rhs: u32) {
        *self = *self >> rhs;
    }
}
