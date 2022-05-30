use core::cmp;
use core::ops;
use core::str;
use crate::u256;
use crate::u384;
use crate::u512;

impl cmp::PartialOrd for u512 {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl cmp::Ord for u512 {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.inner.compare_unsigned(&other.inner)
    }
}

impl ops::Add for &u512 {
    type Output = u512;

    fn add(self, rhs: Self) -> Self::Output {
        (*self).add(*rhs)
    }
}

impl ops::Add<u512> for &u512 {
    type Output = u512;

    fn add(self, rhs: u512) -> Self::Output {
        (*self).add(rhs)
    }
}

impl ops::Add<&u512> for u512 {
    type Output = Self;

    fn add(self, rhs: &u512) -> Self::Output {
        self.add(*rhs)
    }
}

impl ops::Add for u512 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        self.add(rhs)
    }
}

impl ops::AddAssign for u512 {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl ops::AddAssign<&u512> for u512 {
    fn add_assign(&mut self, rhs: &u512) {
        *self = *self + *rhs;
    }
}

impl ops::Sub for &u512 {
    type Output = u512;

    fn sub(self, rhs: Self) -> Self::Output {
        (*self).sub(*rhs)
    }
}

impl ops::Sub<u512> for &u512 {
    type Output = u512;

    fn sub(self, rhs: u512) -> Self::Output {
        (*self).sub(rhs)
    }
}

impl ops::Sub<&u512> for u512 {
    type Output = Self;

    fn sub(self, rhs: &u512) -> Self::Output {
        self.sub(*rhs)
    }
}

impl ops::Sub for u512 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.sub(rhs)
    }
}

impl ops::SubAssign for u512 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl ops::SubAssign<&u512> for u512 {
    fn sub_assign(&mut self, rhs: &u512) {
        *self = *self - *rhs;
    }
}

impl ops::Mul<&u64> for &u512 {
    type Output = u512;

    fn mul(self, rhs: &u64) -> Self::Output {
        (*self).short_mul(*rhs)
    }
}

impl ops::Mul<u64> for &u512 {
    type Output = u512;

    fn mul(self, rhs: u64) -> Self::Output {
        (*self).short_mul(rhs)
    }
}

impl ops::Mul<&u64> for u512 {
    type Output = u512;

    fn mul(self, rhs: &u64) -> Self::Output {
        self.short_mul(*rhs)
    }
}

impl ops::Mul<u64> for u512 {
    type Output = u512;

    fn mul(self, rhs: u64) -> Self::Output {
        self.short_mul(rhs)
    }
}

impl ops::Mul for &u512 {
    type Output = u512;

    fn mul(self, rhs: Self) -> Self::Output {
        (*self).mul(*rhs)
    }
}

impl ops::Mul<u512> for &u512 {
    type Output = u512;

    fn mul(self, rhs: u512) -> Self::Output {
        (*self).mul(rhs)
    }
}

impl ops::Mul<&u512> for u512 {
    type Output = Self;

    fn mul(self, rhs: &u512) -> Self::Output {
        self.mul(*rhs)
    }
}

impl ops::Mul for u512 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        self.mul(rhs)
    }
}

impl ops::MulAssign for u512 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl ops::MulAssign<&u512> for u512 {
    fn mul_assign(&mut self, rhs: &u512) {
        *self = *self * *rhs;
    }
}

impl ops::MulAssign<u64> for u512 {
    fn mul_assign(&mut self, rhs: u64) {
        *self = *self * rhs;
    }
}

impl ops::MulAssign<&u64> for u512 {
    fn mul_assign(&mut self, rhs: &u64) {
        *self = *self * *rhs;
    }
}

impl ops::Div<&u64> for &u512 {
    type Output = u512;

    fn div(self, rhs: &u64) -> Self::Output {
        (*self).short_div(*rhs)
    }
}

impl ops::Div<u64> for &u512 {
    type Output = u512;

    fn div(self, rhs: u64) -> Self::Output {
        (*self).short_div(rhs)
    }
}

impl ops::Div<&u64> for u512 {
    type Output = u512;

    fn div(self, rhs: &u64) -> Self::Output {
        self.short_div(*rhs)
    }
}

impl ops::Div<u64> for u512 {
    type Output = u512;

    fn div(self, rhs: u64) -> Self::Output {
        self.short_div(rhs)
    }
}

impl ops::Div for &u512 {
    type Output = u512;

    fn div(self, rhs: Self) -> Self::Output {
        (*self).div(*rhs)
    }
}

impl ops::Div<u512> for &u512 {
    type Output = u512;

    fn div(self, rhs: u512) -> Self::Output {
        (*self).div(rhs)
    }
}

impl ops::Div<&u512> for u512 {
    type Output = Self;

    fn div(self, rhs: &u512) -> Self::Output {
        self.div(*rhs)
    }
}

impl ops::Div for u512 {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self.div(rhs)
    }
}

impl ops::DivAssign for u512 {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl ops::DivAssign<&u512> for u512 {
    fn div_assign(&mut self, rhs: &u512) {
        *self = *self / *rhs;
    }
}

impl ops::DivAssign<u64> for u512 {
    fn div_assign(&mut self, rhs: u64) {
        *self = *self / rhs;
    }
}

impl ops::DivAssign<&u64> for u512 {
    fn div_assign(&mut self, rhs: &u64) {
        *self = *self / *rhs;
    }
}

impl ops::Rem<&u64> for &u512 {
    type Output = u64;

    fn rem(self, rhs: &u64) -> Self::Output {
        (*self).short_rem(*rhs)
    }
}

impl ops::Rem<u64> for &u512 {
    type Output = u64;

    fn rem(self, rhs: u64) -> Self::Output {
        (*self).short_rem(rhs)
    }
}

impl ops::Rem<&u64> for u512 {
    type Output = u64;

    fn rem(self, rhs: &u64) -> Self::Output {
        self.short_rem(*rhs)
    }
}

impl ops::Rem<u64> for u512 {
    type Output = u64;

    fn rem(self, rhs: u64) -> Self::Output {
        self.short_rem(rhs)
    }
}

impl ops::Rem for &u512 {
    type Output = u512;

    fn rem(self, rhs: Self) -> Self::Output {
        (*self).rem(*rhs)
    }
}

impl ops::Rem<u512> for &u512 {
    type Output = u512;

    fn rem(self, rhs: u512) -> Self::Output {
        (*self).rem(rhs)
    }
}

impl ops::Rem<&u512> for u512 {
    type Output = Self;

    fn rem(self, rhs: &u512) -> Self::Output {
        self.rem(*rhs)
    }
}

impl ops::Rem for u512 {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        self.rem(rhs)
    }
}

impl ops::RemAssign for u512 {
    fn rem_assign(&mut self, rhs: Self) {
        *self = *self % rhs;
    }
}

impl ops::RemAssign<&u512> for u512 {
    fn rem_assign(&mut self, rhs: &u512) {
        *self = *self % *rhs;
    }
}

impl ops::RemAssign<u64> for u512 {
    fn rem_assign(&mut self, rhs: u64) {
        *self = Self::from_u64(*self % rhs);
    }
}

impl ops::RemAssign<&u64> for u512 {
    fn rem_assign(&mut self, rhs: &u64) {
        *self = Self::from_u64(*self % *rhs);
    }
}

impl ops::Not for u512 {
    type Output = Self;

    fn not(self) -> Self::Output {
        self.not()
    }
}

impl ops::Not for &u512 {
    type Output = u512;

    fn not(self) -> Self::Output {
        (*self).not()
    }
}

impl ops::BitAnd for &u512 {
    type Output = u512;

    fn bitand(self, rhs: Self) -> Self::Output {
        (*self).bitand(*rhs)
    }
}

impl ops::BitAnd<u512> for &u512 {
    type Output = u512;

    fn bitand(self, rhs: u512) -> Self::Output {
        (*self).bitand(rhs)
    }
}

impl ops::BitAnd<&u512> for u512 {
    type Output = Self;

    fn bitand(self, rhs: &u512) -> Self::Output {
        self.bitand(*rhs)
    }
}

impl ops::BitAnd for u512 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        self.bitand(rhs)
    }
}

impl ops::BitAndAssign for u512 {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

impl ops::BitAndAssign<&u512> for u512 {
    fn bitand_assign(&mut self, rhs: &Self) {
        *self = *self & *rhs;
    }
}

impl ops::BitOr for &u512 {
    type Output = u512;

    fn bitor(self, rhs: Self) -> Self::Output {
        (*self).bitor(*rhs)
    }
}

impl ops::BitOr<u512> for &u512 {
    type Output = u512;

    fn bitor(self, rhs: u512) -> Self::Output {
        (*self).bitor(rhs)
    }
}

impl ops::BitOr<&u512> for u512 {
    type Output = Self;

    fn bitor(self, rhs: &u512) -> Self::Output {
        self.bitor(*rhs)
    }
}

impl ops::BitOr for u512 {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        self.bitor(rhs)
    }
}

impl ops::BitOrAssign for u512 {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

impl ops::BitOrAssign<&u512> for u512 {
    fn bitor_assign(&mut self, rhs: &Self) {
        *self = *self | *rhs;
    }
}

impl ops::BitXor for &u512 {
    type Output = u512;

    fn bitxor(self, rhs: Self) -> Self::Output {
        (*self).bitxor(*rhs)
    }
}

impl ops::BitXor<u512> for &u512 {
    type Output = u512;

    fn bitxor(self, rhs: u512) -> Self::Output {
        (*self).bitxor(rhs)
    }
}

impl ops::BitXor<&u512> for u512 {
    type Output = Self;

    fn bitxor(self, rhs: &u512) -> Self::Output {
        self.bitxor(*rhs)
    }
}

impl ops::BitXor for u512 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        self.bitxor(rhs)
    }
}

impl ops::BitXorAssign for u512 {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs;
    }
}

impl ops::BitXorAssign<&u512> for u512 {
    fn bitxor_assign(&mut self, rhs: &Self) {
        *self = *self ^ *rhs;
    }
}

impl From<u8> for u512 {
    fn from(n: u8) -> Self {
        Self::from_u8(n)
    }
}

impl From<u16> for u512 {
    fn from(n: u16) -> Self {
        Self::from_u16(n)
    }
}

impl From<u32> for u512 {
    fn from(n: u32) -> Self {
        Self::from_u32(n)
    }
}

impl From<u64> for u512 {
    fn from(n: u64) -> Self {
        Self::from_u64(n)
    }
}

impl From<u128> for u512 {
    fn from(n: u128) -> Self {
        Self::from_u128(n)
    }
}

impl From<u256> for u512 {
    fn from(n: u256) -> Self {
        Self::from_u256(n)
    }
}

impl From<u384> for u512 {
    fn from(n: u384) -> Self {
        Self::from_u384(n)
    }
}

impl str::FromStr for u512 {
    type Err = crate::ParseIntError;

    fn from_str(src: &str) -> Result<Self, Self::Err> {
        Self::from_str(src)
    }
}

impl ops::Shl<&u32> for u512 {
    type Output = Self;

    fn shl(self, rhs: &u32) -> Self::Output {
        self.shl(*rhs)
    }
}

impl ops::Shl<u32> for u512 {
    type Output = Self;

    fn shl(self, rhs: u32) -> Self::Output {
        self.shl(rhs)
    }
}

impl ops::ShlAssign<&u32> for u512 {
    fn shl_assign(&mut self, rhs: &u32) {
        *self = *self << rhs;
    }
}

impl ops::ShlAssign<u32> for u512 {
    fn shl_assign(&mut self, rhs: u32) {
        *self = *self << rhs;
    }
}

impl ops::Shr<&u32> for u512 {
    type Output = Self;

    fn shr(self, rhs: &u32) -> Self::Output {
        self.shr(*rhs)
    }
}

impl ops::Shr<u32> for u512 {
    type Output = Self;

    fn shr(self, rhs: u32) -> Self::Output {
        self.shr(rhs)
    }
}

impl ops::ShrAssign<&u32> for u512 {
    fn shr_assign(&mut self, rhs: &u32) {
        *self = *self >> rhs;
    }
}

impl ops::ShrAssign<u32> for u512 {
    fn shr_assign(&mut self, rhs: u32) {
        *self = *self >> rhs;
    }
}
