use core::cmp;
use core::ops;
use core::str;
use crate::u256;
use crate::u384;

impl cmp::PartialOrd for u384 {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl cmp::Ord for u384 {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.inner.compare_unsigned(&other.inner)
    }
}

impl ops::Add for &u384 {
    type Output = u384;

    fn add(self, rhs: Self) -> Self::Output {
        (*self).add(*rhs)
    }
}

impl ops::Add<u384> for &u384 {
    type Output = u384;

    fn add(self, rhs: u384) -> Self::Output {
        (*self).add(rhs)
    }
}

impl ops::Add<&u384> for u384 {
    type Output = Self;

    fn add(self, rhs: &u384) -> Self::Output {
        self.add(*rhs)
    }
}

impl ops::Add for u384 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        self.add(rhs)
    }
}

impl ops::AddAssign for u384 {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl ops::AddAssign<&u384> for u384 {
    fn add_assign(&mut self, rhs: &u384) {
        *self = *self + *rhs;
    }
}

impl ops::Sub for &u384 {
    type Output = u384;

    fn sub(self, rhs: Self) -> Self::Output {
        (*self).sub(*rhs)
    }
}

impl ops::Sub<u384> for &u384 {
    type Output = u384;

    fn sub(self, rhs: u384) -> Self::Output {
        (*self).sub(rhs)
    }
}

impl ops::Sub<&u384> for u384 {
    type Output = Self;

    fn sub(self, rhs: &u384) -> Self::Output {
        self.sub(*rhs)
    }
}

impl ops::Sub for u384 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.sub(rhs)
    }
}

impl ops::SubAssign for u384 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl ops::SubAssign<&u384> for u384 {
    fn sub_assign(&mut self, rhs: &u384) {
        *self = *self - *rhs;
    }
}

impl ops::Mul<&u64> for &u384 {
    type Output = u384;

    fn mul(self, rhs: &u64) -> Self::Output {
        (*self).short_mul(*rhs)
    }
}

impl ops::Mul<u64> for &u384 {
    type Output = u384;

    fn mul(self, rhs: u64) -> Self::Output {
        (*self).short_mul(rhs)
    }
}

impl ops::Mul<&u64> for u384 {
    type Output = u384;

    fn mul(self, rhs: &u64) -> Self::Output {
        self.short_mul(*rhs)
    }
}

impl ops::Mul<u64> for u384 {
    type Output = u384;

    fn mul(self, rhs: u64) -> Self::Output {
        self.short_mul(rhs)
    }
}

impl ops::Mul for &u384 {
    type Output = u384;

    fn mul(self, rhs: Self) -> Self::Output {
        (*self).mul(*rhs)
    }
}

impl ops::Mul<u384> for &u384 {
    type Output = u384;

    fn mul(self, rhs: u384) -> Self::Output {
        (*self).mul(rhs)
    }
}

impl ops::Mul<&u384> for u384 {
    type Output = Self;

    fn mul(self, rhs: &u384) -> Self::Output {
        self.mul(*rhs)
    }
}

impl ops::Mul for u384 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        self.mul(rhs)
    }
}

impl ops::MulAssign for u384 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl ops::MulAssign<&u384> for u384 {
    fn mul_assign(&mut self, rhs: &u384) {
        *self = *self * *rhs;
    }
}

impl ops::MulAssign<u64> for u384 {
    fn mul_assign(&mut self, rhs: u64) {
        *self = *self * rhs;
    }
}

impl ops::MulAssign<&u64> for u384 {
    fn mul_assign(&mut self, rhs: &u64) {
        *self = *self * *rhs;
    }
}

impl ops::Div<&u64> for &u384 {
    type Output = u384;

    fn div(self, rhs: &u64) -> Self::Output {
        (*self).short_div(*rhs)
    }
}

impl ops::Div<u64> for &u384 {
    type Output = u384;

    fn div(self, rhs: u64) -> Self::Output {
        (*self).short_div(rhs)
    }
}

impl ops::Div<&u64> for u384 {
    type Output = u384;

    fn div(self, rhs: &u64) -> Self::Output {
        self.short_div(*rhs)
    }
}

impl ops::Div<u64> for u384 {
    type Output = u384;

    fn div(self, rhs: u64) -> Self::Output {
        self.short_div(rhs)
    }
}

impl ops::Div for &u384 {
    type Output = u384;

    fn div(self, rhs: Self) -> Self::Output {
        (*self).div(*rhs)
    }
}

impl ops::Div<u384> for &u384 {
    type Output = u384;

    fn div(self, rhs: u384) -> Self::Output {
        (*self).div(rhs)
    }
}

impl ops::Div<&u384> for u384 {
    type Output = Self;

    fn div(self, rhs: &u384) -> Self::Output {
        self.div(*rhs)
    }
}

impl ops::Div for u384 {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self.div(rhs)
    }
}

impl ops::DivAssign for u384 {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl ops::DivAssign<&u384> for u384 {
    fn div_assign(&mut self, rhs: &u384) {
        *self = *self / *rhs;
    }
}

impl ops::DivAssign<u64> for u384 {
    fn div_assign(&mut self, rhs: u64) {
        *self = *self / rhs;
    }
}

impl ops::DivAssign<&u64> for u384 {
    fn div_assign(&mut self, rhs: &u64) {
        *self = *self / *rhs;
    }
}

impl ops::Rem<&u64> for &u384 {
    type Output = u64;

    fn rem(self, rhs: &u64) -> Self::Output {
        (*self).short_rem(*rhs)
    }
}

impl ops::Rem<u64> for &u384 {
    type Output = u64;

    fn rem(self, rhs: u64) -> Self::Output {
        (*self).short_rem(rhs)
    }
}

impl ops::Rem<&u64> for u384 {
    type Output = u64;

    fn rem(self, rhs: &u64) -> Self::Output {
        self.short_rem(*rhs)
    }
}

impl ops::Rem<u64> for u384 {
    type Output = u64;

    fn rem(self, rhs: u64) -> Self::Output {
        self.short_rem(rhs)
    }
}

impl ops::Rem for &u384 {
    type Output = u384;

    fn rem(self, rhs: Self) -> Self::Output {
        (*self).rem(*rhs)
    }
}

impl ops::Rem<u384> for &u384 {
    type Output = u384;

    fn rem(self, rhs: u384) -> Self::Output {
        (*self).rem(rhs)
    }
}

impl ops::Rem<&u384> for u384 {
    type Output = Self;

    fn rem(self, rhs: &u384) -> Self::Output {
        self.rem(*rhs)
    }
}

impl ops::Rem for u384 {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        self.rem(rhs)
    }
}

impl ops::RemAssign for u384 {
    fn rem_assign(&mut self, rhs: Self) {
        *self = *self % rhs;
    }
}

impl ops::RemAssign<&u384> for u384 {
    fn rem_assign(&mut self, rhs: &u384) {
        *self = *self % *rhs;
    }
}

impl ops::RemAssign<u64> for u384 {
    fn rem_assign(&mut self, rhs: u64) {
        *self = Self::from_u64(*self % rhs);
    }
}

impl ops::RemAssign<&u64> for u384 {
    fn rem_assign(&mut self, rhs: &u64) {
        *self = Self::from_u64(*self % *rhs);
    }
}

impl ops::Not for u384 {
    type Output = Self;

    fn not(self) -> Self::Output {
        self.not()
    }
}

impl ops::Not for &u384 {
    type Output = u384;

    fn not(self) -> Self::Output {
        (*self).not()
    }
}

impl ops::BitAnd for &u384 {
    type Output = u384;

    fn bitand(self, rhs: Self) -> Self::Output {
        (*self).bitand(*rhs)
    }
}

impl ops::BitAnd<u384> for &u384 {
    type Output = u384;

    fn bitand(self, rhs: u384) -> Self::Output {
        (*self).bitand(rhs)
    }
}

impl ops::BitAnd<&u384> for u384 {
    type Output = Self;

    fn bitand(self, rhs: &u384) -> Self::Output {
        self.bitand(*rhs)
    }
}

impl ops::BitAnd for u384 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        self.bitand(rhs)
    }
}

impl ops::BitAndAssign for u384 {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

impl ops::BitAndAssign<&u384> for u384 {
    fn bitand_assign(&mut self, rhs: &Self) {
        *self = *self & *rhs;
    }
}

impl ops::BitOr for &u384 {
    type Output = u384;

    fn bitor(self, rhs: Self) -> Self::Output {
        (*self).bitor(*rhs)
    }
}

impl ops::BitOr<u384> for &u384 {
    type Output = u384;

    fn bitor(self, rhs: u384) -> Self::Output {
        (*self).bitor(rhs)
    }
}

impl ops::BitOr<&u384> for u384 {
    type Output = Self;

    fn bitor(self, rhs: &u384) -> Self::Output {
        self.bitor(*rhs)
    }
}

impl ops::BitOr for u384 {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        self.bitor(rhs)
    }
}

impl ops::BitOrAssign for u384 {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

impl ops::BitOrAssign<&u384> for u384 {
    fn bitor_assign(&mut self, rhs: &Self) {
        *self = *self | *rhs;
    }
}

impl ops::BitXor for &u384 {
    type Output = u384;

    fn bitxor(self, rhs: Self) -> Self::Output {
        (*self).bitxor(*rhs)
    }
}

impl ops::BitXor<u384> for &u384 {
    type Output = u384;

    fn bitxor(self, rhs: u384) -> Self::Output {
        (*self).bitxor(rhs)
    }
}

impl ops::BitXor<&u384> for u384 {
    type Output = Self;

    fn bitxor(self, rhs: &u384) -> Self::Output {
        self.bitxor(*rhs)
    }
}

impl ops::BitXor for u384 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        self.bitxor(rhs)
    }
}

impl ops::BitXorAssign for u384 {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs;
    }
}

impl ops::BitXorAssign<&u384> for u384 {
    fn bitxor_assign(&mut self, rhs: &Self) {
        *self = *self ^ *rhs;
    }
}

impl From<u8> for u384 {
    fn from(n: u8) -> Self {
        Self::from_u8(n)
    }
}

impl From<u16> for u384 {
    fn from(n: u16) -> Self {
        Self::from_u16(n)
    }
}

impl From<u32> for u384 {
    fn from(n: u32) -> Self {
        Self::from_u32(n)
    }
}

impl From<u64> for u384 {
    fn from(n: u64) -> Self {
        Self::from_u64(n)
    }
}

impl From<u128> for u384 {
    fn from(n: u128) -> Self {
        Self::from_u128(n)
    }
}

impl From<u256> for u384 {
    fn from(n: u256) -> Self {
        Self::from_u256(n)
    }
}

impl str::FromStr for u384 {
    type Err = crate::ParseIntError;

    fn from_str(src: &str) -> Result<Self, Self::Err> {
        Self::from_str(src)
    }
}

impl ops::Shl<&u32> for u384 {
    type Output = Self;

    fn shl(self, rhs: &u32) -> Self::Output {
        self.shl(*rhs)
    }
}

impl ops::Shl<u32> for u384 {
    type Output = Self;

    fn shl(self, rhs: u32) -> Self::Output {
        self.shl(rhs)
    }
}

impl ops::ShlAssign<&u32> for u384 {
    fn shl_assign(&mut self, rhs: &u32) {
        *self = *self << rhs;
    }
}

impl ops::ShlAssign<u32> for u384 {
    fn shl_assign(&mut self, rhs: u32) {
        *self = *self << rhs;
    }
}

impl ops::Shr<&u32> for u384 {
    type Output = Self;

    fn shr(self, rhs: &u32) -> Self::Output {
        self.shr(*rhs)
    }
}

impl ops::Shr<u32> for u384 {
    type Output = Self;

    fn shr(self, rhs: u32) -> Self::Output {
        self.shr(rhs)
    }
}

impl ops::ShrAssign<&u32> for u384 {
    fn shr_assign(&mut self, rhs: &u32) {
        *self = *self >> rhs;
    }
}

impl ops::ShrAssign<u32> for u384 {
    fn shr_assign(&mut self, rhs: u32) {
        *self = *self >> rhs;
    }
}
