use core::cmp;
use core::ops;
use core::str;
use crate::i256;

impl cmp::PartialOrd for i256 {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl cmp::Ord for i256 {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.inner.compare_unsigned(&other.inner)
    }
}

impl ops::Neg for &i256 {
    type Output = i256;

    fn neg(self) -> Self::Output {
        (*self).neg()
    }
}

impl ops::Neg for i256 {
    type Output = Self;

    fn neg(self) -> Self::Output {
        self.neg()
    }
}

impl ops::Add for &i256 {
    type Output = i256;

    fn add(self, rhs: Self) -> Self::Output {
        (*self).add(*rhs)
    }
}

impl ops::Add<i256> for &i256 {
    type Output = i256;

    fn add(self, rhs: i256) -> Self::Output {
        (*self).add(rhs)
    }
}

impl ops::Add<&i256> for i256 {
    type Output = Self;

    fn add(self, rhs: &i256) -> Self::Output {
        self.add(*rhs)
    }
}

impl ops::Add for i256 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        self.add(rhs)
    }
}

impl ops::AddAssign for i256 {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl ops::AddAssign<&i256> for i256 {
    fn add_assign(&mut self, rhs: &i256) {
        *self = *self + *rhs;
    }
}

impl ops::Sub for &i256 {
    type Output = i256;

    fn sub(self, rhs: Self) -> Self::Output {
        (*self).sub(*rhs)
    }
}

impl ops::Sub<i256> for &i256 {
    type Output = i256;

    fn sub(self, rhs: i256) -> Self::Output {
        (*self).sub(rhs)
    }
}

impl ops::Sub<&i256> for i256 {
    type Output = Self;

    fn sub(self, rhs: &i256) -> Self::Output {
        self.sub(*rhs)
    }
}

impl ops::Sub for i256 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.sub(rhs)
    }
}

impl ops::SubAssign for i256 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl ops::SubAssign<&i256> for i256 {
    fn sub_assign(&mut self, rhs: &i256) {
        *self = *self - *rhs;
    }
}

impl ops::Mul<&i64> for &i256 {
    type Output = i256;

    fn mul(self, rhs: &i64) -> Self::Output {
        (*self).short_mul(*rhs)
    }
}

impl ops::Mul<i64> for &i256 {
    type Output = i256;

    fn mul(self, rhs: i64) -> Self::Output {
        (*self).short_mul(rhs)
    }
}

impl ops::Mul<&i64> for i256 {
    type Output = i256;

    fn mul(self, rhs: &i64) -> Self::Output {
        self.short_mul(*rhs)
    }
}

impl ops::Mul<i64> for i256 {
    type Output = i256;

    fn mul(self, rhs: i64) -> Self::Output {
        self.short_mul(rhs)
    }
}

impl ops::Mul for &i256 {
    type Output = i256;

    fn mul(self, rhs: Self) -> Self::Output {
        (*self).mul(*rhs)
    }
}

impl ops::Mul<i256> for &i256 {
    type Output = i256;

    fn mul(self, rhs: i256) -> Self::Output {
        (*self).mul(rhs)
    }
}

impl ops::Mul<&i256> for i256 {
    type Output = Self;

    fn mul(self, rhs: &i256) -> Self::Output {
        self.mul(*rhs)
    }
}

impl ops::Mul for i256 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        self.mul(rhs)
    }
}

impl ops::MulAssign for i256 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl ops::MulAssign<&i256> for i256 {
    fn mul_assign(&mut self, rhs: &i256) {
        *self = *self * *rhs;
    }
}

impl ops::MulAssign<i64> for i256 {
    fn mul_assign(&mut self, rhs: i64) {
        *self = *self * rhs;
    }
}

impl ops::MulAssign<&i64> for i256 {
    fn mul_assign(&mut self, rhs: &i64) {
        *self = *self * *rhs;
    }
}

impl ops::Div<&i64> for &i256 {
    type Output = i256;

    fn div(self, rhs: &i64) -> Self::Output {
        (*self).short_div(*rhs)
    }
}

impl ops::Div<i64> for &i256 {
    type Output = i256;

    fn div(self, rhs: i64) -> Self::Output {
        (*self).short_div(rhs)
    }
}

impl ops::Div<&i64> for i256 {
    type Output = i256;

    fn div(self, rhs: &i64) -> Self::Output {
        self.short_div(*rhs)
    }
}

impl ops::Div<i64> for i256 {
    type Output = i256;

    fn div(self, rhs: i64) -> Self::Output {
        self.short_div(rhs)
    }
}

impl ops::Div for &i256 {
    type Output = i256;

    fn div(self, rhs: Self) -> Self::Output {
        (*self).div(*rhs)
    }
}

impl ops::Div<i256> for &i256 {
    type Output = i256;

    fn div(self, rhs: i256) -> Self::Output {
        (*self).div(rhs)
    }
}

impl ops::Div<&i256> for i256 {
    type Output = Self;

    fn div(self, rhs: &i256) -> Self::Output {
        self.div(*rhs)
    }
}

impl ops::Div for i256 {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self.div(rhs)
    }
}

impl ops::DivAssign for i256 {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl ops::DivAssign<&i256> for i256 {
    fn div_assign(&mut self, rhs: &i256) {
        *self = *self / *rhs;
    }
}

impl ops::DivAssign<i64> for i256 {
    fn div_assign(&mut self, rhs: i64) {
        *self = *self / rhs;
    }
}

impl ops::DivAssign<&i64> for i256 {
    fn div_assign(&mut self, rhs: &i64) {
        *self = *self / *rhs;
    }
}

impl ops::Rem<&i64> for &i256 {
    type Output = i64;

    fn rem(self, rhs: &i64) -> Self::Output {
        (*self).short_rem(*rhs)
    }
}

impl ops::Rem<i64> for &i256 {
    type Output = i64;

    fn rem(self, rhs: i64) -> Self::Output {
        (*self).short_rem(rhs)
    }
}

impl ops::Rem<&i64> for i256 {
    type Output = i64;

    fn rem(self, rhs: &i64) -> Self::Output {
        self.short_rem(*rhs)
    }
}

impl ops::Rem<i64> for i256 {
    type Output = i64;

    fn rem(self, rhs: i64) -> Self::Output {
        self.short_rem(rhs)
    }
}

impl ops::Rem for &i256 {
    type Output = i256;

    fn rem(self, rhs: Self) -> Self::Output {
        (*self).rem(*rhs)
    }
}

impl ops::Rem<i256> for &i256 {
    type Output = i256;

    fn rem(self, rhs: i256) -> Self::Output {
        (*self).rem(rhs)
    }
}

impl ops::Rem<&i256> for i256 {
    type Output = Self;

    fn rem(self, rhs: &i256) -> Self::Output {
        self.rem(*rhs)
    }
}

impl ops::Rem for i256 {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        self.rem(rhs)
    }
}

impl ops::RemAssign for i256 {
    fn rem_assign(&mut self, rhs: Self) {
        *self = *self % rhs;
    }
}

impl ops::RemAssign<&i256> for i256 {
    fn rem_assign(&mut self, rhs: &i256) {
        *self = *self % *rhs;
    }
}

impl ops::RemAssign<i64> for i256 {
    fn rem_assign(&mut self, rhs: i64) {
        *self = Self::from_i64(*self % rhs);
    }
}

impl ops::RemAssign<&i64> for i256 {
    fn rem_assign(&mut self, rhs: &i64) {
        *self = Self::from_i64(*self % *rhs);
    }
}

impl ops::Not for i256 {
    type Output = Self;

    fn not(self) -> Self::Output {
        self.not()
    }
}

impl ops::Not for &i256 {
    type Output = i256;

    fn not(self) -> Self::Output {
        (*self).not()
    }
}

impl ops::BitAnd for &i256 {
    type Output = i256;

    fn bitand(self, rhs: Self) -> Self::Output {
        (*self).bitand(*rhs)
    }
}

impl ops::BitAnd<i256> for &i256 {
    type Output = i256;

    fn bitand(self, rhs: i256) -> Self::Output {
        (*self).bitand(rhs)
    }
}

impl ops::BitAnd<&i256> for i256 {
    type Output = Self;

    fn bitand(self, rhs: &i256) -> Self::Output {
        self.bitand(*rhs)
    }
}

impl ops::BitAnd for i256 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        self.bitand(rhs)
    }
}

impl ops::BitAndAssign for i256 {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

impl ops::BitAndAssign<&i256> for i256 {
    fn bitand_assign(&mut self, rhs: &Self) {
        *self = *self & *rhs;
    }
}

impl ops::BitOr for &i256 {
    type Output = i256;

    fn bitor(self, rhs: Self) -> Self::Output {
        (*self).bitor(*rhs)
    }
}

impl ops::BitOr<i256> for &i256 {
    type Output = i256;

    fn bitor(self, rhs: i256) -> Self::Output {
        (*self).bitor(rhs)
    }
}

impl ops::BitOr<&i256> for i256 {
    type Output = Self;

    fn bitor(self, rhs: &i256) -> Self::Output {
        self.bitor(*rhs)
    }
}

impl ops::BitOr for i256 {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        self.bitor(rhs)
    }
}

impl ops::BitOrAssign for i256 {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

impl ops::BitOrAssign<&i256> for i256 {
    fn bitor_assign(&mut self, rhs: &Self) {
        *self = *self | *rhs;
    }
}

impl ops::BitXor for &i256 {
    type Output = i256;

    fn bitxor(self, rhs: Self) -> Self::Output {
        (*self).bitxor(*rhs)
    }
}

impl ops::BitXor<i256> for &i256 {
    type Output = i256;

    fn bitxor(self, rhs: i256) -> Self::Output {
        (*self).bitxor(rhs)
    }
}

impl ops::BitXor<&i256> for i256 {
    type Output = Self;

    fn bitxor(self, rhs: &i256) -> Self::Output {
        self.bitxor(*rhs)
    }
}

impl ops::BitXor for i256 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        self.bitxor(rhs)
    }
}

impl ops::BitXorAssign for i256 {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs;
    }
}

impl ops::BitXorAssign<&i256> for i256 {
    fn bitxor_assign(&mut self, rhs: &Self) {
        *self = *self ^ *rhs;
    }
}

impl From<u8> for i256 {
    fn from(n: u8) -> Self {
        Self::from_u8(n)
    }
}

impl From<u16> for i256 {
    fn from(n: u16) -> Self {
        Self::from_u16(n)
    }
}

impl From<u32> for i256 {
    fn from(n: u32) -> Self {
        Self::from_u32(n)
    }
}

impl From<u64> for i256 {
    fn from(n: u64) -> Self {
        Self::from_u64(n)
    }
}

impl From<u128> for i256 {
    fn from(n: u128) -> Self {
        Self::from_u128(n)
    }
}
impl From<i8> for i256 {
    fn from(n: i8) -> Self {
        Self::from_i8(n)
    }
}

impl From<i16> for i256 {
    fn from(n: i16) -> Self {
        Self::from_i16(n)
    }
}

impl From<i32> for i256 {
    fn from(n: i32) -> Self {
        Self::from_i32(n)
    }
}

impl From<i64> for i256 {
    fn from(n: i64) -> Self {
        Self::from_i64(n)
    }
}

impl From<i128> for i256 {
    fn from(n: i128) -> Self {
        Self::from_i128(n)
    }
}

impl str::FromStr for i256 {
    type Err = crate::ParseIntError;

    fn from_str(src: &str) -> Result<Self, Self::Err> {
        Self::from_str(src)
    }
}

impl ops::Shl<&u32> for i256 {
    type Output = Self;

    fn shl(self, rhs: &u32) -> Self::Output {
        self.shl(*rhs)
    }
}

impl ops::Shl<u32> for i256 {
    type Output = Self;

    fn shl(self, rhs: u32) -> Self::Output {
        self.shl(rhs)
    }
}

impl ops::ShlAssign<&u32> for i256 {
    fn shl_assign(&mut self, rhs: &u32) {
        *self = *self << rhs;
    }
}

impl ops::ShlAssign<u32> for i256 {
    fn shl_assign(&mut self, rhs: u32) {
        *self = *self << rhs;
    }
}

impl ops::Shr<&u32> for i256 {
    type Output = Self;

    fn shr(self, rhs: &u32) -> Self::Output {
        self.shr(*rhs)
    }
}

impl ops::Shr<u32> for i256 {
    type Output = Self;

    fn shr(self, rhs: u32) -> Self::Output {
        self.shr(rhs)
    }
}

impl ops::ShrAssign<&u32> for i256 {
    fn shr_assign(&mut self, rhs: &u32) {
        *self = *self >> rhs;
    }
}

impl ops::ShrAssign<u32> for i256 {
    fn shr_assign(&mut self, rhs: u32) {
        *self = *self >> rhs;
    }
}
