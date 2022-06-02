use core::cmp;
use core::marker::StructuralPartialEq;
use core::marker::StructuralEq;
use core::ops;
use core::str;
use crate::u256;
use crate::i256;
use crate::i384;

impl const Default for i384 {
    fn default() -> Self {
        Self::ZERO
    }
}

impl const cmp::PartialEq for i384 {
    fn eq(&self, other: &Self) -> bool {
        self.inner.equals(&other.inner)
    }
}

impl Eq for i384 {}

impl StructuralPartialEq for i384 {}

impl StructuralEq for i384 {}

impl const cmp::PartialOrd for i384 {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl const cmp::Ord for i384 {
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

impl const ops::Neg for &i384 {
    type Output = i384;

    fn neg(self) -> Self::Output {
        (*self).neg()
    }
}

impl const ops::Neg for i384 {
    type Output = Self;

    fn neg(self) -> Self::Output {
        self.neg()
    }
}

impl const ops::Add for &i384 {
    type Output = i384;

    fn add(self, rhs: Self) -> Self::Output {
        (*self).add(*rhs)
    }
}

impl const ops::Add<i384> for &i384 {
    type Output = i384;

    fn add(self, rhs: i384) -> Self::Output {
        (*self).add(rhs)
    }
}

impl const ops::Add<&i384> for i384 {
    type Output = Self;

    fn add(self, rhs: &i384) -> Self::Output {
        self.add(*rhs)
    }
}

impl const ops::Add for i384 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        self.add(rhs)
    }
}

impl const ops::AddAssign for i384 {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl const ops::AddAssign<&i384> for i384 {
    fn add_assign(&mut self, rhs: &i384) {
        *self = *self + *rhs;
    }
}

impl const ops::Sub for &i384 {
    type Output = i384;

    fn sub(self, rhs: Self) -> Self::Output {
        (*self).sub(*rhs)
    }
}

impl const ops::Sub<i384> for &i384 {
    type Output = i384;

    fn sub(self, rhs: i384) -> Self::Output {
        (*self).sub(rhs)
    }
}

impl const ops::Sub<&i384> for i384 {
    type Output = Self;

    fn sub(self, rhs: &i384) -> Self::Output {
        self.sub(*rhs)
    }
}

impl const ops::Sub for i384 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.sub(rhs)
    }
}

impl const ops::SubAssign for i384 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl const ops::SubAssign<&i384> for i384 {
    fn sub_assign(&mut self, rhs: &i384) {
        *self = *self - *rhs;
    }
}

impl const ops::Mul<&i64> for &i384 {
    type Output = i384;

    fn mul(self, rhs: &i64) -> Self::Output {
        (*self).short_mul(*rhs)
    }
}

impl const ops::Mul<i64> for &i384 {
    type Output = i384;

    fn mul(self, rhs: i64) -> Self::Output {
        (*self).short_mul(rhs)
    }
}

impl const ops::Mul<&i64> for i384 {
    type Output = i384;

    fn mul(self, rhs: &i64) -> Self::Output {
        self.short_mul(*rhs)
    }
}

impl const ops::Mul<i64> for i384 {
    type Output = i384;

    fn mul(self, rhs: i64) -> Self::Output {
        self.short_mul(rhs)
    }
}

impl const ops::Mul for &i384 {
    type Output = i384;

    fn mul(self, rhs: Self) -> Self::Output {
        (*self).mul(*rhs)
    }
}

impl const ops::Mul<i384> for &i384 {
    type Output = i384;

    fn mul(self, rhs: i384) -> Self::Output {
        (*self).mul(rhs)
    }
}

impl const ops::Mul<&i384> for i384 {
    type Output = Self;

    fn mul(self, rhs: &i384) -> Self::Output {
        self.mul(*rhs)
    }
}

impl const ops::Mul for i384 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        self.mul(rhs)
    }
}

impl const ops::MulAssign for i384 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl const ops::MulAssign<&i384> for i384 {
    fn mul_assign(&mut self, rhs: &i384) {
        *self = *self * *rhs;
    }
}

impl const ops::MulAssign<i64> for i384 {
    fn mul_assign(&mut self, rhs: i64) {
        *self = *self * rhs;
    }
}

impl const ops::MulAssign<&i64> for i384 {
    fn mul_assign(&mut self, rhs: &i64) {
        *self = *self * *rhs;
    }
}

impl const ops::Div<&i64> for &i384 {
    type Output = i384;

    fn div(self, rhs: &i64) -> Self::Output {
        (*self).short_div(*rhs)
    }
}

impl const ops::Div<i64> for &i384 {
    type Output = i384;

    fn div(self, rhs: i64) -> Self::Output {
        (*self).short_div(rhs)
    }
}

impl const ops::Div<&i64> for i384 {
    type Output = i384;

    fn div(self, rhs: &i64) -> Self::Output {
        self.short_div(*rhs)
    }
}

impl const ops::Div<i64> for i384 {
    type Output = i384;

    fn div(self, rhs: i64) -> Self::Output {
        self.short_div(rhs)
    }
}

impl const ops::Div for &i384 {
    type Output = i384;

    fn div(self, rhs: Self) -> Self::Output {
        (*self).div(*rhs)
    }
}

impl const ops::Div<i384> for &i384 {
    type Output = i384;

    fn div(self, rhs: i384) -> Self::Output {
        (*self).div(rhs)
    }
}

impl const ops::Div<&i384> for i384 {
    type Output = Self;

    fn div(self, rhs: &i384) -> Self::Output {
        self.div(*rhs)
    }
}

impl const ops::Div for i384 {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self.div(rhs)
    }
}

impl const ops::DivAssign for i384 {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl const ops::DivAssign<&i384> for i384 {
    fn div_assign(&mut self, rhs: &i384) {
        *self = *self / *rhs;
    }
}

impl const ops::DivAssign<i64> for i384 {
    fn div_assign(&mut self, rhs: i64) {
        *self = *self / rhs;
    }
}

impl const ops::DivAssign<&i64> for i384 {
    fn div_assign(&mut self, rhs: &i64) {
        *self = *self / *rhs;
    }
}

impl const ops::Rem<&i64> for &i384 {
    type Output = i64;

    fn rem(self, rhs: &i64) -> Self::Output {
        (*self).short_rem(*rhs)
    }
}

impl const ops::Rem<i64> for &i384 {
    type Output = i64;

    fn rem(self, rhs: i64) -> Self::Output {
        (*self).short_rem(rhs)
    }
}

impl const ops::Rem<&i64> for i384 {
    type Output = i64;

    fn rem(self, rhs: &i64) -> Self::Output {
        self.short_rem(*rhs)
    }
}

impl const ops::Rem<i64> for i384 {
    type Output = i64;

    fn rem(self, rhs: i64) -> Self::Output {
        self.short_rem(rhs)
    }
}

impl const ops::Rem for &i384 {
    type Output = i384;

    fn rem(self, rhs: Self) -> Self::Output {
        (*self).rem(*rhs)
    }
}

impl const ops::Rem<i384> for &i384 {
    type Output = i384;

    fn rem(self, rhs: i384) -> Self::Output {
        (*self).rem(rhs)
    }
}

impl const ops::Rem<&i384> for i384 {
    type Output = Self;

    fn rem(self, rhs: &i384) -> Self::Output {
        self.rem(*rhs)
    }
}

impl const ops::Rem for i384 {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        self.rem(rhs)
    }
}

impl const ops::RemAssign for i384 {
    fn rem_assign(&mut self, rhs: Self) {
        *self = *self % rhs;
    }
}

impl const ops::RemAssign<&i384> for i384 {
    fn rem_assign(&mut self, rhs: &i384) {
        *self = *self % *rhs;
    }
}

impl const ops::RemAssign<i64> for i384 {
    fn rem_assign(&mut self, rhs: i64) {
        *self = Self::from_i64(*self % rhs);
    }
}

impl const ops::RemAssign<&i64> for i384 {
    fn rem_assign(&mut self, rhs: &i64) {
        *self = Self::from_i64(*self % *rhs);
    }
}

impl const ops::Not for i384 {
    type Output = Self;

    fn not(self) -> Self::Output {
        self.not()
    }
}

impl const ops::Not for &i384 {
    type Output = i384;

    fn not(self) -> Self::Output {
        (*self).not()
    }
}

impl const ops::BitAnd for &i384 {
    type Output = i384;

    fn bitand(self, rhs: Self) -> Self::Output {
        (*self).bitand(*rhs)
    }
}

impl const ops::BitAnd<i384> for &i384 {
    type Output = i384;

    fn bitand(self, rhs: i384) -> Self::Output {
        (*self).bitand(rhs)
    }
}

impl const ops::BitAnd<&i384> for i384 {
    type Output = Self;

    fn bitand(self, rhs: &i384) -> Self::Output {
        self.bitand(*rhs)
    }
}

impl const ops::BitAnd for i384 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        self.bitand(rhs)
    }
}

impl const ops::BitAndAssign for i384 {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

impl const ops::BitAndAssign<&i384> for i384 {
    fn bitand_assign(&mut self, rhs: &Self) {
        *self = *self & *rhs;
    }
}

impl const ops::BitOr for &i384 {
    type Output = i384;

    fn bitor(self, rhs: Self) -> Self::Output {
        (*self).bitor(*rhs)
    }
}

impl const ops::BitOr<i384> for &i384 {
    type Output = i384;

    fn bitor(self, rhs: i384) -> Self::Output {
        (*self).bitor(rhs)
    }
}

impl const ops::BitOr<&i384> for i384 {
    type Output = Self;

    fn bitor(self, rhs: &i384) -> Self::Output {
        self.bitor(*rhs)
    }
}

impl const ops::BitOr for i384 {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        self.bitor(rhs)
    }
}

impl const ops::BitOrAssign for i384 {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

impl const ops::BitOrAssign<&i384> for i384 {
    fn bitor_assign(&mut self, rhs: &Self) {
        *self = *self | *rhs;
    }
}

impl const ops::BitXor for &i384 {
    type Output = i384;

    fn bitxor(self, rhs: Self) -> Self::Output {
        (*self).bitxor(*rhs)
    }
}

impl const ops::BitXor<i384> for &i384 {
    type Output = i384;

    fn bitxor(self, rhs: i384) -> Self::Output {
        (*self).bitxor(rhs)
    }
}

impl const ops::BitXor<&i384> for i384 {
    type Output = Self;

    fn bitxor(self, rhs: &i384) -> Self::Output {
        self.bitxor(*rhs)
    }
}

impl const ops::BitXor for i384 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        self.bitxor(rhs)
    }
}

impl const ops::BitXorAssign for i384 {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs;
    }
}

impl const ops::BitXorAssign<&i384> for i384 {
    fn bitxor_assign(&mut self, rhs: &Self) {
        *self = *self ^ *rhs;
    }
}

impl const From<u8> for i384 {
    fn from(n: u8) -> Self {
        Self::from_u8(n)
    }
}

impl const From<u16> for i384 {
    fn from(n: u16) -> Self {
        Self::from_u16(n)
    }
}

impl const From<u32> for i384 {
    fn from(n: u32) -> Self {
        Self::from_u32(n)
    }
}

impl const From<u64> for i384 {
    fn from(n: u64) -> Self {
        Self::from_u64(n)
    }
}

impl const From<u128> for i384 {
    fn from(n: u128) -> Self {
        Self::from_u128(n)
    }
}

impl const From<u256> for i384 {
    fn from(n: u256) -> Self {
        Self::from_u256(n)
    }
}

impl const From<i8> for i384 {
    fn from(n: i8) -> Self {
        Self::from_i8(n)
    }
}

impl const From<i16> for i384 {
    fn from(n: i16) -> Self {
        Self::from_i16(n)
    }
}

impl const From<i32> for i384 {
    fn from(n: i32) -> Self {
        Self::from_i32(n)
    }
}

impl const From<i64> for i384 {
    fn from(n: i64) -> Self {
        Self::from_i64(n)
    }
}

impl const From<i128> for i384 {
    fn from(n: i128) -> Self {
        Self::from_i128(n)
    }
}

impl const From<i256> for i384 {
    fn from(n: i256) -> Self {
        Self::from_i256(n)
    }
}

impl const str::FromStr for i384 {
    type Err = crate::ParseIntError;

    fn from_str(src: &str) -> Result<Self, Self::Err> {
        Self::from_str(src)
    }
}

impl const ops::Shl<&u32> for i384 {
    type Output = Self;

    fn shl(self, rhs: &u32) -> Self::Output {
        self.shl(*rhs)
    }
}

impl const ops::Shl<u32> for i384 {
    type Output = Self;

    fn shl(self, rhs: u32) -> Self::Output {
        self.shl(rhs)
    }
}

impl const ops::ShlAssign<&u32> for i384 {
    fn shl_assign(&mut self, rhs: &u32) {
        *self = *self << rhs;
    }
}

impl const ops::ShlAssign<u32> for i384 {
    fn shl_assign(&mut self, rhs: u32) {
        *self = *self << rhs;
    }
}

impl const ops::Shr<&u32> for i384 {
    type Output = Self;

    fn shr(self, rhs: &u32) -> Self::Output {
        self.shr(*rhs)
    }
}

impl const ops::Shr<u32> for i384 {
    type Output = Self;

    fn shr(self, rhs: u32) -> Self::Output {
        self.shr(rhs)
    }
}

impl const ops::ShrAssign<&u32> for i384 {
    fn shr_assign(&mut self, rhs: &u32) {
        *self = *self >> rhs;
    }
}

impl const ops::ShrAssign<u32> for i384 {
    fn shr_assign(&mut self, rhs: u32) {
        *self = *self >> rhs;
    }
}
