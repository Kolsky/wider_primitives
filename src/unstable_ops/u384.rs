use core::cmp;
use core::marker::StructuralPartialEq;
use core::marker::StructuralEq;
use core::ops;
use core::str;
use crate::u256;
use crate::u384;

impl const Default for u384 {
    fn default() -> Self {
        Self::ZERO
    }
}

impl const cmp::PartialEq for u384 {
    fn eq(&self, other: &Self) -> bool {
        self.inner.equals(&other.inner)
    }
}

impl Eq for u384 {}

impl StructuralPartialEq for u384 {}

impl StructuralEq for u384 {}

impl const cmp::PartialOrd for u384 {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl const cmp::Ord for u384 {
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

impl const ops::Add for &u384 {
    type Output = u384;

    fn add(self, rhs: Self) -> Self::Output {
        (*self).add(*rhs)
    }
}

impl const ops::Add<u384> for &u384 {
    type Output = u384;

    fn add(self, rhs: u384) -> Self::Output {
        (*self).add(rhs)
    }
}

impl const ops::Add<&u384> for u384 {
    type Output = Self;

    fn add(self, rhs: &u384) -> Self::Output {
        self.add(*rhs)
    }
}

impl const ops::Add for u384 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        self.add(rhs)
    }
}

impl const ops::AddAssign for u384 {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl const ops::AddAssign<&u384> for u384 {
    fn add_assign(&mut self, rhs: &u384) {
        *self = *self + *rhs;
    }
}

impl const ops::Sub for &u384 {
    type Output = u384;

    fn sub(self, rhs: Self) -> Self::Output {
        (*self).sub(*rhs)
    }
}

impl const ops::Sub<u384> for &u384 {
    type Output = u384;

    fn sub(self, rhs: u384) -> Self::Output {
        (*self).sub(rhs)
    }
}

impl const ops::Sub<&u384> for u384 {
    type Output = Self;

    fn sub(self, rhs: &u384) -> Self::Output {
        self.sub(*rhs)
    }
}

impl const ops::Sub for u384 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.sub(rhs)
    }
}

impl const ops::SubAssign for u384 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl const ops::SubAssign<&u384> for u384 {
    fn sub_assign(&mut self, rhs: &u384) {
        *self = *self - *rhs;
    }
}

impl const ops::Mul<&u64> for &u384 {
    type Output = u384;

    fn mul(self, rhs: &u64) -> Self::Output {
        (*self).short_mul(*rhs)
    }
}

impl const ops::Mul<u64> for &u384 {
    type Output = u384;

    fn mul(self, rhs: u64) -> Self::Output {
        (*self).short_mul(rhs)
    }
}

impl const ops::Mul<&u64> for u384 {
    type Output = u384;

    fn mul(self, rhs: &u64) -> Self::Output {
        self.short_mul(*rhs)
    }
}

impl const ops::Mul<u64> for u384 {
    type Output = u384;

    fn mul(self, rhs: u64) -> Self::Output {
        self.short_mul(rhs)
    }
}

impl const ops::Mul for &u384 {
    type Output = u384;

    fn mul(self, rhs: Self) -> Self::Output {
        (*self).mul(*rhs)
    }
}

impl const ops::Mul<u384> for &u384 {
    type Output = u384;

    fn mul(self, rhs: u384) -> Self::Output {
        (*self).mul(rhs)
    }
}

impl const ops::Mul<&u384> for u384 {
    type Output = Self;

    fn mul(self, rhs: &u384) -> Self::Output {
        self.mul(*rhs)
    }
}

impl const ops::Mul for u384 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        self.mul(rhs)
    }
}

impl const ops::MulAssign for u384 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl const ops::MulAssign<&u384> for u384 {
    fn mul_assign(&mut self, rhs: &u384) {
        *self = *self * *rhs;
    }
}

impl const ops::MulAssign<u64> for u384 {
    fn mul_assign(&mut self, rhs: u64) {
        *self = *self * rhs;
    }
}

impl const ops::MulAssign<&u64> for u384 {
    fn mul_assign(&mut self, rhs: &u64) {
        *self = *self * *rhs;
    }
}

impl const ops::Div<&u64> for &u384 {
    type Output = u384;

    fn div(self, rhs: &u64) -> Self::Output {
        (*self).short_div(*rhs)
    }
}

impl const ops::Div<u64> for &u384 {
    type Output = u384;

    fn div(self, rhs: u64) -> Self::Output {
        (*self).short_div(rhs)
    }
}

impl const ops::Div<&u64> for u384 {
    type Output = u384;

    fn div(self, rhs: &u64) -> Self::Output {
        self.short_div(*rhs)
    }
}

impl const ops::Div<u64> for u384 {
    type Output = u384;

    fn div(self, rhs: u64) -> Self::Output {
        self.short_div(rhs)
    }
}

impl const ops::Div for &u384 {
    type Output = u384;

    fn div(self, rhs: Self) -> Self::Output {
        (*self).div(*rhs)
    }
}

impl const ops::Div<u384> for &u384 {
    type Output = u384;

    fn div(self, rhs: u384) -> Self::Output {
        (*self).div(rhs)
    }
}

impl const ops::Div<&u384> for u384 {
    type Output = Self;

    fn div(self, rhs: &u384) -> Self::Output {
        self.div(*rhs)
    }
}

impl const ops::Div for u384 {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self.div(rhs)
    }
}

impl const ops::DivAssign for u384 {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl const ops::DivAssign<&u384> for u384 {
    fn div_assign(&mut self, rhs: &u384) {
        *self = *self / *rhs;
    }
}

impl const ops::DivAssign<u64> for u384 {
    fn div_assign(&mut self, rhs: u64) {
        *self = *self / rhs;
    }
}

impl const ops::DivAssign<&u64> for u384 {
    fn div_assign(&mut self, rhs: &u64) {
        *self = *self / *rhs;
    }
}

impl const ops::Rem<&u64> for &u384 {
    type Output = u64;

    fn rem(self, rhs: &u64) -> Self::Output {
        (*self).short_rem(*rhs)
    }
}

impl const ops::Rem<u64> for &u384 {
    type Output = u64;

    fn rem(self, rhs: u64) -> Self::Output {
        (*self).short_rem(rhs)
    }
}

impl const ops::Rem<&u64> for u384 {
    type Output = u64;

    fn rem(self, rhs: &u64) -> Self::Output {
        self.short_rem(*rhs)
    }
}

impl const ops::Rem<u64> for u384 {
    type Output = u64;

    fn rem(self, rhs: u64) -> Self::Output {
        self.short_rem(rhs)
    }
}

impl const ops::Rem for &u384 {
    type Output = u384;

    fn rem(self, rhs: Self) -> Self::Output {
        (*self).rem(*rhs)
    }
}

impl const ops::Rem<u384> for &u384 {
    type Output = u384;

    fn rem(self, rhs: u384) -> Self::Output {
        (*self).rem(rhs)
    }
}

impl const ops::Rem<&u384> for u384 {
    type Output = Self;

    fn rem(self, rhs: &u384) -> Self::Output {
        self.rem(*rhs)
    }
}

impl const ops::Rem for u384 {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        self.rem(rhs)
    }
}

impl const ops::RemAssign for u384 {
    fn rem_assign(&mut self, rhs: Self) {
        *self = *self % rhs;
    }
}

impl const ops::RemAssign<&u384> for u384 {
    fn rem_assign(&mut self, rhs: &u384) {
        *self = *self % *rhs;
    }
}

impl const ops::RemAssign<u64> for u384 {
    fn rem_assign(&mut self, rhs: u64) {
        *self = Self::from_u64(*self % rhs);
    }
}

impl const ops::RemAssign<&u64> for u384 {
    fn rem_assign(&mut self, rhs: &u64) {
        *self = Self::from_u64(*self % *rhs);
    }
}

impl const ops::Not for u384 {
    type Output = Self;

    fn not(self) -> Self::Output {
        self.not()
    }
}

impl const ops::Not for &u384 {
    type Output = u384;

    fn not(self) -> Self::Output {
        (*self).not()
    }
}

impl const ops::BitAnd for &u384 {
    type Output = u384;

    fn bitand(self, rhs: Self) -> Self::Output {
        (*self).bitand(*rhs)
    }
}

impl const ops::BitAnd<u384> for &u384 {
    type Output = u384;

    fn bitand(self, rhs: u384) -> Self::Output {
        (*self).bitand(rhs)
    }
}

impl const ops::BitAnd<&u384> for u384 {
    type Output = Self;

    fn bitand(self, rhs: &u384) -> Self::Output {
        self.bitand(*rhs)
    }
}

impl const ops::BitAnd for u384 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        self.bitand(rhs)
    }
}

impl const ops::BitAndAssign for u384 {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

impl const ops::BitAndAssign<&u384> for u384 {
    fn bitand_assign(&mut self, rhs: &Self) {
        *self = *self & *rhs;
    }
}

impl const ops::BitOr for &u384 {
    type Output = u384;

    fn bitor(self, rhs: Self) -> Self::Output {
        (*self).bitor(*rhs)
    }
}

impl const ops::BitOr<u384> for &u384 {
    type Output = u384;

    fn bitor(self, rhs: u384) -> Self::Output {
        (*self).bitor(rhs)
    }
}

impl const ops::BitOr<&u384> for u384 {
    type Output = Self;

    fn bitor(self, rhs: &u384) -> Self::Output {
        self.bitor(*rhs)
    }
}

impl const ops::BitOr for u384 {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        self.bitor(rhs)
    }
}

impl const ops::BitOrAssign for u384 {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

impl const ops::BitOrAssign<&u384> for u384 {
    fn bitor_assign(&mut self, rhs: &Self) {
        *self = *self | *rhs;
    }
}

impl const ops::BitXor for &u384 {
    type Output = u384;

    fn bitxor(self, rhs: Self) -> Self::Output {
        (*self).bitxor(*rhs)
    }
}

impl const ops::BitXor<u384> for &u384 {
    type Output = u384;

    fn bitxor(self, rhs: u384) -> Self::Output {
        (*self).bitxor(rhs)
    }
}

impl const ops::BitXor<&u384> for u384 {
    type Output = Self;

    fn bitxor(self, rhs: &u384) -> Self::Output {
        self.bitxor(*rhs)
    }
}

impl const ops::BitXor for u384 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        self.bitxor(rhs)
    }
}

impl const ops::BitXorAssign for u384 {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs;
    }
}

impl const ops::BitXorAssign<&u384> for u384 {
    fn bitxor_assign(&mut self, rhs: &Self) {
        *self = *self ^ *rhs;
    }
}

impl const From<u8> for u384 {
    fn from(n: u8) -> Self {
        Self::from_u8(n)
    }
}

impl const From<u16> for u384 {
    fn from(n: u16) -> Self {
        Self::from_u16(n)
    }
}

impl const From<u32> for u384 {
    fn from(n: u32) -> Self {
        Self::from_u32(n)
    }
}

impl const From<u64> for u384 {
    fn from(n: u64) -> Self {
        Self::from_u64(n)
    }
}

impl const From<u128> for u384 {
    fn from(n: u128) -> Self {
        Self::from_u128(n)
    }
}

impl const From<u256> for u384 {
    fn from(n: u256) -> Self {
        Self::from_u256(n)
    }
}

impl const str::FromStr for u384 {
    type Err = crate::ParseIntError;

    fn from_str(src: &str) -> Result<Self, Self::Err> {
        Self::from_str(src)
    }
}

impl const ops::Shl<&u32> for u384 {
    type Output = Self;

    fn shl(self, rhs: &u32) -> Self::Output {
        self.shl(*rhs)
    }
}

impl const ops::Shl<u32> for u384 {
    type Output = Self;

    fn shl(self, rhs: u32) -> Self::Output {
        self.shl(rhs)
    }
}

impl const ops::ShlAssign<&u32> for u384 {
    fn shl_assign(&mut self, rhs: &u32) {
        *self = *self << rhs;
    }
}

impl const ops::ShlAssign<u32> for u384 {
    fn shl_assign(&mut self, rhs: u32) {
        *self = *self << rhs;
    }
}

impl const ops::Shr<&u32> for u384 {
    type Output = Self;

    fn shr(self, rhs: &u32) -> Self::Output {
        self.shr(*rhs)
    }
}

impl const ops::Shr<u32> for u384 {
    type Output = Self;

    fn shr(self, rhs: u32) -> Self::Output {
        self.shr(rhs)
    }
}

impl const ops::ShrAssign<&u32> for u384 {
    fn shr_assign(&mut self, rhs: &u32) {
        *self = *self >> rhs;
    }
}

impl const ops::ShrAssign<u32> for u384 {
    fn shr_assign(&mut self, rhs: u32) {
        *self = *self >> rhs;
    }
}
