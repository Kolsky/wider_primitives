use core::cmp;
use core::marker::StructuralPartialEq;
use core::marker::StructuralEq;
use core::ops;
use core::str;
use crate::u256;

impl const cmp::PartialEq for u256 {
    fn eq(&self, other: &Self) -> bool {
        self.inner.equals(&other.inner)
    }
}

impl Eq for u256 {}

impl StructuralPartialEq for u256 {}

impl StructuralEq for u256 {}

impl const cmp::PartialOrd for u256 {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl const cmp::Ord for u256 {
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

impl const ops::Add for &u256 {
    type Output = u256;

    fn add(self, rhs: Self) -> Self::Output {
        (*self).add(*rhs)
    }
}

impl const ops::Add<u256> for &u256 {
    type Output = u256;

    fn add(self, rhs: u256) -> Self::Output {
        (*self).add(rhs)
    }
}

impl const ops::Add<&u256> for u256 {
    type Output = Self;

    fn add(self, rhs: &u256) -> Self::Output {
        self.add(*rhs)
    }
}

impl const ops::Add for u256 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        self.add(rhs)
    }
}

impl const ops::AddAssign for u256 {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl const ops::AddAssign<&u256> for u256 {
    fn add_assign(&mut self, rhs: &u256) {
        *self = *self + *rhs;
    }
}

impl const ops::Sub for &u256 {
    type Output = u256;

    fn sub(self, rhs: Self) -> Self::Output {
        (*self).sub(*rhs)
    }
}

impl const ops::Sub<u256> for &u256 {
    type Output = u256;

    fn sub(self, rhs: u256) -> Self::Output {
        (*self).sub(rhs)
    }
}

impl const ops::Sub<&u256> for u256 {
    type Output = Self;

    fn sub(self, rhs: &u256) -> Self::Output {
        self.sub(*rhs)
    }
}

impl const ops::Sub for u256 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.sub(rhs)
    }
}

impl const ops::SubAssign for u256 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl const ops::SubAssign<&u256> for u256 {
    fn sub_assign(&mut self, rhs: &u256) {
        *self = *self - *rhs;
    }
}

impl const ops::Mul<&u64> for &u256 {
    type Output = u256;

    fn mul(self, rhs: &u64) -> Self::Output {
        (*self).short_mul(*rhs)
    }
}

impl const ops::Mul<u64> for &u256 {
    type Output = u256;

    fn mul(self, rhs: u64) -> Self::Output {
        (*self).short_mul(rhs)
    }
}

impl const ops::Mul<&u64> for u256 {
    type Output = u256;

    fn mul(self, rhs: &u64) -> Self::Output {
        self.short_mul(*rhs)
    }
}

impl const ops::Mul<u64> for u256 {
    type Output = u256;

    fn mul(self, rhs: u64) -> Self::Output {
        self.short_mul(rhs)
    }
}

impl const ops::Mul for &u256 {
    type Output = u256;

    fn mul(self, rhs: Self) -> Self::Output {
        (*self).mul(*rhs)
    }
}

impl const ops::Mul<u256> for &u256 {
    type Output = u256;

    fn mul(self, rhs: u256) -> Self::Output {
        (*self).mul(rhs)
    }
}

impl const ops::Mul<&u256> for u256 {
    type Output = Self;

    fn mul(self, rhs: &u256) -> Self::Output {
        self.mul(*rhs)
    }
}

impl const ops::Mul for u256 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        self.mul(rhs)
    }
}

impl const ops::MulAssign for u256 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl const ops::MulAssign<&u256> for u256 {
    fn mul_assign(&mut self, rhs: &u256) {
        *self = *self * *rhs;
    }
}

impl const ops::MulAssign<u64> for u256 {
    fn mul_assign(&mut self, rhs: u64) {
        *self = *self * rhs;
    }
}

impl const ops::MulAssign<&u64> for u256 {
    fn mul_assign(&mut self, rhs: &u64) {
        *self = *self * *rhs;
    }
}

impl const ops::Div<&u64> for &u256 {
    type Output = u256;

    fn div(self, rhs: &u64) -> Self::Output {
        (*self).short_div(*rhs)
    }
}

impl const ops::Div<u64> for &u256 {
    type Output = u256;

    fn div(self, rhs: u64) -> Self::Output {
        (*self).short_div(rhs)
    }
}

impl const ops::Div<&u64> for u256 {
    type Output = u256;

    fn div(self, rhs: &u64) -> Self::Output {
        self.short_div(*rhs)
    }
}

impl const ops::Div<u64> for u256 {
    type Output = u256;

    fn div(self, rhs: u64) -> Self::Output {
        self.short_div(rhs)
    }
}

impl const ops::Div for &u256 {
    type Output = u256;

    fn div(self, rhs: Self) -> Self::Output {
        (*self).div(*rhs)
    }
}

impl const ops::Div<u256> for &u256 {
    type Output = u256;

    fn div(self, rhs: u256) -> Self::Output {
        (*self).div(rhs)
    }
}

impl const ops::Div<&u256> for u256 {
    type Output = Self;

    fn div(self, rhs: &u256) -> Self::Output {
        self.div(*rhs)
    }
}

impl const ops::Div for u256 {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self.div(rhs)
    }
}

impl const ops::DivAssign for u256 {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl const ops::DivAssign<&u256> for u256 {
    fn div_assign(&mut self, rhs: &u256) {
        *self = *self / *rhs;
    }
}

impl const ops::DivAssign<u64> for u256 {
    fn div_assign(&mut self, rhs: u64) {
        *self = *self / rhs;
    }
}

impl const ops::DivAssign<&u64> for u256 {
    fn div_assign(&mut self, rhs: &u64) {
        *self = *self / *rhs;
    }
}

impl const ops::Rem<&u64> for &u256 {
    type Output = u64;

    fn rem(self, rhs: &u64) -> Self::Output {
        (*self).short_rem(*rhs)
    }
}

impl const ops::Rem<u64> for &u256 {
    type Output = u64;

    fn rem(self, rhs: u64) -> Self::Output {
        (*self).short_rem(rhs)
    }
}

impl const ops::Rem<&u64> for u256 {
    type Output = u64;

    fn rem(self, rhs: &u64) -> Self::Output {
        self.short_rem(*rhs)
    }
}

impl const ops::Rem<u64> for u256 {
    type Output = u64;

    fn rem(self, rhs: u64) -> Self::Output {
        self.short_rem(rhs)
    }
}

impl const ops::Rem for &u256 {
    type Output = u256;

    fn rem(self, rhs: Self) -> Self::Output {
        (*self).rem(*rhs)
    }
}

impl const ops::Rem<u256> for &u256 {
    type Output = u256;

    fn rem(self, rhs: u256) -> Self::Output {
        (*self).rem(rhs)
    }
}

impl const ops::Rem<&u256> for u256 {
    type Output = Self;

    fn rem(self, rhs: &u256) -> Self::Output {
        self.rem(*rhs)
    }
}

impl const ops::Rem for u256 {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        self.rem(rhs)
    }
}

impl const ops::RemAssign for u256 {
    fn rem_assign(&mut self, rhs: Self) {
        *self = *self % rhs;
    }
}

impl const ops::RemAssign<&u256> for u256 {
    fn rem_assign(&mut self, rhs: &u256) {
        *self = *self % *rhs;
    }
}

impl const ops::RemAssign<u64> for u256 {
    fn rem_assign(&mut self, rhs: u64) {
        *self = Self::from_u64(*self % rhs);
    }
}

impl const ops::RemAssign<&u64> for u256 {
    fn rem_assign(&mut self, rhs: &u64) {
        *self = Self::from_u64(*self % *rhs);
    }
}

impl const ops::Not for u256 {
    type Output = Self;

    fn not(self) -> Self::Output {
        self.not()
    }
}

impl const ops::Not for &u256 {
    type Output = u256;

    fn not(self) -> Self::Output {
        (*self).not()
    }
}

impl const ops::BitAnd for &u256 {
    type Output = u256;

    fn bitand(self, rhs: Self) -> Self::Output {
        (*self).bitand(*rhs)
    }
}

impl const ops::BitAnd<u256> for &u256 {
    type Output = u256;

    fn bitand(self, rhs: u256) -> Self::Output {
        (*self).bitand(rhs)
    }
}

impl const ops::BitAnd<&u256> for u256 {
    type Output = Self;

    fn bitand(self, rhs: &u256) -> Self::Output {
        self.bitand(*rhs)
    }
}

impl const ops::BitAnd for u256 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        self.bitand(rhs)
    }
}

impl const ops::BitAndAssign for u256 {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

impl const ops::BitAndAssign<&u256> for u256 {
    fn bitand_assign(&mut self, rhs: &Self) {
        *self = *self & *rhs;
    }
}

impl const ops::BitOr for &u256 {
    type Output = u256;

    fn bitor(self, rhs: Self) -> Self::Output {
        (*self).bitor(*rhs)
    }
}

impl const ops::BitOr<u256> for &u256 {
    type Output = u256;

    fn bitor(self, rhs: u256) -> Self::Output {
        (*self).bitor(rhs)
    }
}

impl const ops::BitOr<&u256> for u256 {
    type Output = Self;

    fn bitor(self, rhs: &u256) -> Self::Output {
        self.bitor(*rhs)
    }
}

impl const ops::BitOr for u256 {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        self.bitor(rhs)
    }
}

impl const ops::BitOrAssign for u256 {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

impl const ops::BitOrAssign<&u256> for u256 {
    fn bitor_assign(&mut self, rhs: &Self) {
        *self = *self | *rhs;
    }
}

impl const ops::BitXor for &u256 {
    type Output = u256;

    fn bitxor(self, rhs: Self) -> Self::Output {
        (*self).bitxor(*rhs)
    }
}

impl const ops::BitXor<u256> for &u256 {
    type Output = u256;

    fn bitxor(self, rhs: u256) -> Self::Output {
        (*self).bitxor(rhs)
    }
}

impl const ops::BitXor<&u256> for u256 {
    type Output = Self;

    fn bitxor(self, rhs: &u256) -> Self::Output {
        self.bitxor(*rhs)
    }
}

impl const ops::BitXor for u256 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        self.bitxor(rhs)
    }
}

impl const ops::BitXorAssign for u256 {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs;
    }
}

impl const ops::BitXorAssign<&u256> for u256 {
    fn bitxor_assign(&mut self, rhs: &Self) {
        *self = *self ^ *rhs;
    }
}

impl const From<u8> for u256 {
    fn from(n: u8) -> Self {
        Self::from_u8(n)
    }
}

impl const From<u16> for u256 {
    fn from(n: u16) -> Self {
        Self::from_u16(n)
    }
}

impl const From<u32> for u256 {
    fn from(n: u32) -> Self {
        Self::from_u32(n)
    }
}

impl const From<u64> for u256 {
    fn from(n: u64) -> Self {
        Self::from_u64(n)
    }
}

impl const From<u128> for u256 {
    fn from(n: u128) -> Self {
        Self::from_u128(n)
    }
}

impl const str::FromStr for u256 {
    type Err = crate::ParseIntError;

    fn from_str(src: &str) -> Result<Self, Self::Err> {
        Self::from_str(src)
    }
}

impl const ops::Shl<&u32> for u256 {
    type Output = Self;

    fn shl(self, rhs: &u32) -> Self::Output {
        self.shl(*rhs)
    }
}

impl const ops::Shl<u32> for u256 {
    type Output = Self;

    fn shl(self, rhs: u32) -> Self::Output {
        self.shl(rhs)
    }
}

impl const ops::ShlAssign<&u32> for u256 {
    fn shl_assign(&mut self, rhs: &u32) {
        *self = *self << rhs;
    }
}

impl const ops::ShlAssign<u32> for u256 {
    fn shl_assign(&mut self, rhs: u32) {
        *self = *self << rhs;
    }
}

impl const ops::Shr<&u32> for u256 {
    type Output = Self;

    fn shr(self, rhs: &u32) -> Self::Output {
        self.shr(*rhs)
    }
}

impl const ops::Shr<u32> for u256 {
    type Output = Self;

    fn shr(self, rhs: u32) -> Self::Output {
        self.shr(rhs)
    }
}

impl const ops::ShrAssign<&u32> for u256 {
    fn shr_assign(&mut self, rhs: &u32) {
        *self = *self >> rhs;
    }
}

impl const ops::ShrAssign<u32> for u256 {
    fn shr_assign(&mut self, rhs: u32) {
        *self = *self >> rhs;
    }
}
