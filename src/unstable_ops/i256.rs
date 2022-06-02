use core::cmp;
use core::marker::StructuralPartialEq;
use core::marker::StructuralEq;
use core::ops;
use core::str;
use crate::i256;

impl const Default for i256 {
    fn default() -> Self {
        Self::ZERO
    }
}

impl const cmp::PartialEq for i256 {
    fn eq(&self, other: &Self) -> bool {
        self.inner.equals(&other.inner)
    }
}

impl Eq for i256 {}

impl StructuralPartialEq for i256 {}

impl StructuralEq for i256 {}

impl const cmp::PartialOrd for i256 {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl const cmp::Ord for i256 {
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

impl const ops::Neg for &i256 {
    type Output = i256;

    fn neg(self) -> Self::Output {
        (*self).neg()
    }
}

impl const ops::Neg for i256 {
    type Output = Self;

    fn neg(self) -> Self::Output {
        self.neg()
    }
}

impl const ops::Add for &i256 {
    type Output = i256;

    fn add(self, rhs: Self) -> Self::Output {
        (*self).add(*rhs)
    }
}

impl const ops::Add<i256> for &i256 {
    type Output = i256;

    fn add(self, rhs: i256) -> Self::Output {
        (*self).add(rhs)
    }
}

impl const ops::Add<&i256> for i256 {
    type Output = Self;

    fn add(self, rhs: &i256) -> Self::Output {
        self.add(*rhs)
    }
}

impl const ops::Add for i256 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        self.add(rhs)
    }
}

impl const ops::AddAssign for i256 {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl const ops::AddAssign<&i256> for i256 {
    fn add_assign(&mut self, rhs: &i256) {
        *self = *self + *rhs;
    }
}

impl const ops::Sub for &i256 {
    type Output = i256;

    fn sub(self, rhs: Self) -> Self::Output {
        (*self).sub(*rhs)
    }
}

impl const ops::Sub<i256> for &i256 {
    type Output = i256;

    fn sub(self, rhs: i256) -> Self::Output {
        (*self).sub(rhs)
    }
}

impl const ops::Sub<&i256> for i256 {
    type Output = Self;

    fn sub(self, rhs: &i256) -> Self::Output {
        self.sub(*rhs)
    }
}

impl const ops::Sub for i256 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.sub(rhs)
    }
}

impl const ops::SubAssign for i256 {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl const ops::SubAssign<&i256> for i256 {
    fn sub_assign(&mut self, rhs: &i256) {
        *self = *self - *rhs;
    }
}

impl const ops::Mul<&i64> for &i256 {
    type Output = i256;

    fn mul(self, rhs: &i64) -> Self::Output {
        (*self).short_mul(*rhs)
    }
}

impl const ops::Mul<i64> for &i256 {
    type Output = i256;

    fn mul(self, rhs: i64) -> Self::Output {
        (*self).short_mul(rhs)
    }
}

impl const ops::Mul<&i64> for i256 {
    type Output = i256;

    fn mul(self, rhs: &i64) -> Self::Output {
        self.short_mul(*rhs)
    }
}

impl const ops::Mul<i64> for i256 {
    type Output = i256;

    fn mul(self, rhs: i64) -> Self::Output {
        self.short_mul(rhs)
    }
}

impl const ops::Mul for &i256 {
    type Output = i256;

    fn mul(self, rhs: Self) -> Self::Output {
        (*self).mul(*rhs)
    }
}

impl const ops::Mul<i256> for &i256 {
    type Output = i256;

    fn mul(self, rhs: i256) -> Self::Output {
        (*self).mul(rhs)
    }
}

impl const ops::Mul<&i256> for i256 {
    type Output = Self;

    fn mul(self, rhs: &i256) -> Self::Output {
        self.mul(*rhs)
    }
}

impl const ops::Mul for i256 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        self.mul(rhs)
    }
}

impl const ops::MulAssign for i256 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl const ops::MulAssign<&i256> for i256 {
    fn mul_assign(&mut self, rhs: &i256) {
        *self = *self * *rhs;
    }
}

impl const ops::MulAssign<i64> for i256 {
    fn mul_assign(&mut self, rhs: i64) {
        *self = *self * rhs;
    }
}

impl const ops::MulAssign<&i64> for i256 {
    fn mul_assign(&mut self, rhs: &i64) {
        *self = *self * *rhs;
    }
}

impl const ops::Div<&i64> for &i256 {
    type Output = i256;

    fn div(self, rhs: &i64) -> Self::Output {
        (*self).short_div(*rhs)
    }
}

impl const ops::Div<i64> for &i256 {
    type Output = i256;

    fn div(self, rhs: i64) -> Self::Output {
        (*self).short_div(rhs)
    }
}

impl const ops::Div<&i64> for i256 {
    type Output = i256;

    fn div(self, rhs: &i64) -> Self::Output {
        self.short_div(*rhs)
    }
}

impl const ops::Div<i64> for i256 {
    type Output = i256;

    fn div(self, rhs: i64) -> Self::Output {
        self.short_div(rhs)
    }
}

impl const ops::Div for &i256 {
    type Output = i256;

    fn div(self, rhs: Self) -> Self::Output {
        (*self).div(*rhs)
    }
}

impl const ops::Div<i256> for &i256 {
    type Output = i256;

    fn div(self, rhs: i256) -> Self::Output {
        (*self).div(rhs)
    }
}

impl const ops::Div<&i256> for i256 {
    type Output = Self;

    fn div(self, rhs: &i256) -> Self::Output {
        self.div(*rhs)
    }
}

impl const ops::Div for i256 {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self.div(rhs)
    }
}

impl const ops::DivAssign for i256 {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl const ops::DivAssign<&i256> for i256 {
    fn div_assign(&mut self, rhs: &i256) {
        *self = *self / *rhs;
    }
}

impl const ops::DivAssign<i64> for i256 {
    fn div_assign(&mut self, rhs: i64) {
        *self = *self / rhs;
    }
}

impl const ops::DivAssign<&i64> for i256 {
    fn div_assign(&mut self, rhs: &i64) {
        *self = *self / *rhs;
    }
}

impl const ops::Rem<&i64> for &i256 {
    type Output = i64;

    fn rem(self, rhs: &i64) -> Self::Output {
        (*self).short_rem(*rhs)
    }
}

impl const ops::Rem<i64> for &i256 {
    type Output = i64;

    fn rem(self, rhs: i64) -> Self::Output {
        (*self).short_rem(rhs)
    }
}

impl const ops::Rem<&i64> for i256 {
    type Output = i64;

    fn rem(self, rhs: &i64) -> Self::Output {
        self.short_rem(*rhs)
    }
}

impl const ops::Rem<i64> for i256 {
    type Output = i64;

    fn rem(self, rhs: i64) -> Self::Output {
        self.short_rem(rhs)
    }
}

impl const ops::Rem for &i256 {
    type Output = i256;

    fn rem(self, rhs: Self) -> Self::Output {
        (*self).rem(*rhs)
    }
}

impl const ops::Rem<i256> for &i256 {
    type Output = i256;

    fn rem(self, rhs: i256) -> Self::Output {
        (*self).rem(rhs)
    }
}

impl const ops::Rem<&i256> for i256 {
    type Output = Self;

    fn rem(self, rhs: &i256) -> Self::Output {
        self.rem(*rhs)
    }
}

impl const ops::Rem for i256 {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        self.rem(rhs)
    }
}

impl const ops::RemAssign for i256 {
    fn rem_assign(&mut self, rhs: Self) {
        *self = *self % rhs;
    }
}

impl const ops::RemAssign<&i256> for i256 {
    fn rem_assign(&mut self, rhs: &i256) {
        *self = *self % *rhs;
    }
}

impl const ops::RemAssign<i64> for i256 {
    fn rem_assign(&mut self, rhs: i64) {
        *self = Self::from_i64(*self % rhs);
    }
}

impl const ops::RemAssign<&i64> for i256 {
    fn rem_assign(&mut self, rhs: &i64) {
        *self = Self::from_i64(*self % *rhs);
    }
}

impl const ops::Not for i256 {
    type Output = Self;

    fn not(self) -> Self::Output {
        self.not()
    }
}

impl const ops::Not for &i256 {
    type Output = i256;

    fn not(self) -> Self::Output {
        (*self).not()
    }
}

impl const ops::BitAnd for &i256 {
    type Output = i256;

    fn bitand(self, rhs: Self) -> Self::Output {
        (*self).bitand(*rhs)
    }
}

impl const ops::BitAnd<i256> for &i256 {
    type Output = i256;

    fn bitand(self, rhs: i256) -> Self::Output {
        (*self).bitand(rhs)
    }
}

impl const ops::BitAnd<&i256> for i256 {
    type Output = Self;

    fn bitand(self, rhs: &i256) -> Self::Output {
        self.bitand(*rhs)
    }
}

impl const ops::BitAnd for i256 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        self.bitand(rhs)
    }
}

impl const ops::BitAndAssign for i256 {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

impl const ops::BitAndAssign<&i256> for i256 {
    fn bitand_assign(&mut self, rhs: &Self) {
        *self = *self & *rhs;
    }
}

impl const ops::BitOr for &i256 {
    type Output = i256;

    fn bitor(self, rhs: Self) -> Self::Output {
        (*self).bitor(*rhs)
    }
}

impl const ops::BitOr<i256> for &i256 {
    type Output = i256;

    fn bitor(self, rhs: i256) -> Self::Output {
        (*self).bitor(rhs)
    }
}

impl const ops::BitOr<&i256> for i256 {
    type Output = Self;

    fn bitor(self, rhs: &i256) -> Self::Output {
        self.bitor(*rhs)
    }
}

impl const ops::BitOr for i256 {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        self.bitor(rhs)
    }
}

impl const ops::BitOrAssign for i256 {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

impl const ops::BitOrAssign<&i256> for i256 {
    fn bitor_assign(&mut self, rhs: &Self) {
        *self = *self | *rhs;
    }
}

impl const ops::BitXor for &i256 {
    type Output = i256;

    fn bitxor(self, rhs: Self) -> Self::Output {
        (*self).bitxor(*rhs)
    }
}

impl const ops::BitXor<i256> for &i256 {
    type Output = i256;

    fn bitxor(self, rhs: i256) -> Self::Output {
        (*self).bitxor(rhs)
    }
}

impl const ops::BitXor<&i256> for i256 {
    type Output = Self;

    fn bitxor(self, rhs: &i256) -> Self::Output {
        self.bitxor(*rhs)
    }
}

impl const ops::BitXor for i256 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        self.bitxor(rhs)
    }
}

impl const ops::BitXorAssign for i256 {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs;
    }
}

impl const ops::BitXorAssign<&i256> for i256 {
    fn bitxor_assign(&mut self, rhs: &Self) {
        *self = *self ^ *rhs;
    }
}

impl const From<u8> for i256 {
    fn from(n: u8) -> Self {
        Self::from_u8(n)
    }
}

impl const From<u16> for i256 {
    fn from(n: u16) -> Self {
        Self::from_u16(n)
    }
}

impl const From<u32> for i256 {
    fn from(n: u32) -> Self {
        Self::from_u32(n)
    }
}

impl const From<u64> for i256 {
    fn from(n: u64) -> Self {
        Self::from_u64(n)
    }
}

impl const From<u128> for i256 {
    fn from(n: u128) -> Self {
        Self::from_u128(n)
    }
}
impl const From<i8> for i256 {
    fn from(n: i8) -> Self {
        Self::from_i8(n)
    }
}

impl const From<i16> for i256 {
    fn from(n: i16) -> Self {
        Self::from_i16(n)
    }
}

impl const From<i32> for i256 {
    fn from(n: i32) -> Self {
        Self::from_i32(n)
    }
}

impl const From<i64> for i256 {
    fn from(n: i64) -> Self {
        Self::from_i64(n)
    }
}

impl const From<i128> for i256 {
    fn from(n: i128) -> Self {
        Self::from_i128(n)
    }
}

impl const str::FromStr for i256 {
    type Err = crate::ParseIntError;

    fn from_str(src: &str) -> Result<Self, Self::Err> {
        Self::from_str(src)
    }
}

impl const ops::Shl<&u32> for i256 {
    type Output = Self;

    fn shl(self, rhs: &u32) -> Self::Output {
        self.shl(*rhs)
    }
}

impl const ops::Shl<u32> for i256 {
    type Output = Self;

    fn shl(self, rhs: u32) -> Self::Output {
        self.shl(rhs)
    }
}

impl const ops::ShlAssign<&u32> for i256 {
    fn shl_assign(&mut self, rhs: &u32) {
        *self = *self << rhs;
    }
}

impl const ops::ShlAssign<u32> for i256 {
    fn shl_assign(&mut self, rhs: u32) {
        *self = *self << rhs;
    }
}

impl const ops::Shr<&u32> for i256 {
    type Output = Self;

    fn shr(self, rhs: &u32) -> Self::Output {
        self.shr(*rhs)
    }
}

impl const ops::Shr<u32> for i256 {
    type Output = Self;

    fn shr(self, rhs: u32) -> Self::Output {
        self.shr(rhs)
    }
}

impl const ops::ShrAssign<&u32> for i256 {
    fn shr_assign(&mut self, rhs: &u32) {
        *self = *self >> rhs;
    }
}

impl const ops::ShrAssign<u32> for i256 {
    fn shr_assign(&mut self, rhs: u32) {
        *self = *self >> rhs;
    }
}
