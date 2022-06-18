//! Serialization and deserialization, coupled with extra modules (traits, to be more specific)
//! for use in `serde(with(_))` field attribute.

use core::fmt;
use core::fmt::Write;
use core::marker::PhantomData;
use serde::Serialize;
use serde::Deserialize;
use serde::Serializer;
use serde::Deserializer;
use serde::ser;
use serde::ser::SerializeTuple;
use serde::de;
use serde::de::Visitor;
use crate::uint::*;
use crate::int::*;
use crate::ParseIntError;

#[cfg_attr(hide_internal, doc(hidden))]
pub trait Serde: Sized + fmt::Display + fmt::LowerHex + fmt::UpperHex {
    const SIGNED: bool;
    const BITS: u32;

    fn as_ref_inner(&self) -> &[u64];

    fn deserialize_from_inner<'de, D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>;
    
    fn from_str(src: &str) -> Result<Self, ParseIntError>;

    fn from_hex_str(src: &str) -> Result<Self, ParseIntError>;

    fn from_hex_str_sign_aware(src: &str) -> Result<Self, ParseIntError> {
        Self::from_hex_str(src)
    }
}

impl Serde for u256 {
    const SIGNED: bool = Self::MIN.lt(Self::ZERO);

    const BITS: u32 = Self::BITS;

    fn as_ref_inner(&self) -> &[u64] {
        &self.inner.inner
    }

    fn deserialize_from_inner<'de, D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>,
    {
        Deserialize::deserialize(deserializer).map(Self::from_inner)
    }

    fn from_str(src: &str) -> Result<Self, ParseIntError> {
        Self::from_str(src)
    }

    fn from_hex_str(src: &str) -> Result<Self, ParseIntError> {
        Self::from_hex_str(src)
    }
}

impl Serde for u384 {
    const SIGNED: bool = Self::MIN.lt(Self::ZERO);

    const BITS: u32 = Self::BITS;

    fn as_ref_inner(&self) -> &[u64] {
        &self.inner.inner
    }

    fn deserialize_from_inner<'de, D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>,
    {
        Deserialize::deserialize(deserializer).map(Self::from_inner)
    }

    fn from_str(src: &str) -> Result<Self, ParseIntError> {
        Self::from_str(src)
    }

    fn from_hex_str(src: &str) -> Result<Self, ParseIntError> {
        Self::from_hex_str(src)
    }
}

impl Serde for u512 {
    const SIGNED: bool = Self::MIN.lt(Self::ZERO);

    const BITS: u32 = Self::BITS;

    fn as_ref_inner(&self) -> &[u64] {
        &self.inner.inner
    }

    fn deserialize_from_inner<'de, D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>,
    {
        Deserialize::deserialize(deserializer).map(Self::from_inner)
    }

    fn from_str(src: &str) -> Result<Self, ParseIntError> {
        Self::from_str(src)
    }

    fn from_hex_str(src: &str) -> Result<Self, ParseIntError> {
        Self::from_hex_str(src)
    }
}

impl Serde for i256 {
    const SIGNED: bool = Self::MIN.lt(Self::ZERO);

    const BITS: u32 = Self::BITS;

    fn as_ref_inner(&self) -> &[u64] {
        &self.inner.inner
    }

    fn deserialize_from_inner<'de, D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>,
    {
        Deserialize::deserialize(deserializer).map(Self::from_inner)
    }

    fn from_str(src: &str) -> Result<Self, ParseIntError> {
        Self::from_str(src)
    }

    fn from_hex_str(src: &str) -> Result<Self, ParseIntError> {
        u256::from_hex_str(src).map(u256::as_i256)
    }

    fn from_hex_str_sign_aware(src: &str) -> Result<Self, ParseIntError> {
        Self::from_str_radix(src, 16)
    }
}

impl Serde for i384 {
    const SIGNED: bool = Self::MIN.lt(Self::ZERO);

    const BITS: u32 = Self::BITS;

    fn as_ref_inner(&self) -> &[u64] {
        &self.inner.inner
    }

    fn deserialize_from_inner<'de, D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>,
    {
        Deserialize::deserialize(deserializer).map(Self::from_inner)
    }

    fn from_str(src: &str) -> Result<Self, ParseIntError> {
        Self::from_str(src)
    }

    fn from_hex_str(src: &str) -> Result<Self, ParseIntError> {
        u384::from_hex_str(src).map(u384::as_i384)
    }

    fn from_hex_str_sign_aware(src: &str) -> Result<Self, ParseIntError> {
        Self::from_str_radix(src, 16)
    }
}

impl Serde for i512 {
    const SIGNED: bool = Self::MIN.lt(Self::ZERO);

    const BITS: u32 = Self::BITS;

    fn as_ref_inner(&self) -> &[u64] {
        &self.inner.inner
    }

    fn deserialize_from_inner<'de, D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>,
    {
        Deserialize::deserialize(deserializer).map(Self::from_inner)
    }

    fn from_str(src: &str) -> Result<Self, ParseIntError> {
        Self::from_str(src)
    }

    fn from_hex_str(src: &str) -> Result<Self, ParseIntError> {
        u512::from_hex_str(src).map(u512::as_i512)
    }

    fn from_hex_str_sign_aware(src: &str) -> Result<Self, ParseIntError> {
        Self::from_str_radix(src, 16)
    }
}

impl Serialize for u256 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer,
    {
        DefaultModule::serialize(self, serializer)
    }
}

impl Serialize for u384 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer,
    {
        DefaultModule::serialize(self, serializer)
    }
}

impl Serialize for u512 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer,
    {
        DefaultModule::serialize(self, serializer)
    }
}

impl Serialize for i256 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer,
    {
        DefaultModule::serialize(self, serializer)
    }
}

impl Serialize for i384 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer,
    {
        DefaultModule::serialize(self, serializer)
    }
}

impl Serialize for i512 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer,
    {
        DefaultModule::serialize(self, serializer)
    }
}

impl<'de> Deserialize<'de> for u256 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>,
    {
        DefaultModule::deserialize(deserializer)
    }
}

impl<'de> Deserialize<'de> for u384 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>,
    {
        DefaultModule::deserialize(deserializer)
    }
}

impl<'de> Deserialize<'de> for u512 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>,
    {
        DefaultModule::deserialize(deserializer)
    }
}

impl<'de> Deserialize<'de> for i256 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>,
    {
        DefaultModule::deserialize(deserializer)
    }
}

impl<'de> Deserialize<'de> for i384 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>,
    {
        DefaultModule::deserialize(deserializer)
    }
}

impl<'de> Deserialize<'de> for i512 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de>,
    {
        DefaultModule::deserialize(deserializer)
    }
}

struct ByteBuf<const N: usize> {
    buf: [u8; N],
    written: usize,
}

impl<const N: usize> ByteBuf<N> {
    fn as_bytes(&self) -> &[u8] {
        &self.buf[..self.written]
    }

    fn fmt_value<S>(
        write: impl FnOnce(&mut Self) -> fmt::Result,
        serializer: S,
    ) -> Result<S::Ok, S::Error>
        where S: Serializer,
    {
        let mut buf = Self { buf: [0; N], written: 0 };
        write(&mut buf).map_err(ser::Error::custom)?;
        let s = core::str::from_utf8(buf.as_bytes()).map_err(ser::Error::custom)?;
        serializer.serialize_str(s)
    }
}

impl<const N: usize> Write for ByteBuf<N> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let len = s.len();
        if len > N - self.written {
            return Err(fmt::Error);
        }
        let buf = &mut self.buf[self.written..];
        buf[..len].copy_from_slice(s.as_bytes());
        self.written += len;
        Ok(())
    }
}

/// Serialize and deserialize integer as a decimal string.
pub trait DecStr: Serde {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer,
    {
        let slice = self.as_ref_inner();
        match slice.len() {
            4 => ByteBuf::<78>::fmt_value(|buf| write!(buf, "{}", self), serializer),
            6 => ByteBuf::<117>::fmt_value(|buf| write!(buf, "{}", self), serializer),
            8 => ByteBuf::<155>::fmt_value(|buf| write!(buf, "{}", self), serializer),
            _ => Err(ser::Error::custom("not implemented")),
        }
    }
    
    fn deserialize<'de, D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(DecVisitor(PhantomData))
    }
}

impl DecStr for u256 {}

impl DecStr for u384 {}

impl DecStr for u512 {}

impl DecStr for i256 {}

impl DecStr for i384 {}

impl DecStr for i512 {}

/// Serialize and deserialize integer as inner array.
pub trait InnerArray: Serde {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer,
    {
        let slice = self.as_ref_inner();
        let mut tup = serializer.serialize_tuple(slice.len())?;
        for word in slice.iter() {
            tup.serialize_element(word)?;
        }
        tup.end()
    }
    
    fn deserialize<'de, D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::deserialize_from_inner(deserializer)
    }
}

impl InnerArray for u256 {}

impl InnerArray for u384 {}

impl InnerArray for u512 {}

impl InnerArray for i256 {}

impl InnerArray for i384 {}

impl InnerArray for i512 {}

/// Serialize and deserialize integer as a decimal string with human readable formats and as inner array in other cases.
/// Used by implementations of [`Serialize`] and [`Deserialize`].
pub trait DefaultModule: DecStr + InnerArray {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer,
    {
        match serializer.is_human_readable() {
            true => DecStr::serialize(self, serializer),
            false => InnerArray::serialize(self, serializer),
        }
    }
    
    fn deserialize<'de, D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        match deserializer.is_human_readable() {
            true => DecStr::deserialize(deserializer),
            false => InnerArray::deserialize(deserializer),
        }
    }
}

impl DefaultModule for u256 {}

impl DefaultModule for u384 {}

impl DefaultModule for u512 {}

impl DefaultModule for i256 {}

impl DefaultModule for i384 {}

impl DefaultModule for i512 {}

/// Serialize and deserialize integer as a hexadecimal string with several options.
/// 
/// # Generic parameters
/// 
/// * `SIGN_AWARE` -- permit an optional sign. Only affects deserialization for unsigned types,
/// but signed ones are also serialized differently, as if they were cast to unsigned type of the same size.
/// Disabled by default.
/// 
/// * `UPPER_HEX` -- use uppercase hexadecimal characters for serialization. Disabled by default (lowercase preferred).
/// 
/// * `STRICT` -- force deserializer to match the case used to serialize an integer. Disabled by default (case ignored).
pub trait HexStr<const SIGN_AWARE: bool = false, const UPPER_HEX: bool = false, const STRICT: bool = false>: Serde {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer,
    {
        let slice = self.as_ref_inner();
        match slice.len() {
            4 if UPPER_HEX => ByteBuf::<65>::fmt_value(|buf| write!(buf, "{:X}", self), serializer),
            6 if UPPER_HEX => ByteBuf::<97>::fmt_value(|buf| write!(buf, "{:X}", self), serializer),
            8 if UPPER_HEX => ByteBuf::<129>::fmt_value(|buf| write!(buf, "{:X}", self), serializer),
            4 => ByteBuf::<65>::fmt_value(|buf| write!(buf, "{:x}", self), serializer),
            6 => ByteBuf::<97>::fmt_value(|buf| write!(buf, "{:x}", self), serializer),
            8 => ByteBuf::<129>::fmt_value(|buf| write!(buf, "{:x}", self), serializer),
            _ => Err(ser::Error::custom("not implemented")),
        }
    }
    
    fn deserialize<'de, D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(HexVisitor {
            sign_aware: SIGN_AWARE,
            ser_upper_hex: UPPER_HEX,
            de_strict: STRICT,
            marker: PhantomData,
        })
    }
}

impl<const SIGN_AWARE: bool, const UPPER_HEX: bool, const STRICT: bool> HexStr<SIGN_AWARE, UPPER_HEX, STRICT> for u256 {}

impl<const SIGN_AWARE: bool, const UPPER_HEX: bool, const STRICT: bool> HexStr<SIGN_AWARE, UPPER_HEX, STRICT> for u384 {}

impl<const SIGN_AWARE: bool, const UPPER_HEX: bool, const STRICT: bool> HexStr<SIGN_AWARE, UPPER_HEX, STRICT> for u512 {}

impl<const SIGN_AWARE: bool, const UPPER_HEX: bool, const STRICT: bool> HexStr<SIGN_AWARE, UPPER_HEX, STRICT> for i256 {}

impl<const SIGN_AWARE: bool, const UPPER_HEX: bool, const STRICT: bool> HexStr<SIGN_AWARE, UPPER_HEX, STRICT> for i384 {}

impl<const SIGN_AWARE: bool, const UPPER_HEX: bool, const STRICT: bool> HexStr<SIGN_AWARE, UPPER_HEX, STRICT> for i512 {}

/// Trait alias helper for HexStr with default parameters. An escape hatch for [current limitations](https://github.com/rust-lang/rust/blob/1b7c3bcef9dc88e65c4914887071e432436a0b04/src/test/ui/const-generics/defaults/doesnt_infer.rs).
pub trait HexStrDefault: HexStr {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer,
    {
        HexStr::serialize(self, serializer)
    }
    
    fn deserialize<'de, D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        HexStr::deserialize(deserializer)
    }
}

impl<H: HexStr> HexStrDefault for H {}

struct DecVisitor<S>(PhantomData<S>);

impl<'de, S: Serde> Visitor<'de> for DecVisitor<S> {
    type Value = S;

    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "a string containing a base 10 integer between -2^{pow} and 2^{pow}", pow = S::BITS - 1)
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
        where E: serde::de::Error,
    {
        S::from_str(v).map_err(de::Error::custom)
    }
}

struct HexVisitor<S> {
    sign_aware: bool,
    ser_upper_hex: bool,
    de_strict: bool,
    marker: PhantomData<S>,
}

impl<'de, S: Serde> Visitor<'de> for HexVisitor<S> {
    type Value = S;

    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let case = if !self.de_strict { "" } else if self.ser_upper_hex { ", all uppercase" } else { ", all lowercase" };
        if S::SIGNED {
            write!(f, "a string containing a base 16{repr} integer between -2^{pow} and 2^{pow}{case}",
                repr = if self.sign_aware { "" } else { " unsigned representation of" }, 
                pow = S::BITS - 1,
            )
        }
        else {
            write!(f, "a string containing a base 16 integer between 0 and 2^{pow}{case}",
                pow = S::BITS,
            )
        }
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
        where E: de::Error,
    {
        fn is_upper_hex(b: u8) -> bool {
            matches!(b, b'0'..=b'9' | b'A'..=b'F')
        }

        fn is_lower_hex(b: u8) -> bool {
            matches!(b, b'0'..=b'9' | b'a'..=b'f')
        }

        let no_sign = v.strip_prefix(&['-', '+']);
        if !self.sign_aware && no_sign.is_some() {
            return Err(de::Error::custom("expected only hexadecimal, found sign"));
        }
        let no_sign = no_sign.unwrap_or(v);

        if self.de_strict {
            match self.ser_upper_hex {
                true if !no_sign.bytes().all(is_upper_hex) =>
                    return Err(de::Error::custom("expected all uppercase, found lowercase or invalid digit")),
                false if !no_sign.bytes().all(is_lower_hex) =>
                    return Err(de::Error::custom("expected all lowercase, found uppercase or invalid digit")),
                _ => (),
            }
        }
        
        let parse_int = if self.sign_aware {
            S::from_hex_str_sign_aware(v)
        }
        else {
            S::from_hex_str(v)
        };

        parse_int.map_err(de::Error::custom)
    }
}
