#[path ="i256.rs"]
#[cfg_attr(hide_internal, doc(hidden))]
pub mod i256_module;

#[doc(inline)]
pub use i256_module::i256;

#[allow(non_camel_case_types)]
pub type i384 = i256;

#[allow(non_camel_case_types)]
pub type i512 = i256;