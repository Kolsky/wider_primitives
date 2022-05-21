#[path ="u256.rs"]
#[cfg_attr(hide_internal, doc(hidden))]
pub mod u256_module;

#[doc(inline)]
pub use u256_module::u256;

#[allow(non_camel_case_types)]
#[doc(hidden)]
pub type u384 = u256;

#[allow(non_camel_case_types)]
#[doc(hidden)]
pub type u512 = u256;
