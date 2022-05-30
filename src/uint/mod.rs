#[path ="u256.rs"]
#[cfg_attr(hide_internal, doc(hidden))]
pub mod u256_module;

#[path ="u384.rs"]
#[cfg_attr(hide_internal, doc(hidden))]
pub mod u384_module;

#[doc(inline)]
pub use u256_module::u256;

#[doc(inline)]
pub use u384_module::u384;

#[allow(non_camel_case_types)]
#[doc(hidden)]
pub type u512 = u256;
