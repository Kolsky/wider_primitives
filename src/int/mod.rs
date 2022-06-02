#[path ="i256.rs"]
#[cfg_attr(hide_internal, doc(hidden))]
pub mod i256_module;

#[doc(inline)]
pub use i256_module::i256;

#[path ="i384.rs"]
#[cfg_attr(hide_internal, doc(hidden))]
pub mod i384_module;

#[doc(inline)]
pub use i384_module::i384;

#[path ="i512.rs"]
#[cfg_attr(hide_internal, doc(hidden))]
pub mod i512_module;

#[doc(inline)]
pub use i512_module::i512;
