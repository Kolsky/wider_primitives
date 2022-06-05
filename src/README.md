# wider primitives

This library aims to replicate the core vibe of standard integer primitive types, but with more bits in them. Most of their API should be available as-is and documented accordingly, with as much `const`-ness as possible. It also works in a `#![no_std]` environments, unless otherwise stated in optional features that may be added later.

# Feature flags

## internals-doc-visible

Shows publicly available `doc(hidden)` modules, exports, items, methods, functions and so on. No semver compatible guarantees are made w.r.t. breaking changes in any of those. Might be useful with `cargo doc --features internals-doc-visible` to inspect the source code directly.

## unstable

Enables nightly support. Currently makes all impls related to [`ops`](https://doc.rust-lang.org/core/ops/index.html), [`cmp`](https://doc.rust-lang.org/core/cmp/index.html), [`From`](https://doc.rust-lang.org/core/convert/trait.From.html) and [`FromStr`](https://doc.rust-lang.org/core/str/trait.FromStr.html) const. You would also need to manually specify the list of nightly features used inside your crate or a library, such as `const_trait_impl` and `const_mut_refs`.

# The minimum supported rust version (MSRV)

If there is any good reason to use the latest stable release for upcoming updates, then expect it to be used in a next major bump. A table below shall track the history of such occurences.

| Version |  MSRV  |
|---------|--------|
| 0.0.5   | 1.59.0 |