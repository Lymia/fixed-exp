# fixed-exp

[![crates.io](https://img.shields.io/crates/v/fixed-exp)](https://crates.io/crates/fixed-exp)
[![docs.rs](https://docs.rs/fixed-exp/badge.svg)](https://docs.rs/fixed-exp/)

Exponentiation for fixed-point numbers.

```toml
[dependencies]
fixed-exp = "0.1.0"
```

## Usage

This crate provides `powi` and `powf` for most `fixed` number types through the `FixedPowI` and `FixedPowF` extension traits:

```rust
use fixed::types::I32F32;
use fixed_exp::{FixedPowI, FixedPowF};

let x = I32F32::from_num(4.0);
assert_eq!(I32F32::from_num(1024.0), x.powi(5));
assert_eq!(I32F32::from_num(8.0), x.powf(I32F32::from_num(1.5)));
```

## License

Licensed under either of Apache License, Version 2.0 or MIT license at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in this crate by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.