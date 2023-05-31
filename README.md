# raw-parts

[![GitHub Actions](https://github.com/artichoke/raw-parts/workflows/CI/badge.svg)](https://github.com/artichoke/raw-parts/actions)
[![Code Coverage](https://codecov.artichokeruby.org/raw-parts/badges/flat.svg?nocache=2)](https://codecov.artichokeruby.org/raw-parts/index.html)
[![Discord](https://img.shields.io/discord/607683947496734760)](https://discord.gg/QCe2tp2)
[![Twitter](https://img.shields.io/twitter/follow/artichokeruby?label=Follow&style=social)](https://twitter.com/artichokeruby)
<br>
[![Crate](https://img.shields.io/crates/v/raw-parts.svg)](https://crates.io/crates/raw-parts)
[![API](https://docs.rs/raw-parts/badge.svg)](https://docs.rs/raw-parts)
[![API trunk](https://img.shields.io/badge/docs-trunk-blue.svg)](https://artichoke.github.io/raw-parts/raw_parts/)

A wrapper around the decomposed parts of a `Vec<T>`.

This struct contains the `Vec`'s internal pointer, length, and allocated
capacity.

`RawParts` makes [`Vec::from_raw_parts`] and [`Vec::into_raw_parts`] easier to
use by giving names to the returned values. This prevents errors from mixing up
the two `usize` values of length and capacity.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
raw-parts = "1.1.2"
```

Then decompose `Vec<T>`s like:

```rust
use raw_parts::RawParts;

let v: Vec<i32> = vec![-1, 0, 1];

let RawParts { ptr, length, capacity } = RawParts::from_vec(v);

let rebuilt = unsafe {
    // We can now make changes to the components, such as
    // transmuting the raw pointer to a compatible type.
    let ptr = ptr as *mut u32;
    let raw_parts = RawParts { ptr, length, capacity };

    raw_parts.into_vec()
};
assert_eq!(rebuilt, [4294967295, 0, 1]);
```

## `no_std`

raw-parts is `no_std` compatible with a required dependency on [`alloc`].

## Minimum Supported Rust Version

This crate requires at least Rust 1.56.0. This version can be bumped in minor
releases.

## License

`raw-parts` is licensed under the [MIT License](LICENSE) (c) Ryan Lopopolo.

[`vec::from_raw_parts`]:
  https://doc.rust-lang.org/alloc/vec/struct.Vec.html#method.from_raw_parts
[`vec::into_raw_parts`]:
  https://doc.rust-lang.org/alloc/vec/struct.Vec.html#method.into_raw_parts
[`alloc`]: https://doc.rust-lang.org/alloc/
