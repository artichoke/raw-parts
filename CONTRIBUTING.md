# Contributing to Artichoke – raw-parts

👋 Hi and welcome to [Artichoke]. Thanks for taking the time to contribute!
💪💎🙌

Artichoke aspires to be a [recent MRI Ruby][mri-target]-compatible
implementation of the Ruby programming language. [There is lots to do].

[mri-target]:
  https://github.com/artichoke/artichoke/blob/trunk/RUBYSPEC.md#mri-target

raw-parts is a utility crate that makes `Vec::from_raw_parts` and
`Vec::into_raw_parts` APIs easier to use by giving names to the raw parts.
Artichoke uses this crate in its implementations of [`Array`] and [`String`].

If Artichoke does not run Ruby source code in the same way that MRI does, it is
a bug and we would appreciate if you [filed an issue so we can fix it]. [File
bugs specific to raw-parts in this repository].

If you would like to contribute code to raw-parts 👩‍💻👨‍💻, find an issue that looks
interesting and leave a comment that you're beginning to investigate. If there
is no issue, please file one before beginning to work on a PR. [Good first
issues are labeled `E-easy`].

## Setup

raw-parts includes Rust and text sources. Developing on raw-parts requires
configuring several dependencies.

raw-parts uses [mise] to manage the local development toolchain declared in
[`mise.toml`](mise.toml), including Node.js, Rust, and repo-local developer
tools like `cargo-deny`, `cargo-mutants`, `cargo-outdated`, and `zizmor`. For
Rust, `mise` uses [rustup] under the hood. Nightly-only Rust workflows in this
repository continue to use `rustup` directly.

### Rust Toolchain

raw-parts depends on Rust and several compiler plugins for linting and
formatting. raw-parts is guaranteed to build on the latest stable release of the
Rust compiler.

#### Installation

Install and activate [mise], then install the toolchains declared in
[`mise.toml`](mise.toml):

```sh
mise install
```

`mise.toml` configures the latest stable Rust toolchain with the `minimal`
profile plus the `clippy` and `rustfmt` components. `mise` installs that
toolchain via [rustup].

Some repository tasks still require nightly Rust. The `doc` mise task uses
`rustup run --install nightly`, which installs nightly on demand if needed.

To update your stable Rust compiler to the latest version, run:

```sh
rustup update stable
```

### Rust Crates

raw-parts depends on several Rust libraries, or crates. Once you have the Rust
toolchain installed, you can install the crates specified in
[`Cargo.toml`](Cargo.toml) by running:

```sh
cargo build
```

### Development tasks

The pinned versions for Node.js, Rust, and the repo-local developer tools live
in [`mise.toml`](mise.toml). Install the toolchain and text-formatting
dependencies with:

```sh
mise install
mise run pnpm-install
```

Run `mise tasks` to list the available build, test, lint, format, and
documentation tasks.

[mise]: https://mise.jdx.dev/

### Node.js

Node.js is an optional dependency that is used for formatting text sources with
[prettier].

Node.js is only required for formatting if modifying the following filetypes:

- `md`
- `yaml`
- `yml`

Install Node.js with `mise`:

```sh
mise install
```

## Linting

To lint all sources run:

```sh
mise run lint
```

## Testing

A PR must have new or existing tests for it to be merged. The [Rust book chapter
on testing] is a good place to start.

To run tests:

```sh
mise run test
```

`cargo test` accepts a filter argument that will limit test execution to tests
that substring match. For example, to run all of the tests for ascii casecmp:

```sh
cargo test ascii
```

Tests are run for every PR. All builds must pass before merging a PR.

## Publishing

Maintainers publish releases through crates.io trusted publishing. See
[`docs/publishing.md`](docs/publishing.md) for the trust configuration, release
procedure, and failure-recovery guidance.

## Updating Dependencies

### Rust Crates

Version specifiers in `Cargo.toml` are NPM caret-style by default. A version
specifier of `4.1.2` means `4.1.2 <= version < 5.0.0`.

To see what crates are outdated, you can use [cargo-outdated].

If you need to pull in an updated version of a crate for a bugfix or a new
feature, update the version number in `Cargo.toml`. See
[artichoke/artichoke#548] for an example.

Regular dependency bumps are handled by [@dependabot].

[artichoke]: https://github.com/artichoke
[there is lots to do]: https://github.com/artichoke/artichoke/issues
[`array`]: https://ruby-doc.org/core-3.1.2/Array.html
[`string`]: https://ruby-doc.org/core-3.1.2/String.html
[filed an issue so we can fix it]:
  https://github.com/artichoke/artichoke/issues/new
[file bugs specific to raw-parts in this repository]:
  https://github.com/artichoke/raw-parts/issues/new
[good first issues are labeled `e-easy`]:
  https://github.com/artichoke/raw-parts/labels/E-easy
[rustup]: https://rustup.rs/
[homebrew]: https://docs.brew.sh/Installation
[rubocop]: https://github.com/rubocop-hq/rubocop
[prettier]: https://prettier.io/
[node.js]: https://nodejs.org/en/download/package-manager/
[rust book chapter on testing]:
  https://doc.rust-lang.org/book/ch11-00-testing.html
[cargo-outdated]: https://github.com/kbknapp/cargo-outdated
[artichoke/artichoke#548]: https://github.com/artichoke/artichoke/pull/548
[@dependabot]: https://dependabot.com/
