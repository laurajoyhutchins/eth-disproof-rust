# ETH Disproof: Rust Port

An experimental Rust port of executable machinery from OpenAI's [*The Exponential Time Hypothesis is False*](https://github.com/openai/math/blob/main/lean/docs/378.md) Lean development.

**Status:** Incomplete research implementation. This repository does **not** independently verify the ETH result, reproduce the complete native counting algorithm, or establish its time and space bounds. Executable components and unfinished proof obligations are kept distinct.

## Build and test

Use Rust **1.99.1**. The crate has no external Cargo dependencies.

```sh
cd rust/lean_eth_reference
cargo fmt --all -- --check
cargo test --locked --offline --all-targets
cargo clippy --locked --offline --all-targets -- -D warnings
```

For a small CNF counting example:

```sh
printf 'p cnf 3 2\n1 2 0\n1 3 0\n' | cargo run --quiet --offline
```

The Rust-only CI workflow is [`.github/workflows/rust.yml`](.github/workflows/rust.yml); [`cloudbuild.rust.yaml`](cloudbuild.rust.yaml) supplies a separate Cloud Build check. Passing Rust tests is **not** a substitute for an imported-Lean comparison.

## What is here

- [`rust/lean_eth_reference/`](rust/lean_eth_reference/): finite CNF semantics and encodings, a physical bit-program interpreter, selected source-defined machine stages, regression tests, and explicit unavailable stages.
- [Source manifest](rust/lean_eth_reference/reference/source-manifest.json): pinned Lean source objects from [`openai/math` revision `4eaee87`](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT).
- [Implementation detail](rust/lean_eth_reference/README.md): coverage, physical-machine boundaries, and known gaps.

Not yet established: a complete executable native counting path, genuine pinned Lean/Rust differential parity, TM2 primitive time/tape refinement, or the claimed asymptotic complexity guarantee. Missing Lean/Mathlib runtime artifacts must not be replaced with simulated traces or golden fixtures.

## History and research branches

`main` has a source-linked, instructional first-parent history, while original development ancestry is retained. Read it with:

```sh
git log --first-parent --reverse --oneline main
```

See the [history guide](rust/lean_eth_reference/docs/reading-the-history.md). Earlier Python/Cython Sudoku research remains on [`python/sudoku-research`](../../tree/python/sudoku-research); it is not part of the Rust build.

## License and attribution

Original contributions are provided under the [MIT license](LICENSE). Code and other materials adapted from [`openai/math`](https://github.com/openai/math) remain subject to its **Apache-2.0** terms. See [`LICENSE-APACHE`](LICENSE-APACHE) and [`NOTICE`](NOTICE). The Rust crate declares `MIT AND Apache-2.0` to reflect both sets of obligations.
