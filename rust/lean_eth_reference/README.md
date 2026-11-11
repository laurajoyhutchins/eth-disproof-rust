# Rust implementation of the OpenAI Lean ETH machine

This crate implements selected executable components from the pinned
[`openai/math` Lean development](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT).
It contains **two separate CLI programs** with different correctness claims.

## Source-defined physical frontend

```sh
cd rust/lean_eth_reference
printf 'p cnf 3 3\n1 0\n1 2 0\n-2 3 0\n' | \
  cargo run --locked --offline --bin eth-frontend
```

This executes the source-correlated `Native.frontendCommand` as a Rust
`BitProgram` with 80 registers and 1,220 stacks. It prints the preserved
input, ambient header and normalized formula body, together with source
instruction count and peak live stack bits. The answer port remains empty.
It does **not** compute #SAT. See [the physical ABI and example](docs/m2-runnable-frontend.md).

## Bounded semantic counting oracle

```sh
printf 'p cnf 3 2\n1 2 0\n1 3 0\n' | \
  cargo run --locked --offline --bin lean-eth-reference
```

This produces `count=5` using a bounded exponential enumeration leaf.
It is useful as an independent small-input correctness check, **not** an
execution of the proposed fast algorithm.

## Code map

| Location | Responsibility |
| --- | --- |
| `src/bit_program.rs` | Source-correlated register/stack interpreter and program combinators |
| `src/native_frontend.rs`, `src/native_*.rs` | Source-defined executable frontend and other selected machine fragments |
| `src/remaining.rs` | Dependency spine and explicit unsupported/refusal boundaries |
| `src/lib.rs` | Finite CNF semantics, encodings and bounded semantic counting |
| `tests/` | Rust behavior, invariant and refusal tests |
| `reference/source-manifest.json` | Pinned upstream source inventory; not Lean/Rust equivalence evidence |

The [single evidence matrix](docs/evidence.md) gives the accepted execution
claims, reproduction steps, outstanding Lean/Rust comparison, and separate
TM2 accounting obligations. Read [remaining stages](docs/remaining-lean-port.md)
for the dependency graph and [the history guide](docs/reading-the-history.md)
for the reconstructed first-parent study sequence.

## Local Rust checks

Install Rust **1.99.1**. The crate has no third-party Cargo dependencies.

```sh
cargo fmt --all -- --check
cargo test --locked --offline --all-targets
cargo clippy --locked --offline --all-targets -- -D warnings
```

The [public Rust workflow](../../.github/workflows/rust.yml) executes on
PRs, pushes to `main`, and manual dispatch. Check its result for the exact
commit you are evaluating. Imported-Lean differential execution and primitive
TM2 resource verification have distinct acceptance requirements.

Original contributions are MIT-licensed. Adapted upstream source is subject
to Apache-2.0 obligations; see the repository's `LICENSE`,
`LICENSE-APACHE` and `NOTICE`.
