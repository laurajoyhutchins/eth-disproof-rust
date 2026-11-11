# Rust port of the OpenAI ETH Lean program

A source-pinned Rust implementation of **selected executable parts** of OpenAI's Lean development for *The Exponential Time Hypothesis is False*. The upstream source is [`openai/math@4eaee87`](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT); individual Git object identities are recorded in [`reference/source-manifest.json`](reference/source-manifest.json).

This is a work in progress, **not** an independent proof of the theorem or a complete native SAT counter.

## Build and test

Install Rust **1.99.1**, then from this directory run:

```sh
cargo fmt --all -- --check
cargo test --locked --offline --all-targets
cargo clippy --locked --offline --all-targets -- -D warnings
printf 'p cnf 3 2\n1 2 0\n1 3 0\n' | cargo run --quiet --offline
```


## Source and implementation map

| Area | Code | Boundary |
| --- | --- | --- |
| Finite CNF semantics and encoding | [`src/lib.rs`](src/lib.rs) | Executable Rust finite model |
| Physical stack/register machine, structured programs | [`src/bit_program.rs`](src/bit_program.rs) | Executable instruction interpreter and compiler |
| Selected high/tuple/query stages | `src/native_high.rs`, `src/native_tuple.rs`, `src/native_query_prefix.rs` | Source-correlated executable fragments |
| Layout, cache, head and pair stages | `src/native_*.rs` | Selected source-defined fragments, not a complete pipeline |
| Missing and partial stages | [`src/remaining.rs`](src/remaining.rs) | Explicit executable/partial/stub/proof-obligation boundaries |
| Regression and conformance cases | [`tests/`](tests/) | Finite Rust properties and source-derived examples |
| Pinned Lean traces and source metadata | [`reference/`](reference/) | Fixtures and manifests; not proof of an executed Lean/Rust comparison |

The semantic counting fallback is not the Lean program's complete native counting path. Source-instruction counts and live stack-bit metrics are **not** TM2 microstep counts, physical memory measurements, or the theorem's asymptotic resource bounds.

## What would establish stronger correctness

- Compile and execute the **original pinned Lean modules**, including the required Mathlib dependencies.
- Compare complete machine transitions and halt/cleanup behavior against independently executed Rust implementations, without replacing unavailable Lean with fixtures.
- Complete the source-defined counting pipeline, then separately validate primitive TM2 resource accounting and the claimed worst-case bounds.

A passing `cargo test` does not discharge any of these obligations. Incomplete computations must refuse rather than silently substitute a semantic oracle.

For deeper details, see [the remaining-port map](docs/remaining-lean-port.md), [TDD accuracy audit](docs/tdd-accuracy-audit.md), and [guided Git history](docs/reading-the-history.md). The main repository [README](../../README.md) explains the project and licenses.

## Licensing

Original project contributions: MIT. Upstream-derived material: Apache-2.0 obligations also apply. See the repository's `LICENSE`, `LICENSE-APACHE`, and `NOTICE`.
