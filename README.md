# ETH Disproof: Rust Port

An independent, source-pinned Rust port of **selected executable components** of OpenAI's Lean development, [*The Exponential Time Hypothesis is False*](https://github.com/openai/math/blob/main/lean/docs/378.md).

The title identifies the upstream research being studied; **this repository is not an independent disproof of ETH**. It does not yet reproduce the complete source-native algorithm or validate the claimed asymptotic bounds.

## Try the current implementation

Install **Rust 1.99.1**. The Rust crate has no external Cargo dependencies.

```sh
cd rust/lean_eth_reference
cargo test --locked --offline --all-targets
printf 'p cnf 3 2\n1 2 0\n1 3 0\n' | cargo run --quiet --locked --offline
```

For this formula the count is **5**. The command-line example uses an **explicitly bounded exponential enumeration oracle**, not the proposed ETH algorithm. It refuses instances outside its supported limits rather than claiming a fast general-purpose SAT counter.

For full local checks:

```sh
cargo fmt --all -- --check
cargo test --locked --offline --all-targets
cargo clippy --locked --offline --all-targets -- -D warnings
```

The [Rust GitHub workflow](.github/workflows/rust.yml) is manually dispatched, and [Cloud Build configuration](cloudbuild.rust.yaml) is checked in separately. Neither test path establishes equivalence with the original Lean execution.

## What has been implemented?

| Area | Current boundary |
| --- | --- |
| CNF parsing, finite semantics, bounded counting | Executable Rust with tests |
| Bit-program interpreter and selected native machine stages | Executable, source-correlated Rust fragments |
| Original Lean/Mathlib execution and Lean-to-Rust differential traces | Not independently established by this repository |
| Full source-native counting pipeline and primitive TM2 refinement | Incomplete |
| ETH conclusion and worst-case time/space claims | Not established by Rust tests |

The implementation intentionally distinguishes executable, partial, stubbed, noncomputable, and proof-only stages. An unavailable stage must not be silently replaced with a semantic shortcut.

See [the Rust implementation map](rust/lean_eth_reference/README.md) and [remaining-port inventory](rust/lean_eth_reference/docs/remaining-lean-port.md) for concrete module coverage and missing work.

## Where to look

- [Rust crate](rust/lean_eth_reference/): interpreter, source-correlated programs, tests, and command-line example.
- [Pinned source manifest](rust/lean_eth_reference/reference/source-manifest.json): upstream Lean source identities, rooted at [`openai/math@4eaee875`](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT).
- [Tests and reference traces](rust/lean_eth_reference/tests/): bounded Rust assertions and source-derived fixtures. Fixtures alone are **not** an imported-Lean comparison.
- [Guided Git history](rust/lean_eth_reference/docs/reading-the-history.md): a first-parent reading sequence explaining the port's implementation boundaries.

Earlier Python/Cython Sudoku experiments remain on the [`python/sudoku-research` branch](https://github.com/laurajoyhutchins/eth-disproof-rust/tree/python/sudoku-research) and are not required by this Rust crate.

## Reproducibility and contributions

The repository pins the Rust toolchain and identifies the original Lean source revision. A complete Lean-based conformance result requires independently building and running that pinned original with its Mathlib dependencies. This has **not** been demonstrated by the tests on `main`.

Bug reports, small source-faithful port increments, and reproducible counterexamples are welcome; see [CONTRIBUTING.md](CONTRIBUTING.md). Please distinguish *tested Rust behavior*, *original-Lean differential evidence*, and *mathematical proof obligations* in any claim.

## Attribution and license

This is independent research, **not an official OpenAI release**. Original contributions are MIT-licensed ([LICENSE](LICENSE)). Adapted upstream material also carries Apache-2.0 obligations ([LICENSE-APACHE](LICENSE-APACHE), [NOTICE](NOTICE)). The Rust crate declares `MIT AND Apache-2.0` to reflect both sets of obligations.
