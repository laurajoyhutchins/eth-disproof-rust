# ETH: exact counting, from Lean to Rust

Can we execute the actual counting machine defined in [OpenAI's Lean ETH construction](https://github.com/openai/math/blob/main/lean/docs/378.md), and account for all of its work?

That is the purpose of this repository. We preserve source identities, compile what is supported, refuse what is not, and compare the result with independent Lean execution. Mathematical improvements are judged by the *whole counting cost*, not a faster isolated kernel.

**Current boundary:** the source-defined frontend and selected machine fragments run. A complete general nonterminal #SAT count and its primitive-machine complexity bound are not yet established on `main`.

## Run something real

The Rust toolchain is pinned to **1.99.1**. From the repository root:

```sh
cargo test --locked --offline --all-targets

# Execute the source-defined frontend (not a #SAT counter).
printf 'p cnf 3 3\n1 0\n1 2 0\n-2 3 0\n' | \
  cargo run --quiet --locked --offline -p lean-eth-reference --bin eth-frontend
```

That frontend runs `Native.frontendCommand` as a physical register-and-stack machine and reports instruction and occupied-stack-bit counts. It does not report the number of satisfying assignments.

To check a small answer with the **separate exponential oracle**:

```sh
printf 'p cnf 3 2\n1 2 0\n1 3 0\n' | \
  cargo run --quiet --locked --offline -p lean-eth-reference --bin lean-eth-reference
```

The answer is **5**. The oracle never stands in for the proposed algorithm.

For executable boundaries, see [the evidence](rust/lean_eth_reference/docs/evidence.md), [missing source stages](rust/lean_eth_reference/docs/remaining-lean-port.md) and the [frontend interface](rust/lean_eth_reference/docs/m2-runnable-frontend.md).

## Read the mathematics

- [The 2-adic recursion](research/two-adic-recursion.md): packets, weighted modes, group contraction and the Lean theorem still needed.
- [Spectral group actions](research/spectral-group-actions.md): pair swaps, Krawtchouk structure and what compression must preserve.
- [The cost of the complete algorithm](rust/lean_eth_reference/docs/worst-case-and-polynomial-overhead.md): the enormous parameter regime, precision, packet work, interpolation and leaf sizes.
- [Lean-to-Rust correspondence](research/lean-rust-acceptance.md): why a compiler-IR backend alone cannot execute a noncomputable source declaration.
- [Research record](research/README.md) and [literature](research/literature.md).

## Documentation

The [MkDocs site source](docs/index.md) presents the same Markdown with navigation, search and rendered equations. There is no second copy of the research notes.

```sh
python3 -m pip install -r docs/requirements.txt
python3 -m mkdocs serve
# Check the generated site:
python3 -m mkdocs build --strict
```

The documentation workflow builds a static-site artifact. A public GitHub Pages URL is not implied by that build.

## Source and provenance

The [manifest](rust/lean_eth_reference/reference/source-manifest.json) pins `openai/math@4eaee87548250b2682affda7d05d947c05554bae`. The canonical Cargo workspace lives at the repository root; the implementation crate is `rust/lean_eth_reference`. [Source and tests](rust/lean_eth_reference/README.md), [contributing rules](CONTRIBUTING.md), and [the historical port record](rust/lean_eth_reference/docs/reading-the-history.md) explain the rest.

Earlier Python/Cython Sudoku experiments remain on the [historical research branch](https://github.com/laurajoyhutchins/eth-disproof-rust/tree/python/sudoku-research). They are not the active Rust counter.

This is independent research, not an official OpenAI release. Original work is [MIT](LICENSE); upstream adaptations and notices are documented in [Apache-2.0](LICENSE-APACHE) and [NOTICE](NOTICE).
