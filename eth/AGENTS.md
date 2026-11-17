# ETH implementation boundary

`eth/` owns the source-pinned finite machine and ETH counting research,
not the general Lean compiler.

- `src/bit_program/` and `src/machine/`: source-defined finite
  register/stack machine fragments and normalization.
- `src/query/`: original query, pair, node, cache and signature stages.
- `src/counting/`: terminal/high/leaf results and two-adic cost audits.
  The `#[path]` declarations in `src/lib.rs` preserve all existing
  `lean_eth_reference::native_*` module identities.
- `reference/`: pinned original source manifest and Lean comparison
  drivers. Do not edit source identities casually.
- `proofs/`: theorem-level correspondence and outstanding obligations.
- `tools/`: source graph extraction, source checks, independent comparisons
  and Python test harnesses.
- `src/bin/`: bounded diagnostics and source-derived executables.
- `src/bin/eth-compiler.rs` is temporarily the public G1 compiler CLI;
  its canonical emitter lives in `../compiler/`. Do not duplicate it.

Run root `cargo test --locked --offline --all-targets` and the
specific original-Lean parity workflows for the affected component.
Document every unsupported stage. A bounded brute-force oracle is
not the original ETH counting algorithm, and executable Rust does
not prove the manuscript's asymptotic resource bounds.

The machine/query/counting files have been relocated without changing
their Rust module identities. Do not silently turn this directory
split into a semantics change; preserve exact source bindings and
independent physical traces.
