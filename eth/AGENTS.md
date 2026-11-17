# ETH implementation boundary

`eth/` owns the source-pinned finite machine and ETH counting research,
not the general Lean compiler.

- `src/bit_program/` and `src/native_*.rs`: executable register/stack
  machine fragments and stage implementations.
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

A later no-semantics-change refactor may group the flat `native_*`
modules into machine/query/counting. That extraction must preserve
original Lean declaration identities, determinism, and physical traces.
