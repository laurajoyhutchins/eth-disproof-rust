# Experiment: Lean instruction tables compiled to Rust

This experimental branch lowers serialized, pinned finite BitProgram instruction tables to direct Rust control flow. It does not implement the full ETH native counter or establish theorem resource bounds.

## Reproduce

With Rust 1.99.1, from rust/lean_eth_reference:

    cargo test --locked --offline --test lean_table_codegen
    cargo test --locked --offline --bin lean-table-codegen
    cargo run --locked --offline --bin lean-table-codegen -- --fixture tools/fixtures/tiny.table /tmp/compiled_fixture.rs

Cargo build.rs regenerates the synthetic fixture into OUT_DIR, and the integration test compiles the resulting Rust code. It independently constructs the same 16-label machine using Program<4,3> and compares results, source-instruction counts, peak stack bits and complete machine state, including partially executed configurations under resource refusal.

The fixture covers all 12 source instruction variants. It is explicitly synthetic; no Lean-source attestation is claimed.

## Authentic query mode

    cargo run --locked --offline --bin lean-table-codegen -- /path/to/attested-query.table /tmp/query_generated.rs

Default mode requires the exact query table protocol used by the adjacent Lean exporter and Rust importer: source SHA, Git blob, 40 registers, 896 stacks, entry, 330/323 I/O ports and ordered complete labels. The generator accepts only well-typed numeric operands. The generated Rust executes physical operations directly; it does not call a SAT oracle, a table interpreter or untrusted embedded Rust.

This is deliberately a small-program experiment, with an 8 MB input limit and 8,192-label generator limit. Larger programs require a measured chunked code-generation strategy and compiler-resource budget.

## Evidence boundary

Passing the generated fixture tests would demonstrate local Rust interpreter-to-Rust compilation parity on the tested finite cases. It does not demonstrate real original-Lean export, imported-Lean differential equivalence, extraction of the noncomputable full query table, end-to-end native SAT counting or an asymptotic complexity result.

The next accepted increment should be one genuine small table exported from pinned Lean 4.34.1 and Mathlib, checked against both the imported Lean execution trace and the generated Rust machine trace. Preserve the native readable Rust port separately.
