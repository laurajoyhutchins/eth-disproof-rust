# Source-pinned ETH Lean machine port (Rust)

An incremental Rust implementation of selected finite programs from
`openai/math@4eaee87548250b2682affda7d05d947c05554bae`.

The executable crate lives in `rust/lean_eth_reference/`.
Only independently executable, testable program boundaries are called
implemented. Missing Lean machine stages must refuse explicitly.

To check a milestone: `cd rust/lean_eth_reference && cargo test --offline`.
This is neither a complete Lean port nor an ETH theorem or complexity proof.
