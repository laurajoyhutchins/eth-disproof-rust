# Finite machine and input normalization

Source-derived native register/stack operations: CNF reading, literal
cleanup, clauses, tautology filtering and normalization. The exported
Rust modules still live at `lean_eth_reference::native_*`, not below
a new public `machine::` path. These source files moved without
changing their program logic.

See `../lib.rs` for canonical module declarations. Do not replace
original Lean machine semantics with a high-level SAT shortcut.
