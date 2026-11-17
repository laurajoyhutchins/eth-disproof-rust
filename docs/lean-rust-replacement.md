# Optional Rust-hosted Lean compiler experiment

The [backend-first architecture](rust/native_lean_backend/docs/backend-first-architecture.md)
does **not** require porting Lean's parser, elaborator, compiler or proof
kernel to Rust. Lean remains the language implementation. The executable
backend consumes Lean's existing ownership-explicit compiler IR.

[PR #331](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/331)
tests a different question: can original Lean compiler modules themselves
be compiled to Rust using pinned `machinefabric/lungo-rs`? Its work under
`tools/lean-rust-bootstrap` is isolated research, **not** the canonical
native IR backend, a required compiler bootstrap or an ETH counting
implementation.

## Observed stage-zero result

The draft reports original `Lean.Compiler.LCNF.Simp.Config` source
compiled through pinned Lungo with 1,024 independent official Lean/Rust
`UInt8` comparisons and a kernel-checked source theorem, at
[exact-head CI run 43984580084](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43984580084).
This is evidence for that source subset, not self-hosting, full compiler
semantics, complete runtime support or a general Lean-to-Rust compiler.

An attempted imported `Lean.Compiler.IR.Basic` closure refuses
`LNG0401` on four exact runtime externs:

- `lean_expr_dbg_to_string` (`Lean.Expr.dbgToString`)
- `lean_expr_mk_data` (`Lean.Expr.mkData`)
- `lean_profileit` (`Lean.profileit`)
- `lean_manual_get_root` (manual root handling)

There are no accepted substitute implementations for these missing
externs. Retain the refusal until their actual Lean runtime semantics
are established.

## Scope of future experiments

Compiling a Lean compiler transformation, a first-generation hosted
compiler, and a second-generation rebuild are interesting *optional*
experiments. They do not advance the required runtime replacement order
by themselves. A second-generation binary matching its predecessor is
not a source semantics proof.

The corresponding production work belongs to the
[canonical native backend](rust/native_lean_backend/README.md):
first establish generated Rust against Lean C, then independently
validate Rust-native runtime operations. Do not retire the current
reader, primitive registries, publication path or tests merely
because a bootstrap experiment compiles.

The noncomputable original ETH QueryStream construction also remains
separate. Neither the bootstrap experiment nor ordinary compiler IR
code generation makes an unavailable executable closure appear.
