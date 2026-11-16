# Lean-to-Rust replacement gates

Status: **stage-zero experiment; existing compiler retained**.

The [standalone fixture](../tools/lean-rust-bootstrap/README.md) evaluates
pinned `machinefabric/lungo-rs` on unmodified Lean compiler declarations.
It is a candidate replacement for the custom native backend, not an
alternative executable path for the ETH counting algorithm.

## What we intend to remove, and when

| Existing implementation | Required successor evidence |
| --- | --- |
| `native/abi.c`, `reader/decode.rs`, `reader/view.rs` | Typed Lean-side IR extractor handles imported/local closure |
| `reader/ownership.rs`, `borrow.rs`, `usage.rs` | Explicit Lean IR inc/dec/del, borrow, isShared and unique updates match Lean C traces |
| `runtime/immutable_value.rs` | One source-faithful Rust runtime matches values, allocation and lifetimes |
| Remaining custom Reader, primitive registries | Complete admitted constructor and primitive inventories, exact refusals |
| Repeated publication/receipt shells | One transactional build and complete imported-source manifest |

The old `rust/native_lean_backend` stays the trusted regression reference
for *its validated subset* until the replacement meets its gates. We do not
delete the tests with the implementation they currently protect.

## Stages

1. **Stage 0:** official Lean compiles original Lean compiler modules to
   executable Rust, with independent Lean C/Rust oracles and measured runtime.
2. **Stage 1:** a Rust-hosted compiler, generated predominantly from original
   Lean source, successfully builds an unchanged downstream Lean project.
3. **Stage 2:** the stage-one compiler produces a second generation. Verify
   reproducible behavior and semantics independently; matching generated
   artifacts alone is not a correctness proof.

The next real test after `Lean.Compiler.IR.Basic` is an actual compiler
transformation with nontrivial dependency closure, not another scalar fixture.

## Mathematical boundary

G1 (compiler semantic/physical correctness) and G2 (original ETH counting
algorithm and complexity) are independent obligations. A compiler can only
lower declarations with executable IR. Noncomputable mathematical definitions
cannot acquire an executable implementation through backend replacement
alone.
