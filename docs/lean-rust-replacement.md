# Lean-to-Rust compiler architecture

Status: **backend-first migration, not a Lean language rewrite**. This decision
supersedes the runtime-first retirement order recorded after the initial
[stage-zero lungo experiment](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/331).

## Goal and authority

Compile executable **original Lean definitions** into Rust while retaining
Lean's parser, elaborator, compiler optimizations, and trusted source language.
The official Lean 4.34.1 compiler and its final ownership-explicit
`Lean.IR.Decl` are authoritative:

```text
unmodified Lean source and proofs
         |
official Lean frontend / compiler / LCNF
         |
canonical ownership-explicit Lean.IR.Decl
         |
single Rust code generator
         |                  [initially] pinned Lean C runtime
generated Rust  ------------------------------------------> executable
         |                  [only after semantic gate] Rust runtime
         +------------------------------------------------> executable
                               |
                     independent Lean/C reference
```

LCNF is useful for analysis and diagnostics. It must not become a second
production lowering path. Lean's ownership, borrow, reuse, call, and
reference-counting decisions are inputs to the backend, not decisions to
redo in another Rust optimizer. A typed serialization layer can transport the
**same** compiler IR without creating a second compiler semantics.

**The initial implementation order is fixed:**

1. **Rust backend first.** Generate Rust implementing the actual source IR,
   and link to the official Lean runtime through a tiny version-pinned C ABI
   shim. Preserve emitted IR instructions, observable aliasing, allocation,
   release, direct/indirect calls, joins, and error paths. Rust code may
   contain `unsafe` within a precisely scoped runtime boundary.
2. **Rust runtime second.** Replace the reference runtime behind the **same
   generated-code contract**. Prove/test its instruction-level and
   physical-ownership correspondence separately. Do not accept Rust
   `Rc::strong_count` or automatic Drop behavior as substitutes for Lean
   `inc`/`dec`/`del`.
3. **Independent kernel separately.** A Rust Lean proof checker is an
   interesting independent assurance project, not part of the compiler's
   release-critical path. The official Lean kernel checks source proofs.

This ordering isolates whether a mismatch comes from lowering or from a new
runtime. Neither a complete Rust kernel nor a self-hosting Lean distribution
is necessary to demonstrate a useful Lean-to-Rust compiler.

## First release: backend on Lean's existing runtime

The detailed code-generation and ABI contract lives in
[backend-runtime-boundary](../rust/native_lean_backend/docs/backend-runtime-boundary.md).

The native `rust/native_lean_backend` Reader is the **one existing in-process
code generator**. Its current standalone GMP/`Rc` runtime is retained for
regression until the new runtime target is admitted, not deleted prematurely.

An implementation must:

- Derive calls, operations, types and ownership flags from actual
  `Lean.IR.Decl`, including imported IR, with no Lean source reparser.
- Use a version-pinned C shim against official `lean.h` because some Lean
  runtime operations are `static inline`, not exported ABI symbols.
- Distinguish borrowed handles from owned values. Translate explicit
  `inc`, `dec`, `del`, moves, `reset`, `reuse`, and unique updates in
  source order. Rust destructors cannot silently introduce an extra source
  reference-count event.
- Preserve allocation identity where the IR can observe it through
  `isShared`, mutation, reuse, or an object trace. `isShared` is not just
  a performance hint.
- Refuse unsupported instructions, externs, incomplete dependency closures
  and noncomputable declarations **before publishing an executable**.
- Run identical unmodified-source fixtures through Lean/C and the generated
  Rust executable with official runtime. Require value/state, heap/RC event,
  and refusal agreement on admitted cases.

The existing Rust Reader's ownership/lifetime analysis remains a
**conservative admission safeguard**, not a second producer of Lean's
ownership schedule. It should become unnecessary only after the replacement
translation is verified for the supported instruction grammar.

## Four release gates

| Gate | Required evidence |
| --- | --- |
| Execution | Original Lean compiler IR lowers through one Rust backend, linked to the reference Lean runtime, and the executable runs on real imported programs |
| Semantics | Corresponding control-flow, calls, objects, branch choices, borrow/transfer, `isShared`, allocation identity and release behavior under the admitted trace contract |
| Trust | Exact Lean/runtime/header/source identities, independent Lean/C oracle, explicit unsupported refusals, source-bound artifacts and a separately stated proof boundary |
| Performance | Total compile time, binary runtime, peak allocations, live bytes, peak RSS and generated Rust size against Lean C for identical inputs |

First establish the baseline with **the same Lean runtime**. Optimize
generated Rust only if the optimized version remains observationally
equivalent for all admitted runtime observations; stronger physical trace
identity is required for ownership acceptance fixtures until a validated
trace abstraction justifies otherwise. No universal semantic-refinement
theorem is claimed by differential tests alone.

The entry gate is a small, **source-derived object program** with an actual
`inc`/`dec`, borrowed projection, `isShared`, and a possible release,
not another pure UInt64 arithmetic fixture. Next expand to source `reset`
and `reuse`, closures, joins, and imported multi-module programs.

## Runtime migration: only after the backend gate

Define a single generated-Rust runtime API and two independently selectable
implementations:

| Provider | Meaning | Evidence |
| --- | --- | --- |
| `lean-c` | Official pinned Lean runtime reached via a C header shim | Source-C/Rust backend translation baseline |
| `rust-native` | Faithful Rust replacement for the **same** operations | Value, ownership, lifetime and performance correspondence against `lean-c` |

No silent fallback from `rust-native` to `lean-c` on a missing primitive.
Experimental Lungo Bridge IR may be reused as an **adapter** if it preserves
this exact source IR and one backend contract. It cannot certify an
alternative source algorithm or substitute its own runtime in the initial
backend acceptance gate.

The [initial lungo compatibility fixture](https://github.com/laurajoyhutchins/eth-disproof-rust/tree/main/tools/lean-rust-bootstrap)
is retained as useful evidence: 1,024 differential comparisons passed for
`Lean.Compiler.LCNF.Simp.Config`. The broader `Lean.Compiler.IR.Basic`
attempt refused on four missing Rust-native runtime externs. That is a
**later runtime-coverage issue**, not a blocker to the backend-first
`lean-c` target.

## Retirement order

| Current code | Action |
| --- | --- |
| `src/reader/*`, `NativeRust.lean` | Keep as canonical bounded emitter while adding `lean-c` as a runtime target. Refactor decoding only when an equivalent typed adapter is accepted |
| `native/abi.c` | Keep the pinned Lean header boundary; make ownership/execution helpers distinct from borrowed IR decoding, then consolidate after parity |
| `src/runtime/immutable_value.rs` | Keep for old-runtime regression; remove only after the Rust-native replacement passes the complete gate |
| `tools/lean-rust-bootstrap` | Keep as a separate Lungo compatibility experiment, not another production backend |
| Independent proof checker | Neither required nor developed in this repository as part of compiler migration |

Do not delete successful source/C or generated Rust fixtures to make the
migration appear complete. Retire the old code only after exact-head
equivalence, original external-project coverage, and physical ownership
regressions pass.

## ETH is a distinct acceptance target

G1 proves the **general executable compiler and runtime** contract. G2 must
independently establish that the original QueryStream/leaf/DFS/outer
algorithm has a complete executable source-derived representation and its
claimed physical and resource semantics. In particular,
`noncomputable` declarations do not become executable because a Rust
backend exists; such cases must retain explicit refusal until source
equivalence is established.

See [Lean-to-Rust correspondence](../research/lean-rust-acceptance.md).
