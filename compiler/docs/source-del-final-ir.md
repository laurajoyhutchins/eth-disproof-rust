# Source-derived `FnBody.del`: final-IR discovery

Issue [#344](https://github.com/laurajoyhutchins/eth-disproof-rust/issues/344).
The runtime milestone in #351 proved a bounded **physical primitive** for
`lean_del_object`, not execution of source-derived compiler IR.

## Why begin with the compiler's final IR?

Lean 4.34.1 expands LCNF `reset`/`reuse` before producing the final
`Lean.IR.Decl`. In `LCNF/ExpandResetReuse.lean`, `processResetCont`
replaces the matching decrement of a reset token with `.del`. The Rust
Reader already handles `FnBody.del` by emitting `source_del()`. Adding
lowering for *unexpanded* `IR.Expr.reset` and `IR.Expr.reuse` would be
premature without a genuine final-IR example demonstrating either one.

## Source and evidence

- `examples/RuntimeHeapDelKernels.lean`: six ordinary Lean expressions
  using `RuntimeHeap.Box` and `Pair`. The first four are negative candidates. The two **ByPayload** definitions
  produce real final-IR deletion instructions, not yet executed Rust.
- `examples/RuntimeHeapDelIRProbe.lean`: calls the same pinned
  `Lean.Compiler.compile` entrypoint used by the Reader, obtains each
  final `Lean.IR.Decl` using `Lean.IR.findDecl`, and traverses each
  `FnBody` (including branch alternatives and join bodies) to count
  actual `del` and `jdecl` instructions.
- `runtime/lean-c/check-generated-heap.sh`: runs this exact-compiler
  probe before the unchanged generated-heap differential execution.
- `artifacts/source-del-final-ir.txt`: full, source-derived final compiler declarations as formatted by pinned `Lean.IR.declToString`, including the actual join and branch structure.
- `artifacts/source-del-final-ir.tsv`: row per declaration, with
  `final_ir_del` and `final_ir_jdecl` counts.
- `artifacts/source-del-final-ir-status.txt`: explicitly distinguishes
  `NO_SOURCE_DEL_CANDIDATE` from `SOURCE_DEL_FOUND_NOT_EXECUTED`.
  Both retain `emitted_ir_source_del=NOT_YET_ESTABLISHED`.

The native CI evidence bundle retains both generated files and their
checksums are included in the runtime receipt.

## Acceptance still required

The probe cannot establish source-to-Rust execution. After a final-IR
candidate has at least one actual `del`, freeze its exact source and
final compiler declaration, generate its complete unchanged Reader
closure, and verify that the generated `source_del()` call executes in
the original pinned Lean C runtime process. Preserve its ownership
flags and join-point parameter transfers, compare pointer identities,
physical RC and destructor events against independently compiled Lean
C on unique/shared cases, and reject any unsupported shape.

In particular, the #351 `source_del` implementation admits only one
live projected `RuntimeHeap.Box.mk` child with a tagged second field.
A generated `del` on an arbitrary reset token is **not automatically
covered**. Inspect the exact object's tag, fields, projection and
ownership state before broadening the runtime. A shared parent,
unprojected child, or unmatched transfer must fail closed.

Only after those checks can a separate exact-head receipt say
`emitted_ir_source_del=PASS`. General G1 and the original ETH G2
counting/resource obligations are independent and still open.

## Pinned positive witness and Reader boundary

On pinned Lean 4.34.1, each of `rebuildOrDiscardByPayload` and
`rebuildOrExtractByPayload` has exactly one real final-IR `FnBody.del`
and two join points. The probe now checks these counts fail-closed.

The canonical Reader emission probe in `RuntimeHeapDelEmitFixture.lean`
requests the unchanged dependency closure of `rebuildOrExtractByPayload`.
The pinned exact-head runtime run at commit
`fa63f6494e3ab31304058cd5e24303767f1e03c0` passed, but the
Reader correctly refused with:

```text
source object x_16: release of 1 source references exceeds 0 known owned credits in source dec
```

The original final Lean IR decrements a `proj[1]` stamp from a uniquely
owned `RuntimeHeap.Box.mk` before passing the parent through reset/reuse
joins. The Reader currently treats that projection as only borrowed.
The next implementation must recognize precisely the guarded physical
slot-credit transition and corresponding join ownership. Simply
relaxing the static credit underflow would be unsound.

The emission gate distinguishes expected Reader refusal from incidental
Lean failures and preserves the refusal text as CI evidence. The source
to final IR witness is established; emitted Rust execution is not.
