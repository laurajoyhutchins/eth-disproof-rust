# Source-derived `FnBody.del`: bounded physical execution

Issue [#344](https://github.com/laurajoyhutchins/eth-disproof-rust/issues/344).
This study extends the physical `lean_del_object` primitive established in
[PR #351](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/351)
to **actual Reader-generated Rust** from unchanged Lean source. It does
not claim general Lean IR-to-Rust correctness or ETH algorithm execution.

## 1. Original source to final compiler IR

Lean 4.34.1 runs `reset`/`reuse` insertion and expansion before final
`Lean.IR.Decl`. The Reader therefore need not duplicate those passes.

`examples/RuntimeHeapDelKernels.lean` contains six ordinary source
functions. Four simpler reconstructions yield **zero** final-IR `del`
instructions. Both `rebuildOrDiscardByPayload` and
`rebuildOrExtractByPayload` yield **one real `FnBody.del` and two joins**
each. This is verified by `RuntimeHeapDelIRProbe.lean` using the pinned
`Lean.Compiler.compile`, `Lean.IR.findDecl`, and Lean's own
`Lean.IR.declToString`. CI requires those exact instruction counts.
Complete final IR and its hashes are retained as native artifacts.

The child-dependent predicate keeps the child projection live before
deciding whether to rebuild; without that dependency, Lean's optimizer
can avoid the shell-deletion path entirely.

## 2. Ownership refinement required by the source

In the source-unique `RuntimeHeap.Box.mk` branch the compiler projects
field 1 (the old stamp) and emits `dec` on that projection while the
parent shell remains live. This is a transfer of the **parent slot's
existing owned credit**. It is not an `inc` and cannot be justified by
Rust `Rc` aliases.

The Reader initially refused this exact path:

```text
source object x_16: release of 1 source references exceeds 0 known owned credits in source dec
```

The refinement in `backend/src/reader/lifetime.rs` admits this
transfer only with source evidence for the `Box.mk` identity and
two-field layout, a matching `isShared(parent) == false` path, one
parent credit, and one projected old-stamp view. A field-indexed
`spent_fields` ledger follows owned join transfers. Attempts to reuse
a spent projection, read its slot, or ordinarily release a still-spent
parent are refused. `set` replaces the spent field; shell-only `del`
does not release that same stamp twice.

In the C-backed execution adapter, additional physical guards require
the exact parent tag/arity, exclusive RC, field pointer identity,
and unique projected stamp view before calling the original
`lean_dec` on that old stamp. `source_del` calls the real
`lean_del_object` on a unique shell, transferring the existing field-0
child credit without `lean_inc`. An erased reset token is represented
as an unreadable scalar and cannot become a shell deletion of the shared
parent.

## 3. Evidence at exact head

The unchanged Reader closure for
`RuntimeHeapDel.rebuildOrExtractByPayload` emits a real
`source_del()`. CI typechecks and links the exact generated code
against the pinned Lean 4.34.1 C-backed runtime, with host code limited
to argument and return ABI conversion.

The independent oracle compiles the original Lean source to C,
constructs distinct source-owned parent allocations, and compares
returned child identity, Pair fields, physical reference counts, and
exclusivity after execution on unique and shared paths.

| Evidence | Result |
| --- | --- |
| Source-to-final-IR del witness | 1 `del` and 2 joins in each positive candidate |
| Reader-generated `source_del()` | Emitted and linked into the physical C runtime |
| Tagged old-stamp differential | 360/360 cases passed |
| Heap-allocated old-stamp differential | 360/360 cases passed, including real RC decrements |
| Total independently compared cases | **720/720 passed** |

[Exact-head native workflow](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44107560169)
passed at commit
[`8ace98a1`](https://github.com/laurajoyhutchins/eth-disproof-rust/commit/8ace98a12e2769061aa81409dcc7e35ea8d9b312).
The same head's Rust CI and source-bound review passed. Generated
sources, original compiled C, final IR, output traces and hashes are
retained in the workflow artifact.

## 4. Limits and unresolved obligations

The result is a **finite physical final-state correspondence** for an
explicitly admitted Box/Pair layout and the precise source declaration,
not a universal operational simulation. The tests do not establish
identity of every internal event trace or peak memory usage.

- The physical adapter admits one heap Pair child in field 0; it is not
  a general multi-child destructor or reference-graph implementation.
- Physical Nat comparison in the executed root remains limited to
  tagged Nat operands, although the *old stamp field* is tested with
  genuine heap-allocated Nat values.
- Arbitrary constructor layouts, shared child allocation graphs,
  persistent objects, cyclic references, and general join/field
  ownership are not proven by this witness.
- The original OpenAI ETH counting program and any time/space/precision
  bounds (G2) are completely independent.

For the underlying credit argument, see the
[technical notebook's shell-deletion study](https://github.com/laurajoyhutchins/technical-notebook/blob/main/content/studies/shell-deletion-and-credits.md).
