# Physical ownership control trace

The canonical Lean-to-Rust compiler now records supported `FnBody.inc`,
`FnBody.dec` and `FnBody.del` instructions in a **logical source-reference
ledger**, independently of transient Rust `Rc` handles. The implementation is
derived from the earlier research draft PR #283, with the current pinned IR
reader, machine-readable refusals and single runtime preserved.

## Independent C reference

The exact Lean **4.34.1** C header and runtime are the reference:

- [RC increments, decrements and exclusivity](https://github.com/leanprover/lean4/blob/v4.34.1/src/include/lean/lean.h)
- [Actual ownership-dependent `lean_apply_1` implementation](https://github.com/leanprover/lean4/blob/v4.34.1/src/runtime/apply.cpp)
- [Lean C code emitter](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/Compiler/LCNF/EmitC.lean)

`native/abi.c::lr_source_rc_control_mask` executes real Lean runtime
objects, calls, conditional releases and a real partially applied closure,
once uniquely owned and once shared. The result must be exactly **214**.
It is checked by the native ABI probe at compiler startup.

| Bit | Checkpoint | C sharing result |
| --- | --- | --- |
| 0 | Fresh heap root | Exclusive |
| 1 | Direct call retained another reference | Shared |
| 2 | Branch did not release that reference | Shared |
| 3 | Other branch released it | Exclusive |
| 4 | New PAP closure captured the root | Shared |
| 5 | Unique PAP was applied and released its capture | Exclusive |
| 6 | Shared PAP holds a captured root | Shared |
| 7 | Applying one shared PAP reference leaves the other alive | Shared |
| 8 | Releasing the final PAP reference releases its captured root | Exclusive |

The Rust source-ledger test in `src/lib.rs::SOURCE_RC_TEST_SOURCE` uses
the actual canonical generated `__LeanValue` runtime, with the same
checkpoints. Both independent controls must produce bitmask **214**. A
shared closure's source reference must be consumed on application even if
the Rust `Rc` representation happens to have a different alias count.

## What the passing gate would establish

A passing result is **bounded single-threaded reference/exclusivity
control correspondence** for this sequence, in addition to the existing
same-source Lean/C/Rust returned-value checks.

It is **not** a full source-to-Rust heap simulation. In particular:

- The two programs exercise corresponding *operations*, not compiled
  identical Lean IR, and neither records general per-object allocation IDs.
- `Rc` is still the Rust memory-safety owner; the source ledger is only a
  checked model for the supported part of Lean's RC effects.
- Source `borrow`, external calls, arbitrary closure arities, all
  destructor cascades, sticky/frozen/multithreaded counts, mutation
  identity and complete interprocedural ownership contracts remain open.
- The source-owned `Array.getInternal` increments the element's logical
  count; `Array.getInternalBorrowed` returns a compiler-only alias without
  incrementing it. This is covered by the canonical runtime regression test.
- The existing source-CFG and cross-call refusal rules remain active.
  This control must not be used to promote G1/G2 or claim a theorem.
