# v0.19.0: executable predecessor key comparison and freshness gate

Pinned upstream source: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`.

The following source-defined finite bit machines now execute in Rust:

- `ExecClauseCost.bitEqualityProgram` (exact ten-instruction destructive equality table, result register 4).
- `AttainedSignatureProgram.KeyEquality.command` (preserving copies of both complete keys, destructive comparison of copies, and scratch cleanup), and `KeyEquality.program`.
- `AttainedSignatureProgram.Rescan.equalityCall` on source machine `16 × 24`, and its precise lift into the shared `40 × 896` tuple ABI using `SignatureTupleNative.rescanStacks`.
- `Rescan.storeFresh`, `updateFresh`, and the composed physical duplicate-key gate. Once false, the freshness latch remains false during subsequent predecessor checks.
- `Rescan.setup` and `cleanup`, including physical countdown copy, latch initialization, predecessor clear, and transfer of the final fixed-width zero word.

No host-language bitstring equality appears in the implementation. The Rust equality operator appears only in **independent tests**. Tests cover all word pairs through four bits, repeated predecessor freshness monotonicity, long word prefixes and bit mismatches, actual stack preservation, two-step lift identity, failure under instruction limits, and source step-cost formulas for setup and cleanup.

**Scope limitation:** `AttainedSignatureProgram.program` (full raw-row signature-key production) and the `CounterForPrograms.forCmd` predecessor scan are still required to form the complete `Rescan.candidateProgram`; `SignatureTupleComplete.command` also needs real loader and visitor integration. The tests use externally supplied *key input words* to exercise the actual equality gate; they do not substitute a fake key producer into the full machine. Source Lean 4.34.1 imported differential tests have **not** been run.

Standalone local verification: Rust 1.99.1, 145 tests in both debug and release, `cargo fmt --check`, and `cargo clippy --offline --all-targets -- -D warnings`.
