# Source-defined attained-signature frame protocol (v0.17.0)

Pinned Lean reference: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`, `SqrtLogSpace/SignatureTupleProgram.lean` and `SqrtLogSpace/SignatureTupleNative.lean`.

The new `native_signature_frames.rs` implements the **physical stack instructions** for `pushFrameProgram`, `suspendCommand`, `resumeCommand`, `pushWordCommand`, `popWordCommand`, `saveCursorCommand`, `restoreCursorCommand`, `recordRepresentativeCommand`, `dropRepresentativeCommand`, `descendLevelCommand`, `ascendLevelCommand`, `testParentCommand`, `leaveHeadCommand`, and `initializeFreshCommand`.

- Twelve tuple stacks are 836 through 847; controller flags are registers 36 through 39. Suspended frames are stored on 836 and representative frames on 837.
- The eight-label `pushFrameProgram` pushes a real delimiter for empty words and costs exactly `5*n+5` executed instructions. Its frame encoding is `Encoding.frame (word.reverse)`. A source `ParserProgram.frameProgram` call decodes the same frame.
- `saveCursorCommand` pushes candidate stack 838, then remaining stack 843, onto frame stack 836. `restoreCursorCommand` reverses that precise order. Tests validate nested existing frame suffixes and both empty and nonempty words.
- `recordRepresentativeCommand` copies the candidate to scratch 840, pushes an encoded frame to 837, and clears 840. `dropRepresentativeCommand` consumes one frame and leaves 840 empty.
- `descendLevelCommand`/`ascendLevelCommand` physically update unary stacks 842 and 845. The parent guard checks frame *presence*, not whether the top bit is true.
- `leaveHeadCommand` clears precisely [838,839,840,841,843,844,846,847], keeping controller cursor, frame and address ports.
- All operations compile through `BitProgram` finite instructions with explicit `RunLimits`. No host-side stack mutation is part of the generated program.

## Verification

11 focused tests, including exhaustive short masks, empty delimiters, nested frame restoration, representative preservation, level round trips, dirty-latch reset, protected-port preservation, and bounded-resource refusal. Standalone v0.17.0: 128 tests passed in debug and release, `cargo fmt --check` and `cargo clippy --all-targets -- -D warnings` passed using the offline Rust 1.99.1 toolchain.

## Explicit remaining boundary

This is **not** the complete `SignatureTupleComplete.command`. The physical loader (`SignatureTupleLoader.loadHead`), full `AttainedSignatureProgram.Rescan.candidateProgram` predicate, and `QueryVisitorProgram.visitor` must still be assembled with these primitives and tested with imported Lean traces. The complete GitHub branch, including concurrent changes, has not yet been run as a single local checkout.
