# H coefficient cache iteration: executable finite instructions (v0.11.0)

Pinned Lean source: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`.

## Exact machine boundaries

`src/native_cache_iteration.rs` ports the following finite control tables:

- `ParserProgram.frameProgram` as used twice by `RowSelectionProgram.parsePair`;
- `SubexpPostfixControl.literalService` 17 labels with entry 7, lifted into `RowSelectionProgram.Entries.emitPair`;
- `LayoutScalarEmitter.emitPair` and `finishList`, including copies, escaped framing, and reversal;
- `LayoutProgramScalar.cacheRow` with actual `cacheCell` arithmetic and preservation;
- `LayoutProgramScalar.cachePass`, clearing the row carry;
- `LayoutProgramScalar.cacheProgram`, a unary-counted loop over paid passes;
- `LayoutProgramScalar.buildProgram`, composing the source-defined all-one initialization with the cache iteration.

The compiled Rust machine consumes unary `A` and `R` on stacks 17 and 18 of an 8×19 machine and leaves the physical framed H-coefficient row on stack 15. No coefficient values are injected as inputs. The Rust test's independent recurrence oracle uses `next = 2 * previous + old`, not a source machine step implementation. This is *not* an imported-source Lean/Rust differential.

## Local acceptance

Nine new tests cover arbitrary little-endian words and framed pairs, exact emitter instruction count, the literal 17-label writer, parser end sentinel behavior, preservation and cleanup, pass/iteration/build over multiple heights and lengths, static command sizes, and fail-closed step limits.

The original v0.10.0 suite had 71 tests; the v0.11.0 suite contains 80 tests. Verified locally with Rust 1.99.1, offline Cargo tests, Cargo format check, and strict Clippy.

## Remaining boundary

`LayoutProgramScalar.hFlatProgram` needs the actual `LayoutBinomialProgram.finalFlatten` fixed-width writer. Until that is ported and composed, `LayoutProgram.IntegerCache.program`, the 16×768 `LeafHeadSetupProgramBoot.initializeCache`, and full `SignatureHeadLoader.bootstrapProgram` remain unimplemented. The TM2 primitive refinement and worst-case time/visited-space proofs are entirely separate.
