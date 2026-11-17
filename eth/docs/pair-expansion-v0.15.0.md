# Pair expansion: executable Rust v0.15.0

**Lean source:** [`openai/math@4eaee87548250b2682affda7d05d947c05554bae`](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT)

Implementations:

- `SqrtLog/HighIncidenceProgramRestriction.lean`: `Restriction.command` and `Restriction.program` (reused from the existing `native_query_prefix` module rather than cloned)
- `SqrtLogSpace/PairNativeSetup.lean`: `fillCommand true`, `fillCommand false`, `expandCommand`, and `expandCaller`
- `SubexpSetupStorage.lean`: actual source `prepare` and `finish` operations, preserving copy, port clearing, and work-register reset

## Finite-machine contracts

The 4-register, 4-stack restriction program processes the mask in top-first order. On each mask bit it consumes from stack 1 when the bit is true and stack 2 when the bit is false; a missing selected bit is read as false by the underlying `BitProgram.pop`, as in Lean. Its output stack accumulates the reverse of the consumed sequence. It runs in exactly `5*n + 3` instructions for `n` mask bits (including halt), independent of the bit values.

`fillCommand(true)` copies stack 338 and reversed E on stack 834 into scratch 325 and 327; the restriction program reads those ports and writes scratch 328, which is preserving-copied to stack 858. `fillCommand(false)` does the same from reversed U on stack 835 into output 857. Fixed/high slots are padded with false because the high source (scratch 326) is intentionally empty.

Both isolated calls clear the temporary 329, clear all of 325–329 on return, reset work registers 0–8 and leave the original inputs and unrelated stacks untouched. The two outputs overwrite earlier output data; they do *not* append stale bits. The composed 16×896 expansion is compiled once and lifted into registers 0–15 of a 40×896 caller with identity stack mapping, exactly as the source's `liftCommand expandCommand 338 857 callerRegister id`.

## Validation

Six new tests cover:

1. Exhaustive masks of width 0–9 with nonzero high- and low-stream values, exact `5*n+3` source instruction count, and output suffix preservation.
2. E and U isolated fill stages across empty, full, and mixed masks through width 16, exact paid instruction counts, dirty scratch and output replacement, protected-frame preservation.
3. Full `expandCaller` output meaning and all 896 stack frame positions plus all 40 register positions.
4. Composite expansion versus two independently executed compiled stage programs.
5. `setupCaller`, installation of residual inputs, then expansion, retaining metadata and free-coordinate count.
6. Bounded step-limit refusal with no successful terminal state.

The full standalone crate suite passed **107 tests** in debug and release. `cargo fmt --check` and `cargo clippy --offline --all-targets -- -D warnings` also passed under Rust 1.99.1.

## Limits

These tests establish machine behavior against source-derived output specifications, *not* a differential execution of imported Lean Mathlib code. Well-formed inputs require the high mask to have `n` bits and each residual word to have exactly as many bits as the mask has false positions. A malformed stream is not converted into a success claim for the whole query; `BitProgram.pop` returns a false bit for missing input. The signed difference-pair traversal, bucket aggregation, query-node finish and full ETH proof obligations are still unported.
