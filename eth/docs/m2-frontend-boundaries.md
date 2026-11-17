# M2 literal native frontend boundaries

Pinned original: `openai/math@4eaee87548250b2682affda7d05d947c05554bae` (Lean 4.34.1). The original source is in `FrontendProgram.lean` (blob `f475610fae2eddf2fb197c2b98a5acb18b5d60dc`), `SqrtLogSpace/NativeProgram.lean` (blob `864ccb2308317df3cc7d218c8b45d43d32558ffd`) and `SqrtLogSpace/NativeFrontend.lean` (blob `bdf989fb6a58332fe298ad157357ca684f6e1a41`). All three pins are recorded in the source manifest.

## Real executable prefix

`native_frontend_header::initialize_program()` is the **source 19-label linked instruction table** `FrontendProgram.initializeProgram`. It splices the five-label `ParserProgram.natProgram` into `CounterPrograms.lengthProgram`, retaining the distinct source port and control maps; its parser halt becomes a `goto` into the counter. It consumes unary `true^n ++ [false]` from stack 0; leaves the trailing formula body on 0, clears work stack 1, produces little-endian binary `n` on 2, and empties counter scratch 3. There is no Rust-side integer parser or counting shortcut.

`native_frontend_header::header_command()` is the exact 80-register/1220-stack `Native.headerCommand`: preserve-copy the encoded input from 256 to 1218, then run the linked initializer on registers `[72,73,74]` and stacks `[1218,268,267,269]`. It preserves the original complete encoded input 256, produces raw unnormalized body 1218, and puts the binary variable count on 267.

## Real executable suffix

`native_frontend_tail::place_body_command()` is exact `Native.placeBodyCommand`: physically copy the already-normalized body from 1218 to 265 through scratch 1219, then clear 1218. It preserves existing destination bits: the machine produces `old(1218) ++ old(265)`, not a host-side assignment. The source step count is `9 * |old(1218)| + 8` or `+1` for a standalone halt.

`native_frontend_tail::frontend_tail_command()` composes source `placeBodyCommand; ambientCommand`. The existing source-defined `ambientCommand` preserves input 256 and constructs unary ambient `true^n ++ [false]` on 258. The resulting normalized body is on 265, temporary 1218 and 1219 are empty, binary count 267 and protected frames survive. For a normalized body of length `L`, canonical input header `n`, and original body length `M`, the compiled suffix takes exactly `(9L+8) + (7(n+1+M)+4n+2M+14) + 1` BitProgram steps.

## Missing link (not silently bypassed)

The original `Native.frontendCommand` is `headerCommand; normalizationCommand; placeBodyCommand; ambientCommand`. **`SubexpNormalizationProgram.program` remains unported**, so there is *no* complete source-equivalent frontend, not even for a trivially normalized formula. Prefix and suffix are exposed independently, and `remaining::outer::frontend()` still explicitly returns `NotImplemented`. No host-side normalization or semantic SAT oracle is substituted.

Both stages assume the same canonical encoding and empty caller-owned work ports that the Lean source proves. They are not arbitrary-bit-string validators.

## Local verification and exact-head gap

Restored pinned Rust **1.99.1** from the verified two-part archive and executed the v0.16.0 standalone crate, including the two new modules and six tests:

- `cargo test --offline --locked`: **123 passing tests** in debug.
- `cargo test --offline --locked --release`: **123 passing tests** in release.
- `cargo fmt --check`: passes.
- `cargo clippy --offline --locked --all-targets -- -D warnings`: passes.

The 19-label initializer was tested on unary dimensions `0..=96` with trailing payload bits, and the outer header on `n=0..=32` with multiple body lengths, binary integer results, original-input retention, complete protected frame, and capacity refusal. The placement test covers body lengths `0..=18` including nonempty destination, exact step count and untouched control state. The suffix test covers `n=0..=12`, original body lengths `0..=9`, staged vs physical outputs, frame state and exact source steps. Both new source files and both test files match the locally compiled versions by exact Git blob SHA.

**Not executed**: an exact-head full combined GitHub checkout (`remaining.rs` and concurrent M1/M2 modules are not in the standalone archive), a live Lean imported-source differential test, or the source TM2 machine refinement. Those remain integration/proof obligations, not successful checks. The GitHub checkpoint workflow has previously failed before allocating a runner and should not be treated as a Rust compiler failure.
