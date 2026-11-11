# M2 terminal count producers: executable but not yet classified

This increment ports two **constructive source commands**, not the entire outer terminal dispatcher, at original `openai/math@4eaee87548250b2682affda7d05d947c05554bae`.

## Pinned source-to-Rust mapping

- `SqrtLogSpace/NativeProgram.lean`, blob `864ccb2308317df3cc7d218c8b45d43d32558ffd`: `Native.powerSeed`, `powerBody`, `powerCommand`, `powerProgram`.
- `SqrtLogSpace/NativeTerminal.lean`, blob `ebcd509ab86db459822f3ee211e7e70064291c2f`: `NativeTerminal.power` and `NativeTerminal.zero`.

The source `Native.powerCommand` takes canonical unary `true^n ++ [false]` on stack 0, and physically produces `false^n ++ [true]` on stack 1, the little-endian full count word for `2^n`. It uses a two-register, two-stack seed and a real conditional finite loop, not Rust exponentiation, `u64`, or host enumeration. The compiled machine runs in **exactly `4n + 5` BitProgram instructions**.

`NativeTerminal.power` preserves/copies the unary ambient word on stack 258 to stack 268, with temporary stack 269, then executes the lifted two-stack program on `[268, 263]` with registers `[72, 73]`. When stacks 263, 268 and 269 start empty, the program preserves 258, produces the full count word at 263, cleans its work/scratch, and runs in **exactly `11n + 18` instructions including the compiled halt**.

`NativeTerminal.zero` executes two real instruction atoms and writes `[false]` to stack 263, provided that stack was initially empty. Its test wrapper adds one halt, for exactly three instructions.

## Explicitly outside this increment

`NativeTerminal.classifier` uses `SqrtLog.LeafProgram.Trivial.program`, `SubexpEmptyClauseProgram.program` and a real `ExecCNFMembership` stack-scanning comparator. That source classifier is **not** yet ported. Consequently, neither the Rust tests nor the production API autonomously decide whether a CNF has an empty clause, is empty, or is nonterminal. The caller must establish source terminal branch premises independently. No `SAT.count`, semantic `LeafCounter`, or host truth table is injected. `NativeTerminal.command` and `NativeLeafDispatch.command` remain unresolved.

The local source snapshot tests both native count producers up to 128 variables and 256 variables as a non-word-sized count, asserts exact instruction costs, preserved ambient/protected ABI state, and fail-closed step/stack capacity. The full local standalone crate was checked in debug and release with **129 passing tests each**, plus `cargo fmt --check` and strict Clippy on Rust 1.99.1.

This standalone crate does not include the repository's `remaining.rs`, and the exact GitHub stacked-head must still be verified before integration. Imported Lean source traces and TM2 resource results are separate obligations.

**Next implementation dependency:** physically port the original encoded-record classifier; only then compose `NativeTerminal.command`, `NativeTerminal.readyCommand`, and `NativeLeafDispatch.command` with the real nonterminal callback.
