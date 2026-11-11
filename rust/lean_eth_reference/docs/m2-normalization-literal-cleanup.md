# Milestone 2: executable normalization prerequisites and literal cleanup

Original source pinned at `openai/math@4eaee87548250b2682affda7d05d947c05554bae` (Lean 4.34.1). These are literal ports of finite BitProgram and StructuredCalls commands. The host-side formulas in tests are **only independent oracles** and never affect the production instruction machine.

## Executable original source stages

| Source | Runtime and source-defined behavior |
|---|---|
| `SubexpNormalizeProgram.negateProgram` | Original 15-label 2×2 unary polarity machine. On canonical unary code `c`, produces unary `c xor 1` using physical pops and pushes, preserving the input suffix and existing output accumulator; source cost `8*(c/2)+10+(c%2)` including halt. |
| `SubexpPostfixControl.literalService`, `SubexpNormalizeProgram.emitRecordProgram` | Source 17-label 3×4 frame writer entered at label 7, consuming reversed payload on stack 3 and prepending exactly `true :: frame payload` to stack 2; `5*payload_length+7` source steps including halt. |
| `SubexpNormalizeProgram.emitIfSelected` | Physical branch to either frame writer or source clear program, followed by the three source register-reset atoms. Both selected and discarded paths execute and are tested. |
| `SubexpNormalizeProgram.reverseRecordsCmd` | Original `RecordPrograms.iterate` with `filterPorts=(0,1,2,0,3)`, using actual framed reader and emitter to reverse **record order**, not bits within records; trailing input suffix and unrelated work stack are preserved. |
| Original four downstream lifts | `ExecLiteralDedupProgram.reverseProgram` 10×8 with register map `[7,8,9]` and stack map `[2,7,0,1]`; `ExecCleanLiteralsProgram.reverseProgram` 13×11 with `[10,11,12]`, `[2,10,0,1]`; `SubexpTautologyFilterProgram.reverseProgram` 13×11 with `[10,11,12]`, `[2,3,0,1]`; `ExecClauseFilterReverse.program` 15×16 with `[0,1,14]`, `[14,9,13,15]`. |
| `ExecLiteralDedupProgram.dedup` | Complete physical 10×8 callback and record iteration: preserve-copy suffix 0→3 via stack 7, execute the already ported `ExecCNFSubset.memberCall`, branch on actual membership flag, physically clear comparison work, emit only the last occurrence, and reverse records into original source order. No Rust equality or deduplication implementation appears in runtime code. |
| `ExecCleanLiteralsProgram.clean` | Complete physical 13×11 clausewise literal cleanup. Decodes each outer clause frame, transfers its payload into the real nested 10×8 deduplicator, transfers its result back, emits the framed clause, then reverses clauses into original order. The source `Fin.castAdd 3` register injection **is identity** (registers 0..9), while `Fin.natAdd 3` shifts the 8 local stacks to 3..10. |

The original `Encoding.frame` uses a `true` escape tag before **every** payload bit, ending in `false`; and `Encoding.encodeList` adds an outer `true` tag for every framed list element, then a final `false`. The tests intentionally include empty payload records, repeated records, multiple clauses and nonempty accumulators. Correcting an initially incorrect test oracle for that nested framing was necessary; the implementation uses the original reader/writer rather than altering it to satisfy a bad oracle.

## Local verification

Restored pinned Rust 1.99.1 and ran offline in the existing local v0.16.0 standalone crate with restored M2 dependency modules:

- **135 tests passed in debug, 0 failed** via `cargo test --offline --locked`.
- **135 tests passed in release, 0 failed** via `cargo test --offline --locked --release`.
- `cargo fmt --check` passed.
- `cargo clippy --offline --locked --all-targets -- -D warnings` passed.
- New tests cover all 256+ unary polarity cases (`n=0..256`) with exact machine-step counts; escaped writer payloads of length 0..8; both branch directions; deterministic and randomized record reversal; frame preservation in all four lift maps; original 10×8 last-occurrence oracle and seeded duplicates; source 13×11 nested clause cleanup (including empty clauses, repeated literals, duplicate clauses and 65 random formulas); fail-closed instruction limits.

The local restoration included independently reconstructed files for earlier source-native M2 modules that are already committed in PR #132; its local stub module files are **not** part of this PR. The GitHub versions of the six new production/test Rust files contain corresponding logic, but the GitHub **exact combined head has not been compiled independently**, and the copied source text is not claimed byte-identical to the locally formatted source. Do not interpret an allocation-failed GitHub Actions run as compiler evidence.

## Remaining normalization and counting blockers

The original `SubexpNormalizationProgram.program` is `prefixCall; dedupCall; removeSupersetsCall`, where `prefixCall` itself chains `ExecCleanLiteralsProgram.clean` and `SubexpTautologyFilterProgram.filter`. The literal-cleanup stage is now executable; **`SubexpTautologyFilterProgram.filter`, `ExecClauseDedupProgram.program`, `ExecClauseFiltersProgram.selfFilterProgram .strictSubset`, and their shared clause-relation/tautology subprograms remain unported**. Full normalization and `Native.frontendCommand` must therefore remain `NotImplemented`.

This work does **not** establish the source TM2 microstep/space bounds, Lean imported-reference differential equivalence, or the overall ETH theorem. Nonterminal high-query execution, native leaf and disjoint DFS still remain incomplete. Future work must link the source normalization stages, not add a semantic host normalizer or return a fabricated terminal count.

## Exact-head integration hygiene (static audit, not a complete compile)

The existing GitHub-only `tests/remaining.rs` and `tests/remaining_tdd.rs` retained hard-coded `remaining::STAGES.len() == 42` despite the parent M2 branch already registering 52 source stages. They also incorrectly asserted that two successfully ported command constructors (`NativeLeafDispatch.command` generic dispatcher and `Native.answerCommand` positivity suffix) return `NotImplemented`. Those assertions would produce false CI failures independently of this change. Both test files now enforce source identity, DAG topology/reachability, explicit new executable statuses/machine dimensions, and the correct **still unsupported** full normalization, native frontend, nonterminal leaf and outer counting stages. The implemented generic dispatcher and answer suffix must construct actual physical commands.

A connected-source static audit of this branch after those fixes found **57 unique stages** with no missing or forward prerequisites, **no orphans** relative to `final_theorem`, and a well-formed pinned blob entry for **every catalogued Lean source file** (91 manifest entries). The normalization stage dependency graph now includes the polarity-bit routine, and the still-stubbed full source `SubexpNormalizationProgram.program` has its own pin (`0d425a55a1d936dda93b1638fad908a51627cee6`).

This audit does **not** replace compiling the complete exact-head GitHub crate or running the original Lean interpreter; neither is verified here. The local 135-test result is limited to the standalone restored sources described above.
