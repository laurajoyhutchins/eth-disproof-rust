# M2: complete source-defined terminal classification

Pinned original: `openai/math@4eaee87548250b2682affda7d05d947c05554bae` (Lean 4.34.1).

This increment implements **the entire physical terminal detection chain**, not a Rust-host predicate:

| Original executable construction | Rust machine | Original Git blob |
|---|---|---|
| `ParserProgram.frameProgram` | `native_record_membership::frame_program` (2×2, seven labels) | `9461361e12630b91419b6788ea8d2af4b2de5e9b` |
| `RecordPrograms.iterate` + `ExecCNFMembership.membership` | `native_record_membership::iterate_command` and `membership_command` (7×5) | `c9df05c33224e16019f3504d37f079f035dd7ac2`, `50e7a70685a6a1132da9a5a1c7ae31a2f59db1df` |
| `ExecCNFSubset.memberCall` | `native_terminal_classifier::subset_member_call` (10×8) | `8da2d5592e5c52fedbd724e4ad4fe8b1226bd2a7` |
| `SubexpScopeMembershipProgram.member` | `native_terminal_classifier::scope_member_command` (10×10) | `631aa5aacd984b90051f9d64bb82a71e5334e813` |
| `SubexpEmptyClauseProgram.command` | `native_terminal_classifier::empty_clause_command` (10×10) | `49824f224b4772c5356ffdb097b04eb23fdac756` |
| `SqrtLog.LeafProgram.Trivial.command` | `native_terminal_classifier::trivial_command` (10×10) | `4ecb36211c04c27268cb9bf261fcbb97b2610fe1` |
| `NativeTerminal.classifier/command/readyCommand` | `native_terminal_classifier::terminal_classifier_command/terminal_command/ready_command` (80×1220) | `ebcd509ab86db459822f3ee211e7e70064291c2f` |

The signed terminal outcome is physically determined by the encoded CNF record list, not a Rust semantic #SAT oracle:

- If a clause has **zero literals** (record `[false]`), classifier register 0 becomes true and the terminal output is the canonical full count word `[false]` on stack 263.
- If **no clauses** are present, classifier register 7 becomes false and `NativeTerminal.power` produces `countWord (2^n)` using the source finite seed/loop, including unused ambient variables and `n=0`.
- A **nonempty formula with no empty clause** leaves stack 263 empty and sets the two flags for the unresolved native leaf path. An empty stack 263 in this case is explicitly **not** a zero count or accepted SAT decision.

The `readyCommand` physically clears dirty stacks 263/268/269 before classification and respects the original low-bank-empty preconditions. The classifier retains encoded body 265, ambient header 258 and nonlocal protected registers/stacks. Its source-defined port maps retain index order: `Fin.castAdd` is not an offset. For the 10×8 subset call, the source stack map is `[3,4,1,5,6]`; for the 10×10 scope lift it is `[5,2,6,0,1,3,4,7]`; the outer classifier maps stack 9 to 265 and other local stacks 0–8 unchanged.

## Exact generic nonterminal dispatch (source-defined but dependent on a real leaf)

The same branch now ports `NativeLeafDispatch.command nonterminal` (pinned Git blob `4431251b1417e742d9625f08028f2847053332fb`) on the shared 80×1220 machine: `NativeTerminal.readyCommand` followed by `ite 0 skip (ite 7 nonterminal skip)`. It is **fully runnable as a command factory** for a supplied physical callback and has its own three tests checking guard paths, protected state and instruction-budget refusal. The callback in these tests only sets a distinct sentinel register/stack (79/1200 or 78/1199); it does **not** produce a count or stand in for the real native leaf. The registry now returns this actual command from `remaining::leaf::terminal_dispatch` and marks the stage **Partial**, not `Executable` for a complete accepted counting path, because `NativeLeafExecution.command` is still missing.

For terminal CNFs, the provided callback is bypassed and source terminal counts remain correct. For a nonterminal CNF, the callback actually executes on the classified state while count output 263 remains empty until the future real leaf produces it. Incorrectly treating an arbitrary empty record `[]` as the special empty-clause record `[false]` initially failed one test; the fixtures were corrected to match `Encoding.encodeList` semantics.

## Verified and unverified boundaries

**Executed locally:** Restored Rust 1.99.1 standalone v0.16.0 crate with M2 changes: `cargo test --offline --locked` **147/147 passed** in debug, `cargo test --offline --locked --release` **147/147 passed**, `cargo fmt --check` passed, and `cargo clippy --offline --all-targets -- -D warnings` passed. Five new record tests cover 2^n bit words up to length 8, all single-record word-pairs through length 5, multi-record first/middle/last/absent/duplicate, short-circuit and capacity refusal. Five new terminal tests cover empty CNF, empty clause, nonterminal, n=0..8, preserved ABI frame, dirty scratch, flags and capacity refusal. The two **committed test blobs** match the locally executed test files exactly by SHA-1 Git object identity.

**Verification still required:** The standalone archive does not include the source repository's `remaining.rs`, recent M1 module additions, or an actual imported-source Lean execution. The new GitHub branch's complete exact-head combined repository has not been compiled independently. The new Rust module bodies are structurally the locally tested implementation but their documentation text was edited when uploading. No proof of Lean/Rust differential trace equivalence, TM2 microstep bounds, or ETH complexity follows from bounded tests.

**Source premises:** The machine assumes canonical `Encoding.encodeList id` record encoding on stack 265, canonical unary `Encoding.encodeNat n` on 258, and the source's empty low scratch banks. It is not an arbitrary malformed-byte-string validator. `NativeTerminal.readyCommand` does not create those input premises; the missing frontend/normalizer must do so.

**Still unsupported:** `NativeLeafDispatch.command`, actual high-query/accepted callbacks, greedy leaf rounds, `DFSCountProgram.command`, `Native.outerCommand`, `Native.entryCommand`, and `Native.countingProgram`. The noncomputable finite fallback remains explicitly unsupported. Terminal classification may now be composed with the real leaf once it is available, but the full end-to-end source native #SAT counter is not complete.
