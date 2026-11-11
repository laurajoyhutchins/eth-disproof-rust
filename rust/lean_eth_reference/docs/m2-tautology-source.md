# Source-native tautology detection and formula filtering

Upstream Lean is pinned to `openai/math@4eaee87548250b2682affda7d05d947c05554bae`. This increment implements actual finite BitProgram/StructuredCalls instructions, **not** a host-side formula simplifier.

## Exact program provenance and machine layout

| Original source (Git blob) | Rust construction | Work |
| --- | --- | --- |
| `SubexpNegatedQueryProgram.lean` (`df9ee2e2fd1208a9c5915f077532937391847be8`) | `native_negated_query::program`, 2 registers × 4 stacks | Preserve-copy the reversed unary query to stack 2; run two real 10-label `StackRoutines.reverseProgram` calls, with the original 15-label unary complement between them. Input stack 0 retained, reversed opposite on stack 1, stacks 2/3 cleared. |
| `SubexpTautologyProgram.lean` (`2c9b093c91aaa6516768d99d01321ff20f3bb825`) | `native_tautology_core::program`, 10 × 8 | Preserve-copy the entire encoded clause 0→2; physically iterate tagged literal records, run the preserving complement on reverse payload 7, preserve-copy clause 2→3, use actual `ExecCNFSubset.memberCall`, and set reg 9 from the physical membership flag. Clear work and emit a one-bit result on stack 1, with source clause retained on stack 2. |
| `SubexpTautologyFilterProgram.lean` (`50884940290289fe287192b484bf9b6c1cfee02c`) | `native_tautology_filter::program`, 13 × 11 | Iterate the encoded formula's clause records, transfer payload 1→3, lift the clause tautology machine on register identity 0..9 and stacks 3..10, reverse-transfer the preserved clause 5→1, clear output flag port 4, invert reg 9 into selected reg 12, invoke original `SubexpNormalizeProgram.emitIfSelectedProgram`, then reverse retained records back to input stack 0. |

The `SubexpTautologyProgram.negateQueryProgram` lift maps registers `[0,1]` to themselves and stacks `[0,1,2,3]` to `[7,1,5,6]`. The formula filter lifts core registers `[0..9]` unchanged and stacks `[0..7]` to `[3..10]`. **Lean `Fin.castAdd` is an identity mapping; it must not be interpreted as an offset.** The source, output and scratch maps in the code are explicit and independently exercised.

The original input encoding is `Encoding.encodeList` of `Encoding.encodeList Encoding.encodeNat` clauses; unary code `2v+b` uses adjacent polarity indices. Boolean `true` before each escaped payload bit and `false` as its terminator are not arbitrary byte-string normalization rules. Source correctness assumes valid framed encoding and initially empty work stacks.

## Executed verification

Using the verified restored Rust **1.99.1** compiler and offline standalone `lean-eth-reference` v0.16.0 baseline, plus **physical** reconstructed M2 dependencies:

- `cargo test --offline --locked`: **122 passed, 0 failed**, debug.
- `cargo test --offline --locked --release`: **122 passed, 0 failed**, release.
- `cargo fmt --check`: pass.
- `cargo clippy --offline --locked --all-targets -- -D warnings`: pass.
- Five new targeted tests: exact source negated-query steps for `c = 0..=128`, original input/response/scratch preservation, real clause tautology results (empty, complementary, noncomplementary, repeated literals), multiple formula cases retaining non-tautological clauses in original order, 100 deterministic randomized CNFs compared to an independent test-only oracle, and fail-closed instruction-budget refusal. No host tautology predicate appears in executable production code.
- The **four new GitHub Rust source/test files are byte-for-byte identical to those compiled/tested locally**. Their Git blob SHAs were independently checked: `a6d6772`, `c7800ee`, `06ea560`, and `ce5ad76`.

The local compiler snapshot is not the complete GitHub HEAD: base modules `native_membership`, `native_record_membership`, `native_terminal_classifier`, and `native_normalization_primitives` were reconstructed from already pinned source/earlier ports and checked through the same physical machine tests. The complete combined GitHub HEAD, including its `remaining.rs` registry, is **not independently compiled or covered by the local test claim**. A static audit of this branch confirms **60 unique stage entries, topologically ordered and reachable from `final_theorem`**, with a source blob pin for every catalogued stage (93 manifest entries). A source pin and structural audit are not a live imported-Lean differential trace or proof.

## Still unsupported

`SubexpNormalizationProgram.program` still requires the original **clause deduplication** (`ExecClauseDedupProgram.program`) and **strict-superset removal** (`ExecClauseFiltersProgram.selfFilterProgram .strictSubset`), plus their physical relation-scanning subprograms. Source `Native.frontendCommand` is still a stub. No nonterminal high-query, native leaf, disjoint DFS, primitive TM2 refinement or theorem acceptance claim follows from this bounded tautology-filter implementation.

## Newly executable exact normalization prefix

The same branch now composes `SubexpNormalizationPrefixProgram.command` as the actual `Cmd::seq(ExecCleanLiteralsProgram.clean, SubexpTautologyFilterProgram.filter)` on **13 registers × 11 stacks**, compiled with source input/output ports **0/0**. Upstream blob `a384d93bc723c51b7ab9430673a86fa4759b6f3c` is pinned in the manifest. The Rust entry point is `native_normalization_prefix::program()` and `remaining::outer::normalization_prefix()`. It does not perform a semantic host normalizer.

The executable prefix now cleans repeated literals *within* each clause, removes clauses containing complementary polarity literals, and preserves the order and multiplicity of the remaining clauses. The latter is important: **clause deduplication belongs to a separate later source program**, not this prefix. An independent source-encoding oracle in the two new tests checks empty formulas, empty clauses, repeated literals, repeated clauses, complementary polarity, and **100 additional seeded random CNFs**.

Restored Rust 1.99.1 offline standalone **124 tests passed debug, 124 release**, `cargo fmt --check` and strict Clippy pass. Both new prefix source/test Git blobs **exactly match** the locally compiled source by SHA: `2aed0ae6625ca88f94c802d8c2e9e52ed56eeb45`, `b4d4f1b943b7ca619af97bc6424867843d69ef08`. The earlier local Rust snapshot still uses reconstructed M2 dependency modules, so this is **not** a combined GitHub-HEAD compile or Lean/Rust differential run.

A connected-source static check of the amended branch confirms **61 unique stages** in source order, **94 pinned upstream Git blobs**, no missing/forward dependencies and no orphans from `final_theorem`. It caught and corrected one accidental self-dependency in the new `normalization_prefix` stage *before* final PR review. The current graph correctly has `normalization_prefix` depending on `normalization_literal_cleanup` and `normalization_tautology_filter`, and the still-stubbed `normalization_full` depending on that executable prefix.

**Remaining original normalization path:** `SubexpNormalizationProgram.absorbCommand = dedupCall; removeSupersetsCall`. Until both source programs and their physical clause-relation loops are ported, neither `SubexpNormalizationProgram.program` nor `Native.frontendCommand` is marked executable.
