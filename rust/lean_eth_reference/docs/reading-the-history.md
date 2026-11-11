# Read the port as a sequence of executable boundaries

The first-parent history of `main` is a *constructed study sequence*, not a
reconstruction of the dates or authorship of the original experiments. Every
code chapter reuses an exact historical Git tree. Original ancestry remains
reachable through the final merge's second parent, and the former mixed
repository is retained on `python/sudoku-research`.

```sh
git log main --first-parent --reverse --format='%h %s'
git show --stat <chapter-commit>
git show <chapter-commit>:rust/lean_eth_reference/src/bit_program.rs
```

Each chapter asks one specific question, adds an executable boundary,
or isolates a correctness obligation before the next chapter. The tests listed below are a reading map, **not** a claim that all
historical checkpoints were independently recompiled after reconstruction.

| Chapter | Question | Read code / tests |
| --- | --- | --- |
| 00 | What is a formula, encoding, instruction, and finite-machine state? | `src/lib.rs`, `src/bit_program.rs`; `tests/lean_vectors.rs`, `tests/bit_program.rs` |
| 01 | How is a high assignment enumerated using physical stacks? | `src/native_tuple.rs`, `src/native_query_prefix.rs`; matching tests |
| 02 | How are node, layout and pair state represented? | `src/native_nodes.rs`, `src/native_layout.rs`, `src/native_pair_setup.rs` |
| 03 | How is an unimplemented Lean stage distinguished from a halt? | `src/remaining.rs`, `src/native_integer_cache.rs`; `tests/remaining.rs` |
| 04 | How are cache rows iterated as finite programs? | `src/native_cache_iteration.rs`, `tests/native_cache_iteration.rs` |
| 05 | How are H-cache values flattened to explicit bit words? | `src/native_flatten.rs`, `tests/native_flatten.rs` |
| 06 | How do cache stages compose into a head bootstrap? | `src/native_bootstrap.rs`, `src/native_cache_normalize.rs`; bootstrap tests |
| 07 | How are head frames and pair masks preserved across calls? | `src/native_loader_frames.rs`, `tests/native_pair_expand.rs` |
| 08 | Which strict difference pairs are visited, in what order? | `src/native_difference_pairs.rs`, `tests/native_difference_pairs.rs` |
| 09 | How are signature tuples and head support staged? | `src/native_signature_tuple.rs`, `src/native_head_support.rs`, `src/native_head_scatter.rs` |
| 10 | How does the Rust crate stand apart from the Python research tree? | Repository `README.md`, isolated workflow and source fixtures |
| 12 | Does Lean's finite-index embedding preserve the original register index? | `src/native_bootstrap.rs`, `src/native_difference_pairs.rs`, `src/native_head_support.rs`, `src/lib.rs` |
| 13 | Do tests catch corruption of otherwise unmapped machine state? | `tests/bootstrap_integration.rs`, `tests/native_difference_pairs.rs`, `tests/native_head_support.rs` |
| 14 | Which changes are purely formatting under the pinned Rust compiler? | `src/lib.rs`, `src/native_head_support.rs`, and the changed tests |
| 15 | How do the parts fit, and what remains unproved? | This guide, `src/remaining.rs`, the source manifest |

## Four checks to make at every boundary

1. **State.** Which registers, stacks and encoded words represent the current
   mathematical objects? Are port maps and bounds explicit?
2. **Semantics.** Which instruction sequence actually runs? A Rust host
   shortcut or a semantic oracle is not a literal Lean machine port.
3. **Invariants.** Which inputs and frames are preserved, which scratch
   banks are cleared, and what happens on a capacity refusal?
4. **Evidence.** Which tests compare exact words, source-instruction costs
   or transitions? Which comparisons still require original Lean execution?

To check the *current* checkout using the pinned toolchain:

```sh
cd rust/lean_eth_reference
cargo fmt --all -- --check
cargo test --locked --offline --all-targets
cargo clippy --locked --offline --all-targets -- -D warnings
```

**Evidence boundaries:** finite machine tests establish properties of tested
Rust executions. They do not by themselves establish imported-source
Lean/Rust equivalence, TM2 resource refinement, a complete source-native SAT
counter, or a polynomial/subexponential worst-case bit-complexity theorem.
The dependency spine in `src/remaining.rs` deliberately distinguishes
`Executable`, `Partial`, `Stub`, `Noncomputable`, and `ProofObligation`.

## Why the main branch has a two-parent join

The pedagogical sequence is the **first parent** of the final join. The live,
already CI-verified `main` from before this change is the **second parent**.
That makes the update a fast-forward, keeps existing GitHub pull-request
ancestry intact, and preserves the actual development history. Use
`git log --first-parent main` for the study sequence and `git log --all`
to inspect the full Merkle graph. Do not mistake the instructional commit
timestamps for when the original engineering work occurred.
