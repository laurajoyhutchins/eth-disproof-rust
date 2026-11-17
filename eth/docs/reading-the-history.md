# Reading the implementation through Git history

The `main` branch contains a **constructed first-parent teaching sequence**.
It is a reading aid, not the original chronological development history,
authorship timeline, or proof that every intermediate checkpoint was rebuilt.
The original ancestry remains accessible in the full Git graph; the earlier
mixed research tree is retained on `python/sudoku-research`.

```sh
git log main --first-parent --reverse --format='%h %s'
git show --stat <commit>
git log --all --graph --oneline
```

## Follow the source-defined computation

| Question | Start with |
| --- | --- |
| What is a finite CNF and its canonical bit encoding? | `src/lib.rs`, `tests/lean_vectors.rs` |
| What does one machine instruction do to the entire state? | `src/bit_program.rs`, `tests/bit_program.rs` |
| How are source-defined high assignments and tuple states represented? | `src/native_tuple.rs`, `src/native_query_prefix.rs` |
| How do layout, head, cache and pair machines compose? | `src/native_layout.rs`, `src/native_bootstrap.rs`, `src/native_difference_pairs.rs` |
| Which complete original command can run? | `src/native_frontend.rs`, `src/bin/eth-frontend.rs`, `docs/m2-runnable-frontend.md` |
| Which stages still refuse? | `src/remaining.rs`, `tests/remaining.rs` |
| What does the current test evidence establish? | `docs/evidence.md` |

At each boundary, inspect the *full* register/stack state, the real instruction
sequence rather than a semantic Rust shortcut, preserved/cleared frames,
bounded refusal, and the evidence for the claim.

Formatting-only and CI commits are maintenance, not mathematical chapters.
The original source pins, machine ABI and executable test cases are more
informative than a version-number sequence in PR titles.

The present accepted `main` has a runnable source-defined frontend but not a
complete nonterminal native SAT counter, independently executed
original-Lean/Rust transition comparison, or theorem-level primitive TM2
complexity result. See [evidence](evidence.md) for the exact distinction.
