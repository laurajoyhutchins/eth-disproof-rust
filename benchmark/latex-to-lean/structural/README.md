# Structural LaTeX frontend (experimental)

**A typed, deterministic companion backend, NOT a patch to upstream Leanify.**

The pinned Leanify 8/12 benchmark remains immutable. This independent Rust
frontend covers a distinct mathematical fragment that the Leanify scalar core
currently cannot elaborate. Its results are reported separately; do **not**
claim that upstream Leanify now supports products, matrices or finite words.

## Scope

- Real vector functions `R^n -> R^m` with explicit coordinate definitions,
  arithmetic coordinates, and typed function application/composition;
- finite `n x m` real matrices given by `pmatrix` and equality of powers
  to dimension-matched identities;
- cardinality of finite-alphabet words, modeled as functions `Fin n -> Fin k`,
  with binary/ternary/quaternary and explicit `base-k` word families;
- explicit real/vector quantifiers and closed equality statements.

Original LaTeX source is never rewritten. Unknown constructs, dynamic inputs,
unsupported macros, missing variables, dimension disagreements, and implicit
quantification are errors, not substitutions or `sorry`.

## Build & run

```
cargo test --offline
cargo clippy --offline --all-targets -- -D warnings
cargo build --release --offline
./target/release/structural-latex --batch examples/ out/
./target/release/structural-latex --batch holdouts/ out/holdouts/
```

Requires Rust 1.99.1 (standard library only, zero third-party crates).
The benchmark CI additionally runs Lean 4.34.0 with pinned Mathlib to elaborate
and check generated definitions, independent semantic equivalences, true
claims, and refutations of deliberately false claims. Neither the parser nor
these tests supply an automatic theorem prover.

## Non-overfitting test strategy

`cargo test` sweeps vector dimensions 2–16 and word bases 2–8 over lengths
1–10, covers differing map domain/codomain arities, rejects type errors, and
preserves false statements. Separate held-out LaTeX exercises 5-dimensional
maps, 3x3 matrices, ternary cardinality, and negative claims. Every generated
Lean source is archived with the source SHA-256 and verifier output.

## Trust boundary

Passing the Rust parser proves syntax/type safety only in its supported grammar.
Lean kernel elaboration and independent reference equivalence are separate
verification obligations. We do not attribute handwritten proof oracles to the
compiler. This fragment is **not general-purpose LaTeX mathematical English**.

## Performance

`--batch` compiles all `.tex` articles inside one native process, reducing
process startup and eliminating repeated Leanify builds at parse time.
The pipeline records warm/cold wall and RSS, Rust compiler version, source
hashes, and Lean proof times. Compare parser stage to parser stage, not
parser time to agent proof-completion time.