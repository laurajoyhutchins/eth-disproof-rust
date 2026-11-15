# LaTeX-to-Lean semantic faithfulness benchmark

A Lean file can typecheck while stating a different theorem from the source LaTeX. The benchmark evaluates typechecking, semantic faithfulness, and kernel verification separately.

The targets under study are **Leanify**, **PaperFormalizer**, and **AutoformBot**. Before comparing them, pin each executable repository revision, model version, prompt, decoding settings, Lean/Mathlib toolchain and token budget. Model output counts as a proof only after independent Lean kernel verification and a semantic-faithfulness check.

## Benchmark corpus

| Collection | Examples | What the translation must keep |
| --- | --- | --- |
| Elementary | Quantifiers, integer identities, definitions | Binder order, domains, coercions |
| Spectral | Commuting involutions, eigenspaces, selector rows | Exact actions, equality, rank versus row norm |
| Algorithmic | Mode cutoffs, recurrence bounds, Hermite jets | Finite sums, precision, decreasing measures |
| Adversarial | False claims, missing units, swapped quantifiers | The **failure** rather than an invented stronger hypothesis |

Keep a gold proposition, a known proof or counterexample, source hashes and a held-out family of notation changes for each instance.

## Evaluation stages

**1. Did it parse?** Lean accepts the declarations and reports what it depends on.

**2. Did it mean the same thing?** Compare quantifier order, types, hypotheses, modular equalities, source symbols and precision. A translation that adds “assuming \(a\ne0\)” to a false division claim has changed the task.

**3. Did the kernel check the proof?** No `sorry`, `admit`, hidden axiom or opaque escape hatch. Audit the proposition and its dependencies with `#print axioms` and the pinned source closure.

Record typecheck success and semantic faithfulness **separately**. Where independent statement equivalence is not proved, report it as unverified.

## Adversarial mathematical cases

- Make two pair swaps noncommuting; a proof that silently assumes simultaneous diagonalization must fail.
- Try to factor \(\begin{pmatrix}1&1/2\\1/2&3/8\end{pmatrix}\) as rank one. Its determinant is \(1/8\).
- Change the mode cutoff from \(<p\) to \(\le p\), or remove \(2^p=0\). The intended truncation proof must reject the change.
- Swap two ports in a routed packet. A true source correspondence proof must expose the mismatch.
- Divide by a nonunit modulo \(2^p\). The prover must not conjure an inverse.
- Turn a uniform resource bound into a statement about a fixed input. The two are not interchangeable.

## Metrics and evidence

Measure faithful-proposition rate, kernel-checked proof rate *conditional on faithfulness*, false-claim rejection, unauthorized assumptions, and time/token cost. Store source hashes, generated Lean, complete diagnostics, model settings and exact toolchain versions.

Report unauthorized changes to hypotheses or conclusions separately from the number of generated files that typecheck.

The result we want is not a pile of toy theorems. A successful translation must feed the actual [packet recursion proof](two-adic-recursion.md), with its source-side hypotheses and an independent acceptance check.

[Compiler/source correspondence](lean-rust-acceptance.md) · [Reading list](literature.md)
