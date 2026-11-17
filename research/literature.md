# References for counting, interpolation, and formalization

The references below cover exact counting, tensor contraction, polynomial arithmetic, and Lean semantics. Applying a published theorem to the ETH construction requires checking its hypotheses in the intended setting.

## Counting and sparsification

**Valiant, 1979.** *The Complexity of Enumeration and Reliability Problems.* SIAM J. Comput. 8(3), 410–421. [DOI](https://doi.org/10.1137/0208032).  
This paper distinguishes decision from exact counting. \(\#P\)-completeness does not imply a time lower bound for one proposed algorithm.

**Impagliazzo, Paturi & Zane, 2001.** *Which Problems Have Strongly Exponential Complexity?* JCSS 63, 512–530. [DOI](https://doi.org/10.1006/jcss.2001.1774).  
The sparsification framework and parameter-preserving reductions define what has to be counted when going from general CNF to bounded density.

**Lokshtanov, Saurabh & Xue, 2026.** *The Sparsification Lemma via Measure and Conquer.* SOSA, 291–297. [DOI](https://doi.org/10.1137/1.9781611978964.22).  
Provides another proof and quantitative reference for the preprocessing stage. Improving sparsification constants does not prove the recursive contractor.

## Tensor networks and width

**Markov & Shi, 2008.** *Simulating Quantum Computation by Contracting Tensor Networks.* SIAM J. Comput. 38(3), 963–981. [DOI](https://doi.org/10.1137/050644756).  
Use this to define ordinary contraction cost and a width-aware exact baseline.

**Bodlaender & Koster, 2010.** *Treewidth Computations I. Upper Bounds.* Information and Computation 208(3), 259–275. [DOI](https://doi.org/10.1016/j.ic.2009.03.008).  
Useful for checking decomposition-width estimates. A high treewidth estimate is not a lower bound on the proposed new method.

**Curticapean, Dell & Marx, 2017.** *Homomorphisms Are a Good Basis for Counting Small Subgraphs.* STOC, 210–223. [DOI](https://doi.org/10.1145/3055399.3055502).  
A disciplined example of changing a counting basis. The idea is relevant to selector measurements; its correctness does not automatically transfer to pair swaps.

## Algebra and interpolation

**Cantor & Kaltofen, 1991.** *On Fast Multiplication of Polynomials over Arbitrary Algebras.* Acta Informatica 28, 693–701. [DOI](https://doi.org/10.1007/BF01178683).  
Use the exact algebraic operation model when pricing repeated Hermite reconstruction. Add coefficient bit complexity separately.

**van der Poorten, 1976.** *Hermite Interpolation and p-adic Exponential Polynomials.* J. Austral. Math. Soc. 22(1), 12–26. [DOI](https://doi.org/10.1017/S144678870001332X).  
Valuations and interpolation are relevant, but this analytic setting is not identical to arithmetic in a finite quotient ring. Reprove any transferred statement with the correct units and precision.

For pair-swap spectra, Delsarte's *An Algebraic Approach to the Association Schemes of Coding Theory* and MacWilliams–Sloane's *The Theory of Error-Correcting Codes* supply Hamming-scheme and Krawtchouk background. These are references for the algebra, not peer-reviewed proofs of our incidence compatibility.

## Lean and formal libraries

**de Moura & Ullrich, 2021.** *The Lean 4 Theorem Prover and Programming Language.* CADE 28, 625–635. [DOI](https://doi.org/10.1007/978-3-030-79876-5_37).  
The compiler-IR runtime requires source-compatible handling of sharing, in-place optimization, and closures.

**The mathlib Community, 2020.** *The Lean Mathematical Library.* CPP, 367–381. [DOI](https://doi.org/10.1145/3372885.3373824).  
Reuse algebra and polynomial results, pinned to the original Mathlib commit. Do not silently upgrade the source environment.

## The source under study

**OpenAI, October 25, 2026.** [*The Exponential Time Hypothesis is False*, source and manuscript](https://github.com/openai/math/tree/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026). This is a **preprint**, not part of the peer-reviewed list above.

The [Lean formalization scope](https://github.com/openai/math/blob/main/lean/docs/378.md) describes a bound of the form

\[
2^{O_k(n(\log\log n)^2/\sqrt{\log n})},
\]

up to polynomial encoding factors. The manuscript states a sharper \(2^{O_k(n\log\log n/\sqrt{\log n})}\) route. Do not transfer the sharper statement to the Lean scope without checking the corresponding theorem.

Our [pinned source](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT) and [execution evidence](../eth/docs/evidence.md) are separate from claims about the mathematical result.

## Formalization and reproduction

For every borrowed lemma: record the exact statement, ring, units/nonzero assumptions, quantifiers, source and a small counterexample when one hypothesis is removed. Then implement the intended statement in Lean and audit its axioms.

For every borrowed algorithm: include its construction cost and intermediate bit lengths. A resource claim also requires construction and bit-complexity bounds, regardless of the citation.

[Research questions](README.md) · [Formalization test design](formalization-evaluation.md)
