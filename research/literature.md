# Literature and source index for ETH algorithm research

**Curated 14 November 2026.** This is an *annotated reading map*, not a claim that every cited result is directly usable in OpenAI's proof. DOI links below were checked against publisher or bibliographic records. Keep the publications' status and the upstream 2026 preprint distinct.

## Peer-reviewed foundations

| Reference | What to extract for this project | Caution |
| --- | --- | --- |
| Impagliazzo, Paturi & Zane (2001), **“Which Problems Have Strongly Exponential Complexity?”**, *Journal of Computer and System Sciences* 63, 512–530. [DOI 10.1006/jcss.2001.1774](https://doi.org/10.1006/jcss.2001.1774) | ETH framing, sparsification lemma, instance-size/parameter-preserving reduction discipline | Its conditional framework is not evidence for or against the new theorem |
| Lokshtanov, Saurabh & Xue (2026), **“The Sparsification Lemma via Measure and Conquer”**, *SOSA 2026*, 291–297. [DOI 10.1137/1.9781611978964.22](https://doi.org/10.1137/1.9781611978964.22) | Cleaner proof and quantitative sparsification constants; independent crosscheck for preprocessing | Improved sparsification does not itself replace the tensor-contraction proof |
| Valiant (1979), **“The Complexity of Enumeration and Reliability Problems”**, *SIAM Journal on Computing* 8(3), 410–421. [DOI 10.1137/0208032](https://doi.org/10.1137/0208032) | Counting complexity and the difference between decision and exact counting | A \(\#P\)-completeness classification is not a time lower bound |
| Markov & Shi (2008), **“Simulating Quantum Computation by Contracting Tensor Networks”**, *SIAM Journal on Computing* 38(3), 963–981. [DOI 10.1137/050644756](https://doi.org/10.1137/050644756) | Tensor-network contraction, width-based exact baseline, ordering cost | Width can explain one solver's cost without proving the novel method hard |
| Bodlaender & Koster (2010), **“Treewidth Computations I. Upper Bounds”**, *Information and Computation* 208(3), 259–275. [DOI 10.1016/j.ic.2009.03.008](https://doi.org/10.1016/j.ic.2009.03.008) | Width heuristics/upper bounds for instrumented adversarial families | Estimated width is neither an exact invariant nor an ETH lower-bound proof |
| Cantor & Kaltofen (1991), **“On Fast Multiplication of Polynomials over Arbitrary Algebras”**, *Acta Informatica* 28, 693–701. [DOI 10.1007/BF01178683](https://doi.org/10.1007/BF01178683) | Exact polynomial multiplication cost models for many Hermite/interpolation kernels | Algebraic operations still have coefficient bit costs |
| van der Poorten (1976), **“Hermite Interpolation and p-adic Exponential Polynomials”**, *Journal of the Australian Mathematical Society* 22(1), 12–26. [DOI 10.1017/S144678870001332X](https://doi.org/10.1017/S144678870001332X) | Valuation-sensitive interpolation and coefficient-height reasoning | Different analytic setting; do not import its lemmas into a quotient ring without proof |
| Curticapean, Dell & Marx (2017), **“Homomorphisms Are a Good Basis for Counting Small Subgraphs”**, *STOC 2017*, 210–223. [DOI 10.1145/3055399.3055502](https://doi.org/10.1145/3055399.3055502) | Change of counting basis and precise transformations of finite combinatorial counts | A useful analogy, not direct proof of a pair-swap measurement basis |
| de Moura & Ullrich (2021), **“The Lean 4 Theorem Prover and Programming Language”**, *CADE 28*, 625–635. [DOI 10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37) | Lean compiler/runtime semantics, “functional but in-place” execution and codegen | General Lean semantics do not automatically validate custom Rust codegen |
| The mathlib Community (2020), **“The Lean Mathematical Library”**, *CPP 2020*, 367–381. [DOI 10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824) | Reuse formal ring/algebra, polynomial and tensor infrastructure; kernel discipline | Always pin the exact Mathlib revision of the original development |

## Primary source and contemporary discussion (not peer-reviewed literature)

- **OpenAI (October 25, 2026), “The Exponential Time Hypothesis is False.”** [Original manuscript/source tree](https://github.com/openai/math/tree/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026), [formalization scope](https://github.com/openai/math/blob/main/lean/docs/378.md), and the [pinned Lean source used here](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT). **Preprint**, not a peer-reviewed theorem in this bibliography. The published Lean scope describes \(2^{O_k(n(\log\log n)^2/\sqrt{\log n})}\) up to polynomial encoding factors; the manuscript asserts sharper \(2^{O_k(n\log\log n/\sqrt{\log n})}\) and fixed-density improvements. Do not conflate them.
- [OpenAI's announcement and expert-review plan](https://openai.com/index/building-scientific-understanding-with-academic-communities/) records why independent mathematical evaluation remains necessary.
- [This repo's evidence matrix](../rust/lean_eth_reference/docs/evidence.md) is the implementation-level ledger. The [source manifest](../rust/lean_eth_reference/reference/source-manifest.json) is the exact byte-identity ledger. Neither alone validates a mathematical theorem.
- **Background not claimed peer-reviewed here:** Delsarte's *An Algebraic Approach to the Association Schemes of Coding Theory* and MacWilliams–Sloane's *The Theory of Error-Correcting Codes* provide Hamming association-scheme/Krawtchouk context for the symmetry experiment. Read them for definitions and orthogonality, not as a proof of incidence compatibility.

## Reading order by proof obligation

1. **Exact counting and reductions:** Valiant → Impagliazzo/Paturi/Zane → 2026 sparsification. Derive count-preserving transformations explicitly.
2. **Tensor network baseline:** Markov/Shi → Bodlaender/Koster. Use this for controlled baseline and counterexamples to naive hardness inferences.
3. **Spectral/operator design:** association-scheme background → independently derive pair-swap joint spectrum and rational/integer measurement properties; test lost symmetry when incidence labels break orbits.
4. **Interpolation/bit complexity:** Cantor/Kaltofen → van der Poorten as heuristic reference. Prove local unit differences, exact quotient-ring equations and bit heights in Lean rather than transplanting field-only results.
5. **Implementation correspondence:** de Moura/Ullrich → Mathlib → actual pinned source IR/Expr, original execution and machine refinement.

## Reuse protocol

For each imported lemma or algorithm, record title/DOI, the exact theorem (including all rings, nonzero/unit hypotheses, parameter ranges and quantifier order), its proposed role, the Lean formal statement, source commit and a negative test where one hypothesis is removed. Avoid copying article text or including copyrighted PDFs in the repository. The useful artifact is a small formally checked theorem/definition and a precise reference.

Every paper above earns its place by informing a *specific proof or benchmark obligation*. Adding more references without an extraction/verification plan is not progress.
