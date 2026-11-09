# Mathematical bibliography and research map

**Status:** working bibliography, started 2026-11-09. This is a map of established
ideas onto specific, inspected code, **not** a claim that the repository
establishes a new worst-case complexity theorem.

## How to use this bibliography

- **Direct:** the code implements an instance of the established idea or an
  exact identity of that type.
- **Adjacent:** a useful mathematical language or comparison, not an
  established reduction or implementation equivalence.
- **Open:** a possible research direction or complexity claim that still
  needs a proof.

See [the system map](system-map.md), [Sudoku algebra](sudoku.md),
[ETH constructions](eth.md), [contraction mathematics](mathematics.md),
[bit-complexity audit](bit-complexity.md), and [claim boundaries](claims.md).
The relevant size measure, intermediate representation, coefficient height,
and refusal behavior belong in any claim citing these works.

## I. Counting, constraint systems and tensor contraction

**1. Exact cover and combinatorial search [Direct].** Donald E. Knuth,
*Dancing Links* (2000), [arXiv:cs/0011047](https://arxiv.org/abs/cs/0011047).
In `sudoku/state.py` and `sudoku/frontier.py`, each cell-digit candidate
occupies three unit-digit obligations; exactly one candidate is selected per
cell. This is a weighted exact-cover/hypergraph-packing formulation.
Dancing Links supplies the classic exact-cover comparison, **not** a claim
that the frontier algorithm is DLX or uses its exponential backtracking.

**2. #P and exact enumeration [Direct context].** Leslie G. Valiant,
*The Complexity of Enumeration and Reliability Problems*, SIAM Journal on
Computing 8 (1979), 410–421,
[doi:10.1137/0208032](https://doi.org/10.1137/0208032).
For the significance of exact counts and the distinction between finding
and counting, especially `eth/cnf.py`, `sudoku/three_cnf.py`, and the
independent counting oracles. Also see Valiant, *The Complexity of Computing
the Permanent*, Theoretical Computer Science 8 (1979), 189–201,
[doi:10.1016/0304-3975(79)90044-6](https://doi.org/10.1016/0304-3975(79)90044-6).

**3. Generalized distributive law [Direct].** Srinivas M. Aji and Robert J.
McEliece, *The Generalized Distributive Law*, IEEE Transactions on
Information Theory 46 (2000), 325–343,
[doi:10.1109/18.825794](https://doi.org/10.1109/18.825794).
The common algebraic object across the exact counters is
`Z = sum_x product_a f_a(x_{S_a})`, evaluated over different exact rings
or semirings. Distributivity explains legal local elimination; it does
not bound the size of the resulting factors.

**4. Bucket elimination and induced width [Direct].** Rina Dechter,
*Bucket Elimination: A Unifying Framework for Reasoning*, Artificial
Intelligence 113 (1999), 41–85,
[doi:10.1016/S0004-3702(99)00059-4](https://doi.org/10.1016/S0004-3702(99)00059-4).
The closest ancestor of `eth/factorized_taylor.py`, the fused Taylor
evaluator, frontier dynamic programming, and the separator counters.
Ordinary dense-table elimination scales exponentially in induced width,
even if the number of factor groups or measurement rows is small.

**5. Tensor-network contraction and treewidth [Direct].** Igor L. Markov
and Yaoyun Shi, *Simulating Quantum Computation by Contracting Tensor
Networks*, SIAM Journal on Computing 38 (2008), 963–981,
[doi:10.1137/050644756](https://doi.org/10.1137/050644756).
Read alongside `contraction/`, `elimination/`, and `eth/tensor_train.py`.
Network size, contraction order, cut width, and intermediate tensor rank
are distinct parameters. A short network description does not imply cheap
exact contraction.

**6. Holographic reductions and Holant [Adjacent].** Jin-Yi Cai and Vinay
Choudhary, *Valiant's Holant Theorem and Matchgate Tensors*, Theoretical
Computer Science 384 (2007), 22–32,
[doi:10.1016/j.tcs.2007.05.015](https://doi.org/10.1016/j.tcs.2007.05.015).
A useful neighboring framework for treating constraint counts as tensor
signatures and examining when a basis change reveals tractable structure.
**No matchgate identity or holographic tractability result is currently
claimed for the Sudoku tensors.**

## II. Exact compressed representations and symmetry

**7. Zero-suppressed decision diagrams [Direct].** Shin-ichi Minato,
*Zero-Suppressed BDDs for Set Manipulation in Combinatorial Problems*,
DAC (1993), 272–277,
[author publication list](https://www.algo.cce.i.kyoto-u.ac.jp/minato/papers.html);
and *Zero-Suppressed BDDs and Their Applications*, STTT 3 (2001), 156–170,
[doi:10.1007/s100090100038](https://doi.org/10.1007/s100090100038).
`sudoku/weighted_zdd.py` applies exact restriction, union, projection,
and weighted addition to a compressed finite map. The number of diagram
nodes is instance- and ordering-dependent, not automatically polynomial.

**8. Knowledge compilation [Direct comparison].** Adnan Darwiche and
Pierre Marquis, *A Knowledge Compilation Map*, JAIR 17 (2002), 229–264,
[doi:10.1613/JAIR.989](https://doi.org/10.1613/JAIR.989).
Use for `sudoku/hybrid.py` and the frontier/ZDD conversions: the relevant
questions are **succinctness**, construction cost, and which exact queries
can be performed cheaply on the compiled form. Optimizing one does not
settle the others.

**9. Finite permutation-group actions [Direct].** Peter J. Cameron,
*Permutation Groups*, Cambridge University Press (1999),
[book resources](https://cameroncounts.github.io/web/books/permgps/pgbook.html).
`sudoku/symmetry.py` and `sudoku/suffix_graph.py` use certified
automorphism actions and orbit-stabilizer counts. The special
`PGL(2,8)` action on nine digit labels has 504 elements, but only its
domain-preserving subgroup is safe. The significant condition is
equivariance of all remaining transitions, not merely an attractive
group order.

**10. Tensor trains and cut-rank [Direct, developing].** I. V. Oseledets,
*Tensor-Train Decomposition*, SIAM Journal on Scientific Computing 33
(2011), 2295–2317,
[doi:10.1137/090752286](https://doi.org/10.1137/090752286).
The `research/eth-exact-tensor-contraction` branch has
`benchmarks/eth/tensor_bond_obstruction.py`: for
`AND_i (x_i OR y_i)`, a cut separating all x's from all y's has
exact flattening rank `2**k`, whereas an interleaved ordering admits
maximum bond at most 2. This is a valid **fixed-order representation**
obstruction, not a lower bound for the best ordering or all #SAT algorithms.
A source of testable questions about ordering and exact tensor rank.

## III. Finite differences, spectral algebra, interpolation and local rings

**11. Möbius inversion on the Boolean lattice [Direct].** Gian-Carlo
Rota, *On the Foundations of Combinatorial Theory I: Theory of Möbius
Functions*, Z. Wahrscheinlichkeitstheorie verw. Gebiete 2 (1964),
340–368, [doi:10.1007/BF00531932](https://doi.org/10.1007/BF00531932).
The alternating `U subset E` Taylor sum in `docs/eth.md` is a
Boolean finite difference / incidence-algebra operation. The fused
evaluation performs the cancellation **before** expanding all pairs.
The identity eliminates an explicit enumeration, but the resulting
polynomial factors can still have exponentially large scopes.

**12. Fourier analysis of symmetric Boolean functions [Direct].** Ryan
O'Donnell, *Analysis of Boolean Functions* (2014),
[book PDF](https://www.cs.cmu.edu/~./odonnell/papers/Analysis-of-Boolean-Functions-by-Ryan-ODonnell.pdf).
`eth/construction.py` computes Walsh coefficients of a
Hamming-weight-dependent function by cardinality. The
`(C_2)^Q` commuting-swap action admits a character decomposition;
weight-class aggregation is closely related to Krawtchouk transforms
and the Hamming association scheme. This makes a virtual exponential
spectral operator implicit, **not** its restricted measurement rank
or contraction cost automatically small.

**13. Binomial basis and p-adic interpolation [Adjacent].** Kurt Mahler,
*An Interpolation Series for Continuous Functions of a p-adic Variable*
(1958), [reprint](https://ems.press/books/dms/252/4989).
The Newton/binomial basis in `eth/construction.py` and the 2-adic
coefficient rings in `core/` resonate with integer-valued polynomial
and p-adic interpolation techniques. This is **not** a claim that the
implementation uses Mahler's theorem to justify its finite constructions.

**14. Exact Cauchy deformation, Hermite recovery, and 2-adic arithmetic
[Direct, manuscript-specific].** OpenAI, *The Exponential Time
Hypothesis is False* (25 October 2026), especially
[quantitative-contraction.tex](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex)
and
[quantitative-reduction.tex](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-reduction.tex).
`contraction/packets.py`, `recovery/streaming.py`, and
`core/` implement finite-ring calculations where powers of two
need not be units, so odd-denominator normalization, valuations,
truncated-series inversion, and exact rational cancellation matter.
`eth/interpolation.py` also uses local Hermite/CRT readout to avoid
constructing a full interpolant. These identities do not discharge
total bit complexity or the inherited-oracle cost.

**15. Derandomization by conditional expectation [Direct].** Noga Alon
and Joel H. Spencer, *The Probabilistic Method*, 3rd ed. (2008),
[book PDF](https://math.bme.hu/~gabor/oktatas/SztoM/AlonSpencer.ProbMethod3ed.pdf).
`eth/balance.py` and packet-label balancing make deterministic
choices against expected overload. The required mathematical obligation
is that the **implemented** potential function and finite choices
preserve the paper's packing hypothesis across every admitted child.

## IV. Complexity hypotheses and the current frontier

**16. ETH, sparsification and size-preserving reductions [Direct context].**
Russell Impagliazzo, Ramamohan Paturi and Francis Zane,
*Which Problems Have Strongly Exponential Complexity?*, JCSS 63 (2001),
512–530, [doi:10.1006/jcss.2001.1774](https://doi.org/10.1006/jcss.2001.1774).
Relevant to `eth/preprocess.py`, `eth/sparsification.py`,
and `docs/paper-admissibility.md`. Keep the actual counted-variable
semantics, auxiliary extension multiplicity, clause incidence, and
size parameter explicit. Standard satisfiability-preserving
reductions need not preserve the number of satisfying assignments.

**17. Candidate subexponential exact #SAT theorem [Direct source, not
independently certified here].** OpenAI, *The Exponential Time Hypothesis
is False* (25 October 2026),
[paper and source](https://github.com/openai/math/tree/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026).
This is the explicit ancestor of the packet/Cauchy recursion and the
ETH construction. Compare **the mathematical theorem**, its
hypotheses, the source algorithm, and the repository's actual
bounded execution separately. The project has **not** established a
non-refusing worst-case bit-operation recurrence for generalized Sudoku.

**18. Quantitative stress test of that manuscript [Critical context].**
Fabio Dias and Yvens Lima, *Limits and Constants of OpenAI's Claimed ETH
Refutation* (2026), [arXiv:2611.00517](https://arxiv.org/abs/2611.00517).
A useful independent analysis of astronomical constants, the distinction
between interpolation and the stronger contraction route, and the
limitations of particular clause-product evaluation models.
Its scoped lower bounds must not be misreported as a refutation of
every contraction strategy.

## Connections worth investigating, without promoting them to theorems

1. **Rank versus width.** `docs/eth.md` records both full restricted
   measurement rank on finite cases and a family where low measurement
   count coexists with complete group interaction width. Can a different
   spectral basis, or a joint structural invariant, control **both**?
   Row operations preserve rank; they do not create sparsity for free.
2. **Representation-aware contraction.** Use the exact cut-rank
   obstruction from the research branch as a unit test for proposed
   tensor orderings. Ask for a constructive ordering or a lower bound
   applying to *all* permitted orders, not only one.
3. **Symbolic cancellation before expansion.** Extend the Boolean
   finite-difference fusion and local Hermite-origin functionals, but
   measure the induced scopes, degree, coefficient height, and total
   rational/2-adic bit operations of the replacement computation.
4. **Algebraic quotienting and compositional certificates.** A
   representation may share equal states by an exact group action,
   ZDD node, spectral weight class, or local ring identity. Catalog
   precisely which operation preserves that quotient and when
   subsequent updates force it to expand.
5. **The parameter that matters.** The direct Sudoku network has
   `M = Theta(N log N)` Boolean edges for `N` cells. A hypothetical
   `2**o(M)` network result is not automatically `2**o(N)`.
   Keep input cells, edges, vertices, precision, intermediate bits,
   and refusal/non-refusal separate.

## Future bibliography maintenance

For every added citation, record: (a) the exact theorem/identity being used;
(b) repository implementation and test path; (c) whether the connection is
direct, adjacent or open; (d) the quantity controlled (correctness,
state count, arithmetic operations, bit operations, memory, or
representation rank); and (e) a counterexample or missing hypothesis.
This prevents a long reference list from becoming an accidental proof.
