# Worst-case inputs and complexity costs

**Research note | Updated 14 November 2026 | Status: adversarial test plan and polynomial-overhead reduction agenda; not proved worst-case families**

## Scope

Identify the inputs and internal states that maximize **total exact counting cost**, and distinguish (a) genuine structural difficulty, (b) pathological overhead of the published construction, and (c) unfinished execution in the independent Rust port. Do not call a smaller matrix, a faster kernel, or a lower asymptotic upper-bound constant an optimization unless **complete cost** improves against an appropriate exact #SAT baseline.

Two different routes must be tracked separately:

1. **Global rational interpolation (body):** auxiliary dimension `D = r^(2Q)`, measurement signatures, degree `R`, Taylor order `q`, Boolean Möbius terms, Hermite interpolation. This is the weaker asymptotic route.
2. **Recursive two-adic tensor contraction (appendix):** bounded-degree tensor-network encoding, packet construction, local interpolation, modes, modular precision, recursive child networks, and direct-sum leaves. This supplies the sharper bounded-density asymptotic claim. It is **not** just the global matrix construction accelerated.

The present `eth-disproof-rust` main branch does not execute the complete source-defined nonterminal counting program. Thus current measurements of auxiliary prototypes or a bounded brute-force oracle are not runtime measurements of the complete Lean-defined algorithm.

## Principal cost drivers

| Priority | Stressor | Why it matters | Status of claim |
|---|---|---|---|
| P0 | **Pre-asymptotic parameter ineligibility** | The appendix fixes `r=64`, `epsilon=1/131072`, `u_0=floor(epsilon*ceil(log2 s))`, and stringent packing inequalities. Normal-size inputs fail the sufficient recursive regime and fall to a finite direct branch in the mathematical presentation. | **Directly from explicit proof parameters**; not a universal lower bound against tighter parameters |
| P0 | **Many nonzero cross-group modes at high precision** | Each mode tuple with total weight `< p_t` may spawn up to 64 child contractions. Weak valuation pruning plus densely populated packets can make recursive branching enormous. | **Stress hypothesis**; the paper gives an upper bound, not a matching worst-case lower bound |
| P0 | **Large leaf after unsuccessful partition/recursion** | The designated leaf threshold is `H=ceil(s/floor(sqrt(ceil(log2 s))))`. Direct summation can inspect `2^H` edge assignments at a leaf, before tensor-entry work. | **Exact algorithmic branch cost**; preprocessing may eliminate or simplify special inputs |
| P1 | **High-width, strongly coupled bounded-density formulas** | Expansion/high treewidth frustrate ordinary decomposition and can keep tensor networks and cross-group dependencies large at every level. | **Adversarial benchmark hypothesis**, not a proof these are worst for OAI's new method |
| P1 | **Dense/high-incidence CNFs invoking the general reduction** | Sparsification/branching, sparse parity tests, multilinearized factors, and `O(n log log n)`-wire encodings can dominate the fixed-density route. | **Directly identified stages**; instance-by-instance blowup needs measurement |
| P1 | **Huge “polynomial-time” setup factors** | The appendix sets extension degree `e=4 lambda`, searches up to `2^e` binary polynomial candidates and tests divisors through degree `e/2`. A literal nested search has a crude worst-case `s^6`-scale trial envelope before lower-level arithmetic. | **Direct from stated construction**, not a necessary finite-field cost |

### Parameter example: one million edges

At `s = 10^6` edges, `lambda = ceil(log2 s) = 20`, so the appendix's `u_0 = floor(20/131072) = 0`. The displayed leaf threshold is `H = ceil(10^6 / floor(sqrt(20))) = 250,000`. Merely running a direct `2^H` leaf is not remotely practical; the published quantitative assumptions also do not authorize running the active recursive construction at this scale.

The appendix further imposes `u >= lambda^(4/5)` throughout active recursion. A **necessary** scale for the root's nominal `epsilon*lambda` to be at least `lambda^(4/5)` is `lambda >= (131072)^5 = 2^85`, before any packing and other constraints. This exhibits how conservative the **stated sufficient schedule** is; it is not proof that no better finite-size schedule exists.

## Resource costs by stage

| Stage | Formula or limiting mechanism | Worst-case signal to measure | Avoidable vs intrinsic |
|---|---|---|---|
| CNF -> tensor network | Clause/equality trees + bipartite subdivision; `s = O_k(n+m)` | Encoded edges per original variable `s/n`, vertex degrees, duplicate equality wires | Encoding overhead partly avoidable; high connectivity is structural |
| Fixed-density branch | `P_0=n+1` for exact count modulo `2^(n+1)` | Network edges, actual entry cost, decomposition width | Precision `n+1` is a sufficient exactness budget for arbitrary counts in `[0,2^n]` |
| Coefficient field construction | `e=4 lambda`; at most `2^e` candidate polynomials, each tested against monic divisors of degree at most `e/2` | Count candidate trials, divisor trials, setup bit operations; note this can be `s^4`-to-`s^6`-scale in the literal search | Replace literal enumeration with a certified irreducible polynomial constructor; preserve deterministic correctness |
| Packet packing | `L=2^a`, `D_arr=64^(2a)`, `a=2 sum_{j<=d}u_j`; `M >= 2 D_arr^2 Delta`, `M >= L D_arr`, `2L <= Delta` | Packet utilization, collision slack, port imbalance, feasibility failures | Proof slack may be reducible, but replacement needs certified packing |
| Node interpolation | `deg F <= M(2L-1)`; up to polynomially many interpolation evaluations | Active nodes, per-node interpolation values and Taylor multiplicities | Can optimize weights and evaluate only required jets, without changing identities |
| Precision | `p_t = p + 8hD_t + 8M(a+1)` with `h=ceil(3M/u)`, `D_t=L/2^{v_2(t)}` | Bit width at each node; amount of precision spent on canceled terms | Sufficient bound may be loose; any reduction needs a recovery certificate |
| Crossing modes | `sum_Z w_Z beta_Z < p_t`; count bounded by `exp(O(sqrt(M p_t / D_t)))` | Actual admissible beta tuples, zero coefficient rate, number of nonempty children | Avoidably enumerated zero terms; many nonzero terms may be intrinsic to this representation |
| Implicit packet entries | Generic expansion `exp(O(L log s))` | Nonzero monomials, intermediate coefficients, valuations, cache misses | Sparse/truncated exact multiplication is plausible engineering gain |
| Leaves | Direct enumeration `2^H`, `H=ceil(s/floor(sqrt lambda))` | Actual leaf edge count, contraction work per assignment | Can dispatch to independent exact counting methods with separate correctness evidence |
| Global interpolation, separately | `D=r^(2Q)`, `q=floor(d_H/Q)`, `C_q=sum_{j<=q}2^j binom(n,j)`, measurement signatures at most `(2D+1)^c` | `log2 C_q`, reachable signatures, factor evaluations, total exact bit operations | Optimizing rank alone does not address reconstruction |
| End-stage source machine | Source-defined QueryStream/high/leaf/DFS and primitive TM correspondence are unfinished in Rust main | First nonterminal source-defined count, instruction totals, independent Lean trace equality | **Functional blocker**, not a hard-input complexity measurement |

**Important mathematical distinction:** The expressions above are the paper's *cost bounds or sufficient parameter conditions*. They are not automatically attained lower bounds. A benchmark that stresses one term is not proven to maximize total algorithm cost.

## Reducing polynomial overhead without changing the counting claim

**Boundary:** speedups must reduce complete exact-counting work on a runnable, source-correlated implementation. A lower asymptotic polynomial factor, a faster isolated kernel, or fewer field elements stored is not a demonstrated end-to-end gain. Do not mix the **body's global rational interpolation** with the **appendix's two-adic tensor recursion**. The current Rust `main` is not yet a complete nonterminal implementation of the latter or of the Lean-defined query program.

### Prioritized overhead map

| Priority | Stage | Published bound / work | Concrete reduction | Proof and benchmark gate |
|---|---|---|---|---|
| **P0: safe** | Coefficient-field setup | `e=4 ceil(log2 s)`, up to `2^e` degree-`e` candidates, tested against monic divisors through degree `e/2`. Literal search permits a crude `s^6` trial-pair envelope, excluding polynomial arithmetic. | Use a verified, version-pinned irreducible polynomial for the required `e`, or an independently implemented construction algorithm with an irreducibility certificate. Cache by field degree and representation; never enumerate the full candidate space in production. | Verify irreducibility over `F_2`, exact field operations, unit inversion, deterministic replay and **total initialization time**. |
| **P0: safe if dimension bound is proved** | Field extension degree | `e=4 ceil(log2 s)` ensures at least `s^4` residue-field elements, far more than many actual nodes need. | Choose one global `e` satisfying `2^e >= max_node (M(2L-1)+1)` under a **certified upper bound for all reachable nodes**, while keeping the same coefficient field along recursion. | Prove all required interpolation points have pairwise unit differences; regression test the original and smaller fields on the same contracted networks. Do not silently change fields inside a recursive call. |
| **P0: safe** | Hermite / Lagrange reconstruction | Repeated interpolation at many nodes with degree up to `K-1`, `K=M(2L-1)+1`. | Precompute reused nodes, products and weights; use product trees and exact fast polynomial arithmetic in an existing validated library. | Match exact coefficients and final residues. Count all modular multiplications, allocations, and precompute time, including cases with `K` small enough that naive interpolation wins. |
| **P1: safe after exact differential tests** | Implicit packet tensor entries | Generic product expansion admits `exp(O(L log s))` time per entry. **This is subexponential, not polynomial overhead.** | Sparse requested-coefficient extraction, weighted-degree truncation, early discarding of coefficients with certified valuation `>= p_t`, memoized immutable packet-local subproducts. | Compare exact entry residues at creation precision and later canonical lifts. Measure **nonzero coefficients, extracted terms, cache misses, total work**, not only one fast kernel. |
| **P1: proof required** | Tapered Hermite precision | `p_t=p+8hD_t+8M(a+1)`, `h=ceil(3M/u)`, `D_t=L/2^{v_2(t)}`. | Precompute exact valuations of rational recovery weights; propagate a smaller per-node or per-jet precision where independent error bounds certify it. | Prove final residue remains correct modulo `2^p`, including inherited precision, odd-unit inverses, canonical lifting and cancellation. Stress at all-odd/zero/power-of-two tensors. |
| **P2: research, not drop-in** | Need only early Taylor coefficients | Appendix reconstructs a polynomial from `K` distinct evaluations although tapered recovery retains only `q_t=h max(0,u-v_2(t))` jets. | Investigate direct evaluation in `A_{p_t}[z]/(z^{q_t})`, potentially eliminating evaluation/reconstruction of unused high coefficients. | Prove the mode identity, inversions, coefficient extraction, and canonical lifts commute with truncated jet arithmetic. Differentially compare every retained coefficient and total child-call count. **Not automatically valid.** |
| **P2: constrained optimization** | Parameters and packet packing | Fixed `r=64`, `epsilon=1/131072`, `L=2^a`, `D_arr=64^{2a}`; sufficient inequalities often fail at practical `s`. | Search finite-size admissible tuples; tighten the packing lemma, if needed, without sacrificing child-size or precision invariants. | Exact verification of `M>=2 D_arr^2 Delta`, `M>=L D_arr`, `2L<=Delta`, child `M_child<=M/8`, valuation bounds and all other prerequisites. New weaker conditions require a new proof, not a benchmark alone. |

### Exact quantitative observations

**Field search.** For `s=10^6`, the paper sets `lambda=20`, `e=80` and `2^e=2^80` *possible* candidate polynomials. This is a **search-space size**, not a measured or necessary run count. With naive trial divisibility up to degree 40, the total pairs considered in a pessimal literal implementation can scale roughly as `2^80 * 2^40 = 2^120 ~ s^6`, before arithmetic cost. A certified field representation removes this artificial setup search without changing the characteristic-2 residue-field model.

**Point requirement.** The appendix states that a node's full-polynomial interpolation uses

`K = M(2L-1)+1`

points; it retains `q_t = ceil(3M/u) max(0,u-v_2(t))` coefficients at nonzero node `t`. If all points lie in one fixed residue field of order `2^e`, the simple sufficient condition is `2^e >= K_max` with a *proved* global `K_max`. Field arithmetic is polynomial in `e` and `p`, not in the number `2^e` of field elements. A smaller `e` is useful only if it preserves every required distinct-residue point.

**Fast interpolation.** Product-tree interpolation changes the algebraic work from quadratic in `K` to approximately `O(Mul(K) log K)` field operations, where `Mul(K)` denotes the cost of multiplying degree-`K` polynomials. It does **not** eliminate the `K` distinct **recursive evaluations** in the existing identity. Only a proven direct-jet scheme could alter that call count.

**Precision.** If the final recovery is an exact linear combination `F(0)=sum_{t,j} w_{t,j} a_{t,j}`, and **if** the jet coefficients are integral and supplied with independent residue errors, it is sufficient to retain at least `p + max(0,-v_2(w_{t,j}))` bits of each `a_{t,j}`. This observation alone is *not* an admissible replacement for the paper's recursive precision schedule: the interpolation denominator, child-level errors and entrywise canonical lifts must also be accounted for.

**Subexponential core.** The weighted-mode cost `exp(O(sqrt(M p_t / D_t)))`, the recursion tree, the packet-entry cost `exp(O(L log s))`, and the leaf `2^H` remain after polynomial-kernel optimization. Do not relabel them as polynomial or claim they have been removed.

### Proposed execution sequence and gates

1. **Make field setup negligible and reproducible.** Pin a certified binary irreducible polynomial; implement certified selection of minimal global degree; compare initialization and complete counting time. Accept only if it preserves exactness and is no slower overall on the tested workload.
2. **Optimize reconstruction arithmetic without changing recursive calls.** Reuse point sets and exact weights, and apply fast interpolation selectively. Compare against a naive implementation using identical field arithmetic and count *all* setup operations.
3. **Instrument packet coefficients and precision simultaneously.** Identify the actual dominant cost on dense-crossing synthetic tensors and bounded-degree connected CNF networks. Implement sparse extraction only when the retained coefficient support is genuinely smaller than brute expansion.
4. **Prototype truncated-jet recursion separately.** Start with one active node with independently known contraction. Require equality of every required jet and exact residue, including adversarial valuation cases. Reject if extra jet bookkeeping and child work outweigh avoided evaluations.
5. **Only then revisit parameter lemmas.** The published sufficient schedule is overwhelmingly pre-asymptotic. A smaller admissible schedule is valuable, but it must retain a defensible finite-size correctness and resource theorem.

### Revised profiling ledger for every benchmark

Add the following fields to the existing per-instance ledger:

`field_degree; field_polynomial_sha256; irreducibility_certificate; field_setup_ns; interpolation_points_K; interpolation_jet_orders_qt; interpolation_weight_cache_hits; interpolation_multiplications; child_calls_at_interpolation_points; requested_packet_coefficients; materialized_packet_coefficients; dropped_terms_by_val; packet_cache_hits; precision_requested_bits; precision_used_bits; unit_inversion_count; modular_mul_limb_ops; time_by_stage_ns; peak_bytes_by_stage; total_bit_operation_proxy; exact_final_residue; baseline_count; baseline_total_ns; budget_decision`.

Compare `T_total` under **the same input and hardware** for the unchanged baseline and every proposed optimization. Include preprocessing, field initialization, tensor construction, all recursive children, arithmetic, interpolation, and leaves. Test easy instances as negative controls, bounded-degree expanders as structural stress tests, and synthetic dense-crossing networks as arithmetic stress tests. Record `unsupported`, `guarded_refusal`, `timed_out`, and `wrong_answer` separately.

### Evidence required to revise the complexity assessment

- A complete source-correlated, nonterminal counting path with a reproducible resource ledger; **or** an explicitly separate faithful implementation of the appendix. Do not confuse either with the bounded exponential oracle.
- One or more **whole-pipeline speedups**, including field setup and all recursive work, with exact output parity and repeatable benchmark receipts.
- A rigorously justified reduction in actual recursive evaluation count, admissible precision, packet expansion complexity, or packing requirements. These are more significant than a faster polynomial subroutine by itself.
- A cost-based dispatcher that refuses the purported general method whenever conventional exact counting is demonstrably cheaper, without claiming that this establishes a better worst-case complexity theorem.

## Reproducible adversarial instance families

### T1. Bounded-degree expander Tseitin, consistent and inconsistent

Generate a seeded connected 3-regular graph `G=(V,E)` with even `|V|`. Introduce one Boolean variable per edge. At each vertex, assert XOR of its three incident edge variables equals a prescribed charge; convert the parity condition to four 3-CNF clauses. This gives `n=|E|`, `m=4|V|`, bounded clause density and bounded occurrence. On a connected graph:

- If the XOR of the charges is `0`, the exact count is **`2^(|E|-|V|+1)`**.
- If the XOR of the charges is `1`, the exact count is **`0`**.

This gives a large, independently computable correctness oracle. Record actual graph expansion/treewidth proxies and do **not** label a seeded random regular graph a certified expander without checking. These families are hard for some resolution-based systems, but are easy under Gaussian elimination. They test whether the proposed contraction is structurally efficient and whether the pipeline sensibly recognizes linear algebra.

### T2. Bounded-occurrence random and planted 3-CNF around the threshold

Choose fixed seeds and `m/n` in `{3.5, 4.2, 5.0}`, with near-regular literal incidence and no tautological or duplicate clauses. Maintain both unplanted and planted-solution variants. Planted instances are guaranteed satisfiable, **not** known to have one or few solutions. Independently count small cases; for larger cases use trusted external exact counters and compare receipts. Measure actual network expansion, nonzero mode count, recursive branching, and true wall time. This is a **candidate stress family**, not a proved worst case for OAI.

### T3. High-incidence and high-density CNFs

Use fixed-size CNFs with a few hub variables versus near-regular variable incidence, and increasing `m/n` and distinct scope complexity. Compare identical `n,m,k` when possible. Track branching on frequently used variables, parity-test count, monomial count, scope size, incidence duplication, and wire growth in the general dense route. A hub may make a formula *easier* after conditioning, so report post-preprocessing size, not just raw density.

### T4. Dense, nonzero synthetic tensor networks

Create bounded-degree bipartite networks with seeded, dense local tensor tables over `Z/2^p Z`, choosing many odd entries. Force a broad spread of packet orientations and nonempty crossing tiles where admissible. At small scales, compare contraction against independent exhaustive edge summation; at larger scales, stop on a resource budget and retain the partial ledger. This isolates mode multiplicities, coefficient extraction, and packet packing from SAT preprocessing. It does **not** establish that any CNF encoding realizes the same worst-case tensors.

### T5. Precision and cancellation stress

Use paired networks with the same graph but different local values, including all-odd entries, exact zero contractions, and large powers-of-two factors. Check that child precisions, canonical lifts, and tapered Hermite recovery produce identical residues to an independent high-precision calculation. The goal is to reveal wasted precision and incorrect truncation, not to assume canceled final sums are computationally hard.

### Controls that must be cheaper, not harder

- **Path independent-set CNF:** `and_{i=1}^{n-1} (not x_i or not x_{i+1})`, with exact count `Fib(n+2)`. This has a linear-time dynamic-programming oracle. Expensive algebra here is avoidable algorithmic overhead.
- **Disconnected components:** exact count is the product of component counts; tests preprocessing and cost-based dispatch.
- **Trivial UNSAT and tautologies:** test early exact simplification.
- **Treewidth-bounded CNF:** independently verify against junction-tree or variable-elimination counts.

Tseitin and path families deliberately test *different* weaknesses: structural hardness for standard decompositions versus avoidable overhead of the proposed general machinery.

## Worst-case criteria

Store **both absolute cost and competitive cost**. For a family `F_n`, compare observed total work `T_A(F_n)` with the best justified available baseline `T_best(F_n)` among exhaustive count, connected-component decomposition, exact variable elimination, parity/linear-algebra counting, and a vetted #SAT solver. A useful benchmark objective is the worst observed ratio `T_A/T_best`, accompanied by raw wall time, exact operation counts, and peak memory. Do not claim a worst-case time lower bound for OAI from failure on a heuristic instance.

For each instance, record:

`instance_sha256; family; seed; n; m; k; exact_count_oracle; field_setup_trials; variable_occurrence_max; primal/incidence graph stats; preprocessed_n,m; encoded_edges_s; initial_precision; Q,R,r or tensor (u,a,L,D_arr,H); nodes_by_depth; admissible_modes; nonzero_modes; tensor_entry_evaluations; actual_child_calls; precision_bits; leaf_assignments; bit_operations; wall_time; peak_RSS; outcome/timeout; source_revision; compiler_revision; host.`

Use deterministic seeds, fixed hardware/runtime limits, exact counts when feasible, and reproducible trace receipts. Report unsupported/unavailable separately from timeout or wrong answer.

## Optimization acceptance criteria

1. **Correctness first:** small-instance exact counts and all intermediate identities agree with independent verification. No silent fallback from the source-defined machine to exponential counting.
2. **Complete cost accounting:** any claimed win must include preprocessing, encoding, mode enumeration, all child calls, precision, interpolation and leaves. Report `T_total`, not only rank or kernel speed.
3. **Use easy controls as a veto:** if a new general scheme slows down paths, components, parity systems, or trivial formulas, the dispatcher must prefer the simple exact method.
4. **Use hard connected families for scaling:** increase `n` and track both the effective slope of `log2 T(n)` and the finite crossover with baselines. Do not infer an exponent from one or two small inputs.
5. **Keep proofs separate:** practical acceleration, faithful execution of the appendix, equivalence to the original Lean source-defined machine, and the ETH complexity theorem are four different claims.

## Next experiments

**First:** complete a source-defined nonterminal counting path or an explicitly independent, faithful appendix implementation; instrument the full cost ledger. Without that there is no measured worst case for the actual algorithm.

**Second:** build T1 (parity expander, known exact count), T2 (random/planted bounded-degree CNF), and the path negative control. Use the same seeds and canonical CNF hashes for every revision.

**Third:** remove certified polynomial overhead in this order: finite-field construction and field size, reused interpolation arithmetic, then sparse packet coefficient extraction. Run T4/T5 to identify whether the actual leading cost is mode count, packet expansion, precision, or interpolation calls. Demand a full end-to-end improvement before accepting code.

**Fourth:** investigate direct truncated-jet recursion and exact valuation-based precision only as proof-gated research. Evaluate whether finite-size certified parameters satisfy all packing, interpolation and precision inequalities without the published asymptotic safety margins. A failure should be documented as a proof-schedule limitation, not mistaken for evidence that the theorem is false.

## Sources and scope notes

- [OAI full preprint source](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex), retrieved blob SHA `f7af85e623b58e0ca9f4b9416916d442defa963a`.
- [Quantitative tensor contraction appendix](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex), retrieved blob SHA `51ba54efc29f51bbc0426f848003030da484f354`.
- [Sharper reduction](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-reduction.tex), retrieved blob SHA `80389ac39d987133b71b2ddc2593e6fcdd99871a`.
- [Dias & Lima, *Limits and Constants of OpenAI's Claimed ETH Refutation*](https://arxiv.org/abs/2611.00517), independent analysis of finite-size constants and restrictions of the clause-product interpolation cost model; its results do not prove failure of the sharper route.
- [Itsykson, Riazanov & Smirnov, *Tight Bounds for Tseitin Formulas*](https://doi.org/10.4230/LIPIcs.SAT.2022.6), hardness for particular proof/representation systems, **not** a hardness theorem for OAI's contraction.
- [Independent Rust repository's evidence ledger](https://github.com/laurajoyhutchins/eth-disproof-rust/blob/main/eth/docs/evidence.md), retrieved blob SHA `5b6585d1efcb6ddc0cbebc0dd34c873945ecf578`.

**Current conclusion:** No explicit CNF family is proved to maximize the runtime of OAI's claimed algorithm. The clear worst *proof bottlenecks* are pre-asymptotic admissibility, mode branching, packet expansion, precision, and large leaves. The next useful result is an experimentally witnessed, end-to-end bottleneck on a connected bounded-density input, with independent exact count and total-cost evidence.