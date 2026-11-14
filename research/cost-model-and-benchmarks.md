# Full-pipeline cost model, adversarial families and acceptance experiments

**Purpose:** reject hidden exponentials, separate mathematical work from implementation overhead, and find the first complete **source-defined** algorithmic bottleneck. See the [detailed parameter study](../rust/lean_eth_reference/docs/worst-case-and-polynomial-overhead.md) for derivations of the source bounds.

## The accounting unit is the whole exact counter

For each input \(x\), record a *cost vector*, not one scalar elapsed time:
\[
C(x)=(T_{\rm setup},T_{\rm encode},T_{\rm packet},
T_{\rm interpolation},T_{\rm modes},T_{\rm child},
T_{\rm leaf},T_{\rm reconstruct};
B_{\rm arithmetic},S_{\rm peak},R_{\rm refusals}).
\]
Distinguish wall time, exact arithmetic operations, total operand-bit work, allocated bytes and **simultaneously retained** bytes. A mathematically better asymptotic exponent requires a bound on all stages in the stated cost model. A fast Cython/Rust/FLINT microkernel is not a non-exponential theorem. Cached results must include their construction and verification cost for an uncached first run, and separately report amortized subsequent runs.

A useful machine-readable per-run record has: source/git/toolchain pins; formula generator/version/seed; \(n,m,k,s\); preprocessing expansion; active schedule and reasons for refusal; packet parameters; width/treewidth estimate; \(P_0,p_t,K,q_t\); visited modes, nonzero modes, mode-weight histogram; child depth and calls; live coefficient counts and max bit width; leaf work; output count and independent oracle; time and peak resident bytes. Report “not observed” for unavailable counters, never zero.

## Source parameter hazards

- **Root scheduling:** \(\epsilon=1/131072\), \(r=64\), \(u_0=\lfloor\epsilon\lceil\log_2s\rceil\rfloor\). Many attainable instances have \(u_0=0\). A paper-admissible regime is not the same as a finite practical implementation.
- **Packet growth:** \(D_{\rm arr}=64^{2a}\), \(L=2^a\); packing demands \(M\ge 2D_{\rm arr}^2\Delta\), \(M\ge LD_{\rm arr}\), \(2L\le\Delta\).
- **Leaf threshold:** \(H=\lceil s/\lfloor\sqrt{\lceil\log_2s\rceil}\rfloor\rceil\) (when defined) can make direct \(2^H\) work enormous.
- **Field construction:** a literal search over \(2^e\) candidate degree-\(e\) polynomials with divisibility checks introduces a large polynomial *in \(s\)*, not an exponential in \(s\), because \(e=4\lceil\log_2s\rceil\). The naive trial-pair envelope can be roughly \(s^6\). A certified polynomial/irreducibility constructor can attack this without weakening the theorem.
- **Hermite and modes:** \(K=M(2L-1)+1\) evaluations may dominate node cost; the admitted weighted mode count has a subexponential envelope and may generate many children at high \(p_t\). Reusing weights cannot eliminate required child evaluations.
- **Exact bit complexity:** the fact that the *final* count fits in \(n+1\) bits does not bound intermediate rational denominators, ring lifts, factor tables or recursive workspace size.

A proposed improvement must state whether it decreases the number of *original mathematical calls*, the algebraic operation count per call, the bit complexity per operation or only the implementation constant. Never blur those categories.

## Input families (none is certified worst-case)

| Family | Construction and known answer, when simple | Stress target and countercheck |
| --- | --- | --- |
| Empty, contradictory, unit, unused-variable CNFs | Immediate counts \(2^n\) or \(0\), carefully tracking declared unused variables | Frontend/refusal/terminal consistency; no evidence of hard recursion |
| Complete bipartite OR CNF \(B_k=\bigwedge_{i,j=1}^k(x_i\lor y_j)\) | Exactly \(2^{k+1}-1\) assignments among \(2k\) variables | Dense elimination/scope without intrinsic hard count; check that the exact solver does not use exponential factor tables unnecessarily |
| Rectangular grid constraints | Recover count from independent row-transfer DP \(2^{O(\sqrt n)}\operatorname{poly}(n)\) | Cross-row coupling, width and input geometry; **not** a hardness lower bound |
| Affine / XOR-derived 3-regular incidence families | Count by independent Gaussian elimination over \(\mathbf F_2\) when appropriate | Dense source representation versus easy algebraic count; ensure reduction preserves #SAT exactly |
| Seeded bounded-degree/high-expansion 3-CNF | Use certified exact solver for small cases, return “unknown” when oracle limit reached | Cross-group modes, recursion depth, packet collisions and negative cases |
| High-occurrence CNF with duplicates/tautologies | Validate count-preserving simplification and multiplicity | General-density preprocessing/sparsification and large coefficient transfer |
| Hand-constructed packet tensors with alternating signs/valuations | Exact quotient-ring oracle on tiny networks | Precision loss, zero-mode pruning, interpolation inverses and within-group coupling |
| Mutated source-structure fixtures | Known expected refusal | Wrong head label, swapped ports, unsupported constructor, erased-proof misuse, nonunit division, hidden finite fallback |

Seeded random instances are for discovery and regression; do not generalize from them to an asymptotic worst-case theorem. Keep the direct exact solver as an **independent oracle only**, never as the implementation path under test.

## The measurement protocol

1. **Correctness first.** Pin the original Lean definition/fixture, input canonicalization and expected count. Check small instances with a separately implemented exact solver and enumerate only within a declared resource limit.
2. **Separate admissibility.** State whether the proof's quantitative prerequisites actually hold for this input. Report inactive recursion and source-level branch choice. Do not substitute smaller “engineering” parameters without a new proof.
3. **Two independent producers.** Run source Lean and generated Rust when both are actually supported, comparing every ABI output and relevant physical state; a Rust oracle comparing to itself does not count.
4. **Instrument full composition.** Include packet construction, field/precision setup, mode generation, child calls, interpolation, final lift/recovery, teardown and memory. Freeze source and code revision and run uncached as well as warmed.
5. **Baseline fairly.** Include trivial algebraic counts for special families, row DP for grid, Gaussian elimination for affine cases, and a widely used exact #SAT solver for bounded realistic instances. Count preprocessing and conversion costs in both methods.
6. **Adversarial and negative tests.** Force boundary modes at weight \(p-1,p\), nonunit interpolation point differences, zero/canceling coefficients, high precision, shared-object writes, incomplete source graph and timeouts.
7. **Publish refusal and failure data.** Record first divergent state, smallest counterexample, compiler error and source-dependent limitation. Avoid quietly dropping hard instances from plots.

## Optimization pass/fail

**Pass (local):** source-preserving identity or kernel equivalence, exact differential tests and a statistically credible reduction in its measured isolated cost. Label it “local” and report total cost unchanged if that is the case.

**Pass (end-to-end):** one complete accepted source-defined nonterminal count; full exact result; all invariants satisfied; total bit work, peak memory and time improve on a disclosed family with no hidden \(2^{\Omega(n)}\) preprocessing or fallback. Further distinguish empirical performance from a theorem.

**Pass (asymptotic):** a Lean-checked or equally rigorous cost recurrence proves the new whole-pipeline bound with all field, tuple, precision, packet and recursion parameters represented. A bounded benchmark alone cannot establish this.

**Fail:** unsupported code paths masquerading as count success, silent paper-schedule changes, exponential auxiliary tables, denominator/precision assumptions without witnesses, cherry-picked fixture-only optimizations, or invalid factorization across coupled group components.

## Practical priority

First complete the source query/count program and differential acceptance; then measure the actual dominant stage. In parallel, proofs can eliminate needless *polynomial* overhead (certified field setup, shared interpolation products, O(1)-state tuple iterators) without claiming they improve the exponent. Only after an active end-to-end recurrence exists should the higher group-action or direct-jet proposals be treated as replacement algorithms.
