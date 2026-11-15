# Full-pipeline cost model and benchmarks

An improvement to matrix rank or Hermite interpolation is an end-to-end optimization only when it reduces the cost of the **complete exact count**, including setup and reconstruction.

## Cost decomposition

For a formula \(x\), separate

\[
T(x)=T_{\rm encode}+T_{\rm field}+T_{\rm packet}
+T_{\rm interpolate}+T_{\rm modes}+T_{\rm children}
+T_{\rm leaves}+T_{\rm recover}.
\]

Alongside time, track arithmetic **bit operations**, the widest intermediate coefficient, retained coefficients, recursive calls and *peak simultaneous memory*. A final count may fit in \(n+1\) bits while its intermediate rationals do not.

An optimization needs to name the term it changes. Deleting an \(O(D)\)-sized iterator pool does not delete its \(D\) tuples. Faster multiplication does not delete the child contractions.

## Source parameter schedule

The appendix's sufficient schedule includes

\[
\epsilon=2^{-17},\qquad u_0=\left\lfloor
\epsilon\lceil\log_2s\rceil\right\rfloor,\qquad
D_{\rm arr}=64^{2a},\quad L=2^a.
\]

The packing conditions require, among other things,

\[
M\ge2D_{\rm arr}^{2}\Delta,\qquad
M\ge LD_{\rm arr},\qquad 2L\le\Delta.
\]

For \(s=10^6\), \(u_0=0\). With \(\lambda=20\), the nominal direct leaf contains \(H=250{,}000\) edge variables. Its \(2^H\) enumeration is beyond practical reach. This says the *published sufficient schedule* is punishing, not that a tighter mathematically valid one is impossible.

Before timing the recursive stages, check that the chosen schedule actually
admits recursion. The fixed appendix schedule cannot activate its root on
any `u128` edge count, since `lambda <= 128` gives `u_0 = 0`.
Run `cargo run --locked -p lean-eth-reference --bin appendix-admission -- 1000000`
to record the exact refusal and nominal leaf exponent; exit code 2 is
intentional. This is **not a benchmark or a contraction implementation**.

Any alternate finite-size schedule must have its own verified packing,
child-size, valuation and recovery conditions before its runtime is compared
with an independent exact #SAT baseline.

Retuning the original root's \(\varepsilon\) does not rescue this
schedule by itself. The first packing inequality with \(M=s\),
\(\Delta=\lceil s^{9/10}\rceil\) and \(u_0\ge1\) already requires
\(s\ge2^{490}\) at \(r=64\). A degree-aware candidate may meet
the three arithmetic packing inequalities while failing the separate
\(u\), child-invariant, recovery, and complexity requirements.
See [root-packing feasibility](root-packing-feasibility.md) for the
exact proof and CLI receipts. Such receipts are refusals, **not** runtime
benchmarks.

The [matching-potential packing argument](matching-potential-packing.md)
replaces the *sufficient* quadratic-in-label-class collision requirement
with a deterministic condition proportional to \(D_{\rm arr}\Delta\log D_{\rm arr}\).
This reduces a real polynomial factor of setup but **does not** remove
the independent field, weighted-mode, packet-entry, precision, or leaf
costs. The full recursive count remains unexecuted.

The [multi-level depth gate](two-adic-depth-gate.md) is an additional
independent acceptance condition. At `r=64` and any `u128` root,
the source leaf cutoff makes all second-generation children direct
leaves; at `lambda<=120`, even the first child is a leaf.
This is a mathematical bottleneck in the full recurrence, not a
packing kernel performance issue. The `appendix-depth` audit records
conditional child upper bounds without simulating a #SAT count.

Five places worth instrumenting first:

| Stage | What to record |
| --- | --- |
| Field setup | \(e=4\lceil\log_2s\rceil\), candidate/divisor trials and actual bit work |
| Packets | \(L\), \(D_{\rm arr}\), collisions, live monomials, coefficient sizes |
| Interpolation | \(K=M(2L-1)+1\) calls, jet order, reused weights |
| Modes/children | Admissible and nonzero mode tuples, depth, child calls, precision \(p_t\) |
| Leaves | Actual size \(H\), direct assignments visited, retained memory |

A literal irreducible-polynomial search can have an \(s^4\)-scale candidate space and a crude \(s^6\)-scale trial-pair envelope before polynomial arithmetic. This is **large polynomial** setup work, not \(2^{\Theta(s)}\); \(e=O(\log s)\). Replace it with a certified construction, not with a randomly chosen polynomial.

The mode envelope \(\exp(O(\sqrt{Mp_t/D_t}))\) and packet-entry bound \(\exp(O(L\log s))\) are **subexponential** costs, not polynomial overhead.

For full derivations, see [Worst-case stressors and polynomial overhead](../rust/lean_eth_reference/docs/worst-case-and-polynomial-overhead.md).

## Test input families

### 1. Complete bipartite OR formulas

\[
B_k=\bigwedge_{i=1}^{k}\bigwedge_{j=1}^{k}
(x_i\lor y_j).
\]

For \(2k\) variables its count is

\[
\#B_k=2^{k+1}-1.
\]

Why? Either all the \(x_i\) are true and every \(y_j\) is free, or at least one \(x_i\) is false and all \(y_j\) must be true. A dense elimination order may still materialize \(2^k\) entries. The example distinguishes elimination-induced table growth from the complexity of computing the count itself.

### 2. Grids

A row-transfer dynamic program gives a \(2^{O(\sqrt n)}\operatorname{poly}(n)\) baseline for appropriately encoded grids. A grid minor or large treewidth alone does not prove that the new method is hard. Measure its actual coupling and compare with the row DP.

### 3. Affine formulas

Use XOR-derived or linear systems whose counts are independently computable by Gaussian elimination over \(\mathbf F_2\). They expose whether expensive preprocessing is manufacturing difficulty from algebraically easy inputs. Check that every encoding preserves the original count.

### 4. Coupled and high-expansion cases

Generate bounded-degree incidence graphs with fixed seeds, plus tiny hand-built tensors with zero, negative and high-valuation entries. These stress routing, mode pruning, cancellation and precision. An exact solver supplies small-instance answers; beyond its resource limit the reference answer is **unknown**, not zero.

Also keep contradictory, empty and tautological CNFs as low-cost frontend tests. Mutation tests should swap ports, change a cutoff at \(p-1/p\), introduce nonunit interpolation differences and attempt a hidden finite fallback.

## Measurement protocol

For each input, pin the generator seed, CNF hash, source Lean Git revision, toolchains and actual Rust head. Record \(n,m,s\), branch admissibility, preprocessing expansion, full stage timings, arithmetic bits, peak live memory and exact count. Record the first divergent state when independent Lean/Rust traces differ.

Measure **cold** construction and cache-warmed execution separately. Include conversion and preprocessing in both the new method and the baseline.

Use the right baseline for the family: closed-form count for \(B_k\), row DP for a grid, Gaussian elimination for affine systems, and an independently implemented exact #SAT solver for general small CNFs. Do not use the solver under test as its own oracle.

## Evaluation criteria

**A local speedup:** the source-equivalent kernel is faster on a declared family. Record the measured total cost, even if unchanged.

**An end-to-end speedup:** one complete original-source nonterminal count is correct and measurably cheaper in total bit work, wall time or memory on disclosed inputs, with no hidden exponential table.

**A better asymptotic algorithm:** the *whole* cost recurrence is proved with its field setup, precision, packet expansion, modes, children and memory accounted for. No finite benchmark proves this claim.

The immediate priorities are a working source-defined recursive execution path and certified reductions in setup cost. Performance results from inactive recursion do not measure the proposed algorithm.

[Recursion theorem](two-adic-recursion.md) · [Source/compiler acceptance](lean-rust-acceptance.md)
