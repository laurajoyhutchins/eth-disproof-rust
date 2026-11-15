# Root packing feasibility for the two-adic contraction

**15 November 2026.** This is an exact arithmetic obstruction and a necessary-condition checker, **not** an active recursive counter or a new asymptotic algorithm.

Source: OpenAI's [quantitative-contraction.tex](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex), Git blob `51ba54efc29f51bbc0426f848003030da484f354`, sections “Parameters and collision packing”, “Packing into packets”, and “The child networks and their descriptions”.

## Quantitative obstruction at the root

Take the root to have **exactly** `M=s` tensor-network edges. Keep the paper's parameters

\[
\Delta=\lceil s^{9/10}\rceil, \quad
a_0=2u_0,\quad L=2^{a_0},\quad
D_{\rm arr}=r^{2a_0}.
\]

An active root must have `u_0 >= 1` to use the specified positive packet scale. Therefore `a_0 >= 2` and `D_arr >= r^4`. The packing lemma requires

\[
M\ge 2D_{\rm arr}^{2}\Delta
\quad\Longrightarrow\quad
s\ge 2r^8\lceil s^{9/10}\rceil.
\]

Consequently, for `s>0`, we need

\[
s^{1/10}\ge 2r^8.
\]

With the original `r=64`, this implies

\[
\boxed{s\ge (2\cdot 64^8)^{10}=2^{490}.}
\]

This is only a **necessary** lower bound from the first packing inequality. It does not assert that the fixed schedule activates at `2^490`: the original `u_0=floor(lambda/131072)`, deeper levels, the bound `u>=lambda^(4/5)`, precision, leaf threshold and all other obligations remain.

### Exact 128-bit impossibility, even after retuning epsilon

For every positive `s<=2^128-1`,

\[
s^{1/10}<2^{13},
\qquad
\Delta=\lceil s^{9/10}\rceil\ge s/8192.
\]

Thus the first packing requirement would imply

\[
s\ge 2r^8\Delta\ge\frac{2r^8}{8192}s.
\]

For every `r>=3`, `2r^8>=2\cdot3^8=13122>8192`. This contradicts `s>0`. **No positive `u_0`, and no retuning of epsilon alone, satisfies the published first packing inequality for these root sizes.**

The paper uses `r=64`; its child bound is `6M/r=3M/32 < M/8`. Keeping the same strict `M/8` shrink from this estimate requires `r>48`, well within the impossibility range.

This is **not** a lower bound on alternative packet constructions, actual maximum degree, or other tensor algorithms. It assumes the root scale `M=s` and the global envelope `Delta=ceil(s^(9/10))`. If the theorem parameter `s` and the root edge count `M` are deliberately different, rerun the inequalities with both sizes: this proof does not silently replace `M<=Cs` by equality.

## Unavoidable edge floor even with ideal degree

The packet construction itself introduces vertices with at most `2L`
ports, and its hypothesis requires `2L <= delta`. Therefore, independently
of the published `s^(9/10)` maximum-degree envelope, the **same three
packing inequalities** imply

\[
M\ge2D_{\rm arr}^{2}\delta
 \ge 4L D_{\rm arr}^{2}.
\]

At the root, `u_0>=1` gives `a>=2`, `L>=4`,
`D_arr=r^(2a)>=r^4`, so necessarily

\[
\boxed{M\ge 16r^8.}
\]

The source bounds each child's edges by `6M/r`. If one insists on
the source's **strict** `M/8` child bound, `r>48`; hence the least
possible edge count permitted by these *numeric* hypotheses is

\[
\boxed{M\ge16\cdot49^8=531{,}726{,}889{,}113{,}616.}
\]

At the published `r=64`, this minimum is `M>=2^52`.
If only *some* guaranteed contraction (`6/r<1`) is required, `r>=7`
and the minimum is `16*7^8=92,236,816` edges, but this loses the
1/8 shrink and **does not** prove a usable recurrence at later depths.

These are conditional lower bounds for invoking this **particular
sufficient packing lemma**, not complexity lower bounds on general
tensor contraction or on a better collision-packing construction.
They are optimistic: they choose `u=1`, the smallest permissible
new-vertex degree cap `delta=2L=8`, and ignore stronger source
constraints and all counting costs.

The CLI reports `unavoidable_minimum_root_edges` using checked integer
arithmetic. A missing value means the bound exceeds `u128`, never
that zero edges suffice.

## Distinguish the degree envelope from the measured degree

The packing lemma's proof uses a *maximum-degree bound*. For a specific tensor network, an invariant `delta` satisfying the maximum original degree and every new packet degree could be smaller than the published worst-case `Delta`. At a single root, the same three **numerical packing inequalities** become

\[
s\ge2r^{4a}\delta,\qquad
s\ge 2^a r^{2a},\qquad
2^{a+1}\le\delta.
\]

The Rust audit checks these exactly, refusing on overflow. This **does not** certify that `delta` remains valid under every recursive child, that the packet construction has actually run, or that changing the schedule preserves the interpolation and precision analysis.

Two instructive examples:

| Root hypothesis | First packing bound | Other observations |
|---|---|---|
| `r=64, u_0=1, a=2, delta=8` | `s>=2^52` | `s=2^52` meets the three packing inequalities and `r>48`, but violates `u>=lambda^(4/5)` and has no verified full recursion schedule |
| `r=2, u_0=1, a=2, s=2^100, delta=2^90` | `s>=2^99` | The first packing inequality passes, but the bound `6M/r=3M` supplies no shrink at all |

Neither is a practical active-recursion benchmark. The first involves over four quadrillion edges even before counting. The second loses the claimed child contraction.

The lower bound `u>=lambda^(4/5)` belongs to the paper's asymptotic cost argument; it is **not**, in isolation, an algebraic prerequisite for the local tensor identity. An alternative finite-size algorithm could relax it, but would need an independent global cost proof.

## Reproducible exact arithmetic

```sh
# Fixed published schedule: always a refusal for representable edge counts.
cargo run --locked -p lean-eth-reference --bin appendix-admission -- 1000000

# Hypothetical root: report necessary packing inequalities, but not a count.
cargo run --locked -p lean-eth-reference --bin appendix-packing -- 4503599627370496 64 1 8
```

Both commands intentionally exit with status 2. The latter prints `packing_arithmetic_holds=true`, `original_child_shrink_bound_holds=true`, and `source_asymptotic_u_bound_holds=false`. It also explicitly marks `source_degree_invariant_verified=false`, `active_recursion_executed=false`, and `sat_count=null`. No tensor entries, Boolean assignments or modes are enumerated.

`src/two_adic_packing.rs` uses checked powers/multiplications and integer comparisons; `u^5>=lambda^4` checks the source asymptotic inequality without floating point. Unit and CLI tests include overflow, the exact packing threshold, loss of shrink when reducing `r`, and failures masquerading as counts.

## Alternative matching-potential packing

The earlier no-go bounds in this document assume the paper's original
`M>=2D_arr^2 Delta` packing lemma. They are **not necessary conditions**
for a different, stronger lemma. A [constructive matching-potential bound](matching-potential-packing.md)
replaces that collision inequality with the sufficient
`M>=D_arr*((2*Delta-1)*ceil(log2(D_arr))+L)`.
It preserves the old slot-orientation and child-edge conclusions under
the new explicit degree requirement. This does **not** establish the
paper's fixed parameter schedule, full recursive correctness or an
executable ETH disproof.

## Research implication

A useful finite-size breakthrough must change more than the root's epsilon. Three substantive directions remain:

1. **Instance-certified degree invariant:** prove a smaller bound survives every child, including all packet vertices and all actual recursion depths. Recompute the entire schedule and its work from this proof.
2. **Stronger packing:** replace the costly `M>=2D_arr^2 Delta` requirement with a proved alternative, retaining packet collision control, fixed-slot orientation and the `6M/r` child bound.
3. **Different group/precision schedule:** derive the exact child shrink, interpolation, valuation, precision and mode-count recurrence for the new choice. The original `2^{O(s/sqrt(log s))}` bound does not transfer automatically.

Until one of these is certified and coupled to a faithful executor, the right output is **unsupported active recursion**, not a fast exact count. Full-source correctness and total-cost comparisons remain [issue #258](https://github.com/laurajoyhutchins/eth-disproof-rust/issues/258).
