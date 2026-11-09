# Global mode-factor support under the literal paper schedule

**Result: conditional subexponential factor-table *row count* in the Boolean-network size `s`.** This closes the specific global-support obligation raised by [per-packet reachability](paper-mode-reachability.md). It does **not** close the total bit-operation recurrence, the oracle-cost closure, non-refusal, or subexponential time in Sudoku *cells*.

The executable companion is `reference/global_mode_support.py`; independent tests are in `tests/unit/test_global_mode_support.py`.

## 1. One positive-weight budget applies to the entire factor graph

`mode_catalog` creates at most one mode of each positive weight for each pair
`(packet, y0)`. The original conservative bound was `w=b+1`.
Production now uses the stronger **rowwise crossing-coefficient bound**.
Let `a` be the packet slot exponent, `i=v2(t)`, and for a target
row slot `x` and tile `y0` let `v=v2(t-y0+x)<=i`. The cross coefficient
has an explicit factor `2^(a+1-v+b*(i+1-v))`. Thus a mode may use

\[
w_m=\min_{x\in\mathrm{target\ rows}}
\bigl((a+1-v_x)+b(i+1-v_x)\bigr)
=(a+1-v_{\max})+b(i+1-v_{\max}).
\]

The normalized Cauchy numerator and all remaining inverse-unit factors
are 2-adically integral. A mode with `w_m>=p(t)` is identically zero
and need not be generated. For each fixed packet and tile, this weight
is strictly increasing in `b`, so there is still at most **one mode
per positive weight**. The published colored-partition upper bound
therefore remains valid, but actual admissible support can be much smaller.
The original count `b+1` remains a safe but weaker lower bound. At an evaluated center `t`, write `i=v2(t)`, `P` for the number of packets, `L=2^a` slots, and `p(t)` for the 2-adic precision. There are exactly `2^(i+1)` possible values of `y0`, so for each weight there are **at most**

\[
K_i=P\,2^{i+1}
\]

mode variables. Every admissible multiplicity tuple obeys the strict global budget

\[
\sum_{m}w_m\beta_m<p(t),\qquad \beta_m\in\mathbb Z_{\ge0}.
\]

The factor builder emits only assignments meeting this condition on each factor scope. The enumerate projection and sparse join routes also retain only assignments whose **current union scope** meets the same strict inequality, because all weights and polynomial degrees are nonnegative. Thus each factor row injects into the global admissible weighted domain by padding missing mode variables with zeros. This works even when the primal factor graph is connected, scopes are huge, or the variable ordering has poor width.

It bounds the *number of distinct factor rows*, not the number of modes in a scope or the work needed to obtain each factor's coefficients.

## 2. A uniform bound via colored integer partitions

For `K` available mode colors at every positive integer weight, let `A(K,p)` count all finitely supported multiplicity assignments satisfying total weight `< p`. Extra colors, unlimited multiplicities and weights not present in the actual catalog can only **increase** this count.

The ordinary generating function is

\[
F_K(x)=\prod_{w\ge1}(1-x^w)^{-K}.
\]

For `x=e^{-\delta}` with `\delta>0`, coefficient nonnegativity gives

\[
A(K,p)\le e^{\delta p}F_K(e^{-\delta}).
\]

Expanding `-log(1-y)` and using `e^z-1\ge z` yields

\[
\begin{aligned}
\log F_K(e^{-\delta})
 &=K\sum_{m\ge1}\frac1{m(e^{m\delta}-1)}\\
 &\le\frac{K}{\delta}\sum_{m\ge1}\frac1{m^2}
 <\frac{7K}{4\delta}.
\end{aligned}
\]

Choose `delta=sqrt(7K/(4p))`. Using `log 2 > 2/3` gives

\[
\boxed{\log_2 A(K,p)<4\sqrt{Kp}.}
\]

For `K=0` or `p=1` the count is one. The helper returns the integer ceiling `4*ceil(sqrt(K*p))` without constructing the generating function or its coefficients. Separate tests enumerate small weighted domains exactly using an independent polynomial DP and exhaustive Cartesian-product oracle.

**Scope independence:** every intermediate factor table has at most `A(K_i,p(t))` rows, and at most `p(t)*A(K_i,p(t))` stored formal polynomial coefficients. Each pairwise sparse join inspects at most the product of two support sizes, hence at most `A(K_i,p(t))^2` candidate pairs. This does not include coefficient evaluation, hashing and allocations, native backend internals, or recursively generated child oracles.

## 3. Center-dependent precision cancels mode multiplicity growth

Under the packing lemma's numerical hypotheses,

\[
P\,L\le 3M,
\]

where `M` is the current network edge count. Only centers with `i=v2(t)<u` are evaluated: the endpoint `t=-L` has `i=a>=u` and is skipped before constructing modes. For each such center, the code computes

\[
\begin{aligned}
h &=\lceil3M/u\rceil,\\
p(t)&=p+8hL/2^i+8M(a+1),\\
K_i&=P\,2^{i+1}.
\end{aligned}
\]

The product, **not** the separate maxima of `K_i` and `p(t)`, satisfies

\[
\boxed{
K_i p(t)\le P\,2^u\bigl(p+8M(a+1)\bigr)+16PhL.
}
\]

Notice that the potentially largest precision increment is inversely proportional to `2^i`, exactly canceling the `2^i` growth in the number of mode families. Multiplying independent worst-case maxima would lose this essential cancellation and fail to establish the desired bound.

`center_color_precision_product` calculates this exact integer envelope; the tests compare it with every eligible center valuation of the source paper schedule at several symbolic sizes.

## 4. Uniform asymptotic bound along **all** recursion depths

Assume input edge count `M_0<=s`, initial precision `p_0<=s`, every active packing satisfies the packet bound, and each recursive child satisfies `M_{d+1}<=floor(3M_d/32)`. Put `rho=3/32`, `lambda=ceil(log2 s)`, `u_d=floor(lambda/(131072*2^d))`, `a_d=2*sum_{j<=d}u_j`, and `L_d=2^a_d`.

Then `M_d<=rho^d*s`, `L_d>=2^(2u_d)`, and `L_d/L_{d-1}=2^(2u_d)` for `d>0`. The existing precision envelope, `h<=3M` and `a+1<=L`, gives a precision rise at most `32*M_d*L_d`. Since `sum_{j<d}rho^j<32/29`,

\[
p_d\le s+36sL_{d-1}\quad (d>0).
\]

Because an active call has `M_d>=u_d`, also `h_d=ceil(3M_d/u_d)<=4M_d/u_d`. Substituting into the center product inequality yields the **uniform** ratio

\[
\frac{K_i p(t)}{s^2}
\le B_\lambda
:=\max_{d:u_d\ge1}\left[
\frac{3\rho^d(37+8(a_d+1))}{2^{u_d}}
+\frac{192\rho^{2d}}{u_d}\right].
\]

This estimate is intentionally loose. At depth zero the `37` also safely covers `p_0<=s`.

**Proof that `B_lambda -> 0`:** split depths at `d=floor((log2 lambda)/2)`. In the shallower half, `u_d=Omega(sqrt(lambda))`, so `2^-u_d` decays faster than the `O(lambda)` factor, while `1/u_d` tends to zero. In the deeper half, `rho^d=O(lambda^{-gamma/2})`, with `gamma=log2(32/3)>2`; hence `lambda*rho^d -> 0` and `rho^(2d)/u_d -> 0`, uniformly in that half. Therefore the maximum over **all active depths** tends to zero.

The tests check the exact integer frame product against `B_lambda*s^2`. For enormous symbolic `lambda`, they evaluate only `B_lambda`, in `O(log lambda)` rational operations, without constructing a `2^lambda`-bit Sudoku instance.

Combining the two lemmas,

\[
\log_2 A(K_i,p(t))<4\sqrt{K_ip(t)}
\le4s\sqrt{B_\lambda}=o(s),
\]

so the **entire admissible factor-table support domain** is bounded by `2^{o(s)}` for every center at every successful paper-recursion depth. The same support bound holds for every factor scope, no matter the elimination width. A bounded number of joins of these tables remains subexponential *in the number of row combinations*, provided that the number of factors and modes and their descriptor costs are also accounted for.

## 5. Admitted packing witness and test limitations

The tests include a **symbolic, supplied-label construction** at the paper's actual `r=64`, `a=2` initial active schedule: one degree-one edge per repeated pair of full left/right labels, with all `D=r^(2a)` ordered label classes equally populated. Its `M=2^lambda` edges, `2M` vertices and `H=M/D` edges per class fill exactly `P=M/L` packets, with group-side load `M/r`, and satisfy the actual numerical packing hypotheses using the safe upper bound `Delta<=2^ceil(0.9*lambda)`. This family is described by formulas; it is **not** materialized, does not claim to be generated by the greedy `balanced_labels` routine, and does not run the entire paper contraction. The support theorem itself is uniform over every packing satisfying the stated numerical conditions.

Independently, small **real** `pack()` and `mode_catalog()` results are checked against the color and weight ceilings, and actual factor elimination with sparse joins is compared with exact enumeration and a support trace. These are finite implementation checks, not an asymptotic proof by benchmarking.

## 6. What remains genuinely red

- **Bit costs per factor row:** child contraction, recursively inherited `PacketEntry` oracles, nested ring arithmetic, expensive integer powers, intermediate bignums, and memory ownership.
- **Totality:** the existing finite `ModeLimits` and leaf limits can still refuse valid Sudoku instances. This theorem is conditional on successful packing and the source schedule's shrinkage/precision assumptions.
- **Other solver paths:** paper mode enumeration, native sparse kernels, lazy coefficient DAGs and unrelated Sudoku frontiers need separate accounting to establish their precise operational costs. The support combinatorics cover admissible *mathematical* assignments independently of the chosen implementation, but not their running-time overhead.
- **Sudoku input parameter:** for the current direct encoding `s=Theta(N log N)` in `N` cells, `2^{o(s)}` alone does not imply `2^{o(N)}`.

The global acceptance test in `research_acceptance/test_complete_bit_recurrence.py` therefore **remains red**. This increment closes *global mode-factor state support*, not the whole worst-case complexity proof.


### Finite falsification witness: four crossing wires

At `a=2`, `t=1`, `p=5`, the independently generated legacy
catalog and the valuation-pruned catalog both contain four `b=0`
modes. Their weights change from `1` to `3`, so the admissible
binary mode assignments fall from `16` to `5`. In
`tests/unit/test_mode_valuation_pruning.py` the two paths agree
exactly on concrete tensor contractions, not merely on tuple counts.
Thus this is a verified elimination of **eleven mode products** in
this finite example, not a proven runtime speedup or improved
worst-case asymptotic exponent. The 16x16 forced precision-three
catalog regression independently illustrates the stronger case in
which all previously generated mode descriptors disappear.
