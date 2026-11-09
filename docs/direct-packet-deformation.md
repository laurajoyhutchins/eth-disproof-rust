# Direct packet deformation: exact change of summation order

The mode recursion and the lifted packet contraction are two *different*
exact ways to evaluate the same deformation polynomial. The independent
Boolean oracle `independently_evaluate_F` evaluates

\[
F(t+2Lz)=
\sum_{Y,X\in\{0,1\}^M}
\left(\prod_{u\in\mathrm{left}}T_u(Y_{\partial u})\right)
\left(\prod_{v\in\mathrm{right}}T_v(X_{\partial v})\right)
\prod_{k}\prod_{e\in P_k}
\left[Y_e S_e(X)+(1-Y_e)(1-S_e(X))\right],
\]
where
\[
S_e(X)=\sum_{f\in P_k}X_f W_{\mathrm{slot}(f)-\mathrm{slot}(e)}(t+2Lz).
\]

The proposed `packet_eliminate` route treats each bracketed packet
product as a *single factor*. Every original edge is lifted to two
Boolean wires `Y_e` and `X_e`, the original left and right vertex
oracles are retained on one side of a bipartite factor network, and
the packet factors occupy the other side. Ordinary exact variable
elimination then contracts the lifted graph.

This **does not enumerate any mode multiplicities, does not create
any mode factor table and does not recursively construct child networks**.
The Cauchy factors and ring precision remain unchanged. Tests compare
against the independent \(2^{2M}\) oracle at packet widths 2, 4 and 8,
including nested Taylor jets. A separate full-recovery test covers
the dense four-slot two-wire example which previously exceeded the
4,096-state mode factor limit.

### Structural boundary

This route is efficient only for networks whose **lifted** factor graph
has small elimination width. An occupied packet with \(k\) edges
introduces a factor with \(2k\) binary ports. The executor uses
`compile_leaf_plan` to verify the complete elimination order before
evaluating an oracle. If it exceeds `LeafConfig.max_width`, the
execution refuses rather than falling back to exhaustive enumeration.
The existing `LeafConfig.max_factor_bytes` bounds table allocation.
These are existing settings, not new global performance parameters.

At width \(w\), ordinary elimination uses tables of size at most
\(2^{O(w)}\) times the cost of coefficient-ring arithmetic and local
oracles. Nothing here proves a subexponential bound on *arbitrary*
networks, or the paper's recursive worst case. The mathematical
advantage can disappear for high-arity Sudoku vertices or densely
coupled packets.

### Use

\`\`\`python
from non_exponential_sudoku import ContractorConfig, ModeConfig, LeafConfig

config = ContractorConfig(
    s=2, precision=5, schedule="geometry64",
    mode=ModeConfig(strategy="packet_eliminate"),
    leaf=LeafConfig(strategy="eliminate", max_width=8),
)
\`\`\`

The strategy is explicitly experimental and rejected under the literal
`paper` schedule. It is appropriate as an exact, falsifiable alternative
for low-width deformations, **not** a general fallback whenever the
published mode algorithm refuses.

The source of truth is `src/non_exponential_sudoku/contraction/packet_factorization.py`.
Tests are `tests/unit/test_packet_factor_deformation.py`.


### TDD observations and non-equivalence boundary

This exact route was added after the rowwise 2-adic pruning study
showed a full-recursive **negative result**: small mode domains at
expanded Hermite precision admit every assignment. A dense two-wire,
four-slot full-recovery case then refused under the default 4,096-state
mode budget. `test_dense_four_slot_full_recovery_overcomes_mode_factor_refusal`
now tests the competing methods on the same exact input: the original
mode-factor strategy refuses, while the packet-lift strategy returns
the independently computed exact count.

Because the packet factor evaluation changes the contraction order,
the resource parameters that matter are graph width and factor-memory
limits rather than the number of mode descriptors. A refusal by one
route is not evidence of an asymptotic improvement by the other.
