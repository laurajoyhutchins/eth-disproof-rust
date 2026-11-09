# Complete theorem acceptance: independent proof gates

**Status: RED, deliberately and for multiple independent reasons.** The source of the opt-in acceptance test is `research_acceptance/test_complete_bit_recurrence.py`. The companion logic lives in `reference/complete_theorem_gate.py` and `reference/cell_rate_transfer.py`. Green finite tests verify **that the gate rejects unsupported claims**, not that a non-exponential generalized-Sudoku algorithm has been proved.

Run the gate and symbolic-rate regression tests normally:

```bash
PYTHONPATH=src:. python -m pytest -q tests/unit/test_complete_theorem_gate.py tests/unit/test_cell_rate_transfer.py
```

Run the complete theorem acceptance **explicitly** (expected to fail at the final theorem test):

```bash
PYTHONPATH=src:. python -m pytest -q -o addopts='' research_acceptance/test_complete_bit_recurrence.py
```

The acceptance requirements are intentionally independent:

1. **Complete local bit work:** every frame term, including canonicalization, oracle callbacks, planning and allocation, must be justified by a universal source-linked cost lemma. `LocalBitBound` merely checks a numerical dictionary's shape. Supplying invented positive integers is **not** a proof.
2. **Source correspondence and totality:** `reference/whole_frame_recurrence.py` tracks open source/totality premises, including non-refusal, working-set bit accounting and all generated-oracle operations. The full test must reject the current implementation even if every `LocalBitBound` entry is supplied.
3. **Sudoku-cell parameter:** a bound `log2 T(s) = O(s (loglog s)^beta / (log s)^alpha)` and an encoding using `s=Theta(N (log N)^delta)` transfer to `log2 T(N)=o(N)` from this upper bound only when `alpha>delta` or `alpha=delta` and `beta<0`. The tightened depth-sensitive conditional parameters are `alpha=1/2, beta=0`, whereas the direct Sudoku encoding has `delta=1`. Consequently the *displayed upper bound* is too weak to establish subexponential behavior in the number `N` of Sudoku cells.

The sharpened support summation and the restricted three-copy interface cut are proved in [depth-summed-paper-support.md](depth-summed-paper-support.md). The last conclusion is about the available **proof bound**, not a lower bound on the solver. An algorithm might be faster than a loose upper bound suggests. For the explicit growing box-order family `b=2**k`, one has `N=2**(4k)`, `M=6kN`, and `lambda=ceil(log2 M)<=10k`. Hence

\[
\left(\frac{M}{N\sqrt\lambda}\right)^2
=\frac{36k^2}{\lambda}\ge\frac{18}{5}k\longrightarrow\infty.
\]

A proof of `2**o(s)` measured in Boolean network edges does not by itself discharge the stronger `2**o(N)` cell claim for this reduction.

`CompleteTheoremStatus.require_complete()` reports *all current blockers* instead of raising only on the first missing local term. It obtains the source/totality blockers from the composed recurrence's `OPEN_PREMISES` and the cell-transfer gap from the actual published rate and reduction. There is no caller-supplied boolean that makes these obligations vanish. This is an engineering guard, **not** a formal proof checker: future positive results must update the independent mathematical source proofs, their implemented correspondence, and the gate together.

The single complete-theorem test remains **unskipped and un-xfailed**, outside ordinary checkpoint CI. It cannot be marked green merely by filling local cost fields. A non-refusing worst-case theorem, its bit-operation recurrence, and its claimed input-size parameter must be established independently.
