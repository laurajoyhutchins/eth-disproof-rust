# Original Sudoku oracle invocation closure

**Status:** a source-derived, conservative *conditional event-count ceiling*
for all invocations of original Sudoku entry programs in the direct
bipartite tensor reduction. This is **not** a non-exponential bit-time
theorem. It is not about packet-entry callbacks, Cython inner loops or the
separate CNF/band Sudoku reductions.

## Exact possible callback sites

The actual Python contractor invokes original Sudoku vertex callbacks in
three places only:

1. `Network.direct`: one call per vertex in each Boolean edge assignment,
   up to `V * 2**M` in one terminal call. Zero-factor short-circuits may
   reduce this number.
2. `eliminate_leaf`: constructs one Boolean factor table for each retained
   source vertex, up to `2**deg(v)` calls per vertex. The compiled plan
   does this once per input tensor. **The uncompiled implementation can
   generate some tables and then call `direct` when an intermediate factor
   is too wide**, so the safe local ceiling is the **sum** of the table and
   exhaustive costs, not their maximum.
3. `certify_zero`: when explicitly enabled and the support preflight
   accepts the child, evaluates at most `2**deg(v)` rows per original
   vertex. This happens **before** the child's `contract()` call; on a
   proved zero, recursion is skipped. Such pruned *attempts* cannot be
   omitted from the total just because no new recursion frame was created.

New `PacketEntry` evaluations do not re-enter the original oracle
programs. Both direct and compiled child construction retain the identical
original oracle object with the same number of incident wires. Existing
oracle-lineage tests verify the source correspondence. The new
`audit_retained_original_oracles` independently rejects new/forged
callbacks, duplicate references and arity changes in a claimed descendant.

## The root-based symbolic envelope

Let box order be `b`, board side `n=b**2`, cell count
`N=n**2`, and digit width `t=max(1,ceil(log2(n)))`. The original
network has

\[
M_0=3Nt,\qquad V_0=N+3n.
\]

There are `N` cell factors of arity `3t` and `3n` unit factors of
arity `nt`. Therefore one complete round of original dense table
construction, or one zero-support probe, uses at most

\[
D_0=N2^{3t}+3n2^{nt}
\]

original callback invocations. If `M_*` bounds the number of edges in
every terminal `direct` call under consideration, then one such call
makes at most

\[
E_*=V_0 2^{M_*}
\]

original callback invocations. A single **candidate child attempt** costs
no more than

\[
A_* \le E_* + \mathbf{1}_{\mathrm{eliminate}}D_0
           + \mathbf{1}_{\mathrm{zero\ support}}D_0.
\]

It is intentionally pessimistic: it assumes *every* root vertex can still
appear in every child and charges the uncompiled fallback even when no
fallback occurs. It does **not** count calls made by generated
`PacketEntry` or by arbitrary noncanonical callbacks.

In `reference/sudoku_oracle_invocations.py`, the event-count logarithmic
bounds are computed without constructing `2**M_*` explicitly, so they can
be used with the literal astronomical paper schedule. The mathematical
per-call source cost is inherited from
[original-sudoku-oracle-contract.md](original-sudoku-oracle-contract.md).

## Conditional potential-child tree, not just observed recursion

The source's `assemble_paper_recurrence` already supplies
`log2_recursive_calls_ceiling` from positive-weight support. This is a
bound on the **full potential tree** before zero-support pruning, so it can
also cover calls made by children that are *attempted but proved zero before
contract()*.

If `C` bounds the potential node count, then the total original oracle
call count is conditionally at most `C*A_*`. The model exposes the
resulting base-two logarithmic ceiling as
`sudoku_original_oracle_invocation_envelope.all_potential_nodes_log2_ceiling`
and separately charges the maximum schoolbook source entry cost evaluated
at the largest modeled Padic precision. It takes `M_*` from the larger of
the scheduled terminal edge ceiling and the explicit early numeric fallback
ceiling.

**Unresolved conditions:** the paper positive-support/fanout lemma must
correspond to the live implementation; all relevant children must satisfy
the assumed shrinkage and original-oracle lineage; the model excludes native
leaf implementations; the solver must not refuse for resource reasons; and
generated packet oracle evaluation, factor-state allocation, recovery,
modulus creation and whole-frame memory must still be paid for.

Most importantly, `E_*` includes **exhaustive `2**M_*` work**. A bound
containing this term does not prove a subexponential implementation or make
exponentially expensive work acceptable. It identifies which fallback
must be removed or bounded more tightly.

Tests use the real Python network direct evaluation, compiled and
uncompiled factor-table paths, zero-support and a deliberately partially
materialized fallback, with callback interception to check event ceilings.
The research theorem's `require_complete_theorem()` remains red.
