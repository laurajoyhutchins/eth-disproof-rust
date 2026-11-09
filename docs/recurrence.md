# Recursive-call recurrence: what can and cannot be proved

This note gives a complete worst-case upper bound for the **number of calls to
`ContractionEngine.contract()`** under a fixed validated `ContractorConfig`.
It is *not* a bound on Python execution time, bit operations, or success on
all generalized Sudoku instances. In particular, user-supplied vertex oracles
may be arbitrary functions, and the solver can refuse its resource budgets.

## An analyzable family

Fix a configuration and a family of finite bipartite tensor networks with
`M` edges and an explicit contract for each oracle. Define `C_d(M)` as the
maximum number of recursive `contract()` invocations begun by any call at
depth `d` with at most `M` edges, including the current invocation. The
bound counts invocations even when execution ends in a capacity refusal;
this makes no claim about the cost or correctness of the returned result.

Let `r_d` be the scheduled group count, `a_d` the scheduled slot exponent,
and `L_d=2^{a_d}`. There are at most `J_d=2L_d-1` nonzero deformation
centers. Each center evaluates at most `E_d(M)=1` deformations for jet
recovery, or `E_d(M)=M J_d+1` for interpolation. The latter is the actual
`degree + 1` sampling loop in `engine.py`.

Each deformation performs at most `B` child contractions:

* With factor elimination, `B = limits.max_child_contractions`, enforced by
  `ModeBudget.charge_child()` before the next child is evaluated.
* With explicit enumeration, `B = r_d * mode.max_tuples`, since at most
  `max_tuples` assignments are processed and each visits at most `r_d`
  occupied groups. Cache hits can only reduce this count.

For any active call, define `K_d(M) = J_d E_d(M) B`. The complete bound is

\[
  C_d(M) \leq 1 + K_d(M) \, C_{d+1}(M'_d),
\]

with `C_d(M)=1` when the schedule makes a terminal call. For the literal
paper schedule, `M'_d=floor(3M/32)` because **each actual child** is checked
against `32 * child.edges <= 3 * parent.edges` before recursion. For `micro`
and `geometry64`, a conservative bound is `M'_d=2M`: every child edge is
constructed from a port of a retained parent vertex, and there are `2M`
parent ports across both sides. The finite active-depth setting ensures the
experimental schedules terminate their recursion.

**Proof by backward induction on depth.** At a terminal depth exactly one
call is begun. At an active depth there is one current call; the loops above
begin at most `K_d(M)` recursive children. By induction each child begins at
most `C_{d+1}(M'_d)` calls, yielding the displayed bound. Capacity refusals,
empty factors, early zero products, and child-cache hits only decrease the
number of begun calls. Paper execution becomes terminal when
`floor(lambda/(131072*2^d))=0`, with `lambda=(s-1).bit_length()`. Experimental
execution becomes terminal by `micro_active_depth`. Thus backward induction
has a finite base for every finite configuration.

`reference/recurrence_calls.py` evaluates this **call-count** bound for
materializable configuration values, and checkpoint tests compare the bound
with observed recursive invocations. It intentionally does not guess the
number of machine instructions per invocation.

## Why this is not a subexponential Sudoku theorem

The minimum literal paper input parameter with any active scheduled level is
`lambda = 131072`, corresponding to `s = 2**131071 + 1`. The leaf threshold
is also proportional to `s / sqrt(lambda)`. Thus a practical network with
small `M` is terminal even if its `s` is enormous. Setting `lambda`
symbolically, as the schedule auditor does, does not execute such a network.

A complete worst-case **bit-operation** recurrence would additionally need
uniform bounds on mode-descriptor construction, factor elimination, packing,
exact ring arithmetic including coefficient bit lengths, oracle evaluation,
interpolation, memory allocations, and the input-to-network reduction.
Crucially, the resulting bound must be solved as a function of a precisely
defined *growing Sudoku input size*, including capacity refusals or a proof
that none occur on that family. Those obligations have not been proved.
The call-count recurrence above is an upper bound on one component, not an
assertion of polynomial, subexponential, or non-exponential Sudoku solving.

## Complementary bit-cost audit

See [bit-complexity.md](bit-complexity.md) for an explicit 4x4 Sudoku
capacity-refusal witness, the necessary vertex-count and oracle-cost
parameters, exact direct-leaf and interpolation operation envelopes, and
a conservative vertex/precision recurrence. That analysis does **not**
complete the worst-case bit-operation proof.
