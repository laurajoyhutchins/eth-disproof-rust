# Mathematical totality versus resource admission

**Result:** two *conditional sufficient resource-budget lemmas* for the actual
Python leaf and mode-elimination algorithms. Neither turns the current
paper-schedule implementation into a total solver, nor establishes a new
worst-case complexity theorem. The original deliberately red research
acceptance test stays red. The executable source is
`reference/totality_admission.py`, independently checked by
`tests/unit/test_totality_admission.py`.

The central error to avoid is using **a configurable refusal limit to bound
work**. A program that refuses once it has spent a fixed amount of work may
be bounded, but it does not thereby compute its required answer. Conversely,
a finite exact reference algorithm can be total in a mathematical model but
impossible to execute on available hardware.

## 1. Terminal factor elimination has a sufficient finite guard budget

Let a validated finite `Network` have `M` wires and `V` vertices, and let the
finite coefficient ring's **production factor-storage estimate** be `b`
bytes per coefficient, computed by `estimated_coefficient_bytes`. Assume each
input vertex oracle is a total function returning a canonical ring value.
Set the *explicitly requested* Python `LeafConfig` to:

- `strategy='eliminate'`, `limit=max(1,M)`;
- `max_width=max(1,M)` and `lookup_entries=0`;
- `max_factor_bytes >= (V+M+2) * 2**M * b`.

**Proof for the implemented resource guards.** Any factor table over `M`
binary wires has at most `2**M` entries. Elimination consumes incident factors
and introduces at most one new factor on each of exactly `M` steps. At most
`V+M+1` source or output tables can be live or being inspected, and the
`+2` in the budget covers the current output table and slack. Every initial
arity and intermediate elimination scope has width `<=M`; neither width
condition triggers the fallback to `Network.direct`. The explicit edge cap
`limit=M` also makes that exact fallback size-admissible if reached by other
legal control flow. All loops are finite in the abstract model; no factor
memory or edge-width `CapacityError` is necessary.

This proves **only** the absence of those resource-guard refusals given the
premises. It does **not** bound actual allocator overhead, resident RSS,
input-oracle descriptions, CPU or wall time. The displayed byte budget is an
*upper bound on the source's approximate guard accounting*, not an OS memory
reservation. Runtime `MemoryError`, exception-raising callbacks, a defective
backend, and precision/canonicality violations are outside the result.

`symbolic_terminal_budget` computes the **base-two logarithm** of these
sufficient entries and estimated bytes without allocating an integer with
`2**M` digits or enumerating an assignment. Materializing a `LeafConfig` is
explicitly gated by a caller-chosen size threshold. Even a successfully
materialized configuration can be too demanding to execute.

## 2. Prepared positive-weight mode elimination has sufficient local guards

Fix an already-constructed mode catalog of `m` modes, coefficient precision
`p>=1`, and at most `F>=1` starting factor scopes. All mode weights must be
positive. Let

\[
A=\#\left\{\beta:\ 0\leq\beta_i\leq |\mathrm{rows}_i|,
 \ \sum_i w_i\beta_i<p\right\}.
\]

`exact_weighted_support` obtains `A` by an independent degree-indexed DP,
not by enumeration over Cartesian assignments. Every scoped assignment can
be padded with zeros and injects into that global domain, so any retained
or temporary factor table has at most `A` distinct assignment rows and
at most `p*A` polynomial coefficients.

There are at most `F+m` simultaneously retained factors because each of the
`m` elimination steps removes some factors and adds at most one. Define
`H=F+m+1` and let `b` be the exact `ModeEliminator` guard's per-coefficient
*estimate*. The following `ModeLimits` are sufficient for the current **Python**
`ModeEliminator` guard checks, assuming child callbacks return and its factor
scopes are valid:

\[
\begin{aligned}
\mathrm{max\_factor\_states}&\geq A,\\
\mathrm{max\_live\_terms}&\geq HAp,\\
\mathrm{max\_child\_contractions}&\geq FA,\\
\mathrm{max\_estimated\_bytes}&\geq HA(pb+128),\\
\mathrm{max\_operations}&\geq
 256(m+1)^3(F+1)^3(p+1)^4(A+1)^2.
\end{aligned}
\]

The final majorant deliberately dominates all source `budget.work` and
`budget.order_work` calls. One scoped-degree DP costs at most `m*p**2`
transition checks; greedy fill-order scans are polynomial in `F+m`; at most
`m*(F+m)` natural joins each see at most `A**2` compatible row pairs; each
sparse polynomial multiplication scans at most `p**2` coefficient pairs;
reference enumerating elimination scans at most `m*A*p` projected choices,
with at most `F+m` incident factors and polynomial convolutions. The final
polynomial accumulation has `<=F+m` factors. Each is dominated by the very
loose displayed positive polynomial for `m,F,p,A>=1`. No unrecorded
exponential Cartesian table is required to prove these specific guard
ceilings.

`finite_mode_budget` constructs the limits for small prepared catalogs. The
separate `symbolic_mode_budget` accepts a proved `A<=2**alpha` and returns
*logarithmic* resource requirements without making `2**alpha` objects. The
`materialize()` operation is an opt-in finite conversion and refuses to
materialize huge exponents.

**Critical scope boundary:** a sufficient `ModeBudget` bound does **not**
prove an entire center is admitted. `ModeLimits.max_estimated_bytes` is also
used by `mode_catalog` as an allocation guard *before* `ModeEliminator`
exists. The witness does not bound mode-catalog `sys.getsizeof` ownership,
packing construction, arbitrary child oracle evaluation, native sparse code,
Python recursion limits, allocator overhead, or the cost of comparing huge
intermediate ordering scores. Those need independent source-to-proof
correspondence. No fixed default or machine capacity is claimed sufficient.

## 3. Composition with the preceding paper-schedule lemmas

On paper-admitted frames the prior colored-partition result supplies
`A<=2**alpha` with `alpha=o(s)` *uniformly across active depths*, and the
mode count, number of factors, precision, and canonical coefficient shape
have conditional polynomial bounds in `s`. Hence all five **local mode
resource-guard requirements** above have logarithms `o(s)`. Likewise the
previous terminal-fallback proof bounds `M_leaf=o(s)`; the sufficient
terminal table budget above has logarithm

\[
M_{\mathrm{leaf}}+O(\log(V_{\mathrm{leaf}}+M_{\mathrm{leaf}})
  +\log b)=o(s)
\]

conditional on polynomial vertex and coefficient shapes.

This is an **existence-of-sufficient-resource-functions** result within
those mathematical premises, *not* an implementation that automatically
chooses or guarantees those resources, not a proof of physical feasibility,
and not a complete complexity theorem. A subexponential number of bytes can
still exceed the capacity of every realistic machine.

## 4. Refusal/exception taxonomy and remaining red premises

| Source path | Current guard or error | What the new witnesses establish |
| --- | --- | --- |
| `Network.direct` | Exhaustive edge limit | Explicit `contract_complete` runs a finite exact reference without that limit, for total finite oracles |
| `eliminate_leaf` | Width, edge fallback, factor-byte limit | A topology-dependent sufficient guard budget is constructive |
| `ModeBudget` | Factor states/terms, work, children, estimated memory | A prepared-catalog sufficient guard budget is constructive |
| `mode_catalog` | Mode count (optional), estimated catalog bytes | **Not discharged** by local mode budget |
| `build_factorization_plan` | Component-count cap | A factor-count premise is necessary; not universally proved |
| `ContractionEngine` | Degree, packing, and numerical hypotheses | **Not resource guards**; admission/packing requires a separate proof or exact terminal route |
| Optional native/lazy/jet paths | Backend-specific limits and availability | Outside the Python paper reference proof |
| User-supplied oracles | Can loop, raise, or emit noncanonical output | **No uniform totality or bit-cost contract** currently enforced |
| CPython/host | Memory, stack, integer allocation, time | Not certified by mathematical resource ceilings |

Finite tests compare independent factor-completion counts on disconnected and
connected networks, including 19-edge cases beyond the old default leaf cap;
independently enumerate small weighted domains; run *both* sparse and
enumerating Python factor-elimination policies with and without sufficient
budgets; and confirm an unknown oracle still fails despite a generous budget.
Symbolic tests handle network parameters with 131072-bit `s` without allocating
an enormous factor or capacity integer.

The complete theorem test remains intentionally **RED**. The most valuable
next source-level obligations are mode-catalog memory/creation costs and
component planning under all paper-admitted families; after those, examine
end-to-end oracle contracts and the Sudoku-cell size conversion.
