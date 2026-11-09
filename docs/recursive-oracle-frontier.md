# Inherited packet oracles: one-assignment work and lifting

**Scope:** the actual eager-Python `PacketEntry` and `make_child` / compiled
child topology, evaluated along one recursion path. This establishes a small
**structural closure** lemma, **not** a complete worst-case bit-operation
recurrence, and does not make the opt-in theorem acceptance test green.

## The call graph is not recursively nested

`make_child` and `CompiledChildPlan.instantiate` retain selected parent
`Vertex.oracle` objects by reference. They add one new `PacketEntry` for each
selected packet tensor. `PacketEntry.__call__` evaluates only its own prepared
row/mode terms in its creation-time coefficient ring and, when necessary,
invokes `embed_element` on that result. It does **not** traverse its creation
network or call inherited parent vertex oracles.

By induction, after `d` child constructions, each live vertex oracle is
*either* an unchanged initial oracle *or* an individual `PacketEntry` created
at one prior generation. Thus on one assignment of a leaf with `V_d`
vertices there are at most `V_d` oracle calls, not a product of all parent
vertex counts. If the paper packing invariant holds, the total number of
live oracles on a child path is at most

\[
V_d \le V_0 + \sum_{j<d} P_j,
\qquad P_j\le 3M_j/L_j.
\]

This is an upper bound for one **network instance** and one leaf assignment.
The total number of different child networks/evaluations remains governed by
the *separate* global mode and recursive-call bounds. The cache and shared
`EvaluationContext` can retain additional objects; `V_d` alone is not a
resident-memory bound.

## A closed finite-ring lifting count

For source ring `Padic(e,p)` with nested jet lengths `q_1,...,q_h`, in
innermost-first order, `embed_element` visits exactly

\[
e\prod_{i=1}^h q_i
\]

canonical base coordinates. Lifting the existing Taylor layers creates
`sum_{i=0}^h product_{j=i+1}^h q_j` tuple nodes, counting the final
base-coordinate tuples. (The empty product is 1.) Newly requested **outer**
jet layers add one tuple node each and `q_i - 1` references into existing
zero tails. It does not expand all those shared zero coefficient values.

This count assumes that the source value is well-shaped and canonical, the
extension ring is unchanged, existing jet lengths match, and the target
precision is not lower than creation-time precision. Each base copy performs
`e` integer masks on coefficients represented with at most `p` bits, now
bounded by the requested target precision. The resulting *bit-cost* still
requires an explicit model of Python/Cython integer and tuple allocation and
all coefficient arithmetic: counting masks alone is insufficient.

The `reference/oracle_frontier.py` helper computes the shape-level bound
without evaluating the packet itself, combines it with the existing
`packet_evaluation_envelope` (outer ring calls only), and explicitly
requires an external cost premise for **every** inherited ordinary input
oracle. Passing an arbitrary number for one is **not** proof of that premise.
Native packet execution and lazy coefficient DAGs remain unsupported by this
helper; the underlying packet-envelope checker rejects them rather than
reporting a fabricated bound.

## Verification and adversarial checks

`tests/unit/test_oracle_frontier.py` constructs two successive real child
networks from actual `pack` and `mode_catalog`, verifies inherited object
identity, checks the additive frontier, and instruments `PacketEntry.__call__`
to ensure its call depth never exceeds one. It checks exact lifting
coordinate-mask visits and rejects mismatched ring shapes, decreasing
precision, and uncontracted base-oracle costs. These are finite, executable
correspondence tests for the structural proof, not a proof of an asymptotic
algorithm on their own.

Run:

```bash
PYTHONPATH=src:. python -m pytest -q tests/unit/test_oracle_frontier.py
```

## What remains red

1. **Input-oracle work:** the direct-Sudoku oracles have known polynomial
   Boolean work, but the general `Network` ABI permits arbitrary Python
   callbacks; no universal bit-cost claim can be made for those callbacks.
2. **Packet preparation and retention:** Cauchy, mode/catalog, coefficient
   integer powers, caches, shared ring objects and context lifetimes are not
   costed by this per-call envelope.
3. **Primitive bit costs:** `JetRing` multiplication, inversion, finite
   2-adic arithmetic, key hashing/allocation and recovery bit growth require
   separate bounds, particularly under changing precisions and inherited
   Taylor layers.
4. **Non-refusal and final recurrence:** the literal schedule may still
   refuse; bounding individual oracle calls does not bound their number
   across all recursive children or establish a complete `2^{o(s)}` result.
5. **Cell versus network parameter:** even `2^{o(s)}` does not by itself
   imply `2^{o(N)}` for the current direct Sudoku encoding with
   `s=Theta(N log N)`.

The appropriate next acceptance target is an explicit per-primitive **bit**
cost and peak-description-size recurrence across nested jets and changing
precision, followed by proof-backed bounds for packet preparation.
