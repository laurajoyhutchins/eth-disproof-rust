# Same-source object identity and reference-count checkpoints

This adds an executable, **same-source** correspondence gate alongside the
nine-checkpoint manually matched control in [ownership-trace.md](ownership-trace.md).

The unchanged functions in `examples/OwnershipObjectTraceKernels.lean`
are compiled by Lean 4.34.1 into C, and independently through the canonical
in-process `Lean.IR.Decl` backend into Rust. The C driver observes
`lean_object*` identity and `lean_internal_get_rc` (single-threaded only).
The generated Rust test observes `Rc::as_ptr` allocation identity and the
existing logical source counter. Neither observation API is called from the
kernel source; the C probe and Rust test live only in the test drivers.

The driver calls are deliberately **not compiled from the same source**:
`native/object_trace_probe.c` invokes actual Lean C generated functions;
`examples/ownership_object_trace_test.rs` invokes the corresponding
generated Rust exports. Both drivers make the same explicit retain operations,
unlike a Lean-compiled IO driver that can change reference lifetimes through
its own compiler optimization. The three input pairs `(0,1)`, `(17,23)`,
and `(901,702)` are read at runtime, preventing closed constant data from
being frozen into Lean's persistent object region. This is a test of **the
same compiled kernel definitions under the same ownership schedule**, not
an all-language same-source driver theorem.

### Candidate heap relation

At each observation checkpoint, define a partial relation `R` from an
observed C object address to the observed Rust allocation. The object ID is
the index of the **first occurrence** of the allocation in its respective
run. The check asserts:

1. First-observation IDs correspond in order.
2. Repeated IDs preserve alias relationships across source calls and
   both branch results.
3. The C physical RC equals the Rust logical source count for every
   observed object at each checkpoint.
4. The through-closure result is observed alongside its captured input.
5. For a genuine two-level source-defined tree, both an independently
   retained grandchild and an independently retained direct sibling have
   count two before the root is released. After destroying the root, each
   surviving descendant has count one, proving that the source RC release
   cascaded through the intermediate fork as well as the direct child.

This is a **bounded experimental refinement check**, not a proof that `R`
exists for all reachable allocations or states. The two additional
`graph-before` and `graph-after` checkpoints exercise the same
`OwnershipObjectTrace.createNested` source function compiled to Lean C
and Rust. The independently retained grandchild remains accessible after
its root and intermediate fork have been physically released by Lean C,
which exposes the destructor cascade without reading freed memory. No pointer values leave
the respective processes. The trace records only objects reachable at
explicit public boundaries; internal allocation and destruction events
are not all tracked. The nested-tree case observes source-child release
effects at an intermediate boundary, but does not timestamp every allocator,
call transfer, or destructor event. Differences in transient allocation topology can
therefore remain invisible. It does not cover arbitrary borrow
annotations, all closure paths, sticky/frozen/MT objects, primitive/FFI
effects, mutation allocation identity, or object-finalization cascades.

The script fails on the first divergent trace and retains C/Rust outputs,
generated kernel C, generated Rust and source-hash receipts in exact-head CI. There is no learned mapping, expected-output
substitution, or alternate production Rust runtime.


## Multi-allocation source-credit and physical observation increment

The earlier source accounting proof handled a single allocation.
`compiler/proofs/ReaderObjectCredits.lean` now indexes independent
source ledgers by **allocation identity**. It proves that arbitrary
finite interleavings of owned and borrowed calls, join transfers, and
returns conserve the count **for each individual allocation**. A
successful operation cannot change a different allocation's ownership
slots, and an explicit `inc` changes only its selected allocation's
count. A borrowed object cannot spend a reference belonging to a
second object, no matter how many Rust `Rc` aliases either has.

The existing same-source physical observation driver has gained two
additional checkpoints. Both the original Lean C compilation and the
Reader-generated Rust compilation invoke the actual source-defined
`identity` function on a **second, distinct Token**. They then
observe both identities after source-defined `select` branches.
`scripts/check-object-identity-transfers.py` audits allocation
separation, callee return identity, branch-selected identity, counts
of both aliases of an object, and the retained grandchildren after
destruction. Three mutation controls must fail. This is independently
recorded for three runtime input pairs, with the whole C/Rust transcript
still required to match exactly.

The Lean proof and original C/Rust trace are complementary **but
not mechanically coupled**: the trace IDs are per-run identities
assigned at first observation and are not formal witnesses that
the complete physical heap implements the proof's abstract ledger.
The source conditional exercises real branch paths, but this
does not independently establish that its pinned compiler IR
contains a particular `jdecl/jmp` lowering. The separate
`TransferContractFixture` checks actual source-level join transfers.
A physical-C-versus-Rust complete join-stack/heap
bisimulation, finalizers, optimizations and arbitrary alias cycles
remain unproved.


## Bounded heap-event replay, with explicit release cascades

`proofs/ReaderHeapEvents.lean` defines a finite-fuel operational semantics
for a graph of source-owned heap objects. An object has an allocation ID,
a positive source-reference count, and an ordered sequence of owned child
references. The machine supports a topologically ordered seed of a live
graph, explicit source `retain`, recursive source `release` (with a
fuel limit and underflow refusal), and source-reference observations. It
proves that source-freed objects cannot be resurrected by a retain,
that a final leaf release clears its allocation, and that a five-object
tree's root release destroys its intermediate fork and unretained
cousin while retaining precisely the grandchild and sibling with
explicit extra source references.

This is a semantics for an **observed** graph. Its `seed` event describes
the allocation and owned-child edges visible at first observation.
It does **not** timestamp each underlying `lean_alloc_ctor` call.

The independent C and Reader-generated Rust drivers now record a
separate `HEAP` event stream next to the existing `TRACE` checkpoints.
The C driver samples real pinned Lean C source RC immediately before/after
each explicitly instrumented `lean_inc`/`lean_dec`; the Rust driver
samples the production `__LeanValue` source count before/after the
corresponding operations. The event stream includes the intermediate
fork's previously unobserved second leaf, so the replay covers *all*
owned child edges of the bounded tree. Neither driver dereferences
root or child objects after their last physical release.

`scripts/check-heap-events.py` is a separately implemented, strict
reference-machine replay: it refuses unknown event forms, duplicated
IDs, absent child edges, fabricated retains, mismatched pre/post source
counts, releasing an absent allocation, broken destructor cascades,
and unexpected survivor references. It requires the 17 event records
from each backend to agree exactly, on all three input pairs; seven
adversarially altered event streams must be rejected.

**Trust boundary:** This is a checked event semantics and bounded
instrumented source-heap observation, not yet a machine-checked refinement
from *all* physical Lean C allocator/destructor events to the abstract
machine. Observations sample an already constructed tree and explicit
driver operations; internal allocation chronology, every implicit C
destructor, arbitrary aliasing and finalizer execution remain unproved.
The production Rust runtime still uses its own logical source ledger
and an implementation `Rc`. An observed match to physical Lean C
is evidence, not a general bisimulation theorem.
