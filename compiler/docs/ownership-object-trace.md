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
