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

This is a **bounded experimental refinement check**, not a proof that `R`
exists for all reachable allocations or states. No pointer values leave
the respective processes. The trace records only objects reachable at
explicit public boundaries; internal allocation and destruction events
are not yet tracked. Differences in transient allocation topology can
therefore remain invisible. It does not cover arbitrary borrow
annotations, all closure paths, sticky/frozen/MT objects, primitive/FFI
effects, mutation allocation identity, or object-finalization cascades.

The script fails on the first divergent trace and retains C/Rust outputs,
generated kernel C, generated Rust and source-hash receipts in exact-head CI. There is no learned mapping, expected-output
substitution, or alternate production Rust runtime.
