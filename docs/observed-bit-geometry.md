# Observed recursive wall time and operand geometry

CostLedger now optionally records **input operand bit lengths** at public
`Padic.add/sub/mul` and `JetRing.add/sub/mul` boundaries. These records
work with both the Python and Cython implementations, since the calls cross
the Python ring interface, but **they do not measure the operations performed
inside native kernels**, native allocations, intermediate products, or the
bit cost of inverse/power, oracle bodies and the rest of the algorithm.

The opt-in overhead is substantial. Without an active CostLedger, the
implementation does not traverse any integer operands. With a ledger,
`observe_operand_bits=False` (default) does not traverse operands.
The separate observed arm of the paired benchmark deliberately sets it to
`True`. The baseline arm remains untouched.

For every ring method/phase/precision/depth, the JSON contains exact
**observational** counters:
- calls, scalar coordinates visited, and sum of input coordinate bit lengths
- maximum input scalar bits, maximum coordinates and total bits per call
- independent per-frame values and total values

Because the native `Padic.mul` operates on Python arbitrary-precision ints,
these boundary observations are useful for estimating operand growth. For a
`JetRing.mul` that calls `Padic.mul` underneath, the jet and Padic
observations both cover parts of the same logical work; they **must not** be
added as if they counted distinct elementary integer operations.

The ledger also records exclusive phase wall-clock time, exclusive frame
wall-clock time, child-frame wall-clock time, and inclusive frame wall-clock
time, with the invariant

```text
inclusive(frame) = exclusive(frame) + sum(inclusive(direct children))
exclusive(frame) = sum(exclusive phase intervals within frame)
```

Nested frames and exceptional exits are tested. Timed intervals use
`perf_counter_ns`, and include the expense of tracing, instrumentation,
Python allocation tracking if enabled by a separate study, and any incidental
scheduler pauses. **Do not treat these as uninstrumented CPU times.**

To inspect one concrete recursive fixture locally:

```bash
python scripts/cost_ledger.py nested-2wire --operand-bits \
  --output artifacts/nested-ledger.json
```

The full-input and unified-cost observed arms collect the new data and retain
baseline timing in separate fresh processes.

Still open: primitive/bit operation counts inside native kernels, operand
growth within intermediate Cython/FLINT expressions, oracle cost closure,
native memory, a non-refusing recursive path, and a uniform worst-case
bit-cost recurrence. The finite observed ledger does not prove any
non-exponential complexity claim.
