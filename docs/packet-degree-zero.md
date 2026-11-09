# Packet target-degree zero certificates

This is an exact, source-derived pre-construction rejection in
`ChildEvaluator.evaluate`, shared by compiled and direct child plans and
by eager, native and lazy packet entry kernels.

For packet `q` in a requested group `g`, the prepared packet coefficient
is a target monomial coefficient of

\[
\prod_{r\in R_{q,g}}\left(c_r+\sum_{m\in T_{q,g}}a_{r,m}X_m\right).
\]

Each row factor has total degree at most one in its *target* modes.
Therefore, for any multiplicities `beta_m>=0`,

\[
\boxed{\sum_{m\in T_{q,g}}\beta_m>|R_{q,g}|
\implies [X^\beta]P_{q,g}=0.}
\]

This implication is independent of the Boolean packet bits, Cauchy
coefficients, coefficient-ring precision, exponent dictionary, native
kernel or numerical cancellation. It does not assume an approximate
zero test or arbitrarily discard valid contractions.

The implementation counts the actual parent Y-row slots by packet,
group and coordinate from the verified packing. It validates exact
packet edge ownership and checks every selected positive target mode
before emitting a certificate. When a component-restricted child
omits a packet, its modes are ignored for the certificate. Source-tile
modes are not target exponents and do not contribute to the demand.

The check executes **before** compiling or instantiating a child network,
preparing its `PacketEntry` objects, scanning optional zero-support
tables, or calling a recursive contractor. Each successful certificate
has a separate `packet_degree_zero_certificates` counter and an
explicit cost-ledger event; if work tracing is enabled, it emits a
`packet_degree_zero_certificate` observation with source identifiers.

### Why this is earlier than existing suffix pruning

The native packet evaluator already uses future-row feasibility to
eliminate unreachable exponent states. The Python reference evaluator
does not. The new test concerns an even earlier stage: **a local mode
assignment can be rejected before a packet oracle is created at all**.

The source currently bounds each mode's multiplicity by its own
`len(mode.rows)`, but distinct modes targeting the same packet/group
may each pass that check while their **combined** multiplicity exceeds
the available row count. The new precheck catches this interaction.

### Tests and limitations

`tests/unit/test_packet_degree_zero.py` compares the certificate
against exact per-packet Boolean truth tables. It covers direct and
compiled child paths, malformed multiplicities and component
restriction, and a fully occupied four-slot packed graph with two
distinct *real* mode-catalog entries. Their individually admissible
multiplicities demand degree three from two rows, so every packet
entry is exactly zero. The test verifies that both modes are admitted
by the ordinary weighted-tuple generator.

This is **not** a proof that all packet coefficient dictionaries have
subexponential bit complexity. The full mode tuple/factor enumeration
still visits many candidates, and packet factors with degree demands
within their row capacity may still have exponential reachable states.
The check does not fix finite resource refusals, hidden native work or
the absence of a complete Sudoku-cell worst-case bound.

There is also a separate
[exact target-coefficient research experiment](target-coefficient-extraction.md)
which explores incidence decomposition and future-row pruning inside the
prepared Python evaluator. The default native kernel already performs
suffix pruning and remains unchanged.
