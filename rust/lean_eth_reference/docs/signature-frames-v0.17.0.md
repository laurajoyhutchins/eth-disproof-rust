# Source-defined attained-signature tuple frames (v0.17.0)

Pinned source: openai/math@4eaee87548250b2682affda7d05d947c05554bae, SqrtLogSpace/SignatureTupleProgram.lean and SignatureTupleNative.lean.

This implements the original eight-label pushFrameProgram and the seven-label frame parser through actual lifted machine calls; physical cursor save/restore; representative frame record/drop; level descent/ascent; root presence test; transient-head clearing; and the predecessor fresh-latch initializer.

The frame writer costs exactly 5*n+5 machine instructions and prepends Encoding.frame(word.reverse), including a real delimiter for empty words. The source's 836..847 tuple bank and 36..39 controller-register ABI are reused from native_signature_tuple rather than redeclared. No recursive host tuple enumerator or semantic callback is used.

Independent Rust tests cover bit-level framing, nested empty/nonempty words, representative preservation, unary levels, protected ports, and bounded execution.

Local standalone v0.17.0 archive: 128 passing tests in debug and release and strict fmt/Clippy. The committed incremental file tests are a focused subset of those local checks. The combined GitHub PR has not yet been freshly compiled.

Still unimplemented: SignatureTupleLoader.loadHead, AttainedSignatureProgram.Rescan.candidateProgram, QueryVisitorProgram.visitor, and full SignatureTupleComplete.command. Imported-source Lean/Rust differential trace verification remains outstanding.
