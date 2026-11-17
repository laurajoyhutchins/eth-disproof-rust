# Signature-head import/export ABI, v0.14.0

Source: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`,
`lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureHeadLoaderCore.lean`.

Implemented finite `Cmd 16 896` segments:

```lean
def importAddressFrom (src : Fin 896) :=
  .seq (clearMany [649,659,846,847]) (copyCmd src 649 659)
def exportMatrix :=
  .seq (clearCmd 659) (.seq (copyCmd 668 847 659)
    (clearMany [668,669,846]))
```

The Rust code uses the exact source clear/copy subroutines, with the same
register pair 0/1 and physical temporary 659. It checks the source-frame
precondition that the selected address stack is not among the cleared ports.
Copy destination tails are preserved and prepended to, exactly as
`SubexpSetupStorage.copyState` prescribes. The source register mapping
`leafRegs : Fin 16 ↪ Fin 40` is 24+i; stacks use the identity map.

`tests/native_loader_frames.rs` verifies exact paid instruction counts for
several alternate address sources, nonempty destinations, dirty temporary,
source preservation, address/copy frames, 40×896 register preservation,
invalid alias refusal, and explicit capacity refusal.

**Not implemented here:** `SignatureHeadLoader.localProgram`, which performs
head selection, raw matrix production, shifting, and source-specific numerical
entries. A diagnostic shell that imports an address and exports a *preexisting*
matrix is intentionally not exposed as the complete source `programFrom`.
An imported-original-Lean differential remains blocked by the unavailable
pinned Mathlib A compiled modules; Rust-only tests do not replace it.
