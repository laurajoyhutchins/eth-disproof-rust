import Lungo
import Lean.Compiler.LCNF.Simp.Config

/-!
The original compiler module defines Config and its defaults. This fixture
constructs that original type and tests its field-selection behavior. No
upstream source or runtime operation is substituted.
-/

namespace CompilerConfig

def options (tag : UInt8) : Lean.Compiler.LCNF.Simp.Config :=
  { etaPoly := tag == 1 || tag == 3
    inlinePartial := tag == 2 || tag == 3
    implementedBy := tag == 3
    inlineDefs := tag != 4 }

def probe_eta (tag : UInt8) : Bool :=
  (options tag).etaPoly

def probe_inline_partial (tag : UInt8) : Bool :=
  (options tag).inlinePartial

def probe_implemented_by (tag : UInt8) : Bool :=
  (options tag).implementedBy

def probe_inline_defs (tag : UInt8) : Bool :=
  (options tag).inlineDefs

/-- Modifying a distinct configuration field preserves eta expansion. -/
@[lungo_claim "lungo.law" subject probe_eta]
theorem update_preserves_eta (tag : UInt8) :
    ({ options tag with inlineDefs := false }).etaPoly = probe_eta tag := by
  rfl

end CompilerConfig
