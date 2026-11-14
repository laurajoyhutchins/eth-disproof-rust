import NativeRust

namespace Recovery
  def unsupported (s : String) : String := s ++ "!"
  def supported (x : UInt64) : UInt64 := x + 13
end Recovery

-- An unsupported declaration must report an error without poisoning the
-- loaded Rust library or preventing subsequent independent code generation.
#native_rust Recovery.unsupported as "not_generated" to "examples/recovery_bad.rs"
#native_rust Recovery.supported as "recovery_ok" to "examples/recovery_good.rs"
