import NativeRust

def sorryDependent (x : UInt64) : UInt64 := by
  sorry

#native_rust sorryDependent as "sorry_dependent" to "examples/rejected_sorry.rs"
