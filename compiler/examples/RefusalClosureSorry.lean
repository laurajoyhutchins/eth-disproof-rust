import NativeRust
namespace RefusalClosureSorry
  def helper (x : UInt64) : UInt64 := by sorry
  def root (x : UInt64) : UInt64 := helper x + 1
end RefusalClosureSorry
#native_rust_closure RefusalClosureSorry.root as "bad_sorry_closure" to "examples/rejected_sorry_closure.rs"
