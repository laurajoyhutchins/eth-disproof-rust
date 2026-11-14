import NativeRust
namespace RefusalClosure
  def unsupported (x : UInt64) : UInt64 := x <<< 1
  def root (x : UInt64) : UInt64 := unsupported x + 1
end RefusalClosure
#native_rust_closure RefusalClosure.root as "bad_closure" to "examples/rejected_closure.rs"
