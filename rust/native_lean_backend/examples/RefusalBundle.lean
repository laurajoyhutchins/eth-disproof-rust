import NativeRust

namespace BundleRefusal
  def left (x : UInt64) : UInt64 := x + 1
  def right (x : UInt64) : UInt64 := x + 2
end BundleRefusal

-- Duplicate Rust export names must not cause the previous artifact to change.
#native_rust_bundle [BundleRefusal.left, BundleRefusal.right]
  as ["duplicate", "duplicate"] to "examples/rejected_bundle.rs"
