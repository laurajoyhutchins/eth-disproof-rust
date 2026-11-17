import NativeRust
namespace RefusalBinaryArguments
  def root (x : UInt64) : UInt64 := x + 3
end RefusalBinaryArguments

#native_rust_binary RefusalBinaryArguments.root to "examples/rejected-binary"
