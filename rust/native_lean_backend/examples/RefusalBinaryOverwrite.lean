import NativeRust
namespace RefusalBinaryOverwrite
  def root : UInt64 := (10 : UInt64) + 7
end RefusalBinaryOverwrite

#native_rust_binary RefusalBinaryOverwrite.root to "examples/native-binary"
