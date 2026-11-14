import NativeRust
namespace Overwrite
 def root (x : UInt64) : UInt64 := x + 1
end Overwrite
#native_rust_package [Overwrite.root] to "examples/native-package"
