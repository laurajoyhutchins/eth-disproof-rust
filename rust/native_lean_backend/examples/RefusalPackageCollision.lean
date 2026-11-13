import NativeRust
namespace First
 def calculate (x : UInt64) : UInt64 := x + 1
end First
namespace Second
 def calculate (x : UInt64) : UInt64 := x + 2
end Second
#native_rust_package [First.calculate, Second.calculate] to "examples/rejected-package"
