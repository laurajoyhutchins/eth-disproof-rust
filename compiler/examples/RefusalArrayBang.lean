import NativeRust
namespace RefusalArrayBang
  def unsupported (x : UInt64) : UInt64 :=
    let a : Array UInt64 := #[x]
    a[0]!
end RefusalArrayBang
#native_rust_package [RefusalArrayBang.unsupported] to "examples/rejected-array-package"
