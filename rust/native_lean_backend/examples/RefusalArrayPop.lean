import NativeRust
namespace RefusalArrayPop
  def unsupported (x : UInt64) : UInt64 :=
    let a : Array UInt64 := #[x]
    let b := a.pop
    b.getD 0 99
end RefusalArrayPop
#native_rust_package [RefusalArrayPop.unsupported] to "examples/rejected-array-package"
