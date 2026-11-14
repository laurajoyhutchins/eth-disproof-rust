import NativeRust
namespace RefusalObjectNat
  def addBig (x : Nat) : Nat := x + 2^120
end RefusalObjectNat
#native_rust_package [RefusalObjectNat.addBig] to "examples/rejected-object-package"
