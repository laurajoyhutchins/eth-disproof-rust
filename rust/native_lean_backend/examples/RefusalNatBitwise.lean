import NativeRust
namespace RefusalNatBitwise
  def bitwise (a b : Nat) : Nat := Nat.land a b
end RefusalNatBitwise
#native_rust_package [RefusalNatBitwise.bitwise] to "examples/rejected-nat-package"
