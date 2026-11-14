import NativeRust
namespace UnsupportedNatPow
  def computed (x : Nat) : Nat := x + (2^512 + 19)
end UnsupportedNatPow
#native_rust_package [UnsupportedNatPow.computed] to "examples/rejected-nat-pow-package"
