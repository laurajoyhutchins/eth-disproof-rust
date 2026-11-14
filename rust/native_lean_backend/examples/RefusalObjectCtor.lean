import NativeRust
namespace RefusalObjectCtor
  inductive Unverified where
    | pack (x y : UInt64)
    | empty
  def produce (x : UInt64) : Unverified := .pack x (x + 1)
end RefusalObjectCtor
#native_rust_package [RefusalObjectCtor.produce] to "examples/rejected-object-package"
