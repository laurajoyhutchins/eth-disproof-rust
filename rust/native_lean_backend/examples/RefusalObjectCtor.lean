import NativeRust
namespace RefusalObjectCtor
  inductive Unverified where
    | pack (value : Option UInt64)
    | empty
  def produce (x : UInt64) : Unverified := .pack (some x)
end RefusalObjectCtor
#native_rust_package [RefusalObjectCtor.produce] to "examples/rejected-object-package"
