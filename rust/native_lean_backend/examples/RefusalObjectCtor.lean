import NativeRust
namespace RefusalObjectCtor
  def produce (x : UInt64) : Sum UInt64 UInt64 := Sum.inl x
  def consume (x : Sum UInt64 UInt64) : UInt64 :=
    match x with
    | .inl n => n + 1
    | .inr n => n + 2
  def run (x : UInt64) : UInt64 := consume (produce x)
end RefusalObjectCtor
#native_rust_package [RefusalObjectCtor.run] to "examples/rejected-object-package"
