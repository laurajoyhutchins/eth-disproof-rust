import NativeRust

-- The generic constructor backend supports pointer fields (including Option).
-- A native UInt64 field instead exercises the intentionally unsupported
-- scalar-packed constructor layout; compilation must refuse without publishing.
namespace RefusalObjectCtor
  inductive Unverified where
    | pack (value : UInt64)
    | empty
  def produce (x : UInt64) : Unverified := .pack x
end RefusalObjectCtor
#native_rust_package [RefusalObjectCtor.produce] to "examples/rejected-object-package"
