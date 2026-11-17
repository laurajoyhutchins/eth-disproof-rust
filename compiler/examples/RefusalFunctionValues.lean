import NativeRust

namespace RefusalFunctionValues
  @[noinline] def bad (x : String) : String := x ++ "!"
  @[noinline] def applyValue (f : String → String) (x : String) : String := f x
  def root (s : String) : String := applyValue (bad) s
end RefusalFunctionValues

#native_rust_package [RefusalFunctionValues.root] to "examples/rejected-function-package"
