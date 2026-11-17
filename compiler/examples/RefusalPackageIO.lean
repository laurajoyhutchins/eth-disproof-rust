import NativeRust

namespace RefusalIO
  def root : IO Unit := IO.println "this effect must never be substituted by Rust"
end RefusalIO

#native_rust_package [RefusalIO.root] to "examples/rejected-package"
