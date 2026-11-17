import NativeRust

namespace NameBoundary

def bump (n : UInt64) : UInt64 := n + 1

end NameBoundary

#native_rust_closure NameBoundary.bump as "bad$name" to "examples/unsafe-public-name.rs"
