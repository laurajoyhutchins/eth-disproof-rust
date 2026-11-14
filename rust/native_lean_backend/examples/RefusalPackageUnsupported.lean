import NativeRust
namespace UnsupportedPackage
 def notSupported (x : String) : String := x ++ "!"
end UnsupportedPackage
#native_rust_package [UnsupportedPackage.notSupported] to "examples/rejected-package"
