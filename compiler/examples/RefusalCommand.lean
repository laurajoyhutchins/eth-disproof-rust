import NativeRust

def nativeUnsupportedString (s : String) : String := s ++ "!"

-- The command must fail with an explicit refusal and must not replace or
-- create the requested output. The shell test checks both properties.
#native_rust nativeUnsupportedString as "invalid_output" to "examples/rejected.rs"
