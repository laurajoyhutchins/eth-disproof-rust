import NativeRust
import PropertyDef

-- Measures Lean process startup, plugin loading, and imported module access
-- without executing NativeRust.compileClosure or emitting Rust source.
#check Property.hop
