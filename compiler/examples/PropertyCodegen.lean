import NativeRust
import PropertyDef

-- Code-generation-only benchmark: no seeded Lean oracle runs in this file.
-- It emits the original Property.hop executable IR dependency closure.
#native_rust_closure Property.hop as "property_hop" to "examples/generated_property.rs"
