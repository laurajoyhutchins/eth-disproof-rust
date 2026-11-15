//! One semantic whitelist for both IR dependency discovery and primitive lowering.
//! Registry-backed lowerings and source-specific runtime externs fail closed.

pub(super) const PRIMITIVE_REGISTRY: &str = include_str!("../primitive-registry.tsv");

pub(super) struct PrimitiveSpec<'a> {
    pub(super) operand_type: &'a str,
    pub(super) rust_op: &'a str,
    pub(super) comparison: bool,
}

pub(super) fn primitive_spec(name: &str) -> Option<PrimitiveSpec<'static>> {
    PRIMITIVE_REGISTRY
        .lines()
        .filter(|line| !line.starts_with('#') && !line.is_empty())
        .find_map(|line| {
            let mut cells = line.split('\t');
            let id = cells.next()?;
            let operand_type = cells.next()?;
            let rust_op = cells.next()?;
            let kind = cells.next()?;
            if cells.next().is_some() || id != name {
                return None;
            }
            Some(PrimitiveSpec {
                operand_type,
                rust_op,
                comparison: kind == "comparison",
            })
        })
}

// The supported Nat runtime is explicit, with no fallback to host arithmetic.
// Both dependency discovery and native codegen consult this exact whitelist.
pub(super) fn is_nat_primitive(name: &str) -> bool {
    matches!(
        name,
        "Nat.add"
            | "Nat.sub"
            | "Nat.mul"
            | "Nat.div"
            | "Nat.mod"
            | "Nat.decEq"
            | "Nat.decLt"
            | "Nat.decLe"
    )
}

pub(super) fn is_primitive(name: &str) -> bool {
    primitive_spec(name).is_some()
        || is_nat_primitive(name)
        || runtime_primitive_spec(name).is_some()
        || matches!(
            name,
            "Array.mkEmpty" | "Array.getInternal" | "Array.getInternalBorrowed" | "Array.set!"
        )
}

pub(super) const RUNTIME_PRIMITIVE_REGISTRY: &str = include_str!("../runtime-primitive-registry.tsv");
pub(super) struct RuntimePrimitiveSpec<'a> {
    pub(super) rust_function: &'a str,
    pub(super) shape: &'a str,
}
pub(super) fn runtime_primitive_spec(name: &str) -> Option<RuntimePrimitiveSpec<'static>> {
    RUNTIME_PRIMITIVE_REGISTRY
        .lines()
        .filter(|line| !line.starts_with('#') && !line.is_empty())
        .find_map(|line| {
            let mut cells = line.split('\t');
            let id = cells.next()?;
            let rust_function = cells.next()?;
            let shape = cells.next()?;
            if cells.next().is_some() || id != name {
                return None;
            }
            Some(RuntimePrimitiveSpec {
                rust_function,
                shape,
            })
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unsupported_runtime_primitives_are_not_inferred() {
        for name in ["Nat.pow", "Array.pop", "IO.println", "IO.getLine", "Unknown.foo"] {
            assert!(!is_primitive(name), "{name} must not silently lower");
        }
        for name in ["Nat.add", "Nat.div", "Int.add", "Array.set!", "Array.getInternal"] {
            assert!(is_primitive(name), "{name} must remain supported");
        }
    }
}
