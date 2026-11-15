//! Canonical, injective Lean.Name and generated Rust symbol encoding.
//! Lean object traversal stays in the IR reader; this module owns only text identity.
use std::fmt::Write;

// The path separators cannot occur inside a canonical component: plain
// ASCII components exclude '.', '~'; special strings and Nat segments use
// disjoint prefixed encodings. The original Lean.Name object crosses FFI.
pub(super) fn append_name_component(parent: &str, component: &str) -> String {
    if parent.is_empty() {
        component.to_owned()
    } else {
        format!("{parent}.{component}")
    }
}

pub(super) fn encode_name_str(component: &str) -> Result<String, String> {
    if component.len() > 4096 {
        return Err("Lean.Name string component exceeds safety cap".into());
    }
    if !component.is_empty()
        && !component.as_bytes()[0].is_ascii_digit()
        && component
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'!')
    {
        return Ok(component.to_owned());
    }
    let mut encoded = String::from("~s");
    for byte in component.as_bytes() {
        write!(&mut encoded, "{byte:02x}").unwrap();
    }
    Ok(encoded)
}

// Emitted Rust function names remain injective for all canonical Lean paths.
// Naming is injective over UTF-8 bytes and independent of declaration ordering.
pub(super) fn internal_closure_name(lean_name: &str) -> String {
    format!("__pap_{}", internal_name(lean_name))
}

pub(super) fn internal_name(lean_name: &str) -> String {
    let mut out = String::from("lean_");
    for byte in lean_name.as_bytes() {
        write!(&mut out, "{byte:02x}").unwrap();
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn component_kinds_have_disjoint_encodings() {
        let plain = append_name_component("Pkg", &encode_name_str("a_b").unwrap());
        let dot = append_name_component("Pkg", &encode_name_str("a.b").unwrap());
        let numeric_string = append_name_component("Pkg", &encode_name_str("9").unwrap());
        let numeric_segment = append_name_component("Pkg", "~n9");
        let unicode = append_name_component("Pkg", &encode_name_str("é").unwrap());
        let paths = [plain, dot, numeric_string, numeric_segment, unicode];
        let unique: std::collections::BTreeSet<_> = paths.iter().collect();
        assert_eq!(unique.len(), paths.len());
        for path in paths {
            assert_ne!(internal_name(&path), internal_closure_name(&path));
        }
    }
}
