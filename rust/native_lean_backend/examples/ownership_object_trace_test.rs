// Test-only driver for the *same source-defined* Lean declarations compiled
// into this library by NativeRust. It observes the actual canonical runtime.
// Keep probe IDs local and derived from Rc allocation identity, not value.
#[cfg(test)]
mod source_object_trace_tests {
    use super::*;
    use std::fmt::Write as _;

    fn inspect(x: &__LeanValue, seen: &mut Vec<*const __LeanValueRepr>) -> String {
        assert!(x.source_heap(), "trace requires a source heap object");
        let ptr = std::rc::Rc::as_ptr(&x.0);
        let index = match seen.iter().position(|p| *p == ptr) {
            Some(i) => i,
            None => {
                assert!(seen.len() < 32, "trace allocation cap");
                seen.push(ptr);
                seen.len() - 1
            }
        };
        let count = x.1.get();
        assert!(count > 0, "trace on logically released object");
        format!("{} {}", index + 1, count)
    }

    #[test]
    fn trace() {
        let mut seen = Vec::new();
        let mut result = String::new();
        let first: usize = std::env::var("OWNERSHIP_OBJECT_TRACE_A").unwrap().parse().unwrap();
        let second: usize = std::env::var("OWNERSHIP_OBJECT_TRACE_B").unwrap().parse().unwrap();
        assert!(first < (usize::MAX >> 1) && second < (usize::MAX >> 1));
        let a = create(__LeanValue::tagged(first));
        writeln!(result, "TRACE create {}", inspect(&a, &mut seen)).unwrap();
        let same = identity(a.clone());
        writeln!(result, "TRACE direct {} {}", inspect(&a, &mut seen), inspect(&same, &mut seen)).unwrap();
        let b = create(__LeanValue::tagged(second));
        writeln!(result, "TRACE second {}", inspect(&b, &mut seen)).unwrap();
        let left = select(1u8, same.clone(), b.clone());
        writeln!(result, "TRACE branch-left {} {} {}", inspect(&same, &mut seen), inspect(&left, &mut seen), inspect(&b, &mut seen)).unwrap();
        let right = select(0u8, same.clone(), b.clone());
        writeln!(result, "TRACE branch-right {} {} {}", inspect(&same, &mut seen), inspect(&right, &mut seen), inspect(&b, &mut seen)).unwrap();
        let captured = throughClosure(left.clone());
        writeln!(result, "TRACE closure {} {}", inspect(&left, &mut seen), inspect(&captured, &mut seen)).unwrap();
        // Descendant ownership is observable without reading freed memory.
        // The fork's left child is itself a fork, so releasing the root
        // cascades across two generations; the right leaf is a direct child.
        let tree = createNested(__LeanValue::tagged(first), __LeanValue::tagged(second));
        let inner = tree.field(0);
        let grandchild = inner.field(0);
        let sibling = tree.field(1);
        grandchild.source_inc(1, true, false);
        sibling.source_inc(1, true, false);
        writeln!(
            result,
            "TRACE graph-before {} {} {} {}",
            inspect(&tree, &mut seen),
            inspect(&inner, &mut seen),
            inspect(&grandchild, &mut seen),
            inspect(&sibling, &mut seen),
        ).unwrap();
        // The live Rust aliases are memory-safety handles, not extra Lean
        // source references. Only this source decrement destroys the tree.
        tree.source_dec(1, true, false);
        writeln!(
            result,
            "TRACE graph-after {} {}",
            inspect(&grandchild, &mut seen),
            inspect(&sibling, &mut seen),
        ).unwrap();
        grandchild.source_dec(1, true, false);
        sibling.source_dec(1, true, false);

        std::fs::write(std::env::var_os("OWNERSHIP_OBJECT_TRACE_OUT").expect("trace output path"), result).unwrap();
    }
}
