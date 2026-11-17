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

    fn id_from_observation(s: &str) -> &str {
        s.split(' ').next().expect("source identity")
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
        // A second independent object crosses a genuine source-defined
        // direct call; Rust Rc aliases do not merge its source identity.
        let same_b = identity(b.clone());
        writeln!(result, "TRACE second-direct {} {} {}", inspect(&a, &mut seen), inspect(&b, &mut seen), inspect(&same_b, &mut seen)).unwrap();
        let left = select(1u8, same.clone(), b.clone());
        writeln!(result, "TRACE branch-left {} {} {}", inspect(&same, &mut seen), inspect(&left, &mut seen), inspect(&b, &mut seen)).unwrap();
        let right = select(0u8, same.clone(), b.clone());
        writeln!(result, "TRACE branch-right {} {} {}", inspect(&same, &mut seen), inspect(&right, &mut seen), inspect(&b, &mut seen)).unwrap();
        writeln!(result, "TRACE branch-owners {} {} {} {}", inspect(&same, &mut seen), inspect(&left, &mut seen), inspect(&b, &mut seen), inspect(&right, &mut seen)).unwrap();
        let captured = throughClosure(left.clone());
        writeln!(result, "TRACE closure {} {}", inspect(&left, &mut seen), inspect(&captured, &mut seen)).unwrap();
        // Descendant ownership is observable without reading freed memory.
        // The fork's left child is itself a fork, so releasing the root
        // cascades across two generations; the right leaf is a direct child.
        let tree = createNested(__LeanValue::tagged(first), __LeanValue::tagged(second));
        let inner = tree.field(0);
        let grandchild = inner.field(0);
        let sibling = tree.field(1);
        let cousin = inner.field(1);
        // First-observation boundary of the fully constructed graph.
        // Rust's Rc handles do not grant additional source credits.
        let root_obs = inspect(&tree, &mut seen);
        let inner_obs = inspect(&inner, &mut seen);
        let grand_obs = inspect(&grandchild, &mut seen);
        let sibling_obs = inspect(&sibling, &mut seen);
        let cousin_obs = inspect(&cousin, &mut seen);
        writeln!(result, "HEAP seed {} 0", grand_obs).unwrap();
        writeln!(result, "HEAP seed {} 0", cousin_obs).unwrap();
        writeln!(result, "HEAP seed {} 2 {} {}", inner_obs, id_from_observation(&grand_obs), id_from_observation(&cousin_obs)).unwrap();
        writeln!(result, "HEAP seed {} 0", sibling_obs).unwrap();
        writeln!(result, "HEAP seed {} 2 {} {}", root_obs, id_from_observation(&inner_obs), id_from_observation(&sibling_obs)).unwrap();
        for observed in [&root_obs, &inner_obs, &grand_obs, &cousin_obs, &sibling_obs] {
            writeln!(result, "HEAP observe {}", observed).unwrap();
        }
        let grand_before = grandchild.1.get();
        grandchild.source_inc(1, true, false);
        writeln!(result, "HEAP retain {} {} {}", id_from_observation(&grand_obs), grand_before, grandchild.1.get()).unwrap();
        let sibling_before = sibling.1.get();
        sibling.source_inc(1, true, false);
        writeln!(result, "HEAP retain {} {} {}", id_from_observation(&sibling_obs), sibling_before, sibling.1.get()).unwrap();
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
        writeln!(result, "HEAP release {}", inspect(&tree, &mut seen)).unwrap();
        tree.source_dec(1, true, false);
        writeln!(result, "HEAP observe {}", inspect(&grandchild, &mut seen)).unwrap();
        writeln!(result, "HEAP observe {}", inspect(&sibling, &mut seen)).unwrap();
        writeln!(
            result,
            "TRACE graph-after {} {}",
            inspect(&grandchild, &mut seen),
            inspect(&sibling, &mut seen),
        ).unwrap();
        writeln!(result, "HEAP release {}", inspect(&grandchild, &mut seen)).unwrap();
        grandchild.source_dec(1, true, false);
        writeln!(result, "HEAP release {}", inspect(&sibling, &mut seen)).unwrap();
        sibling.source_dec(1, true, false);

        std::fs::write(std::env::var_os("OWNERSHIP_OBJECT_TRACE_OUT").expect("trace output path"), result).unwrap();
    }
}
