include!("generated_property.rs");
include!("generated_property_cases.rs");

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let filter_seed = match args.as_slice() {
        [_] => None,
        [_, flag, seed] if flag == "--seed" => Some(seed.parse::<u64>().expect("numeric seed")),
        _ => {
            eprintln!("usage: property-test [--seed NUMBER]");
            std::process::exit(2);
        }
    };

    let mut checked: usize = 0;
    // Minimize within the independently evaluated, finite shrink ladder.
    // This is not a general-purpose shrinking engine.
    let mut failure: Option<(u64, u64, u64, u64, u64, u64)> = None;
    for &(seed, fuel, x, expected, shrink_step) in CASES {
        if filter_seed.is_some_and(|s| s != seed) {
            continue;
        }
        checked += 1;
        let actual = property_hop(fuel, x);
        if actual != expected {
            let candidate = (seed, fuel, x, expected, actual, shrink_step);
            let better = failure.is_none_or(|old| {
                (candidate.0, candidate.1, candidate.2) < (old.0, old.1, old.2)
            });
            if better {
                failure = Some(candidate);
            }
        }
    }
    if checked == 0 {
        eprintln!("No cases selected for seed {filter_seed:?}");
        std::process::exit(2);
    }
    if let Some((seed, fuel, x, expected, actual, step)) = failure {
        eprintln!(
            "Lean/Rust mismatch: seed={seed} shrink_step={step} fuel={fuel} x={x} expected={expected} actual={actual}"
        );
        eprintln!("Reproduce with: examples/property-test --seed {seed}");
        std::process::exit(1);
    }
    println!("PASS: {checked} independent Lean/Rust property cases; seeds 0..127; 8 deterministic shrink candidates/seed");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_seeded_original_lean_outputs_match_generated_rust() {
        assert_eq!(CASES.len(), 1024);
        for &(seed, fuel, x, expected, step) in CASES {
            assert_eq!(
                property_hop(fuel, x),
                expected,
                "Lean oracle discrepancy for seed={seed}, fuel={fuel}, x={x}, shrink={step}"
            );
        }
    }

    #[test]
    fn boundaries_and_end_of_seed_series_are_present() {
        assert!(CASES.iter().any(|row| row.0 == 0 && row.2 == 0));
        assert!(CASES.iter().any(|row| row.0 == 127));
        assert!(CASES.iter().any(|row| row.2 == u64::MAX));
    }
}
