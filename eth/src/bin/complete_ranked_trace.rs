//! Emit complete, source-bound Lean obligations from production Rust runs.
//!
//! Unlike the arithmetic-only fixture, these are the *actual ordered calls*
//! made by the ranked-certificate counter. The generated Lean checker
//! independently replays the full schedule, including early overflow.
use lean_eth_reference::Error;
use lean_eth_reference::representation_ranked_certificate::{
    ArithmeticKind, ArithmeticReceipt, RankedComponentCertificate,
    contract_checked_ranked_weights, contract_checked_ranked_weights_with_trace,
};

struct Fixture {
    name: &'static str,
    weights: Vec<[i128; 2]>,
    edges: Vec<(usize, usize)>,
    certificate: RankedComponentCertificate,
}

fn fixtures() -> Vec<Fixture> {
    vec![
        Fixture {
            name: "successful",
            weights: vec![[2, -3], [-1, 4], [5, -2]],
            edges: vec![(0, 1)],
            certificate: RankedComponentCertificate {
                labels: vec![0, 0, 1],
                roots: vec![0, 2],
                parent_edge_indices: vec![None, Some(0), None],
                rank: vec![0, 1, 0],
            },
        },
        Fixture {
            name: "scanRefusal",
            weights: vec![[i128::MAX, 1], [2, 1]],
            edges: vec![(0, 1)],
            certificate: RankedComponentCertificate {
                labels: vec![0, 0],
                roots: vec![0],
                parent_edge_indices: vec![None, Some(0)],
                rank: vec![0, 1],
            },
        },
        Fixture {
            name: "finishRefusal",
            weights: vec![[i128::MAX, 1]],
            edges: vec![],
            certificate: RankedComponentCertificate {
                labels: vec![0],
                roots: vec![0],
                parent_edge_indices: vec![None],
                rank: vec![0],
            },
        },
    ]
}

fn word(value: i128) -> String {
    format!("(BitVec.ofInt 128 ({value} : ℤ))")
}

fn lookup(name: &str, domain: usize, codomain: &str, values: &[String]) {
    assert_eq!(values.len(), domain);
    assert!(!values.is_empty());
    print!("def {name} : Fin {domain} → {codomain} := fun i => ");
    for (index, value) in values.iter().enumerate() {
        if index + 1 < values.len() {
            print!("if i.val = {index} then {value} else ");
        } else {
            println!("{value}");
        }
    }
}

fn emit_source(fixture: &Fixture) {
    let p = fixture.name;
    let n = fixture.weights.len();
    let c = fixture.certificate.roots.len();
    let e = fixture.edges.len();

    assert!(n > 0 && c > 0);
    assert_eq!(fixture.certificate.labels.len(), n);
    assert_eq!(fixture.certificate.parent_edge_indices.len(), n);
    assert_eq!(fixture.certificate.rank.len(), n);

    print!("def {p}Edges : List (Fin {n} × Fin {n}) := [");
    for (index, &(a, b)) in fixture.edges.iter().enumerate() {
        if index != 0 {
            print!(", ");
        }
        print!("({a}, {b})");
    }
    println!("]");

    lookup(
        &format!("{p}Labels"),
        n,
        &format!("Fin {c}"),
        &fixture
            .certificate
            .labels
            .iter()
            .map(|v| format!("({v} : Fin {c})"))
            .collect::<Vec<_>>(),
    );
    lookup(
        &format!("{p}Roots"),
        c,
        &format!("Fin {n}"),
        &fixture
            .certificate
            .roots
            .iter()
            .map(|v| format!("({v} : Fin {n})"))
            .collect::<Vec<_>>(),
    );
    lookup(
        &format!("{p}Parents"),
        n,
        &format!("Option (Fin {p}Edges.length)"),
        &fixture
            .certificate
            .parent_edge_indices
            .iter()
            .map(|v| match v {
                None => "none".to_owned(),
                Some(index) => format!("some ({index} : Fin {e})"),
            })
            .collect::<Vec<_>>(),
    );
    lookup(
        &format!("{p}Rank"),
        n,
        "ℕ",
        &fixture
            .certificate
            .rank
            .iter()
            .map(usize::to_string)
            .collect::<Vec<_>>(),
    );
    lookup(
        &format!("{p}Weights"),
        n,
        "Bool → Word",
        &fixture
            .weights
            .iter()
            .map(|w| format!("(fun bit => if bit then {} else {})", word(w[1]), word(w[0])))
            .collect::<Vec<_>>(),
    );
}

fn emit_receipts(name: &str, receipts: &[ArithmeticReceipt], observed: Option<i128>) {
    println!("def {name}Trace : List Receipt := [");
    for (index, receipt) in receipts.iter().enumerate() {
        let kind = match receipt.kind {
            ArithmeticKind::Add => ".add",
            ArithmeticKind::Mul => ".mul",
        };
        let result = match receipt.observed {
            Some(value) => format!("some {}", word(value)),
            None => "none".to_owned(),
        };
        let end = if index + 1 == receipts.len() {
            ""
        } else {
            ","
        };
        println!(
            "  {{ kind := {kind}, left := {}, right := {}, observed := {result} }}{end}",
            word(receipt.left),
            word(receipt.right)
        );
    }
    println!("]");
    let result = match observed {
        Some(value) => format!("some {}", word(value)),
        None => "none".to_owned(),
    };
    println!("def {name}Result : Option Word := {result}");
}

fn emit_checks(name: &str, successful: bool) {
    let args = format!(
        "{name}Edges {name}Labels {name}Roots {name}Parents {name}Rank {name}Weights"
    );
    println!(
        "example : checkComplete {args} {name}Trace {name}Result = true := by decide"
    );
    println!(
        "example : checkComplete {args} ({name}Trace.drop 1) {name}Result = false := by decide"
    );
    println!(
        "example : checkComplete {args} {name}Trace.reverse {name}Result = false := by decide"
    );
    println!(
        "example : checkComplete {args} {name}Trace (some {}) = false := by decide",
        word(9999)
    );
    println!(
        "example : checkComplete {name}Edges {name}Labels {name}Roots {name}Parents {name}Rank (fun i bit => if i = (0 : Fin {}) then {} else {name}Weights i bit) {name}Trace {name}Result = false := by decide",
        if name == "successful" { 3 } else if name == "scanRefusal" { 2 } else { 1 },
        word(999)
    );
    if successful {
        // The verifier proves the source-level count rather than trusting
        // the claimed integer, including negative weights and a disconnected class.
        println!(
            "example : ({word} : Word).toInt =              (∑ x : {{x : Fin 3 → Bool // ∀ edge ∈ successfulEdges, x edge.1 = x edge.2}},                ∏ i : Fin 3, (successfulWeights i (x.1 i)).toInt) := by",
            word = word(-42)
        );
        println!(
            "  exact checkComplete_success_sound successfulEdges successfulLabels successfulRoots successfulParents successfulRank successfulWeights successfulTrace ({} : Word) (by decide)",
            word(-42)
        );
    }
}

fn main() {
    println!("import ACC.CompleteExecutionTrace");
    println!("open ACC.CompleteExecutionTrace");
    println!("open ACC.ArithmeticReceipts");
    println!("open ACC.CheckedI128BitVec");
    println!("set_option maxRecDepth 4096");
    println!("set_option maxHeartbeats 2000000");

    for fixture in fixtures() {
        let (result, trace) = contract_checked_ranked_weights_with_trace(
            &fixture.weights,
            &fixture.edges,
            &fixture.certificate,
        );
        let ordinary = contract_checked_ranked_weights(
            &fixture.weights,
            &fixture.edges,
            &fixture.certificate,
        );
        assert_eq!(result, ordinary, "traced path changed the counter");
        let observed = match result {
            Ok(receipt) => Some(receipt.value),
            Err(Error::Overflow) => None,
            Err(other) => panic!("fixture {} failed unexpectedly: {other:?}", fixture.name),
        };
        assert!(!trace.is_empty(), "fixture must exercise arithmetic");
        if observed.is_none() {
            assert!(trace.last().is_some_and(|last| last.observed.is_none()));
        }
        emit_source(&fixture);
        emit_receipts(fixture.name, &trace, observed);
        emit_checks(fixture.name, observed.is_some());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn full_trace_is_ordered_and_stops_on_overflow() {
        let cases = fixtures();
        let (success, trace) = contract_checked_ranked_weights_with_trace(
            &cases[0].weights,
            &cases[0].edges,
            &cases[0].certificate,
        );
        assert_eq!(success.unwrap().value, -42);
        assert_eq!(trace.len(), 10); // 2*n scan mul + 2*c final ops
        assert_eq!(trace.iter().filter(|r| r.kind == ArithmeticKind::Add).count(), 2);
        assert!(trace.iter().all(|r| r.observed.is_some()));

        for (index, expected_len) in [(1, 3), (2, 3)] {
            let fixture = &cases[index];
            let (result, trace) = contract_checked_ranked_weights_with_trace(
                &fixture.weights,
                &fixture.edges,
                &fixture.certificate,
            );
            assert_eq!(result, Err(Error::Overflow));
            assert_eq!(trace.len(), expected_len);
            assert!(trace.last().is_some_and(|r| r.observed.is_none()));
            assert!(trace[..trace.len() - 1].iter().all(|r| r.observed.is_some()));
        }
    }
}
