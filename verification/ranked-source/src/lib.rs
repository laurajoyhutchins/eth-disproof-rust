//! Verification-only crate compiling exactly the existing production modules.
//!
//! #[path] keeps the byte decoder, certificate guard, scan/finalizer and
//! observer in their original repository files; no duplicate implementation
//! is permitted. This is useful for Charon to select a library-only entrypoint.
//! A Rust proof about this crate still requires translating the source itself
//! and auditing external library models. Ordinary unit tests are not proofs.
pub use lean_eth_reference::Error;

#[path = "../../../eth/src/representation_ranked_certificate.rs"]
pub mod representation_ranked_certificate;
#[path = "../../../eth/src/representation_ranked_input.rs"]
pub mod representation_ranked_input;

#[cfg(test)]
mod tests {
    use super::representation_ranked_input as source;
    use lean_eth_reference::representation_ranked_certificate::RankedComponentCertificate;
    use lean_eth_reference::representation_ranked_input as production;

    #[test]
    fn identical_source_files_agree_with_production_on_canonical_and_bad_bytes() {
        let input = production::RankedContractionInput {
            source_edges: vec![(0, 1)],
            weights: vec![[2, -3], [-1, 4], [5, -2]],
            certificate: RankedComponentCertificate {
                labels: vec![0, 0, 1],
                roots: vec![0, 2],
                parent_edge_indices: vec![None, Some(0), None],
                rank: vec![0, 1, 0],
            },
        };
        let mut bytes = production::encode_ranked_input(&input).unwrap();
        for case in 0..3 {
            let actual = source::execute_ranked_wire(&bytes);
            let expected = production::execute_ranked_wire(&bytes);
            assert_eq!(
                actual.0.map(|r| (r.value, r.component_count, r.checked_multiplications)),
                expected.0.map(|r| (r.value, r.component_count, r.checked_multiplications))
            );
            let normalize_a = actual.1.iter().map(|r| (r.kind == super::representation_ranked_certificate::ArithmeticKind::Add, r.left, r.right, r.observed)).collect::<Vec<_>>();
            let normalize_b = expected.1.iter().map(|r| (r.kind == lean_eth_reference::representation_ranked_certificate::ArithmeticKind::Add, r.left, r.right, r.observed)).collect::<Vec<_>>();
            assert_eq!(normalize_a, normalize_b);
            if case == 0 { bytes.push(0); }
            if case == 1 { bytes[0] = b'X'; }
        }
    }
}
