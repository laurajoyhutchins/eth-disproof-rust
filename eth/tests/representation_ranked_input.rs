//! Untrusted binary input is the authority, not an emitter's hand-copied
//! arrays. Exercise canonicality, indexed guard rejection, and deterministic
//! full-width signed weights against the *production* Rust parser.
use lean_eth_reference::representation_ranked_certificate::{
    RankedComponentCertificate, contract_checked_ranked_weights_with_trace,
};
use lean_eth_reference::representation_ranked_input::{
    RankedContractionInput, decode_ranked_input, encode_ranked_input,
};

fn fixture() -> RankedContractionInput {
    RankedContractionInput {
        weights: vec![[2, -3], [-1, 4], [5, -2]],
        source_edges: vec![(0, 1)],
        certificate: RankedComponentCertificate {
            labels: vec![0, 0, 1],
            roots: vec![0, 2],
            parent_edge_indices: vec![None, Some(0), None],
            rank: vec![0, 1, 0],
        },
    }
}

fn outcome(input: &RankedContractionInput) -> i128 {
    contract_checked_ranked_weights_with_trace(
        &input.weights,
        &input.source_edges,
        &input.certificate,
    )
    .0
    .unwrap()
    .value
}

#[test]
fn exact_bytes_replay_into_same_source_and_count() {
    let input = fixture();
    let bytes = encode_ranked_input(&input).unwrap();
    assert_eq!(&bytes[..4], b"RKC1");
    assert_eq!(bytes.len(), 28 + 16 + 3 * 56 + 2 * 8);
    let decoded = decode_ranked_input(&bytes).unwrap();
    assert_eq!(decoded, input);
    assert_eq!(encode_ranked_input(&decoded).unwrap(), bytes);
    assert_eq!(outcome(&decoded), -42);
}

#[test]
fn empty_region_is_canonical_and_counts_one() {
    let empty = RankedContractionInput {
        weights: vec![],
        source_edges: vec![],
        certificate: RankedComponentCertificate {
            labels: vec![],
            roots: vec![],
            parent_edge_indices: vec![],
            rank: vec![],
        },
    };
    let bytes = encode_ranked_input(&empty).unwrap();
    assert_eq!(bytes.len(), 28);
    assert_eq!(decode_ranked_input(&bytes).unwrap(), empty);
    assert_eq!(outcome(&empty), 1);
}

#[test]
fn corrupt_header_and_declared_size_are_refused() {
    let original = encode_ranked_input(&fixture()).unwrap();
    for length in 0..original.len() {
        assert!(
            decode_ranked_input(&original[..length]).is_err(),
            "accepted truncated stream length {length}"
        );
    }
    let mut extra = original.clone();
    extra.push(0);
    assert!(decode_ranked_input(&extra).is_err());

    let mut magic = original.clone();
    magic[0] ^= 0x10;
    assert!(decode_ranked_input(&magic).is_err());

    // Count fields are not trusted for allocation or payload slicing.
    let mut overflow_count = original.clone();
    overflow_count[4..12].copy_from_slice(&u64::MAX.to_le_bytes());
    assert!(decode_ranked_input(&overflow_count).is_err());
    let mut huge_edges = original.clone();
    huge_edges[20..28].copy_from_slice(&u64::MAX.to_le_bytes());
    assert!(decode_ranked_input(&huge_edges).is_err());
}

#[test]
fn malformed_indices_and_source_evidence_are_refused() {
    let original = encode_ranked_input(&fixture()).unwrap();
    // Format: header (28), edge (16), labels (24), roots (16),
    // parent links (24), ranks (24), weights (96).
    for (offset, value) in [
        (28usize, 3u64),                 // edge endpoint outside source vertices
        (28 + 16, 2u64),                // class label outside [0, classes)
        (28 + 16 + 24, 3u64),           // root outside source vertices
        (28 + 16 + 24 + 16 + 8, 2u64), // parent link outside edge list
        (28 + 16 + 24 + 16 + 24 + 8, 0u64), // nonroot rank fails decrease
    ] {
        let mut corrupt = original.clone();
        corrupt[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
        assert!(
            decode_ranked_input(&corrupt).is_err(),
            "accepted corrupt 64-bit field at {offset}"
        );
    }
}

fn next(seed: &mut u64) -> u64 {
    *seed = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut x = *seed;
    x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    x ^ (x >> 31)
}

fn weight(seed: &mut u64) -> i128 {
    ((u128::from(next(seed)) << 64) | u128::from(next(seed))) as i128
}

#[test]
fn many_signed_full_width_inputs_roundtrip_and_keep_exact_order() {
    let mut seed = 0x239d_4a1b_9f15_c3e7u64;
    for n in 1usize..=32 {
        for classes in 1..=n {
            let labels: Vec<_> = (0..n).map(|i| i % classes).collect();
            let roots: Vec<_> = (0..classes).collect();
            let mut edges = Vec::new();
            let mut parent_indices = vec![None; n];
            let mut ranks = vec![0; n];
            for i in classes..n {
                parent_indices[i] = Some(edges.len());
                ranks[i] = 1;
                edges.push((i, i % classes));
            }
            let weights = (0..n)
                .map(|_| [weight(&mut seed), weight(&mut seed)])
                .collect();
            let source = RankedContractionInput {
                weights,
                source_edges: edges,
                certificate: RankedComponentCertificate {
                    labels,
                    roots,
                    parent_edge_indices: parent_indices,
                    rank: ranks,
                },
            };
            let encoded = encode_ranked_input(&source).unwrap();
            let decoded = decode_ranked_input(&encoded).unwrap();
            assert_eq!(decoded, source);
            assert_eq!(encode_ranked_input(&decoded).unwrap(), encoded);
        }
    }
}
