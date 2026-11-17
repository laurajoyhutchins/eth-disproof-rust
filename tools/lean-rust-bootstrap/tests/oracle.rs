use std::path::Path;

use lean_rust_bootstrap::{
    probe_eta, probe_implemented_by, probe_inline_defs, probe_inline_partial,
};

fn parse_flag(raw: &str) -> bool {
    match raw {
        "0" => false,
        "1" => true,
        _ => panic!("malformed original Lean oracle flag: {raw:?}"),
    }
}

#[test]
fn upstream_compiler_configuration_matches_lean_for_all_tags() {
    let oracle = Path::new(env!("CARGO_MANIFEST_DIR")).join("oracle.tsv");
    let data = std::fs::read_to_string(&oracle)
        .unwrap_or_else(|e| panic!("original Lean oracle {} is missing: {e}", oracle.display()));
    let mut seen = [false; 256];
    let mut cases = 0;
    for line in data.lines() {
        let fields: Vec<_> = line.split('\t').collect();
        assert_eq!(fields.len(), 5, "malformed oracle row: {line}");
        let tag: u8 = fields[0].parse().expect("oracle tag must be UInt8");
        assert!(
            !seen[usize::from(tag)],
            "duplicate original Lean oracle tag {tag}"
        );
        seen[usize::from(tag)] = true;
        let actual = [
            probe_eta(tag),
            probe_inline_partial(tag),
            probe_implemented_by(tag),
            probe_inline_defs(tag),
        ];
        for (index, (&got, expected)) in actual.iter().zip(fields[1..].iter()).enumerate() {
            assert_eq!(got, parse_flag(expected), "tag={tag} field={index}");
        }
        cases += 1;
    }
    assert_eq!(cases, 256, "must check all 256 UInt8 tags");
    assert!(seen.into_iter().all(|x| x), "oracle skipped a tag");
}
