//! Read-only source-stage and evidence-boundary report.
//!
//! This is a view of the canonical `remaining::STAGES` registry and the
//! locally pinned upstream manifest. No stage status certifies Lean/Rust
//! refinement, proof completeness, or a complexity bound.
use lean_eth_reference::remaining::{Machine, SOURCE_COMMIT, STAGES, Status};
use serde_json::{Value, json};
use std::collections::HashSet;

const SOURCE_PREFIX: &str = "lean/OAI/Algorithms/SubexponentialSAT/";
const MANIFEST: &str = include_str!("../../reference/source-manifest.json");

fn status_name(status: Status) -> &'static str {
    match status {
        Status::Executable => "executable",
        Status::Partial => "partial",
        Status::Stub => "stub",
        Status::Noncomputable => "noncomputable",
        Status::ProofObligation => "proof_obligation",
    }
}

fn machine_name(machine: Machine) -> &'static str {
    match machine {
        Machine::Local => "local",
        Machine::Outer => "outer",
        Machine::Tm2 => "tm2",
        Machine::Proof => "proof",
    }
}

// Return every non-executable ancestor in the canonical topological order.
// An executable stage is only a Rust implementation status, not a proof.
fn blockers(target: &str) -> Result<Vec<&'static str>, String> {
    let mut pending = vec![target];
    let mut reachable = HashSet::new();
    while let Some(id) = pending.pop() {
        if !reachable.insert(id.to_owned()) {
            continue;
        }
        let stage = STAGES
            .iter()
            .find(|stage| stage.id == id)
            .ok_or_else(|| format!("unknown registry prerequisite: {id}"))?;
        pending.extend(stage.requires.iter().copied());
    }
    Ok(STAGES
        .iter()
        .filter(|stage| reachable.contains(stage.id) && stage.status != Status::Executable)
        .map(|stage| stage.id)
        .collect())
}

fn report_from_manifest(source: &str) -> Result<Value, String> {
    let manifest: Value =
        serde_json::from_str(source).map_err(|err| format!("invalid source manifest: {err}"))?;
    if manifest["repository"].as_str() != Some("openai/math")
        || manifest["commit"].as_str() != Some(SOURCE_COMMIT)
    {
        return Err("source repository/commit differs from the canonical registry".into());
    }
    let files = manifest["files"]
        .as_object()
        .ok_or("source manifest has no files object")?;

    let mut seen = HashSet::new();
    let mut stages = Vec::with_capacity(STAGES.len());
    for stage in STAGES {
        if !seen.insert(stage.id) {
            return Err(format!("duplicate stage id: {}", stage.id));
        }
        for dependency in stage.requires {
            if !seen.contains(dependency) {
                return Err(format!(
                    "{} references absent or unordered dependency {dependency}",
                    stage.id
                ));
            }
        }

        let source_path = format!("{SOURCE_PREFIX}{}", stage.source_file);
        let blob = files
            .get(&source_path)
            .and_then(Value::as_str)
            .ok_or_else(|| format!("missing source blob pin for {}", stage.id))?;
        if blob.len() != 40
            || !blob
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            return Err(format!("malformed source blob pin for {}", stage.id));
        }
        stages.push(json!({
            "id": stage.id,
            "lean_symbol": stage.lean_symbol,
            "source_path": source_path,
            "source_blob_sha": blob,
            "machine": machine_name(stage.machine),
            "implementation_status": status_name(stage.status),
            "requires": stage.requires,
            "lean_rust_correspondence": "unassessed",
            "physical_runtime_correspondence": "unassessed",
            "tm2_resource_correspondence": "unassessed"
        }));
    }

    Ok(json!({
        "schema": "eth-source-stage-evidence/v1",
        "source_repository": "openai/math",
        "source_revision": SOURCE_COMMIT,
        "pin_check": "local_manifest_shape_only",
        "evidence_scope": "implementation registry, not a correctness certificate",
        "correspondence_policy": "unassessed until a separate scoped exact-revision receipt is provided",
        "stages": stages,
        "blocked_paths": {
            "query_stream": blockers("query_stream")?,
            "counting_program": blockers("counting_program")?
        }
    }))
}

fn run() -> Result<(), String> {
    match std::env::args().skip(1).collect::<Vec<_>>().as_slice() {
        [] => {}
        [flag] if flag == "--json" => {}
        [flag] if flag == "--help" || flag == "-h" => {
            println!("Usage: eth-stage-evidence [--json]");
            println!("Read-only stage graph; no Lean/Rust proof or runtime receipt is inferred.");
            return Ok(());
        }
        _ => return Err("expected no arguments or --json (use --help)".into()),
    }
    let report = report_from_manifest(MANIFEST)?;
    let rendered = serde_json::to_string_pretty(&report).map_err(|err| err.to_string())?;
    println!("{rendered}");
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eth-stage-evidence: {error}");
        std::process::exit(2);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn report_is_registry_derived_and_never_infers_proof() {
        let report = report_from_manifest(MANIFEST).unwrap();
        let stages = report["stages"].as_array().unwrap();
        assert_eq!(stages.len(), STAGES.len());
        assert_eq!(report["source_revision"], SOURCE_COMMIT);
        for (record, stage) in stages.iter().zip(STAGES) {
            assert_eq!(record["id"], stage.id);
            assert_eq!(record["implementation_status"], status_name(stage.status));
            assert_eq!(record["lean_rust_correspondence"], "unassessed");
            assert_eq!(record["physical_runtime_correspondence"], "unassessed");
            assert_eq!(record["tm2_resource_correspondence"], "unassessed");
        }
        assert_eq!(report["pin_check"], "local_manifest_shape_only");
    }

    #[test]
    fn graph_exposes_actual_missing_prerequisites() {
        let report = report_from_manifest(MANIFEST).unwrap();
        let query = report["blocked_paths"]["query_stream"].as_array().unwrap();
        assert!(query.contains(&json!("signature_loader")));
        assert!(query.contains(&json!("query_stream")));
        let count = report["blocked_paths"]["counting_program"].as_array().unwrap();
        assert!(count.contains(&json!("finite_fallback")));
        assert!(count.contains(&json!("counting_program")));
    }

    #[test]
    fn manifest_drift_refuses_instead_of_inventing_evidence() {
        let mut manifest: Value = serde_json::from_str(MANIFEST).unwrap();
        manifest["commit"] = json!("0".repeat(40));
        assert!(report_from_manifest(&manifest.to_string()).is_err());

        let mut manifest: Value = serde_json::from_str(MANIFEST).unwrap();
        let path = format!("{SOURCE_PREFIX}BitProgram.lean");
        manifest["files"].as_object_mut().unwrap().remove(&path);
        assert!(report_from_manifest(&manifest.to_string()).is_err());

        let mut manifest: Value = serde_json::from_str(MANIFEST).unwrap();
        manifest["files"][path] = json!("NOT_A_GIT_BLOB");
        assert!(report_from_manifest(&manifest.to_string()).is_err());
    }
}
