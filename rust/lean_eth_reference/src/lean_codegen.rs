//! Shared, fail-closed artifact integrity contract for the two Lean codegen routes.
//! This module does NOT certify Lean-to-Rust semantic or physical equivalence.
use serde::de::{DeserializeOwned, Error as _, MapAccess, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fs;
use std::path::{Component, Path};
use std::process::Command;

pub type Result<T> = std::result::Result<T, String>;
const MAX_BYTES: usize = 8 * 1024 * 1024;
const MAX_NODES: usize = 10_000;

pub fn refuse<T>(message: impl Into<String>) -> Result<T> {
    Err(message.into())
}
pub fn ensure(ok: bool, message: impl Into<String>) -> Result<()> {
    if ok { Ok(()) } else { refuse(message) }
}
pub fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Backend {
    CompilerIr,
    ResidualExpr,
}
impl Backend {
    pub fn parse(value: &str) -> Result<Self> {
        match value {
            "compiler-ir" => Ok(Self::CompilerIr),
            "residual-expr" => Ok(Self::ResidualExpr),
            _ => refuse("backend must be compiler-ir or residual-expr"),
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            Self::CompilerIr => "compiler-ir",
            Self::ResidualExpr => "residual-expr",
        }
    }
    pub fn status(self) -> &'static str {
        match self {
            Self::CompilerIr => "generated-unverified",
            Self::ResidualExpr => "residualized-unverified",
        }
    }
}

/// serde_json normally accepts duplicate keys. A standard serde Visitor is
/// used here to reject duplicate keys at *every* level before typed decoding.
struct Unique(Value);
impl<'de> Deserialize<'de> for Unique {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> std::result::Result<Self, D::Error> {
        struct UniqueVisitor;
        impl<'de> Visitor<'de> for UniqueVisitor {
            type Value = Unique;
            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("JSON without duplicate object keys")
            }
            fn visit_bool<E: serde::de::Error>(self, v: bool) -> std::result::Result<Unique, E> {
                Ok(Unique(Value::Bool(v)))
            }
            fn visit_i64<E: serde::de::Error>(self, v: i64) -> std::result::Result<Unique, E> {
                Ok(Unique(Value::from(v)))
            }
            fn visit_u64<E: serde::de::Error>(self, v: u64) -> std::result::Result<Unique, E> {
                Ok(Unique(Value::from(v)))
            }
            fn visit_f64<E: serde::de::Error>(self, v: f64) -> std::result::Result<Unique, E> {
                serde_json::Number::from_f64(v)
                    .map(|n| Unique(Value::Number(n)))
                    .ok_or_else(|| E::custom("nonfinite JSON number"))
            }
            fn visit_str<E: serde::de::Error>(self, v: &str) -> std::result::Result<Unique, E> {
                Ok(Unique(Value::String(v.to_owned())))
            }
            fn visit_string<E: serde::de::Error>(
                self,
                v: String,
            ) -> std::result::Result<Unique, E> {
                Ok(Unique(Value::String(v)))
            }
            fn visit_unit<E: serde::de::Error>(self) -> std::result::Result<Unique, E> {
                Ok(Unique(Value::Null))
            }
            fn visit_none<E: serde::de::Error>(self) -> std::result::Result<Unique, E> {
                Ok(Unique(Value::Null))
            }
            fn visit_some<D: Deserializer<'de>>(
                self,
                d: D,
            ) -> std::result::Result<Unique, D::Error> {
                Unique::deserialize(d)
            }
            fn visit_seq<A: SeqAccess<'de>>(
                self,
                mut seq: A,
            ) -> std::result::Result<Unique, A::Error> {
                let mut out = Vec::new();
                while let Some(item) = seq.next_element::<Unique>()? {
                    out.push(item.0);
                }
                Ok(Unique(Value::Array(out)))
            }
            fn visit_map<A: MapAccess<'de>>(
                self,
                mut map: A,
            ) -> std::result::Result<Unique, A::Error> {
                let mut out = serde_json::Map::new();
                while let Some((key, value)) = map.next_entry::<String, Unique>()? {
                    if out.contains_key(&key) {
                        return Err(A::Error::custom(format!("duplicate JSON field: {key}")));
                    }
                    out.insert(key, value.0);
                }
                Ok(Unique(Value::Object(out)))
            }
        }
        deserializer.deserialize_any(UniqueVisitor)
    }
}

fn strict_json<T: DeserializeOwned>(raw: &[u8]) -> Result<T> {
    ensure(
        !raw.is_empty() && raw.len() <= MAX_BYTES,
        "JSON size outside bound",
    )?;
    ensure(!raw.starts_with(&[0xef, 0xbb, 0xbf]), "UTF-8 BOM forbidden")?;
    let Unique(value) = serde_json::from_slice::<Unique>(raw).map_err(|e| e.to_string())?;
    serde_json::from_value(value).map_err(|e| e.to_string())
}

/// Decode a backend JSON summary without losing duplicate-key evidence.
pub fn strict_json_value(raw: &[u8]) -> Result<Value> {
    strict_json(raw)
}

pub fn declaration(name: &str) -> bool {
    !name.is_empty()
        && name.split('.').all(|segment| {
            let mut chars = segment.chars();
            chars
                .next()
                .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
                && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
        })
}
fn sha1(value: &str) -> bool {
    value.len() == 40
        && value
            .bytes()
            .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
}
fn valid_pin(value: &str) -> bool {
    value.strip_prefix("leanprover/lean4:v").is_some_and(|v| {
        let parts: Vec<_> = v.split('.').collect();
        parts.len() == 3
            && parts
                .iter()
                .all(|p| !p.is_empty() && p.bytes().all(|b| b.is_ascii_digit()))
    })
}
pub fn version_matches(observed: &str, pin: &str) -> bool {
    let Some(v) = pin.strip_prefix("leanprover/lean4:v") else {
        return false;
    };
    observed.split("version ").skip(1).any(|rest| {
        rest.starts_with(v)
            && rest[v.len()..]
                .chars()
                .next()
                .is_none_or(|c| !c.is_ascii_digit() && c != '.')
    })
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceIdentity {
    pub git_revision: String,
    pub git_blob: String,
    pub path: String,
    pub lean_toolchain: String,
    pub lean_toolchain_git_blob: String,
    pub lean_toolchain_path: String,
}

fn git(repo: &Path, args: &[&str]) -> Result<String> {
    let out = Command::new("git")
        .arg("-C")
        .arg(repo)
        .args(args)
        .output()
        .map_err(|e| format!("Git unavailable: {e}"))?;
    ensure(
        out.status.success(),
        format!(
            "Git source identity failed: {}",
            String::from_utf8_lossy(&out.stderr)
        ),
    )?;
    String::from_utf8(out.stdout)
        .map(|v| v.trim().to_owned())
        .map_err(|e| e.to_string())
}
fn checked_path(root: &Path, user: &str) -> Result<String> {
    let p = Path::new(user);
    ensure(
        !p.is_absolute() && !user.contains(':'),
        "source paths must be relative",
    )?;
    ensure(
        p.components().all(|c| matches!(c, Component::Normal(_))),
        "noncanonical relative source path",
    )?;
    let original = root
        .join(p)
        .canonicalize()
        .map_err(|e| format!("missing source path: {e}"))?;
    ensure(
        original.is_file() && original.starts_with(root),
        "source escapes repository or is not a file",
    )?;
    let relative = original
        .strip_prefix(root)
        .map_err(|e| e.to_string())?
        .to_str()
        .ok_or("non-UTF-8 source path")?
        .to_owned();
    ensure(relative == user, "source path is not canonical")?;
    Ok(relative)
}
pub fn source_identity(
    repo: &Path,
    source: &str,
    pin_path: &str,
    revision: &str,
) -> Result<SourceIdentity> {
    ensure(
        sha1(revision),
        "source revision must be a full lowercase Git SHA",
    )?;
    let root = repo.canonicalize().map_err(|e| e.to_string())?;
    ensure(
        git(&root, &["rev-parse", "--show-toplevel"])? == root.to_string_lossy(),
        "source repository is not a Git root",
    )?;
    ensure(
        git(&root, &["rev-parse", "HEAD"])? == revision,
        "source HEAD differs from pinned revision",
    )?;
    let src = checked_path(&root, source)?;
    let pin = checked_path(&root, pin_path)?;
    let src_ref = format!("{revision}:{src}");
    let pin_ref = format!("{revision}:{pin}");
    let src_blob = git(&root, &["rev-parse", &src_ref])?;
    let pin_blob = git(&root, &["rev-parse", &pin_ref])?;
    ensure(
        sha1(&src_blob) && sha1(&pin_blob),
        "invalid source Git blob",
    )?;
    ensure(
        git(&root, &["hash-object", &src])? == src_blob,
        "source working file does not match Git blob",
    )?;
    ensure(
        git(&root, &["hash-object", &pin])? == pin_blob,
        "source Lean toolchain file does not match Git blob",
    )?;
    let toolchain = fs::read_to_string(root.join(&pin)).map_err(|e| e.to_string())?;
    let toolchain = toolchain.trim().to_owned();
    ensure(valid_pin(&toolchain), "invalid pinned Lean toolchain")?;
    Ok(SourceIdentity {
        git_revision: revision.to_owned(),
        git_blob: src_blob,
        path: src,
        lean_toolchain: toolchain,
        lean_toolchain_git_blob: pin_blob,
        lean_toolchain_path: pin,
    })
}

#[derive(Debug, Deserialize)]
#[serde(tag = "tag", rename_all = "lowercase", deny_unknown_fields)]
enum LeanName {
    Anonymous,
    Str {
        parent: Box<LeanName>,
        value: String,
    },
    Num {
        parent: Box<LeanName>,
        value: u64,
    },
}
impl LeanName {
    fn text(&self, depth: usize) -> Result<String> {
        ensure(depth < 200, "Lean name too deep")?;
        match self {
            Self::Anonymous => Ok(String::new()),
            Self::Str { parent, value } => {
                ensure(!value.is_empty(), "empty Lean name segment")?;
                let p = parent.text(depth + 1)?;
                Ok(if p.is_empty() {
                    value.clone()
                } else {
                    format!("{p}.{value}")
                })
            }
            Self::Num { parent, value } => {
                ensure(*value <= u32::MAX.into(), "invalid Lean numeric name")?;
                let p = parent.text(depth + 1)?;
                Ok(if p.is_empty() {
                    value.to_string()
                } else {
                    format!("{p}.{value}")
                })
            }
        }
    }
}
#[derive(Debug, Deserialize)]
#[serde(tag = "tag", rename_all = "lowercase", deny_unknown_fields)]
enum Universe {
    Zero,
    Succ {
        inner: Box<Universe>,
    },
    Max {
        left: Box<Universe>,
        right: Box<Universe>,
    },
    Imax {
        left: Box<Universe>,
        right: Box<Universe>,
    },
    Param {
        name: LeanName,
    },
}
impl Universe {
    fn check(&self, depth: usize) -> Result<()> {
        ensure(depth < 256, "universe nesting too deep")?;
        match self {
            Self::Zero => Ok(()),
            Self::Succ { inner } => inner.check(depth + 1),
            Self::Max { left, right } | Self::Imax { left, right } => {
                left.check(depth + 1)?;
                right.check(depth + 1)
            }
            Self::Param { name } => {
                name.text(0)?;
                Ok(())
            }
        }
    }
}
#[derive(Debug, Deserialize)]
#[serde(tag = "tag", rename_all = "lowercase", deny_unknown_fields)]
enum Expr {
    Bvar {
        index: u64,
    },
    Sort {
        level: Universe,
    },
    Const {
        name: LeanName,
        levels: Vec<Universe>,
    },
    App {
        #[serde(rename = "fn")]
        function: usize,
        arg: usize,
    },
    Lam {
        name: LeanName,
        binder: String,
        #[serde(rename = "type")]
        typ: usize,
        body: usize,
    },
    Forall {
        name: LeanName,
        binder: String,
        #[serde(rename = "type")]
        typ: usize,
        body: usize,
    },
    Let {
        name: LeanName,
        #[serde(rename = "type")]
        typ: usize,
        value: usize,
        body: usize,
        nondep: bool,
    },
    Nat {
        value: Value,
    },
    String {
        value: String,
    },
    Proj {
        name: LeanName,
        index: u64,
        value: usize,
    },
}
impl Expr {
    fn check(&self, position: usize) -> Result<()> {
        let check_ref = |i: usize| {
            ensure(
                i < position,
                format!("non-topological Expr edge at {position}"),
            )
        };
        match self {
            Self::Bvar { index } => {
                let _ = index;
                Ok(())
            }
            Self::Sort { level } => level.check(0),
            Self::Const { name, levels } => {
                name.text(0)?;
                for level in levels {
                    level.check(0)?;
                }
                Ok(())
            }
            Self::App { function, arg } => {
                check_ref(*function)?;
                check_ref(*arg)
            }
            Self::Lam {
                name,
                binder,
                typ,
                body,
            }
            | Self::Forall {
                name,
                binder,
                typ,
                body,
            } => {
                name.text(0)?;
                ensure(
                    matches!(
                        binder.as_str(),
                        "default" | "implicit" | "strictImplicit" | "instImplicit"
                    ),
                    "invalid Lean binder",
                )?;
                check_ref(*typ)?;
                check_ref(*body)
            }
            Self::Let {
                name,
                typ,
                value,
                body,
                nondep,
            } => {
                let _ = nondep;
                name.text(0)?;
                check_ref(*typ)?;
                check_ref(*value)?;
                check_ref(*body)
            }
            Self::Nat { value } => ensure(
                value.as_u64().is_some(),
                "non-natural or oversized numeric literal",
            ),
            Self::String { value } => {
                let _ = value;
                Ok(())
            }
            Self::Proj { name, index, value } => {
                let _ = index;
                name.text(0)?;
                check_ref(*value)
            }
        }
    }
}
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Residual {
    format: String,
    status: String,
    source: LeanName,
    source_root: usize,
    reduced_root: usize,
    nodes: Vec<Expr>,
    node_count: usize,
    source_symbols: Vec<String>,
    metadata_dropped: u64,
    lean_defeq_checked: bool,
    beta_zeta_steps: u64,
    rust_executable: bool,
    physical_refinement: String,
}

pub fn validate_residual(raw: &[u8], root: &str) -> Result<()> {
    ensure(
        raw.ends_with(b"\n") && raw.iter().filter(|&&b| b == b'\n').count() == 1,
        "residual requires one JSON line",
    )?;
    let doc: Residual = strict_json(raw)?;
    ensure(
        doc.format == "lean-core-expr-dag-v1" && doc.status == "residualized-unverified",
        "unknown residual format/status",
    )?;
    ensure(
        doc.source.text(0)? == root,
        "residual declaration identity mismatch",
    )?;
    ensure(
        !doc.rust_executable && doc.physical_refinement == "not-established",
        "symbolic source incorrectly claims executable verification",
    )?;
    ensure(
        doc.lean_defeq_checked,
        "Lean definitional-equality check missing",
    )?;
    ensure(
        !doc.nodes.is_empty() && doc.nodes.len() <= MAX_NODES && doc.node_count == doc.nodes.len(),
        "invalid residual DAG node count",
    )?;
    ensure(
        doc.source_root < doc.nodes.len() && doc.reduced_root < doc.nodes.len(),
        "invalid residual root node",
    )?;
    ensure(
        doc.beta_zeta_steps <= 16,
        "unbounded or invalid residual reduction",
    )?;
    let _ = doc.metadata_dropped;
    let mut symbols = HashSet::new();
    for name in &doc.source_symbols {
        ensure(symbols.insert(name), "duplicate residual source symbol")?;
    }
    for (index, expr) in doc.nodes.iter().enumerate() {
        expr.check(index)?;
    }
    Ok(())
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct NativeIrReport {
    format: String,
    status: String,
    compiler: String,
    module: String,
    roots: Vec<String>,
    lean_toolchain: String,
    lean_version: String,
    source_revision: String,
    source_git_blob: String,
    source_lean_sha256: String,
    semantic_verification: String,
    physical_bitprogram_verification: String,
    generated_sha256: String,
    generated_bytes: u64,
    cargo_manifest_sha256: String,
    native_project_receipt: String,
}

fn sha256_hex(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
}

/// Parse the original in-process compiler's project receipt. The receipt
/// reports a built Cargo package; it does not establish semantic parity.
fn native_project_fields(raw: &str) -> Result<HashMap<&str, &str>> {
    ensure(raw.len() <= 8192, "native project receipt is oversized")?;
    let mut fields = HashMap::new();
    for line in raw.lines() {
        let (key, value) = line
            .split_once('=')
            .ok_or("malformed native project receipt")?;
        ensure(
            !key.is_empty()
                && !value.is_empty()
                && key
                    .bytes()
                    .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'_'),
            "invalid native project receipt field",
        )?;
        ensure(
            fields.insert(key, value).is_none(),
            "duplicate native project receipt field",
        )?;
    }
    Ok(fields)
}

pub fn validate_ir(
    raw: &[u8],
    artifact: &[u8],
    module: &str,
    roots: &[String],
    source: &SourceIdentity,
) -> Result<()> {
    let doc: NativeIrReport = strict_json(raw)?;
    ensure(
        doc.format == "lean-inprocess-ir-project-v1"
            && doc.status == "generated-unverified"
            && doc.compiler == "native-lean-4.34.1",
        "invalid canonical native compiler-IR report",
    )?;
    ensure(
        !roots.is_empty() && doc.roots == roots && doc.module == module,
        "native compiler-IR roots/module mismatch",
    )?;
    ensure(
        doc.semantic_verification == "not-established"
            && doc.physical_bitprogram_verification == "not-established",
        "native IR report claims unproved semantic or physical verification",
    )?;
    ensure(
        doc.generated_sha256 == digest(artifact) && doc.generated_bytes == artifact.len() as u64
            && sha256_hex(&doc.cargo_manifest_sha256),
        "native IR generated Cargo source/manifest digest mismatch",
    )?;
    ensure(
        doc.lean_toolchain == source.lean_toolchain
            && doc.lean_toolchain == "leanprover/lean4:v4.34.1"
            && version_matches(&doc.lean_version, &source.lean_toolchain),
        "native IR toolchain differs from original pinned Lean 4.34.1",
    )?;
    ensure(
        doc.source_revision == source.git_revision
            && doc.source_git_blob == source.git_blob
            && sha256_hex(&doc.source_lean_sha256),
        "native IR report is not bound to original Git source",
    )?;
    let fields = native_project_fields(&doc.native_project_receipt)?;
    let field = |key: &str| fields.get(key).copied().unwrap_or("");
    ensure(
        fields.len() == 13
            && field("status") == "GENERATED_COMPILED_SEMANTICS_NOT_VERIFIED"
            && field("module") == module
            && field("roots") == roots.join(",")
            && field("source_revision") == source.git_revision
            && field("lean_version") == doc.lean_version
            && field("rust_version") == "rustc 1.99.1 (58cf8f9c3 2026-10-13)"
            && field("source_sha256") == doc.source_lean_sha256
            && field("generated_sha256") == doc.generated_sha256
            && field("semantic_verification") == "NOT_PERFORMED"
            && field("transitive_source_manifest") == "NOT_CAPTURED",
        "native project receipt has invalid roots, source, or verification claims",
    )?;
    ensure(
        sha1(field("backend_revision"))
            && sha256_hex(field("backend_sha256"))
            && field("phase_timeout_seconds")
                .parse::<u64>()
                .ok()
                .is_some_and(|n| (1..=3600).contains(&n)),
        "native project receipt is missing build identity or bounded timeout",
    )
}

pub fn validate(
    backend: Backend,
    artifact: &[u8],
    report: Option<&[u8]>,
    module: &str,
    roots: &[String],
    source: &SourceIdentity,
) -> Result<Value> {
    ensure(
        declaration(module) && !roots.is_empty() && roots.iter().all(|r| declaration(r)),
        "invalid Lean module or root",
    )?;
    let set: HashSet<_> = roots.iter().collect();
    ensure(set.len() == roots.len(), "duplicate declaration root")?;
    ensure(
        !artifact.is_empty() && artifact.len() <= MAX_BYTES,
        "empty/oversized artifact",
    )?;
    match backend {
        Backend::CompilerIr => {
            validate_ir(
                report.ok_or("missing compiler-IR report")?,
                artifact,
                module,
                roots,
                source,
            )?;
        }
        Backend::ResidualExpr => {
            ensure(
                report.is_none() && roots.len() == 1,
                "residual requires one root and no IR receipt",
            )?;
            validate_residual(artifact, &roots[0])?;
        }
    }
    Ok(json!({
        "format": "lean-two-path-contract-v1",
        "backend": backend.name(),
        "status": backend.status(),
        "module": module,
        "roots": roots,
        "source_file": source,
        "toolchain": source.lean_toolchain,
        "artifact_sha256": digest(artifact),
        "artifact_bytes": artifact.len(),
        "checks": {
            "git_file_matches_head": true,
            "backend_payload_checked": true,
            "declaration_source_binding": "not-established",
            "transitive_executable_closure": "not-established",
            "residual_actual_lean_version": if backend == Backend::ResidualExpr { "not-established" } else { "backend-reported" },
            "lean_rust_semantic_refinement": "not-established",
            "physical_bitprogram_refinement": "not-established"
        },
        "executable_approved": false
    }))
}

/// Input to the one native in-process Lean 4.34.1 Cargo package compiler.
/// This is an artifact integrity record, not a semantic proof certificate.
pub struct NativeIrProject<'a> {
    pub module: &'a str,
    pub roots: &'a [String],
    pub toolchain: &'a str,
    pub lean_version: &'a str,
    pub source_revision: &'a str,
    pub source_git_blob: &'a str,
    pub source_lean_sha256: &'a str,
    pub generated: &'a [u8],
    pub cargo_manifest: &'a [u8],
    pub native_project_receipt: &'a str,
}

pub fn native_ir_report(project: NativeIrProject<'_>) -> Value {
    json!({
        "format": "lean-inprocess-ir-project-v1",
        "status": "generated-unverified",
        "compiler": "native-lean-4.34.1",
        "module": project.module,
        "roots": project.roots,
        "lean_toolchain": project.toolchain,
        "lean_version": project.lean_version,
        "source_revision": project.source_revision,
        "source_git_blob": project.source_git_blob,
        "source_lean_sha256": project.source_lean_sha256,
        "generated_sha256": digest(project.generated),
        "generated_bytes": project.generated.len(),
        "cargo_manifest_sha256": digest(project.cargo_manifest),
        "semantic_verification": "not-established",
        "physical_bitprogram_verification": "not-established",
        "native_project_receipt": project.native_project_receipt
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    fn source() -> SourceIdentity {
        SourceIdentity {
            git_revision: "a".repeat(40),
            git_blob: "b".repeat(40),
            path: "Demo.lean".into(),
            lean_toolchain: "leanprover/lean4:v4.34.1".into(),
            lean_toolchain_git_blob: "c".repeat(40),
            lean_toolchain_path: "lean-toolchain".into(),
        }
    }
    fn name(a: &str, b: &str) -> Value {
        json!({"tag":"str","parent":{"tag":"str","parent":{"tag":"anonymous"},"value":a},"value":b})
    }
    fn residual() -> Vec<u8> {
        let value = json!({
            "format":"lean-core-expr-dag-v1","status":"residualized-unverified",
            "source":name("Demo","double"),"source_root":0,"reduced_root":0,
            "nodes":[{"tag":"nat","value":42}],"node_count":1,
            "source_symbols":[],"metadata_dropped":0,"lean_defeq_checked":true,
            "beta_zeta_steps":0,"rust_executable":false,"physical_refinement":"not-established"
        });
        format!("{value}\n").into_bytes()
    }
    #[test]
    fn symbolic_remains_unverified() {
        let receipt = validate(
            Backend::ResidualExpr,
            &residual(),
            None,
            "Demo",
            &["Demo.double".into()],
            &source(),
        )
        .unwrap();
        assert_eq!(receipt["executable_approved"], false);
        assert_eq!(
            receipt["checks"]["declaration_source_binding"],
            "not-established"
        );
        assert_eq!(receipt["status"], "residualized-unverified");
    }
    #[test]
    fn refuses_non_topological_and_wrong_roots() {
        let mut d: Value = serde_json::from_slice(&residual()).unwrap();
        d["nodes"] = json!([{"tag":"app","fn":0,"arg":0}]);
        assert!(validate_residual(format!("{d}\n").as_bytes(), "Demo.double").is_err());
        assert!(validate_residual(&residual(), "Other.root").is_err());
    }
    #[test]
    fn rejects_unknown_node_and_executable_claim() {
        let mut d: Value = serde_json::from_slice(&residual()).unwrap();
        d["nodes"] = json!([{"tag":"unknown","value":42}]);
        assert!(validate_residual(format!("{d}\n").as_bytes(), "Demo.double").is_err());
        d["nodes"] = json!([{"tag":"nat","value":42}]);
        d["rust_executable"] = json!(true);
        assert!(validate_residual(format!("{d}\n").as_bytes(), "Demo.double").is_err());
    }
    #[test]
    fn duplicate_json_key_rejected() {
        let raw = String::from_utf8(residual()).unwrap().replace(
            "\"rust_executable\":false",
            "\"rust_executable\":false,\"rust_executable\":true",
        );
        assert!(validate_residual(raw.as_bytes(), "Demo.double").is_err());
    }
    #[test]
    fn native_ir_project_receipt_checks_two_roots_and_rejects_tampering() {
        let mut source = source();
        source.lean_toolchain = "leanprover/lean4:v4.34.1".into();
        let code = b"pub fn inc() {}\npub fn twice() {}";
        let manifest = b"[package]\nname = \"lean_generated\"\n";
        let source_sha = "a".repeat(64);
        let roots = vec!["Demo.inc".into(), "Demo.twice".into()];
        let project_receipt = format!(
            "status=GENERATED_COMPILED_SEMANTICS_NOT_VERIFIED\nmodule=Demo\nroots=Demo.inc,Demo.twice\nsource_sha256={}\nphase_timeout_seconds=300\nsource_revision={}\nbackend_revision={}\nlean_version=Lean (version 4.34.1, x86_64)\nrust_version=rustc 1.99.1 (58cf8f9c3 2026-10-13)\nbackend_sha256={}\ngenerated_sha256={}\nsemantic_verification=NOT_PERFORMED\ntransitive_source_manifest=NOT_CAPTURED\n",
            source_sha, source.git_revision, "c".repeat(40),
            "d".repeat(64), digest(code),
        );
        let report = native_ir_report(NativeIrProject {
            module: "Demo",
            roots: &roots,
            toolchain: &source.lean_toolchain,
            lean_version: "Lean (version 4.34.1, x86_64)",
            source_revision: &source.git_revision,
            source_git_blob: &source.git_blob,
            source_lean_sha256: &source_sha,
            generated: code,
            cargo_manifest: manifest,
            native_project_receipt: &project_receipt,
        });
        let raw = serde_json::to_vec(&report).unwrap();
        let accepted =
            validate(Backend::CompilerIr, code, Some(&raw), "Demo", &roots, &source).unwrap();
        assert_eq!(accepted["executable_approved"], false);
        assert_eq!(accepted["status"], "generated-unverified");

        let bad = |field: &str, value: Value| {
            let mut r = report.clone();
            r[field] = value;
            validate_ir(&serde_json::to_vec(&r).unwrap(), code, "Demo", &roots, &source)
                .is_err()
        };
        assert!(bad("generated_sha256", json!("0".repeat(64))));
        assert!(bad("source_git_blob", json!("0".repeat(40))));
        assert!(bad("source_revision", json!("f".repeat(40))));
        assert!(bad("roots", json!(["Demo.twice","Demo.inc"])));
        assert!(bad("native_project_receipt", json!(project_receipt.replace(
            "semantic_verification=NOT_PERFORMED", "semantic_verification=PROVED",
        ))));
        assert!(bad("native_project_receipt", json!(format!(
            "{project_receipt}status=GENERATED_COMPILED_SEMANTICS_NOT_VERIFIED\n"
        ))));
        assert!(bad("native_project_receipt", json!(project_receipt.replace(
            "roots=Demo.inc,Demo.twice", "roots=Demo.inc",
        ))));
        // Legacy adapter reports cannot impersonate the native G1 runtime.
        assert!(validate_ir(
            br#"{"format":"lean-compiler-ir-backend-probe-v1"}"#,
            code,
            "Demo",
            &roots,
            &source,
        ).is_err());
    }
    #[test]
    fn source_name_and_version_checks() {
        assert!(declaration("My.Module.foo_9"));
        assert!(!declaration("Module;rm -rf"));
        assert!(!declaration("A..b"));
        assert!(version_matches(
            "Lean (version 4.35.0, x86_64)",
            "leanprover/lean4:v4.35.0"
        ));
        assert!(!version_matches(
            "Lean (version 4.35.01)",
            "leanprover/lean4:v4.35.0"
        ));
    }
}
