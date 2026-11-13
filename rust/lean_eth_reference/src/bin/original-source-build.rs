//! Build a specialized native Rust executable from a receipt-bound original
//! Lean source graph. This validates receipt *content*, not the historical
//! authenticity of the independent Lean kernel-check run that issued it.
use lean_eth_reference::bit_program::{SourceGraphBinding, emit_original_source_rust};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::Command;

const SOURCE_COMMIT: &str = "4eaee87548250b2682affda7d05d947c05554bae";
const MAX_GRAPH_BYTES: usize = 4 * 1024 * 1024;
const MAX_CERTIFICATE_BYTES: usize = 16 * 1024 * 1024;
const MAX_RECEIPT_BYTES: usize = 65_536;
const MAX_OUTPUT_BYTES: usize = 16 * 1024 * 1024;

#[derive(Deserialize)]
struct KernelReceipt {
    status: String,
    source_commit: String,
    source_blob: String,
    declaration: String,
    id: String,
    source_graph_sha256: String,
    certificate_sha256: String,
    physical_labels: usize,
    lean_version: String,
}

#[derive(Serialize)]
struct BuildReceipt<'a> {
    status: &'static str,
    source_commit: &'a str,
    source_blob: &'a str,
    declaration: &'a str,
    id: &'a str,
    graph_sha256: &'a str,
    lean_certificate_sha256: &'a str,
    generated_rust_sha256: String,
    binary_sha256: String,
    cargo_lock_sha256: String,
    physical_labels: usize,
    toolchain: &'static str,
    verification_boundary: &'static str,
}

fn read_bounded(path: &Path, max: usize) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let mut file = fs::File::open(path)?;
    let mut bytes = Vec::new();
    file.by_ref()
        .take((max as u64) + 1)
        .read_to_end(&mut bytes)?;
    if bytes.is_empty() || bytes.len() > max {
        return Err(format!("input {} is empty or exceeds byte budget", path.display()).into());
    }
    Ok(bytes)
}

fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn valid_sha256(hash: &str) -> bool {
    hash.len() == 64
        && hash
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

fn check_receipt(
    receipt: &KernelReceipt,
    certificate: &[u8],
) -> Result<(), Box<dyn std::error::Error>> {
    if !matches!(
        receipt.status.as_str(),
        "LEAN_KERNEL_CERTIFIED_PHYSICAL_PROGRAM" | "LEAN_KERNEL_CERTIFIED_SOURCE_DERIVED_FIXTURE"
    ) {
        return Err("receipt does not assert a completed original Lean kernel check".into());
    }
    if receipt.lean_version != "4.34.1"
        || receipt.source_commit != SOURCE_COMMIT
        || !valid_sha256(&receipt.source_graph_sha256)
        || !valid_sha256(&receipt.certificate_sha256)
        || receipt.certificate_sha256 != sha256(certificate)
        || receipt.physical_labels == 0
        || receipt.physical_labels > 4096
    {
        return Err("receipt toolchain, source pin, certificate hash or labels invalid".into());
    }
    Ok(())
}

fn write_cargo_manifest(root: &Path) -> Result<(), Box<dyn std::error::Error>> {
    // A local path dependency retains the single canonical BitProgram runner.
    // This package is buildable alongside the pinned source checkout, not
    // independently vendored, and no untrusted source JSON is run at build time.
    let crate_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).canonicalize()?;
    let quoted = serde_json::to_string(&crate_path.to_string_lossy().as_ref())?;
    fs::write(
        root.join("Cargo.toml"),
        format!(
            "[package]\nname = \"original_lean_aot\"\nversion = \"0.0.0\"\n\
             edition = \"2024\"\n\n[workspace]\n\n[dependencies]\n\
             lean_eth_reference = {{ package = \"lean-eth-reference\", path = {quoted} }}\n"
        ),
    )?;
    fs::write(
        root.join("rust-toolchain.toml"),
        "[toolchain]\nchannel = \"1.99.1\"\nprofile = \"minimal\"\n",
    )?;
    Ok(())
}

fn check_cargo_build(root: &Path) -> Result<(), Box<dyn std::error::Error>> {
    for locked in [false, true] {
        let mut command = Command::new("cargo");
        command.args(["build", "--offline"]);
        if locked {
            command.arg("--locked");
        }
        let output = command
            .arg("--manifest-path")
            .arg(root.join("Cargo.toml"))
            .current_dir(root)
            .output()?;
        if !output.status.success() {
            return Err(format!(
                "generated Rust cargo build failed (locked={locked}): {}",
                String::from_utf8_lossy(&output.stderr)
            )
            .into());
        }
    }
    Ok(())
}

fn build() -> Result<(), Box<dyn std::error::Error>> {
    let args = std::env::args_os().skip(1).collect::<Vec<_>>();
    if args.len() != 4 {
        return Err(
            "usage: original-source-build GRAPH.json CERTIFICATE.receipt.json CERTIFICATE.lean OUTPUT_DIRECTORY"
                .into(),
        );
    }
    let graph_path = PathBuf::from(&args[0]);
    let receipt_path = PathBuf::from(&args[1]);
    let certificate_path = PathBuf::from(&args[2]);
    let destination = PathBuf::from(&args[3]);
    if destination.exists() {
        return Err("output directory already exists; refusing to overwrite".into());
    }
    let graph = read_bounded(&graph_path, MAX_GRAPH_BYTES)?;
    let receipt_bytes = read_bounded(&receipt_path, MAX_RECEIPT_BYTES)?;
    let certificate = read_bounded(&certificate_path, MAX_CERTIFICATE_BYTES)?;
    let receipt: KernelReceipt = serde_json::from_slice(&receipt_bytes)?;
    check_receipt(&receipt, &certificate)?;
    if sha256(&graph) != receipt.source_graph_sha256 {
        return Err("graph SHA-256 differs from kernel receipt".into());
    }
    let generated = emit_original_source_rust(
        &graph,
        SourceGraphBinding {
            id: &receipt.id,
            declaration: &receipt.declaration,
            source_blob: &receipt.source_blob,
            graph_sha256: &receipt.source_graph_sha256,
        },
    )?;
    if generated.len() > MAX_OUTPUT_BYTES
        || !generated.contains(&format!(
            "pub const LABELS: usize = {};",
            receipt.physical_labels
        ))
    {
        return Err("generated source does not match certified physical label count".into());
    }

    // Do not publish an incomplete project or stale successful build receipt.
    let parent = destination
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    let filename = destination
        .file_name()
        .and_then(|s| s.to_str())
        .ok_or("output directory must have a UTF-8 filename")?;
    let mut staging = None;
    for n in 0..100u32 {
        let candidate = parent.join(format!(".{filename}.aot-{}-{n}", std::process::id()));
        match fs::create_dir(&candidate) {
            Ok(()) => {
                staging = Some(candidate);
                break;
            }
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(e) => return Err(e.into()),
        }
    }
    let staging = staging.ok_or("no free staging directory name")?;
    let result = (|| -> Result<(), Box<dyn std::error::Error>> {
        fs::create_dir(staging.join("src"))?;
        fs::write(staging.join("src/main.rs"), &generated)?;
        fs::write(staging.join("source.json"), &graph)?;
        fs::write(staging.join("certificate.lean"), &certificate)?;
        fs::write(staging.join("certificate.receipt.json"), &receipt_bytes)?;
        write_cargo_manifest(&staging)?;
        check_cargo_build(&staging)?;
        let binary = fs::read(staging.join("target/debug/original_lean_aot"))?;
        let lockfile = fs::read(staging.join("Cargo.lock"))?;
        let artifact = BuildReceipt {
            status: "GENERATED_AND_NATIVE_BUILT",
            source_commit: &receipt.source_commit,
            source_blob: &receipt.source_blob,
            declaration: &receipt.declaration,
            id: &receipt.id,
            graph_sha256: &receipt.source_graph_sha256,
            lean_certificate_sha256: &receipt.certificate_sha256,
            generated_rust_sha256: sha256(generated.as_bytes()),
            binary_sha256: sha256(&binary),
            cargo_lock_sha256: sha256(&lockfile),
            physical_labels: receipt.physical_labels,
            toolchain: "1.99.1",
            verification_boundary: "Receipt content and AOT build validated; independent Lean proof-run authenticity is caller responsibility",
        };
        fs::write(
            staging.join("build.receipt.json"),
            format!("{}\n", serde_json::to_string_pretty(&artifact)?),
        )?;
        if destination.exists() {
            return Err("output directory appeared while building; refusing overwrite".into());
        }
        fs::rename(&staging, &destination)?;
        println!(
            "{}",
            destination.join("target/debug/original_lean_aot").display()
        );
        Ok(())
    })();
    if result.is_err() {
        let _ = fs::remove_dir_all(&staging);
    }
    result
}

fn main() {
    if let Err(error) = build() {
        eprintln!("{error}");
        std::process::exit(2);
    }
}
