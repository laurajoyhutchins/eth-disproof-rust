//! Generate a specialized Rust binary source from an original-Lean graph.
//! The identity/digest arguments must come from a separately checked Lean
//! kernel-certificate receipt, not from the candidate JSON itself.
use lean_eth_reference::bit_program::{SourceGraphBinding, emit_original_source_rust};
use std::fs;
use std::path::PathBuf;

fn generate() -> Result<(), Box<dyn std::error::Error>> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if args.len() != 6 {
        return Err(
            "usage: original-source-codegen GRAPH.jsonl CERT_ID CERT_DECLARATION CERT_SOURCE_BLOB CERT_GRAPH_SHA256 OUTPUT.rs".into()
        );
    }
    let input = PathBuf::from(&args[0]);
    let output = PathBuf::from(&args[5]);
    if input == output
        || (output.exists() && fs::canonicalize(&input)? == fs::canonicalize(&output)?)
    {
        return Err("refusing to overwrite input graph".into());
    }
    // Bound the read even when the selected source is not a regular file.
    if fs::metadata(&input)?.len() > 4 * 1024 * 1024 {
        return Err("source graph exceeds protocol byte budget".into());
    }
    let bytes = fs::read(&input)?;
    let rust = emit_original_source_rust(
        &bytes,
        SourceGraphBinding {
            id: &args[1],
            declaration: &args[2],
            source_blob: &args[3],
            graph_sha256: &args[4],
        },
    )?;
    fs::write(output, rust)?;
    Ok(())
}

fn main() {
    if let Err(error) = generate() {
        eprintln!("{error}");
        std::process::exit(2);
    }
}
