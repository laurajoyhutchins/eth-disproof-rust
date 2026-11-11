//! Deterministically generate executable Rust source from a Lean BitProgram
//! table. A query table must carry the exact pinned source identity and ABI.
//! --fixture accepts explicitly synthetic test data, not evidence of Lean.
#[path = "../../tools/lean_table_codegen.rs"]
mod lean_table_codegen;

use std::fs;
use std::path::PathBuf;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args_os().skip(1);
    let first = args
        .next()
        .ok_or("usage: lean-table-codegen [--fixture] INPUT OUTPUT")?;
    let (kind, input) = if first == "--fixture" {
        (
            lean_table_codegen::TableKind::Fixture,
            args.next().ok_or("missing INPUT")?,
        )
    } else {
        (lean_table_codegen::TableKind::Query, first)
    };
    let output: PathBuf = args.next().ok_or("missing OUTPUT")?.into();
    if args.next().is_some() {
        return Err("unexpected extra argument".into());
    }
    let input: PathBuf = input.into();
    if output == input
        || (output.exists() && fs::canonicalize(&output)? == fs::canonicalize(&input)?)
    {
        return Err("cannot overwrite the source table".into());
    }
    // Refuse unexpectedly large materializations before allocating String.
    if fs::metadata(&input)?.len() > 8_000_000 {
        return Err("input table exceeds 8 MB experimental codegen budget".into());
    }
    let source = fs::read_to_string(input)?;
    let generated = lean_table_codegen::generate(&source, kind, 8192)?;
    // Write only after complete parsing/validation. Source path identity and
    // artifact SHA-256 are checked separately by the attested exporter.
    fs::write(output, generated)?;
    Ok(())
}
