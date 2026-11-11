//! Convert a table produced by the pinned original Lean elaborator to direct
//! executable Rust. The PIN line alone is NOT evidence of source provenance:
//! the caller must validate the original Git checkout, build and receipt.
#[path = "../../tools/lean_table_codegen.rs"]
mod lean_table_codegen;

use std::fs;
use std::path::PathBuf;

fn canonical_usize(value: &str) -> Result<usize, String> {
    if value.is_empty()
        || !value.bytes().all(|byte| byte.is_ascii_digit())
        || (value.len() > 1 && value.starts_with('0'))
    {
        return Err(format!("noncanonical original table integer: {value:?}"));
    }
    value
        .parse::<usize>()
        .map_err(|_| "source table integer overflow".into())
}

fn compile(args: &[String]) -> Result<(), Box<dyn std::error::Error>> {
    if args.len() != 4 {
        return Err("usage: lean-original-codegen ID SOURCE_GIT_BLOB INPUT_TABLE OUTPUT_RS".into());
    }
    let (name, source_blob, input_path, output_path) = (
        &args[0],
        &args[1],
        PathBuf::from(&args[2]),
        PathBuf::from(&args[3]),
    );
    if name.is_empty()
        || name.len() > 255
        || !name
            .bytes()
            .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == b'_' || c == b'-')
    {
        return Err("invalid canonical source program ID".into());
    }
    if source_blob.len() != 40
        || !source_blob
            .bytes()
            .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
    {
        return Err("expected exact original source Git blob identity".into());
    }
    if input_path == output_path
        || (output_path.exists()
            && fs::canonicalize(&input_path)? == fs::canonicalize(&output_path)?)
    {
        return Err("cannot overwrite original Lean instruction table".into());
    }
    const MAX_BYTES: u64 = 32_000_000;
    if fs::metadata(&input_path)?.len() > MAX_BYTES {
        return Err("source table exceeds 32 MB input budget".into());
    }
    let input = fs::read_to_string(&input_path)?;
    let header: Vec<_> = input
        .lines()
        .nth(1)
        .ok_or("missing original program header")?
        .split('|')
        .collect();
    if header.len() != 8 || header[0] != "PROGRAM" || header[1] != name {
        return Err("incorrect original program header/ID".into());
    }
    let nums = header[2..]
        .iter()
        .map(|field| canonical_usize(field))
        .collect::<Result<Vec<_>, _>>()?;
    let abi = (nums[0], nums[1], nums[2], nums[3], nums[4], nums[5]);
    if abi.0 == 0 || abi.0 > 256 || abi.1 == 0 || abi.1 > 4096 || abi.2 == 0 || abi.2 > 8192 {
        return Err("source compiled machine dimension budget exceeded".into());
    }
    let generated = lean_table_codegen::generate(
        &input,
        lean_table_codegen::TableKind::Catalog {
            name,
            blob: source_blob,
            abi,
        },
        8192,
    )?;
    if output_path
        .parent()
        .is_some_and(|p| !p.as_os_str().is_empty() && !p.exists())
    {
        return Err("generated output parent directory does not exist".into());
    }
    let tmp = output_path.with_extension(format!("rust-{}.tmp", std::process::id()));
    let result = fs::write(&tmp, generated).and_then(|()| fs::rename(&tmp, &output_path));
    if result.is_err() {
        let _ = fs::remove_file(&tmp);
    }
    result?;
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    compile(&std::env::args().skip(1).collect::<Vec<_>>())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_bounds_and_identity_are_not_guessable() {
        for bad in ["", "01", "-1", "1.0", "3 ", "3\n"] {
            assert!(canonical_usize(bad).is_err());
        }
        assert_eq!(canonical_usize("0").unwrap(), 0);
        assert_eq!(canonical_usize("8192").unwrap(), 8192);
        assert!(
            compile(&[
                "synthetic".into(),
                "not-a-blob".into(),
                "x".into(),
                "y".into()
            ])
            .is_err()
        );
    }
}
