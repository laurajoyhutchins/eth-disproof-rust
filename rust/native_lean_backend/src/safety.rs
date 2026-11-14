//! Fail-closed response and publication for the opt-in native compiler backend.
//!
//! A result is published only after the full IR closure has been accepted. The
//! destination is a caller-selected relative .rs path under pre-existing,
//! non-symlink directories. Concurrent mutation of those directories by an
//! adversary is outside this boundary; the compiler itself must be isolated
//! when compiling untrusted source trees.
use std::fmt::Write as _;
use std::fs::{self, OpenOptions};
use std::io::Write as _;
use std::path::{Component, Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

pub(crate) const MAX_OUTPUT_BYTES: usize = 4 * 1024 * 1024;
static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

fn json_string(input: &str) -> String {
    let mut out = String::from("\"");
    for ch in input.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c <= '\u{1f}' => write!(out, "\\u{:04x}", c as u32).unwrap(),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

pub(crate) fn refusal(default_declaration: &str, detail: &str) -> String {
    let (decl, reason) = detail
        .strip_prefix("declaration=")
        .and_then(|s| s.split_once("; "))
        .unwrap_or((default_declaration, detail));
    let construct = if reason.contains("FnBody constructor")
        || reason.contains("IR body constructor")
    {
        "FnBody"
    } else if reason.contains("Expr constructor") || reason.contains("IR expression constructor") {
        "Expr"
    } else if reason.contains("IRType constructor") || reason.contains("IR type tag") {
        "IRType"
    } else if reason.contains("Arg constructor") {
        "Arg"
    } else if reason.contains("Alt constructor")
        || reason.contains("alternative")
        || reason.contains("Bool case")
    {
        "Alt"
    } else if reason.contains("LitVal constructor") {
        "LitVal"
    } else if reason.contains("Decl constructor") {
        "Decl"
    } else if reason.contains("primitive") || reason.contains("operands") {
        "Primitive"
    } else if reason.contains("dependency") || reason.contains("compiled IR") {
        "Dependency"
    } else if reason.contains("ABI") {
        "ABI"
    } else if reason.contains("limit") || reason.contains("budget") {
        "ResourceLimit"
    } else {
        "Compiler"
    };
    format!(
        "ERROR\n{{\"status\":\"refused\",\"declaration\":{},\"construct\":{},\"reason\":{}}}",
        json_string(decl),
        json_string(construct),
        json_string(reason)
    )
}

fn validate_destination(path: &str) -> Result<PathBuf, String> {
    let dst = Path::new(path);
    if dst.extension().and_then(|s| s.to_str()) != Some("rs") {
        return Err("destination must end in .rs".into());
    }
    let components: Vec<_> = dst.components().collect();
    if components.is_empty()
        || components
            .iter()
            .any(|c| !matches!(c, Component::Normal(_)))
    {
        return Err("destination must be a relative path without . or .. components".into());
    }
    let mut parent = PathBuf::from(".");
    for component in &components[..components.len() - 1] {
        parent.push(component.as_os_str());
        let meta = fs::symlink_metadata(&parent)
            .map_err(|e| format!("destination directory {}: {e}", parent.display()))?;
        if !meta.is_dir() || meta.file_type().is_symlink() {
            return Err(format!(
                "destination directory {} must be an existing non-symlink directory",
                parent.display()
            ));
        }
    }
    match fs::symlink_metadata(dst) {
        Ok(meta) if !meta.is_file() || meta.file_type().is_symlink() => {
            Err("destination already exists and is not a regular file".into())
        }
        Ok(_) => Ok(dst.to_path_buf()),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(dst.to_path_buf()),
        Err(e) => Err(format!("cannot inspect destination: {e}")),
    }
}

/// Atomically replace a caller-selected generated source path, preserving the
/// previous regular file on any validation, write, flush or rename failure.
pub(crate) fn publish(path: &str, source: &str) -> Result<(), String> {
    if source.len() > MAX_OUTPUT_BYTES {
        return Err(format!(
            "generated Rust exceeds {} byte output limit",
            MAX_OUTPUT_BYTES
        ));
    }
    let dst = validate_destination(path)?;
    let parent = dst
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let filename = dst.file_name().unwrap().to_string_lossy();
    let mut temporary = None;
    for _ in 0..32 {
        let n = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
        let candidate = parent.join(format!(
            ".{filename}.lean-native-{}-{n}.tmp",
            std::process::id()
        ));
        match OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&candidate)
        {
            Ok(file) => {
                temporary = Some((candidate, file));
                break;
            }
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(e) => return Err(format!("cannot stage generated Rust: {e}")),
        }
    }
    let (temp, mut file) = temporary.ok_or("cannot allocate a unique output staging file")?;
    let result = (|| -> std::io::Result<()> {
        file.write_all(source.as_bytes())?;
        file.sync_all()?;
        drop(file);
        fs::rename(&temp, &dst)?;
        Ok(())
    })();
    if result.is_err() {
        let _ = fs::remove_file(&temp);
    }
    result.map_err(|e| format!("cannot publish generated Rust atomically: {e}"))
}

#[cfg(test)]
mod tests {
    use super::{publish, refusal};
    use std::fs;

    #[test]
    fn refusals_escape_arbitrary_ir_diagnostics() {
        let msg = refusal(
            "Root",
            "declaration=Module.foo; IR body constructor 7 unsupported: \"quoted\"\nline",
        );
        assert!(msg.starts_with("ERROR\n{\"status\":\"refused\""));
        assert!(msg.contains("\"declaration\":\"Module.foo\""));
        assert!(msg.contains("\"construct\":\"FnBody\""));
        assert!(msg.contains("\\\"quoted\\\"\\nline"));
        assert!(!msg.contains("quoted\"\nline"));
    }

    #[test]
    fn publication_rejects_unsafe_paths_and_preserves_existing_source() {
        let base = std::path::PathBuf::from(format!(
            ".lean-native-publish-test-{}-{}",
            std::process::id(),
            super::NEXT_TEMP.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        ));
        fs::create_dir(&base).unwrap();
        let path = base.join("generated.rs");
        // Absolute paths are never accepted.
        let absolute = std::env::current_dir().unwrap().join(&path);
        assert!(publish(absolute.to_str().unwrap(), "fn main() {}").is_err());
        assert!(publish("../escape.rs", "x").is_err());
        assert!(publish("anything.txt", "x").is_err());
        fs::write(&path, "existing").unwrap();
        assert!(publish(
            path.to_str().unwrap(),
            &"x".repeat(super::MAX_OUTPUT_BYTES + 1)
        )
        .is_err());
        assert_eq!(fs::read_to_string(&path).unwrap(), "existing");
        publish(path.to_str().unwrap(), "replacement").unwrap();
        assert_eq!(fs::read_to_string(&path).unwrap(), "replacement");
        fs::remove_dir_all(base).unwrap();
    }
}
