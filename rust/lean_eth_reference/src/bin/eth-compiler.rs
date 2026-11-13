//! Lean frontend + Rust acceptance gate. Neither backend is an executable ETH proof.
use lean_eth_reference::lean_codegen as contract;

use contract::{Backend, Result, ensure, refuse};
use serde_json::{Value, json};
use std::env;
use std::fs::{self, File};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, Instant, SystemTime};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mode {
    Compile,
    Verify,
}
#[derive(Debug)]
struct Options {
    mode: Mode,
    backend: Backend,
    module: String,
    roots: Vec<String>,
    lake_root: PathBuf,
    source_repo: PathBuf,
    source_path: String,
    revision: String,
    pin_path: String,
    producer: Option<PathBuf>,
    artifact: PathBuf,
    receipt: PathBuf,
    backend_report: Option<PathBuf>,
    timeout: Duration,
    lake_bin: String,
}
impl Options {
    fn parse(arguments: &[String]) -> Result<Self> {
        let Some((command, options)) = arguments.split_first() else {
            return refuse(
                "usage: eth-compiler compile|verify --backend compiler-ir|residual-expr ...",
            );
        };
        let mode = match command.as_str() {
            "compile" => Mode::Compile,
            "verify" => Mode::Verify,
            _ => return refuse("expected compile or verify command"),
        };
        let mut values = std::collections::HashMap::<&str, String>::new();
        let mut roots = Vec::new();
        let mut it = options.iter();
        while let Some(flag) = it.next() {
            ensure(flag.starts_with("--"), "expected --option")?;
            let name = flag.as_str();
            ensure(
                matches!(
                    name,
                    "--backend"
                        | "--module"
                        | "--root"
                        | "--lake-root"
                        | "--source-repo"
                        | "--source-path"
                        | "--source-revision"
                        | "--source-toolchain-path"
                        | "--producer"
                        | "--artifact"
                        | "--output"
                        | "--receipt"
                        | "--backend-report"
                        | "--timeout-seconds"
                        | "--lake-bin"
                ),
                format!("unrecognized compiler option: {flag}"),
            )?;
            let val = it
                .next()
                .ok_or_else(|| format!("missing argument for {flag}"))?;
            if name == "--root" {
                roots.push(val.clone());
            } else {
                ensure(
                    values.insert(name, val.clone()).is_none(),
                    format!("duplicate option: {flag}"),
                )?;
            }
        }
        let required = |k| values.get(k).cloned().ok_or_else(|| format!("missing {k}"));
        let backend = Backend::parse(&required("--backend")?)?;
        let module = required("--module")?;
        let source_repo = PathBuf::from(required("--source-repo")?);
        let source_path = required("--source-path")?;
        let revision = required("--source-revision")?;
        let receipt = PathBuf::from(required("--receipt")?);
        let artifact = match mode {
            Mode::Compile => PathBuf::from(required("--output")?),
            Mode::Verify => PathBuf::from(required("--artifact")?),
        };
        let lake_root = PathBuf::from(
            values
                .get("--lake-root")
                .cloned()
                .unwrap_or_else(|| source_repo.to_string_lossy().into_owned()),
        );
        let pin_path = values
            .get("--source-toolchain-path")
            .cloned()
            .unwrap_or_else(|| "lean-toolchain".into());
        let producer = values.get("--producer").map(PathBuf::from);
        let backend_report = values.get("--backend-report").map(PathBuf::from);
        let timeout = values.get("--timeout-seconds").map_or(Ok(300u64), |x| {
            x.parse::<u64>().map_err(|_| "invalid timeout".to_string())
        })?;
        ensure(
            (1..=3600).contains(&timeout),
            "timeout outside 1..3600 seconds",
        )?;
        ensure(
            contract::declaration(&module)
                && !roots.is_empty()
                && roots.iter().all(|r| contract::declaration(r)),
            "invalid Lean declaration name",
        )?;
        ensure(
            artifact != receipt,
            "artifact and receipt must be different paths",
        )?;
        ensure(
            !(mode == Mode::Verify && producer.is_some()),
            "verify cannot run a Lean producer",
        )?;
        ensure(
            !(mode == Mode::Compile && backend_report.is_some()),
            "compile writes its own backend receipt",
        )?;
        Ok(Self {
            mode,
            backend,
            module,
            roots,
            lake_root,
            source_repo,
            source_path,
            revision,
            pin_path,
            producer,
            artifact,
            receipt,
            backend_report,
            timeout: Duration::from_secs(timeout),
            lake_bin: values
                .get("--lake-bin")
                .cloned()
                .unwrap_or_else(|| "lake".into()),
        })
    }
}

struct Stage(PathBuf);
impl Stage {
    fn new(parent: &Path) -> Result<Self> {
        fs::create_dir_all(parent).map_err(|e| e.to_string())?;
        for n in 0..20 {
            let tick = SystemTime::now()
                .duration_since(SystemTime::UNIX_EPOCH)
                .map_err(|e| e.to_string())?
                .as_nanos();
            let dir = parent.join(format!(".eth-codegen-{}-{tick}-{n}", std::process::id()));
            match fs::create_dir(&dir) {
                Ok(()) => return Ok(Stage(dir)),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {}
                Err(e) => return Err(e.to_string()),
            }
        }
        refuse("cannot allocate unique codegen staging directory")
    }
}
impl Drop for Stage {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn read_bounded(path: &Path) -> Result<Vec<u8>> {
    let meta = fs::metadata(path).map_err(|e| e.to_string())?;
    ensure(
        meta.len() <= 8 * 1024 * 1024,
        "artifact exceeds 8 MiB limit",
    )?;
    fs::read(path).map_err(|e| e.to_string())
}
fn run_command(opts: &Options, work: &Path, label: &str, args: &[&str]) -> Result<Vec<u8>> {
    let stdout = work.join(format!("{label}.stdout"));
    let stderr = work.join(format!("{label}.stderr"));
    let mut child = Command::new(&opts.lake_bin)
        .current_dir(&opts.lake_root)
        .args(args)
        .stdout(Stdio::from(
            File::create(&stdout).map_err(|e| e.to_string())?,
        ))
        .stderr(Stdio::from(
            File::create(&stderr).map_err(|e| e.to_string())?,
        ))
        .spawn()
        .map_err(|e| format!("Lean command {label} unavailable: {e}"))?;
    let started = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().map_err(|e| e.to_string())? {
            break status;
        }
        if started.elapsed() >= opts.timeout {
            let _ = child.kill();
            let _ = child.wait();
            return refuse(format!("Lean command {label} timed out"));
        }
        thread::sleep(Duration::from_millis(25));
    };
    let err = read_bounded(&stderr)?;
    ensure(
        status.success(),
        format!(
            "Lean command {label} refused: {}",
            String::from_utf8_lossy(&err)
        ),
    )?;
    read_bounded(&stdout)
}
fn text(bytes: Vec<u8>) -> Result<String> {
    String::from_utf8(bytes)
        .map(|v| v.trim().to_owned())
        .map_err(|e| e.to_string())
}
fn observed_version(opts: &Options, work: &Path, pin: &str) -> Result<String> {
    let version = text(run_command(
        opts,
        work,
        "lean-version",
        &["env", "lean", "--version"],
    )?)?;
    ensure(
        contract::version_matches(&version, pin),
        format!("actual Lean version does not match source toolchain: {version}"),
    )?;
    Ok(version)
}
fn pinned_lake(opts: &Options, expected: &str) -> Result<()> {
    let pin = fs::read_to_string(opts.lake_root.join("lean-toolchain"))
        .map_err(|e| format!("missing Lake toolchain pin: {e}"))?;
    ensure(
        pin.trim() == expected,
        "Lake toolchain differs from source pin",
    )
}
fn symbolic(opts: &Options, stage: &Stage) -> Result<(Vec<u8>, String)> {
    ensure(
        opts.roots.len() == 1,
        "residual Expr path requires exactly one root",
    )?;
    let producer = opts
        .producer
        .as_ref()
        .ok_or("missing --producer for residual Expr")?;
    let raw = read_bounded(producer)?;
    let source = std::str::from_utf8(&raw).map_err(|e| e.to_string())?;
    ensure(
        source.starts_with("import Lean\n"),
        "symbolic producer must import Lean first",
    )?;
    let driver = stage.0.join("ResidueDriver.lean");
    // Insert an actual Lean module import; no Rust replacement of its computation.
    fs::write(
        &driver,
        format!(
            "import Lean\nimport {}\n{}\n#export_residual_graph {}\n",
            opts.module,
            &source["import Lean\n".len()..],
            opts.roots[0]
        ),
    )
    .map_err(|e| e.to_string())?;
    let path = driver.to_str().ok_or("non-UTF-8 Lean driver path")?;
    let result = run_command(opts, &stage.0, "residual", &["env", "lean", path])?;
    Ok((result, contract::digest(&raw)))
}
fn compiler_ir(
    opts: &Options,
    stage: &Stage,
    pin: &str,
    lean_version: &str,
) -> Result<(Vec<u8>, Vec<u8>)> {
    // leanfran 0.6.0 currently requires 4.35.0, independent of the ETH 4.34.1 pin.
    ensure(
        pin == "leanprover/lean4:v4.35.0",
        "leanfran 0.6.0 incompatible with pinned source Lean; no silent upgrade",
    )?;
    let backend = text(run_command(
        opts,
        &stage.0,
        "backend-version",
        &["env", "leanfran", "--version"],
    )?)?;
    ensure(backend == "leanfran 0.6.0", "unexpected leanfran version")?;
    let generator = text(run_command(
        opts,
        &stage.0,
        "generator-version",
        &["env", "leanfran", "--generator-version"],
    )?)?;
    ensure(generator == "4", "unexpected leanfran generator version")?;
    let target = stage.0.join("generated.rs");
    let target_path = target.to_str().ok_or("non-UTF-8 staged artifact path")?;
    let mut args = vec![
        "env",
        "leanfran",
        "module",
        "generate",
        "--module-name",
        &opts.module,
        "--roots",
    ];
    for root in &opts.roots {
        args.push(root);
    }
    args.extend(["--output-file", target_path, "--output", "json"]);
    let summary_raw = run_command(opts, &stage.0, "leanfran", &args)?;
    let summary = contract::strict_json_value(&summary_raw)?;
    let artifact = read_bounded(&target)?;
    let report = contract::ir_report(
        &opts.module,
        &opts.roots,
        contract::IrVersions {
            toolchain: pin,
            lean: lean_version,
            backend: &backend,
            generator: &generator,
        },
        &artifact,
        summary,
    );
    let receipt = serde_json::to_vec(&report).map_err(|e| e.to_string())?;
    Ok((artifact, receipt))
}
fn write_receipt(stage: &Stage, destination: &Path, receipt: &Value) -> Result<()> {
    let staged = stage.0.join("accepted-receipt.json");
    fs::write(
        &staged,
        format!(
            "{}\n",
            serde_json::to_string_pretty(receipt).map_err(|e| e.to_string())?
        ),
    )
    .map_err(|e| e.to_string())?;
    if let Some(parent) = destination.parent() {
        fs::create_dir_all(parent).map_err(|e| e.to_string())?;
    }
    fs::rename(staged, destination).map_err(|e| e.to_string())
}

fn execute(opts: &Options) -> Result<()> {
    // Invalidate a previous acceptance BEFORE doing any fallible work.
    if opts.receipt.exists() {
        fs::remove_file(&opts.receipt).map_err(|e| e.to_string())?;
    }
    let source = contract::source_identity(
        &opts.source_repo,
        &opts.source_path,
        &opts.pin_path,
        &opts.revision,
    )?;
    let parent = opts
        .artifact
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let stage = Stage::new(parent)?;
    let (artifact, backend_report, actual_version, producer_hash) = match opts.mode {
        Mode::Verify => {
            let artifact = read_bounded(&opts.artifact)?;
            let report = match &opts.backend_report {
                Some(p) => Some(read_bounded(p)?),
                None => None,
            };
            (artifact, report, None, None)
        }
        Mode::Compile => {
            pinned_lake(opts, &source.lean_toolchain)?;
            let actual = observed_version(opts, &stage.0, &source.lean_toolchain)?;
            match opts.backend {
                Backend::CompilerIr => {
                    let (artifact, report) =
                        compiler_ir(opts, &stage, &source.lean_toolchain, &actual)?;
                    (artifact, Some(report), Some(actual), None)
                }
                Backend::ResidualExpr => {
                    let (artifact, hash) = symbolic(opts, &stage)?;
                    (artifact, None, Some(actual), Some(hash))
                }
            }
        }
    };
    let now = contract::source_identity(
        &opts.source_repo,
        &opts.source_path,
        &opts.pin_path,
        &opts.revision,
    )?;
    ensure(now == source, "source changed during compilation")?;
    if opts.mode == Mode::Compile {
        pinned_lake(opts, &source.lean_toolchain)?;
    }
    let mut receipt = contract::validate(
        opts.backend,
        &artifact,
        backend_report.as_deref(),
        &opts.module,
        &opts.roots,
        &source,
    )?;
    if let Some(version) = actual_version {
        receipt["actual_lean_version"] = json!(version);
        if opts.backend == Backend::ResidualExpr {
            receipt["checks"]["residual_actual_lean_version"] = json!("launcher-observed");
        }
    }
    if let Some(hash) = producer_hash {
        receipt["producer_sha256"] = json!(hash);
    }
    if opts.mode == Mode::Compile {
        let staged = stage.0.join("accepted-artifact");
        fs::write(&staged, artifact).map_err(|e| e.to_string())?;
        if let Some(parent) = opts.artifact.parent().filter(|p| !p.as_os_str().is_empty()) {
            fs::create_dir_all(parent).map_err(|e| e.to_string())?;
        }
        fs::rename(staged, &opts.artifact).map_err(|e| e.to_string())?;
    }
    write_receipt(&stage, &opts.receipt, &receipt)?;
    Ok(())
}

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    let opts = Options::parse(&args);
    let result = match &opts {
        Ok(value) => execute(value),
        Err(error) => Err(error.clone()),
    };
    match result {
        Ok(()) => {
            println!("Lean artifact checked; Rust execution and semantic parity NOT established")
        }
        Err(error) => {
            if let Ok(value) = &opts {
                let _ = fs::remove_file(&value.receipt);
            }
            eprintln!("eth-compiler refused: {error}");
            std::process::exit(2);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn parses_backend_root_and_mode() {
        let args = [
            "verify",
            "--backend",
            "residual-expr",
            "--module",
            "Demo",
            "--root",
            "Demo.f",
            "--source-repo",
            "/tmp/src",
            "--source-path",
            "Demo.lean",
            "--source-revision",
            "a",
            "--artifact",
            "/tmp/a",
            "--receipt",
            "/tmp/r",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect::<Vec<_>>();
        let o = Options::parse(&args).unwrap();
        assert_eq!(o.backend, Backend::ResidualExpr);
        assert_eq!(o.mode, Mode::Verify);
    }
    #[test]
    fn invalid_cli_flags_fail_closed() {
        let args = ["verify", "--backend", "compiler-ir", "--bogus", "true"]
            .iter()
            .map(|s| s.to_string())
            .collect::<Vec<_>>();
        assert!(Options::parse(&args).is_err());
    }
    #[test]
    fn no_silent_backend_substitution() {
        assert!(Backend::parse("auto").is_err());
    }
}
