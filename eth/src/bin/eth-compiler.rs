//! One compiler acceptance interface: native Lean IR or a non-executable residual Expr.\n//! The canonical in-process code generator lives in rust/native_lean_backend.
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
            !(mode == Mode::Compile && backend == Backend::CompilerIr && producer.is_some()),
            "native executable-IR backend cannot use a symbolic producer",
        )?;
        ensure(
            artifact != receipt
                && !(backend == Backend::CompilerIr && receipt.starts_with(&artifact)),
            "receipt must be outside the native Cargo package",
        )?;
        ensure(
            !(mode == Mode::Verify && producer.is_some()),
            "verify cannot run a Lean producer",
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
fn run_process(
    work: &Path,
    label: &str,
    program: &str,
    current_dir: &Path,
    args: &[&str],
    timeout: Duration,
    native_budget: Option<u64>,
) -> Result<Vec<u8>> {
    let stdout = work.join(format!("{label}.stdout"));
    let stderr = work.join(format!("{label}.stderr"));
    let mut command = Command::new(program);
    command
        .current_dir(current_dir)
        .args(args)
        .stdout(Stdio::from(
            File::create(&stdout).map_err(|e| e.to_string())?,
        ))
        .stderr(Stdio::from(
            File::create(&stderr).map_err(|e| e.to_string())?,
        ));
    if let Some(budget) = native_budget {
        command.env("NATIVE_PROJECT_TIMEOUT_SECONDS", budget.to_string());
    }
    // A timed-out Lake/Bash launcher must not abandon Lean children that
    // continue compiling after the staging directory is removed.
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        command.process_group(0);
    }
    let mut child = command
        .spawn()
        .map_err(|e| format!("Lean command {label} unavailable: {e}"))?;
    let started = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().map_err(|e| e.to_string())? {
            break status;
        }
        if started.elapsed() >= timeout {
            #[cfg(unix)]
            {
                // process_group(0) made the launched process its own group leader.
                // Kill its descendants before cleaning the atomic staging area.
                let _ = Command::new("kill")
                    .args(["-TERM", "--"])
                    .arg(format!("-{}", child.id()))
                    .status();
            }
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
fn run_command(opts: &Options, work: &Path, label: &str, args: &[&str]) -> Result<Vec<u8>> {
    run_process(
        work,
        label,
        &opts.lake_bin,
        &opts.lake_root,
        args,
        opts.timeout,
        None,
    )
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
    source: &contract::SourceIdentity,
) -> Result<(Vec<u8>, Vec<u8>)> {
    ensure(
        pin == "leanprover/lean4:v4.34.1",
        "canonical native compiler requires original Lean 4.34.1; no upgrade/fallback",
    )?;
    ensure(
        !opts.roots.is_empty(),
        "native compiler requires at least one executable Lean root",
    )?;
    let native_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .ok_or("missing native compiler workspace parent")?
        .join("native_lean_backend")
        .canonicalize()
        .map_err(|e| format!("canonical native compiler unavailable: {e}"))?;
    ensure(
        native_root.join("scripts/compile-project.sh").is_file(),
        "canonical native compile-project.sh is unavailable",
    )?;
    // Always use the existing in-process, multi-root Lean IR compiler.
    // It builds the original Lake module, emits one deduplicated Cargo
    // package, runs Cargo tests, and publishes without overwriting.
    // No leanfran process, JSON-encoded compiler IR or independent runtime.
    let destination = stage.0.join("native-project");
    let input = opts
        .source_repo
        .join(&source.path)
        .canonicalize()
        .map_err(|e| e.to_string())?;
    let input_path = input.to_str().ok_or("non-UTF-8 Lean source path")?;
    let project = opts
        .lake_root
        .canonicalize()
        .map_err(|e| format!("missing original Lake project: {e}"))?;
    let project_path = project.to_str().ok_or("non-UTF-8 Lake project path")?;
    let destination_path = destination.to_str().ok_or("non-UTF-8 native output path")?;
    let roots = opts.roots.join(",");
    let timeout = opts
        .timeout
        .checked_mul(4)
        .ok_or("native project timeout overflow")?;
    run_process(
        &stage.0,
        "native-inprocess-ir",
        "bash",
        &native_root,
        &[
            "scripts/compile-project.sh",
            project_path,
            &opts.module,
            &roots,
            input_path,
            destination_path,
        ],
        timeout,
        Some(opts.timeout.as_secs()),
    )?;
    let artifact = read_bounded(&destination.join("src/lib.rs"))?;
    let manifest = read_bounded(&destination.join("Cargo.toml"))?;
    let native_receipt = read_bounded(&destination.join("receipt.txt"))?;
    let native_text = std::str::from_utf8(&native_receipt).map_err(|e| e.to_string())?;
    let source_hash = contract::digest(&read_bounded(&input)?);
    let report = contract::native_ir_report(contract::NativeIrProject {
        module: &opts.module,
        roots: &opts.roots,
        toolchain: pin,
        lean_version,
        source_revision: &source.git_revision,
        source_git_blob: &source.git_blob,
        source_lean_sha256: &source_hash,
        generated: &artifact,
        cargo_manifest: &manifest,
        native_project_receipt: native_text,
    });
    let raw = serde_json::to_vec(&report).map_err(|e| e.to_string())?;
    Ok((artifact, raw))
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
    // Invalidate an old compile receipt before attempting a new build.
    // Verify may read its embedded backend evidence before reissuing it.
    if opts.mode == Mode::Compile && opts.receipt.exists() {
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
            let artifact = if opts.backend == Backend::CompilerIr {
                read_bounded(&opts.artifact.join("src/lib.rs"))?
            } else {
                read_bounded(&opts.artifact)?
            };
            let report = if opts.backend == Backend::CompilerIr {
                // Validate the original acceptance receipt and the contents
                // of the complete Cargo package, not an external report.
                let prior = contract::strict_json_value(&read_bounded(&opts.receipt)?)?;
                let embedded = prior
                    .get("backend_report")
                    .ok_or("missing native backend evidence in prior receipt")?;
                Some(serde_json::to_vec(embedded).map_err(|e| e.to_string())?)
            } else {
                None
            };
            (artifact, report, None, None)
        }
        Mode::Compile => {
            pinned_lake(opts, &source.lean_toolchain)?;
            let actual = observed_version(opts, &stage.0, &source.lean_toolchain)?;
            match opts.backend {
                Backend::CompilerIr => {
                    let (artifact, report) =
                        compiler_ir(opts, &stage, &source.lean_toolchain, &actual, &source)?;
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
    if opts.backend == Backend::CompilerIr {
        let raw = backend_report
            .as_deref()
            .ok_or("missing native compiler report")?;
        let evidence = contract::strict_json_value(raw)?;
        let original_sha256 =
            contract::digest(&read_bounded(&opts.source_repo.join(&source.path))?);
        ensure(
            evidence["source_lean_sha256"] == json!(original_sha256),
            "native project was compiled from a different Git source file",
        )?;
        let project = if opts.mode == Mode::Compile {
            stage.0.join("native-project")
        } else {
            opts.artifact.clone()
        };
        let manifest_hash = contract::digest(&read_bounded(&project.join("Cargo.toml"))?);
        let original_project_receipt =
            String::from_utf8(read_bounded(&project.join("receipt.txt"))?)
                .map_err(|e| e.to_string())?;
        ensure(
            evidence["cargo_manifest_sha256"] == json!(manifest_hash)
                && evidence["native_project_receipt"] == json!(original_project_receipt),
            "Cargo package manifest or native compiler receipt changed",
        )?;
        // Source and artifact hashes are checked again on every verify;
        // the embedded report does not authorize execution or a proof claim.
        receipt["backend_report"] = evidence;
    }
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
        ensure(
            fs::symlink_metadata(&opts.artifact)
                .is_err_and(|e| e.kind() == std::io::ErrorKind::NotFound),
            "refusing to overwrite existing compiled artifact",
        )?;
        if opts.backend == Backend::CompilerIr {
            // Publish the *complete*, already compiled Cargo package.
            // A failed receipt check leaves the caller's directory untouched.
            fs::rename(stage.0.join("native-project"), &opts.artifact)
                .map_err(|e| e.to_string())?;
        } else {
            let staged = stage.0.join("accepted-artifact");
            fs::write(&staged, artifact).map_err(|e| e.to_string())?;
            fs::rename(staged, &opts.artifact).map_err(|e| e.to_string())?;
        }
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
    #[test]
    fn native_route_accepts_multiple_roots_without_backend_substitution() {
        let args = [
            "compile",
            "--backend",
            "compiler-ir",
            "--module",
            "Sample",
            "--root",
            "Sample.inc",
            "--root",
            "Sample.twice",
            "--source-repo",
            "/tmp/source",
            "--source-path",
            "Sample.lean",
            "--source-revision",
            "a",
            "--output",
            "/tmp/generated-package",
            "--receipt",
            "/tmp/generated.receipt.json",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect::<Vec<_>>();
        let opts = Options::parse(&args).unwrap();
        assert_eq!(opts.backend, Backend::CompilerIr);
        assert_eq!(opts.roots, ["Sample.inc", "Sample.twice"]);
    }
    #[test]
    fn native_route_refuses_receipt_inside_generated_package() {
        let args = [
            "compile",
            "--backend",
            "compiler-ir",
            "--module",
            "Sample",
            "--root",
            "Sample.inc",
            "--source-repo",
            "/tmp/source",
            "--source-path",
            "Sample.lean",
            "--source-revision",
            "a",
            "--output",
            "/tmp/native-package",
            "--receipt",
            "/tmp/native-package/src/lib.rs",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect::<Vec<_>>();
        assert!(Options::parse(&args).is_err());
    }
    #[test]
    fn native_route_refuses_symbolic_producer() {
        let args = [
            "compile",
            "--backend",
            "compiler-ir",
            "--module",
            "Demo",
            "--root",
            "Demo.f",
            "--source-repo",
            "/tmp/source",
            "--source-path",
            "Demo.lean",
            "--source-revision",
            "a",
            "--producer",
            "ResidualGraph.lean",
            "--output",
            "/tmp/generated-package",
            "--receipt",
            "/tmp/receipt.json",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect::<Vec<_>>();
        assert!(Options::parse(&args).is_err());
    }
}
