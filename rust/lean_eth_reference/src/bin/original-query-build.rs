//! Reproducible, stage-scoped original Lean QueryStream dependency builder.
//!
//! This builds *the original pinned Lean modules*, not a Rust substitute or a
//! source graph. A stage is accepted only after Lake succeeds, the module's
//! .olean exists, and a fresh Lean process imports it without errors.
//! Unfinished Lake dependencies may be cached, but never grant acceptance.
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::ffi::OsStr;
use std::fs::{self, File};
use std::io::{self, BufRead, BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

const SOURCE_SHA: &str = "4eaee87548250b2682affda7d05d947c05554bae";
const MATHLIB_SHA: &str = "d13f23b723b8a846827a245b89c10fc7d3f11612";
const TOOLCHAIN: &str = "leanprover/lean4:v4.34.1";
const MODULE_PREFIX: &str = "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.";
const SOURCE_PREFIX: &str = "lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/";

const STAGES: [(&str, &str); 7] = [
    ("signature", "SignatureTupleCommand"),
    ("pairs", "DifferencePairsSpace"),
    ("layout", "NativeLayoutLoad"),
    ("head", "SignatureHeadLoader"),
    ("finish", "QueryNodeFinish"),
    ("reconstruction", "QueryReconstruction"),
    ("query", "QueryStreamProgram"),
];

#[derive(Debug)]
struct Options {
    upstream: PathBuf,
    lake_root: PathBuf,
    output_dir: PathBuf,
    stage: String,
    timeout_secs: u64,
    max_jobs: u8,
}

fn options(args: impl IntoIterator<Item = String>) -> Result<Option<Options>, String> {
    let mut parts = args.into_iter();
    let mut upstream = None;
    let mut lake_root = None;
    let mut output_dir = None;
    let mut stage = None;
    let mut timeout_secs = 1800u64;
    let mut max_jobs = 4u8;
    while let Some(flag) = parts.next() {
        if flag == "--list-stages" {
            println!(
                "{}",
                serde_json::to_string_pretty(
                    &STAGES
                        .iter()
                        .map(|(name, module)| {
                            json!({"stage": name, "module": format!("{MODULE_PREFIX}{module}")})
                        })
                        .collect::<Vec<_>>()
                )
                .map_err(|e| e.to_string())?
            );
            return Ok(None);
        }
        let value = parts
            .next()
            .ok_or_else(|| format!("{flag} needs a value"))?;
        match flag.as_str() {
            "--upstream" => upstream = Some(PathBuf::from(value)),
            "--lake-root" => lake_root = Some(PathBuf::from(value)),
            "--output-dir" => output_dir = Some(PathBuf::from(value)),
            "--stage" => stage = Some(value),
            "--timeout-seconds" => {
                timeout_secs = value.parse().map_err(|_| "invalid timeout")?;
            }
            "--max-jobs" => max_jobs = value.parse().map_err(|_| "invalid max-jobs")?,
            _ => return Err(format!("unknown option: {flag}")),
        }
    }
    let stage = stage.ok_or("missing --stage")?;
    if !STAGES.iter().any(|(name, _)| *name == stage) {
        return Err(format!("unsupported original module stage: {stage}"));
    }
    if !(60..=3600).contains(&timeout_secs) || !(1..=8).contains(&max_jobs) {
        return Err("timeout must be 60..=3600 seconds and max-jobs 1..=8".into());
    }
    Ok(Some(Options {
        upstream: upstream.ok_or("missing --upstream")?,
        lake_root: lake_root.ok_or("missing --lake-root")?,
        output_dir: output_dir.ok_or("missing --output-dir")?,
        stage,
        timeout_secs,
        max_jobs,
    }))
}

fn command_text(mut command: Command) -> Result<String, String> {
    let out = command.output().map_err(|e| e.to_string())?;
    if !out.status.success() {
        return Err(format!(
            "command exited {}: {}",
            out.status,
            String::from_utf8_lossy(&out.stderr).chars().take(1500).collect::<String>()
        ));
    }
    Ok(String::from_utf8(out.stdout)
        .map_err(|e| e.to_string())?
        .trim()
        .to_owned())
}

fn git(repo: &Path, args: &[&str]) -> Result<String, String> {
    let mut cmd = Command::new("git");
    cmd.arg("-C").arg(repo).args(args);
    command_text(cmd)
}

fn sha256_file(path: &Path) -> Result<String, String> {
    let mut file = File::open(path).map_err(|e| e.to_string())?;
    let mut hasher = Sha256::new();
    let mut buffer = [0u8; 64 * 1024];
    loop {
        let len = file.read(&mut buffer).map_err(|e| e.to_string())?;
        if len == 0 {
            break;
        }
        hasher.update(&buffer[..len]);
    }
    Ok(format!("{:x}", hasher.finalize()))
}

fn atomic_json(path: &Path, data: &Value) -> Result<(), String> {
    let tmp = path.with_extension("json.tmp");
    fs::write(
        &tmp,
        format!(
            "{}\n",
            serde_json::to_string_pretty(data).map_err(|e| e.to_string())?
        ),
    )
    .map_err(|e| e.to_string())?;
    fs::rename(tmp, path).map_err(|e| e.to_string())
}

fn count_oleans(root: &Path) -> Result<u64, String> {
    if !root.exists() {
        return Ok(0);
    }
    let mut count = 0u64;
    let mut pending = vec![root.to_path_buf()];
    while let Some(dir) = pending.pop() {
        for entry in fs::read_dir(dir).map_err(|e| e.to_string())? {
            let entry = entry.map_err(|e| e.to_string())?;
            let ty = entry.file_type().map_err(|e| e.to_string())?;
            if ty.is_dir() {
                pending.push(entry.path());
            } else if ty.is_file() && entry.path().extension() == Some(OsStr::new("olean")) {
                count += 1;
            }
        }
    }
    Ok(count)
}

fn check_pins(opts: &Options, leaf: &str) -> Result<(String, String), String> {
    let original = opts.upstream.canonicalize().map_err(|e| e.to_string())?;
    let lake = opts.lake_root.canonicalize().map_err(|e| e.to_string())?;
    if git(&original, &["rev-parse", "HEAD"])? != SOURCE_SHA {
        return Err("original OpenAI source Git revision mismatch".into());
    }
    if !git(
        &original,
        &[
            "status",
            "--porcelain",
            "--untracked-files=no",
            "--",
            "lean/OAI/Algorithms/SubexponentialSAT",
        ],
    )?
    .is_empty()
    {
        return Err("original OpenAI source is modified".into());
    }
    let original_oai = original.join("lean/OAI").canonicalize().map_err(|e| e.to_string())?;
    let linked_oai = lake.join("OAI").canonicalize().map_err(|e| e.to_string())?;
    if original_oai != linked_oai {
        return Err("Lake environment OAI path is not the pinned original checkout".into());
    }
    let expected_toolchain =
        fs::read_to_string(lake.join("lean-toolchain")).map_err(|e| e.to_string())?;
    if expected_toolchain.trim() != TOOLCHAIN {
        return Err("Lean toolchain does not match original 4.34.1".into());
    }
    let mathlib = lake.join(".lake/packages/mathlib");
    if git(&mathlib, &["rev-parse", "HEAD"])? != MATHLIB_SHA {
        return Err("Mathlib Git revision mismatch".into());
    }
    let mut version_cmd = Command::new("lake");
    version_cmd
        .current_dir(&lake)
        .env_remove("LEAN_PATH")
        .env_remove("LEAN_SRC_PATH")
        .args(["env", "lean", "--version"]);
    let lean_version = command_text(version_cmd)?;
    if !lean_version.starts_with("Lean (version 4.34.1,") {
        return Err(format!("wrong Lean compiler version: {lean_version}"));
    }
    let path = format!("{SOURCE_PREFIX}{leaf}.lean");
    let current_blob = git(&original, &["hash-object", &path])?;
    let committed_blob = git(&original, &["rev-parse", &format!("HEAD:{path}")])?;
    if current_blob != committed_blob {
        return Err(format!("original source blob changed: {path}"));
    }
    Ok((lean_version, current_blob))
}

fn relay(
    input: impl Read + Send + 'static,
    label: &'static str,
    logfile: Arc<Mutex<File>>,
) -> thread::JoinHandle<Result<(), String>> {
    thread::spawn(move || {
        for line in BufReader::new(input).lines() {
            let line = line.map_err(|e| e.to_string())?;
            eprintln!("[lake:{label}] {line}");
            let mut log = logfile.lock().map_err(|e| e.to_string())?;
            writeln!(&mut *log, "[{label}] {line}").map_err(|e| e.to_string())?;
        }
        Ok(())
    })
}

fn execute_logged(
    mut cmd: Command,
    log_path: &Path,
    olean_root: &Path,
) -> Result<(), String> {
    let logfile = Arc::new(Mutex::new(File::create(log_path).map_err(|e| e.to_string())?));
    cmd.stdout(Stdio::piped()).stderr(Stdio::piped());
    let mut child = cmd.spawn().map_err(|e| e.to_string())?;
    let stdout = relay(
        child.stdout.take().ok_or("missing child stdout")?,
        "stdout",
        Arc::clone(&logfile),
    );
    let stderr = relay(
        child.stderr.take().ok_or("missing child stderr")?,
        "stderr",
        Arc::clone(&logfile),
    );
    let started = Instant::now();
    let mut last_progress = 0;
    let status = loop {
        if let Some(status) = child.try_wait().map_err(|e| e.to_string())? {
            break status;
        }
        thread::sleep(Duration::from_secs(2));
        let elapsed = started.elapsed().as_secs();
        if elapsed >= last_progress + 60 {
            let count = count_oleans(olean_root)?;
            eprintln!(
                "ORIGINAL_LEAN_BUILD_PROGRESS elapsed={}s completed_oleans={count}",
                elapsed
            );
            last_progress = elapsed;
        }
    };
    stdout.join().map_err(|_| "stdout relay thread panicked")??;
    stderr.join().map_err(|_| "stderr relay thread panicked")??;
    if !status.success() {
        return Err(format!(
            "original Lean build/import failed with {status}; see {}",
            log_path.display()
        ));
    }
    Ok(())
}

fn execute(opts: &Options) -> Result<Value, String> {
    let leaf = STAGES
        .iter()
        .find(|(name, _)| *name == opts.stage)
        .ok_or("invalid stage")?
        .1;
    let module = format!("{MODULE_PREFIX}{leaf}");
    let (lean_version, source_blob) = check_pins(opts, leaf)?;
    let lake = opts.lake_root.canonicalize().map_err(|e| e.to_string())?;
    let output_root = lake.join(".lake/build/lib/lean");
    let before = count_oleans(&output_root)?;
    let log_path = opts.output_dir.join("lake-build.log");

    let mut command = Command::new("timeout");
    command
        .current_dir(&lake)
        .env_remove("LEAN_PATH")
        .env_remove("LEAN_SRC_PATH")
        .args(["--signal=TERM", "--kill-after=20s"])
        .arg(format!("{}s", opts.timeout_secs))
        .arg("lake")
        .args(["-K", &format!("maxJobs={}", opts.max_jobs), "build", &module]);
    let start = Instant::now();
    execute_logged(command, &log_path, &output_root)?;
    let artifact = output_root.join(format!("{}.olean", module.replace('.', "/")));
    if !artifact.is_file() {
        return Err(format!("Lake reported success without {}.olean", module));
    }

    // This is an independent import in a fresh Lean process, not just trust
    // in Lake's return code or a restored cache filename.
    let smoke = opts.output_dir.join("import-check.lean");
    fs::write(&smoke, format!("import {module}\n")).map_err(|e| e.to_string())?;
    let mut import = Command::new("timeout");
    import
        .current_dir(&lake)
        .env_remove("LEAN_PATH")
        .env_remove("LEAN_SRC_PATH")
        .args(["--signal=TERM", "--kill-after=10s", "120s", "lake", "env", "lean"])
        .arg(&smoke);
    execute_logged(
        import,
        &opts.output_dir.join("lean-import.log"),
        &output_root,
    )?;
    let after = count_oleans(&output_root)?;
    let observed_revision = git(&opts.upstream, &["rev-parse", "HEAD"])?;
    if observed_revision != SOURCE_SHA {
        return Err("source revision moved while building".into());
    }
    Ok(json!({
        "status": "PINNED_ORIGINAL_LEAN_IMPORT_VERIFIED",
        "stage": opts.stage,
        "module": module,
        "source_commit": SOURCE_SHA,
        "source_git_blob": source_blob,
        "mathlib_commit": MATHLIB_SHA,
        "lean_toolchain": TOOLCHAIN,
        "lean_version": lean_version,
        "module_olean_sha256": sha256_file(&artifact)?,
        "olean_count_before": before,
        "olean_count_after": after,
        "elapsed_seconds": start.elapsed().as_secs(),
        "query_stream_executable": false,
        "source_graph_compiled": false,
        "independent_lean_rust_parity": false,
        "math_or_resource_theorem": false
    }))
}

fn run() -> Result<(), String> {
    let Some(opts) = options(std::env::args().skip(1))? else {
        return Ok(());
    };
    fs::create_dir_all(&opts.output_dir).map_err(|e| e.to_string())?;
    let receipt_path = opts.output_dir.join("stage.receipt.json");
    let report_path = opts.output_dir.join("stage.report.json");
    // Publication is fail closed even if this is a rerun in an old directory.
    match fs::remove_file(&receipt_path) {
        Ok(()) => {}
        Err(e) if e.kind() == io::ErrorKind::NotFound => {}
        Err(e) => return Err(e.to_string()),
    }
    let result = execute(&opts);
    match result {
        Ok(receipt) => {
            atomic_json(&report_path, &receipt)?;
            atomic_json(&receipt_path, &receipt)?;
            println!(
                "ORIGINAL_LEAN_STAGE_IMPORTED stage={} receipt={}",
                opts.stage,
                receipt_path.display()
            );
            Ok(())
        }
        Err(reason) => {
            let report = json!({
                "status": "REFUSED",
                "stage": opts.stage,
                "reason": reason,
                "original_source_pin": SOURCE_SHA,
                "source_graph_compiled": false,
                "query_stream_executable": false,
                "independent_lean_rust_parity": false
            });
            atomic_json(&report_path, &report)?;
            Err(reason)
        }
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("ORIGINAL_LEAN_STAGE_REFUSED: {error}");
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::{STAGES, TOOLCHAIN, options};
    #[test]
    fn stage_names_are_unique_and_query_is_last() {
        assert_eq!(STAGES.len(), 7);
        assert_eq!(STAGES.last().unwrap().0, "query");
        for (i, (name, module)) in STAGES.iter().enumerate() {
            assert!(!name.is_empty());
            assert!(!module.is_empty());
            assert!(STAGES[..i].iter().all(|(prior, _)| prior != name));
        }
        assert_eq!(TOOLCHAIN, "leanprover/lean4:v4.34.1");
    }
    #[test]
    fn refuses_unknown_stage_and_invalid_limits() {
        let valid = [
            "--upstream", "/tmp/source",
            "--lake-root", "/tmp/lake",
            "--output-dir", "/tmp/out",
            "--stage", "signature",
        ];
        assert!(options(valid.map(str::to_owned)).unwrap().is_some());
        let invalid = ["--stage", "faked", "--upstream", "/tmp/a", "--lake-root", "/tmp/b", "--output-dir", "/tmp/c"];
        assert!(options(invalid.map(str::to_owned)).is_err());
        let limited = ["--timeout-seconds", "9", "--stage", "query", "--upstream", "/tmp/a", "--lake-root", "/tmp/b", "--output-dir", "/tmp/c"];
        assert!(options(limited.map(str::to_owned)).is_err());
    }
}
