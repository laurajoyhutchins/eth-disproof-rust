#![forbid(unsafe_code)]
// Paired, alternating, checksum-checked process timing. Startup is included.
use std::env;
use std::fs;
use std::path::Path;
use std::process::Command;
use std::time::Instant;

fn run(path: &Path, workload: &str, iterations: &str, expected: &[u8]) -> Result<u128, String> {
    let started = Instant::now();
    let output = Command::new(path)
        .arg(workload)
        .arg(iterations)
        .output()
        .map_err(|e| format!("launch {}: {e}", path.display()))?;
    let elapsed = started.elapsed().as_nanos();
    if !output.status.success() {
        return Err(format!(
            "{} {} {} returned {}: {}",
            path.display(), workload, iterations, output.status,
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    if output.stdout != expected {
        return Err(format!(
            "{} {} {} mismatched original C/Rust parity oracle: expected {:?}, observed {:?}",
            path.display(), workload, iterations,
            String::from_utf8_lossy(expected),
            String::from_utf8_lossy(&output.stdout)
        ));
    }
    Ok(elapsed)
}

fn median(values: &mut [u128]) -> u128 {
    values.sort_unstable();
    values[values.len() / 2]
}

fn main() -> Result<(), String> {
    let args: Vec<_> = env::args_os().collect();
    if args.len() != 6 {
        return Err("usage: bench_matrix_subprocess LEAN_C RUST WORKLOAD COUNT EXPECTED_FILE".into());
    }
    let lean = Path::new(&args[1]);
    let rust = Path::new(&args[2]);
    let kind = args[3].to_string_lossy();
    let count = args[4].to_string_lossy();
    let expected = fs::read(&args[5]).map_err(|e| format!("read expected output: {e}"))?;
    if expected.is_empty() || !expected.iter().all(|x| x.is_ascii_digit() || *x == b'\n') {
        return Err("expected output must be a nonempty decimal checksum".into());
    }
    // Prime both binaries once; neither warmup enters the measured samples.
    run(lean, &kind, &count, &expected)?;
    run(rust, &kind, &count, &expected)?;
    let mut c_samples = Vec::new();
    let mut r_samples = Vec::new();
    println!("workload\tcount\ttrial\tbackend\telapsed_ns");
    for trial in 0..12 {
        let order = if trial % 2 == 0 {
            [("lean-c", lean), ("lean-rust", rust)]
        } else {
            [("lean-rust", rust), ("lean-c", lean)]
        };
        for (name, executable) in order {
            let elapsed = run(executable, &kind, &count, &expected)?;
            println!("{kind}\t{count}\t{trial}\t{name}\t{elapsed}");
            if name == "lean-c" {
                c_samples.push(elapsed);
            } else {
                r_samples.push(elapsed);
            }
        }
    }
    eprintln!(
        "workload={kind} count={count} lean_c_median_ns={} lean_rust_median_ns={} samples=12 scope=warm_subprocess_start_to_checked_exit",
        median(&mut c_samples),
        median(&mut r_samples)
    );
    Ok(())
}
