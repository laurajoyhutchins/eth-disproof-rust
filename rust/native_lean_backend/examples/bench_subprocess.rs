#![forbid(unsafe_code)]
// High-resolution subprocess benchmark for matching original-Lean-C and
// extracted-Rust binaries. Every sample independently verifies stdout.
use std::env;
use std::fs;
use std::path::Path;
use std::process::Command;
use std::time::Instant;

fn observed_ns(path: &Path, expected: &[u8]) -> Result<u128, String> {
    let started = Instant::now();
    let output = Command::new(path)
        .output()
        .map_err(|err| format!("failed to launch {}: {err}", path.display()))?;
    let ns = started.elapsed().as_nanos();
    if !output.status.success() {
        return Err(format!(
            "{} failed: {}",
            path.display(),
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    if output.stdout != expected {
        return Err(format!(
            "{} checksum mismatch: expected {:?}, got {:?}",
            path.display(),
            String::from_utf8_lossy(expected),
            String::from_utf8_lossy(&output.stdout)
        ));
    }
    Ok(ns)
}

fn median(samples: &mut [u128]) -> u128 {
    samples.sort_unstable();
    let n = samples.len();
    if n % 2 == 0 {
        samples[n / 2 - 1] / 2 + samples[n / 2] / 2
            + (samples[n / 2 - 1] % 2 + samples[n / 2] % 2) / 2
    } else {
        samples[n / 2]
    }
}

fn main() -> Result<(), String> {
    let args: Vec<_> = env::args_os().collect();
    if args.len() != 4 {
        return Err("usage: bench_subprocess LEAN_BINARY RUST_BINARY EXPECTED_OUTPUT_FILE".into());
    }
    let lean = Path::new(&args[1]);
    let rust = Path::new(&args[2]);
    let expected = fs::read(Path::new(&args[3])).map_err(|e| format!("read oracle: {e}"))?;
    if expected.is_empty() || !expected.iter().all(|b| b.is_ascii_digit() || *b == b'\n') {
        return Err("expected stdout must contain a nonempty numeric checksum".into());
    }

    let mut lean_ns = Vec::new();
    let mut rust_ns = Vec::new();
    println!("trial\tbackend\telapsed_ns");
    for trial in 0..30 {
        // Alternate order, reducing systematic cache/frequency drift.
        let order = if trial % 2 == 0 {
            [("lean-native", lean), ("rust-native", rust)]
        } else {
            [("rust-native", rust), ("lean-native", lean)]
        };
        for (name, path) in order {
            let ns = observed_ns(path, &expected)?;
            println!("{trial}\t{name}\t{ns}");
            if name == "lean-native" {
                lean_ns.push(ns);
            } else {
                rust_ns.push(ns);
            }
        }
    }
    eprintln!("samples_per_backend=30");
    eprintln!("lean_native_median_ns={}", median(&mut lean_ns));
    eprintln!("rust_native_median_ns={}", median(&mut rust_ns));
    eprintln!("measurement_scope=subprocess_start_to_checked_exit");
    eprintln!("warning=hosted_runner_uncontrolled_cache_and_frequency");
    Ok(())
}
